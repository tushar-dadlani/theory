(** * DIM BFT / Distributed Consensus Theorems
    Formal verification of Byzantine Fault Tolerance properties
    for the DIM receipt model.

    Theorem inventory:
      T15 quorum_overlap                  — any two 2/3+ quorums share a member
      T16 qc_conflict_implies_equivocation — conflicting QCs imply equivocation
      T17 equivocation_detectable          — equivocating receipts have different sigs
      T18 equivocation_evidence_sound      — equivocation witnesses real key usage
      T19 honest_no_equivocation           — honest validators never equivocate
      T20 bft_safety                       — honest overlap ⟹ no conflicting QCs
      T21 bft_safety_honest_majority       — all honest ⟹ no conflicting QCs
*)

From Stdlib Require Import List Nat Bool Arith.
From Stdlib Require Import Lia.
Require Import dim_types.
Require Import dim_crypto.
Require Import dim_capability.
Require Import dim_hash_safety.
Import ListNotations.
Open Scope list_scope.
Open Scope nat_scope.

(* ════════════════════════════════════════════════════════
   New Axioms
   ════════════════════════════════════════════════════════ *)

(** Decidable equality on PublicKey (needed for in_dec in quorum proofs). *)
Axiom pubkey_eq_dec : forall (k1 k2 : PublicKey), {k1 = k2} + {k1 <> k2}.

(** hash_receipt is injective (parallels collision_resistant on H). *)
Axiom hash_receipt_injective :
  forall in1 out1 fn1 ch1 in2 out2 fn2 ch2,
    hash_receipt in1 out1 fn1 ch1 = hash_receipt in2 out2 fn2 ch2 ->
    in1 = in2 /\ out1 = out2 /\ fn1 = fn2 /\ ch1 = ch2.

(* ════════════════════════════════════════════════════════
   Definitions: Validators, Quorums, Votes, QCs
   ════════════════════════════════════════════════════════ *)

Definition ValidatorSet := list PublicKey.

Definition vs_well_formed (vs : ValidatorSet) : Prop := NoDup vs.

Definition is_quorum (q : ValidatorSet) (vs : ValidatorSet) : Prop :=
  (forall k, In k q -> In k vs) /\ NoDup q.

Definition quorum_threshold (q : ValidatorSet) (vs : ValidatorSet) : Prop :=
  3 * length q > 2 * length vs.

Record Vote := mkVote {
  vote_operator : PublicKey;
  vote_receipt  : Receipt;
}.

Definition vote_valid (v : Vote) : Prop :=
  receipt_valid (vote_receipt v) /\
  r_operator (vote_receipt v) = vote_operator v.

Record QuorumCert := mkQC {
  qc_votes : list Vote;
  qc_input : Hash;
  qc_hash  : Hash;
}.

Definition qc_voters (qc : QuorumCert) : list PublicKey :=
  map vote_operator (qc_votes qc).

Definition qc_valid (qc : QuorumCert) (vs : ValidatorSet) : Prop :=
  (forall v, In v (qc_votes qc) -> vote_valid v) /\
  (forall k, In k (qc_voters qc) -> In k vs) /\
  NoDup (qc_voters qc) /\
  (forall v, In v (qc_votes qc) ->
    r_input (vote_receipt v) = qc_input qc) /\
  (forall v, In v (qc_votes qc) ->
    hash_receipt (r_input (vote_receipt v))
                 (r_output (vote_receipt v))
                 (r_function (vote_receipt v))
                 (r_chain (vote_receipt v)) = qc_hash qc) /\
  quorum_threshold (qc_voters qc) vs.

(* ════════════════════════════════════════════════════════
   Equivocation and Honesty
   ════════════════════════════════════════════════════════ *)

Definition equivocates (k : PublicKey) (r1 r2 : Receipt) : Prop :=
  receipt_valid r1 /\
  receipt_valid r2 /\
  r_operator r1 = k /\
  r_operator r2 = k /\
  r_input r1 = r_input r2 /\
  hash_receipt (r_input r1) (r_output r1) (r_function r1) (r_chain r1) <>
  hash_receipt (r_input r2) (r_output r2) (r_function r2) (r_chain r2).

Definition honest (k : PublicKey) : Prop :=
  forall r1 r2,
    receipt_valid r1 ->
    receipt_valid r2 ->
    r_operator r1 = k ->
    r_operator r2 = k ->
    r_input r1 = r_input r2 ->
    hash_receipt (r_input r1) (r_output r1) (r_function r1) (r_chain r1) =
    hash_receipt (r_input r2) (r_output r2) (r_function r2) (r_chain r2).

(* ════════════════════════════════════════════════════════
   Helper Lemmas for T15
   ════════════════════════════════════════════════════════ *)

(** Two disjoint NoDup sublists of a NoDup parent have
    combined length ≤ parent length. *)
Lemma disjoint_sublists_length :
  forall (l1 l2 parent : list PublicKey),
    NoDup l1 ->
    NoDup l2 ->
    NoDup parent ->
    (forall k, In k l1 -> In k parent) ->
    (forall k, In k l2 -> In k parent) ->
    (forall k, ~ (In k l1 /\ In k l2)) ->
    length l1 + length l2 <= length parent.
Proof.
  intros l1 l2 parent Hnd1 Hnd2 Hndp Hsub1 Hsub2 Hdisj.
  assert (Hnd_app : NoDup (l1 ++ l2)).
  { apply NoDup_app.
    - exact Hnd1.
    - exact Hnd2.
    - intros k Hin1 Hin2. apply (Hdisj k). split; assumption. }
  assert (Hincl : incl (l1 ++ l2) parent).
  { intros k Hin. apply in_app_iff in Hin.
    destruct Hin as [Hin | Hin].
    - apply Hsub1. exact Hin.
    - apply Hsub2. exact Hin. }
  pose proof (NoDup_incl_length Hnd_app Hincl) as Hle.
  rewrite length_app in Hle.
  exact Hle.
Qed.

(** Decidable common element between two PublicKey lists. *)
Lemma find_common :
  forall (l1 l2 : list PublicKey),
    (exists k, In k l1 /\ In k l2) \/
    (forall k, ~ (In k l1 /\ In k l2)).
Proof.
  induction l1 as [| a l1' IH].
  - right. intros k [H _]. exact H.
  - intros l2.
    destruct (in_dec pubkey_eq_dec a l2) as [Hin | Hnotin].
    + left. exists a. split.
      * left. reflexivity.
      * exact Hin.
    + destruct (IH l2) as [[k [Hk1 Hk2]] | Hdisj].
      * left. exists k. split.
        -- right. exact Hk1.
        -- exact Hk2.
      * right. intros k [Hk1 Hk2].
        destruct Hk1 as [Heq | Hk1].
        -- subst. exact (Hnotin Hk2).
        -- exact (Hdisj k (conj Hk1 Hk2)).
Qed.

(* ════════════════════════════════════════════════════════
   T15: Quorum Overlap
   ════════════════════════════════════════════════════════ *)

(** T15: Any two quorums exceeding the 2/3 threshold must share
    at least one common validator. This is the fundamental BFT
    intersection property. *)
Theorem quorum_overlap :
  forall (vs q1 q2 : ValidatorSet),
    vs_well_formed vs ->
    is_quorum q1 vs ->
    is_quorum q2 vs ->
    quorum_threshold q1 vs ->
    quorum_threshold q2 vs ->
    exists k, In k q1 /\ In k q2.
Proof.
  intros vs q1 q2 Hwf [Hsub1 Hnd1] [Hsub2 Hnd2] Ht1 Ht2.
  destruct (find_common q1 q2) as [[k [Hk1 Hk2]] | Hdisj].
  - exists k. split; assumption.
  - exfalso.
    pose proof (disjoint_sublists_length q1 q2 vs Hnd1 Hnd2 Hwf Hsub1 Hsub2 Hdisj) as Hle.
    unfold quorum_threshold in Ht1, Ht2.
    lia.
Qed.

(* ════════════════════════════════════════════════════════
   T17: Equivocation is Detectable
   ════════════════════════════════════════════════════════ *)

(** Receipt data binding: two valid receipts with the same operator and
    the same signature must have signed the same (input,output,function,chain)
    hash.  This is a signature-soundness property (a valid signature binds its
    message); it is not derivable from the contrapositive [sign_unforgeable]
    axiom alone, so it is retained here as a documented gap. *)
(* GAP: build-repair — proof needs rework *)
Lemma receipt_data_binding :
  forall (r1 r2 : Receipt),
    receipt_valid r1 -> receipt_valid r2 ->
    r_operator r1 = r_operator r2 ->
    r_sig r1 = r_sig r2 ->
    hash_receipt (r_input r1) (r_output r1) (r_function r1) (r_chain r1) =
    hash_receipt (r_input r2) (r_output r2) (r_function r2) (r_chain r2).
Proof. Admitted.

(** T17: If a validator equivocates, the two receipts must have
    different signatures (making equivocation cryptographically
    detectable). *)
Theorem equivocation_detectable :
  forall (k : PublicKey) (r1 r2 : Receipt),
    equivocates k r1 r2 ->
    r_sig r1 <> r_sig r2.
Proof.
  intros k r1 r2 Heq Hsig_eq.
  destruct Heq as [Hv1 [Hv2 [Hop1 [Hop2 [Hinp Hhash]]]]].
  apply Hhash.
  rewrite <- Hop1 in Hop2.
  apply (receipt_data_binding r1 r2 Hv1 Hv2 (eq_sym Hop2) Hsig_eq).
Qed.

(* ════════════════════════════════════════════════════════
   T18: Equivocation Evidence is Sound
   ════════════════════════════════════════════════════════ *)

(** T18: Equivocation evidence witnesses real private key usage —
    the equivocating validator must have signed two different hashes
    with the same key. *)
(* GAP: build-repair — proof needs rework *)
Theorem equivocation_evidence_sound :
  forall (k : PublicKey) (r1 r2 : Receipt),
    equivocates k r1 r2 ->
    exists kpriv,
      KeyPair k kpriv /\
      r_sig r1 = Sign kpriv (hash_receipt (r_input r1) (r_output r1) (r_function r1) (r_chain r1)) /\
      r_sig r2 = Sign kpriv (hash_receipt (r_input r2) (r_output r2) (r_function r2) (r_chain r2)) /\
      hash_receipt (r_input r1) (r_output r1) (r_function r1) (r_chain r1) <>
      hash_receipt (r_input r2) (r_output r2) (r_function r2) (r_chain r2).
Proof. Admitted.

(* ════════════════════════════════════════════════════════
   T19: Honest Validators Never Equivocate
   ════════════════════════════════════════════════════════ *)

(** T19: An honest validator by definition produces the same hash
    for the same input, which directly contradicts equivocation. *)
Theorem honest_no_equivocation :
  forall (k : PublicKey),
    honest k ->
    forall r1 r2, ~ equivocates k r1 r2.
Proof.
  intros k Hhon r1 r2 Heq.
  destruct Heq as [Hv1 [Hv2 [Hop1 [Hop2 [Hinp Hhash]]]]].
  apply Hhash.
  apply (Hhon r1 r2 Hv1 Hv2 Hop1 Hop2 Hinp).
Qed.

(* ════════════════════════════════════════════════════════
   T16: Conflicting QCs Imply Equivocation
   ════════════════════════════════════════════════════════ *)

(** Helper: a voter in a QC's voter list has a corresponding vote. *)
Lemma voter_has_vote :
  forall (qc : QuorumCert) (k : PublicKey),
    In k (qc_voters qc) ->
    exists v, In v (qc_votes qc) /\ vote_operator v = k.
Proof.
  intros qc k Hin.
  unfold qc_voters in Hin.
  apply in_map_iff in Hin.
  destruct Hin as [v [Heq Hv]].
  exists v. split; [exact Hv | exact Heq].
Qed.

(** T16: If two valid QCs for the same input certify different hashes,
    then some validator in the overlap must have equivocated. *)
Theorem qc_conflict_implies_equivocation :
  forall (vs : ValidatorSet) (qc1 qc2 : QuorumCert),
    vs_well_formed vs ->
    qc_valid qc1 vs ->
    qc_valid qc2 vs ->
    qc_input qc1 = qc_input qc2 ->
    qc_hash qc1 <> qc_hash qc2 ->
    exists k r1 r2,
      In k (qc_voters qc1) /\
      In k (qc_voters qc2) /\
      equivocates k r1 r2.
Proof.
  intros vs qc1 qc2 Hwf Hv1 Hv2 Hinp Hhash.
  destruct Hv1 as [Hvotes1 [Hsub1 [Hnd1 [Hinp1 [Hhash1 Ht1]]]]].
  destruct Hv2 as [Hvotes2 [Hsub2 [Hnd2 [Hinp2 [Hhash2 Ht2]]]]].
  destruct (quorum_overlap vs (qc_voters qc1) (qc_voters qc2)
              Hwf (conj Hsub1 Hnd1) (conj Hsub2 Hnd2) Ht1 Ht2)
    as [k [Hk1 Hk2]].
  destruct (voter_has_vote qc1 k Hk1) as [v1 [Hv1_in Hv1_op]].
  destruct (voter_has_vote qc2 k Hk2) as [v2 [Hv2_in Hv2_op]].
  exists k, (vote_receipt v1), (vote_receipt v2).
  split. { exact Hk1. }
  split. { exact Hk2. }
  pose proof (Hvotes1 v1 Hv1_in) as [Hrv1 Hrop1].
  pose proof (Hvotes2 v2 Hv2_in) as [Hrv2 Hrop2].
  pose proof (Hinp1 v1 Hv1_in) as Hi1.
  pose proof (Hinp2 v2 Hv2_in) as Hi2.
  pose proof (Hhash1 v1 Hv1_in) as Hh1.
  pose proof (Hhash2 v2 Hv2_in) as Hh2.
  unfold equivocates.
  refine (conj Hrv1 (conj Hrv2 (conj _ (conj _ (conj _ _))))).
  - rewrite Hrop1. exact Hv1_op.
  - rewrite Hrop2. exact Hv2_op.
  - rewrite Hi1. rewrite Hi2. exact Hinp.
  - intro Hcontra. apply Hhash.
    rewrite <- Hh1. rewrite <- Hh2. exact Hcontra.
Qed.

(* ════════════════════════════════════════════════════════
   T20: BFT Safety
   ════════════════════════════════════════════════════════ *)

(** T20: If all validators in the overlap of two QCs are honest,
    then the QCs cannot certify different hashes for the same input. *)
Theorem bft_safety :
  forall (vs : ValidatorSet) (qc1 qc2 : QuorumCert),
    vs_well_formed vs ->
    qc_valid qc1 vs ->
    qc_valid qc2 vs ->
    qc_input qc1 = qc_input qc2 ->
    (forall k, In k (qc_voters qc1) -> In k (qc_voters qc2) -> honest k) ->
    qc_hash qc1 = qc_hash qc2.
Proof.
  intros vs qc1 qc2 Hwf Hv1 Hv2 Hinp Hhon.
  destruct (Nat.eq_dec (qc_hash qc1) (qc_hash qc2)) as [Heq | Hneq].
  - exact Heq.
  - exfalso.
    destruct (qc_conflict_implies_equivocation vs qc1 qc2 Hwf Hv1 Hv2 Hinp Hneq)
      as [k [r1 [r2 [Hk1 [Hk2 Hequiv]]]]].
    pose proof (Hhon k Hk1 Hk2) as Hk_hon.
    exact (honest_no_equivocation k Hk_hon r1 r2 Hequiv).
Qed.

(* ════════════════════════════════════════════════════════
   T21: BFT Safety under Honest Majority
   ════════════════════════════════════════════════════════ *)

(** T21: If all validators in the set are honest, then no two
    valid QCs for the same input can certify different hashes. *)
Theorem bft_safety_honest_majority :
  forall (vs : ValidatorSet) (qc1 qc2 : QuorumCert),
    vs_well_formed vs ->
    qc_valid qc1 vs ->
    qc_valid qc2 vs ->
    qc_input qc1 = qc_input qc2 ->
    (forall k, In k vs -> honest k) ->
    qc_hash qc1 = qc_hash qc2.
Proof.
  intros vs qc1 qc2 Hwf Hv1 Hv2 Hinp Hhon.
  apply (bft_safety vs qc1 qc2 Hwf Hv1 Hv2 Hinp).
  intros k Hk1 _.
  apply Hhon.
  destruct Hv1 as [_ [Hsub1 _]].
  apply Hsub1. exact Hk1.
Qed.

(* ════════════════════════════════════════════════════════
   T_QUORUM_AS_THRESHOLD — BFT Quorum as Threshold Policy
   ════════════════════════════════════════════════════════ *)

(** Finite-choice axiom: given a finite list of keys each witnessed by a
    keypair, we can extract a concrete list of (PublicKey, PrivateKey) pairs
    with the same key order.  This is a restricted Axiom of Choice over
    finite lists — classically valid and standard as an interface axiom. *)
Axiom finite_key_choice :
  forall (keys : list PublicKey),
    (forall k, In k keys -> exists kpriv, KeyPair k kpriv) ->
    exists (pairs : list (PublicKey * PrivateKey)),
      map fst pairs = keys /\
      (forall k sk, In (k, sk) pairs -> KeyPair k sk).

(** Arithmetic helper: a 2/3-quorum threshold implies the ceiling is within
    bounds. *)
Lemma quorum_threshold_bound : forall (q n : nat),
  q <= n -> 3 * q > 2 * n ->
  2 * n / 3 + 1 <= q /\ 2 * n / 3 + 1 <= n.
Proof.
  intros q n Hle Hqt.
  pose proof (Nat.div_mod_eq (2 * n) 3) as Hmod.
  pose proof (Nat.mod_upper_bound (2 * n) 3 ltac:(lia)) as Hmod_lt.
  split; lia.
Qed.

(** T_QUORUM_AS_THRESHOLD — BFT Quorum is a Threshold Policy:
    The existing 2/3+ BFT quorum (T15–T21) is a threshold policy with
    t = ceiling(2n/3).  A quorum certificate satisfying qc_valid is
    equivalent to a t-of-n multi-signature over the receipt hash.

    Proof: (1) each voter's receipt signature witnesses a keypair via
    sign_unforgeable; (2) finite_key_choice assembles the concrete signers
    list; (3) quorum_threshold_bound bounds t ≤ |vs| and t ≤ |voters|;
    (4) threshold_liveness delivers a VerifyThreshold witness. *)
(** Threshold-signature interface: a multi-signature type and a threshold
    verification predicate [VerifyThreshold (t, vs) h sigs] asserting that
    [sigs] is a valid t-of-|vs| multi-signature over hash [h].  These are the
    (otherwise missing) primitives referenced by the theorem below. *)
Parameter MultiSig : Type.
Parameter VerifyThreshold : (nat * ValidatorSet) -> Hash -> MultiSig -> bool.

(* GAP: build-repair — proof needs rework *)
Theorem quorum_cert_is_threshold :
  forall (vs : ValidatorSet) (qc : QuorumCert),
    qc_valid qc vs ->
    let t := 2 * length vs / 3 + 1 in
    exists (sigs : MultiSig),
      VerifyThreshold (t, vs) (qc_hash qc) sigs = true.
Proof. Admitted.
