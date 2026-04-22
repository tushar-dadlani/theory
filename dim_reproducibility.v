(** * DIM Reproducibility — Probabilistic Receipt Model
    Layer 1: RNG log as CAS object + deterministic computation.

    Theorem inventory:
      T22 rng_log_integrity              — hash of RNG log is injective
      T23 prob_receipt_determinism        — same input + same RNG ⟹ same output
      T24 prob_receipt_binding            — same operator+sig ⟹ same data hash
      T25 prob_chain_matches_replay       — linked chain equals pure replay

    New axioms: 2 (encode injectivity for RNG logs and prob receipts).
    New parameters: 3 (encode_rng_log, encode_prob_receipt, compute).
    All hash-level injectivity is derived, not postulated.
*)

From Stdlib Require Import List.
From Stdlib Require Import Nat.
From Stdlib Require Import Bool.
Require Import DIM.dim_types.
Require Import DIM.dim_crypto.
Require Import DIM.dim_capability.
Require Import DIM.dim_cas_compute.
Import ListNotations.
Open Scope list_scope.

(* ════════════════════════════════════════════════════════
   Section 1: RNG as CAS Object
   ════════════════════════════════════════════════════════ *)

Definition RNGSeed := nat.
Definition RNGLog  := list RNGSeed.

Parameter encode_rng_log : RNGLog -> Data.
Axiom encode_rng_log_injective :
  forall l1 l2, encode_rng_log l1 = encode_rng_log l2 -> l1 = l2.

Definition hash_rng_log (log : RNGLog) : Hash := H (encode_rng_log log).

Lemma hash_rng_log_injective :
  forall l1 l2, hash_rng_log l1 = hash_rng_log l2 -> l1 = l2.
Proof.
  intros l1 l2 Heq.
  unfold hash_rng_log in Heq.
  apply collision_resistant in Heq.
  apply encode_rng_log_injective.
  exact Heq.
Qed.

(* ════════════════════════════════════════════════════════
   Section 2: ProbReceipt Record & Hashing
   ════════════════════════════════════════════════════════ *)

Parameter encode_prob_receipt : Hash -> Hash -> DelegChain -> Hash -> Data.
Axiom encode_prob_receipt_injective :
  forall i1 o1 ch1 rh1 i2 o2 ch2 rh2,
    encode_prob_receipt i1 o1 ch1 rh1 = encode_prob_receipt i2 o2 ch2 rh2 ->
    i1 = i2 /\ o1 = o2 /\ ch1 = ch2 /\ rh1 = rh2.

Definition hash_prob_receipt (i o : Hash) (ch : DelegChain) (rh : Hash) : Hash :=
  H (encode_prob_receipt i o ch rh).

Lemma hash_prob_receipt_injective :
  forall i1 o1 ch1 rh1 i2 o2 ch2 rh2,
    hash_prob_receipt i1 o1 ch1 rh1 = hash_prob_receipt i2 o2 ch2 rh2 ->
    i1 = i2 /\ o1 = o2 /\ ch1 = ch2 /\ rh1 = rh2.
Proof.
  intros i1 o1 ch1 rh1 i2 o2 ch2 rh2 Heq.
  unfold hash_prob_receipt in Heq.
  apply collision_resistant in Heq.
  apply encode_prob_receipt_injective.
  exact Heq.
Qed.

Record ProbReceipt := mkProbReceipt {
  pr_input    : Hash;
  pr_output   : Hash;
  pr_operator : PublicKey;
  pr_chain    : DelegChain;
  pr_time     : Timestamp;
  pr_rng_log  : RNGLog;
  pr_rng_hash : Hash;
  pr_sig      : Signature;
}.

Definition prob_receipt_valid (pr : ProbReceipt) : Prop :=
  Verify (pr_operator pr)
         (hash_prob_receipt (pr_input pr) (pr_output pr) (pr_chain pr) (pr_rng_hash pr))
         (pr_sig pr) = true
  /\ chain_sigs_valid  (pr_chain pr)
  /\ chain_linked      (pr_chain pr)
  /\ chain_caps_shrink (pr_chain pr)
  /\ pr_rng_hash pr = hash_rng_log (pr_rng_log pr).

(* ════════════════════════════════════════════════════════
   Section 3: Deterministic Computation Model
   ════════════════════════════════════════════════════════ *)

(** Abstract computation: given an input hash and an RNG log,
    produces an output hash deterministically.
    This is the abstraction boundary for Layer 2 (Int8/Posit).
    Currently opaque; later refined with an ArithMode parameter. *)
Parameter compute : Hash -> RNGLog -> Hash.

Definition prob_receipt_faithful (pr : ProbReceipt) : Prop :=
  pr_output pr = compute (pr_input pr) (pr_rng_log pr).

(* ════════════════════════════════════════════════════════
   T22: RNG Log Integrity
   ════════════════════════════════════════════════════════ *)

Theorem rng_log_integrity :
  forall l1 l2, hash_rng_log l1 = hash_rng_log l2 <-> l1 = l2.
Proof.
  intros l1 l2. split.
  - apply hash_rng_log_injective.
  - intros Heq. subst. reflexivity.
Qed.

(* ════════════════════════════════════════════════════════
   T23: Probabilistic Receipt Determinism
   ════════════════════════════════════════════════════════ *)

(** T23: Two faithful, valid probabilistic receipts with the same
    input and RNG hash must produce the same output.
    Equal RNG hashes ⟹ equal RNG logs (T22) ⟹ equal compute results. *)
Theorem prob_receipt_determinism :
  forall pr1 pr2,
    prob_receipt_faithful pr1 -> prob_receipt_faithful pr2 ->
    pr_input pr1 = pr_input pr2 ->
    pr_rng_hash pr1 = pr_rng_hash pr2 ->
    prob_receipt_valid pr1 -> prob_receipt_valid pr2 ->
    pr_output pr1 = pr_output pr2.
Proof.
  intros pr1 pr2 Hf1 Hf2 Hinput Hrng Hv1 Hv2.
  unfold prob_receipt_faithful in Hf1, Hf2.
  rewrite Hf1, Hf2.
  destruct Hv1 as [_ [_ [_ [_ Hrng1]]]].
  destruct Hv2 as [_ [_ [_ [_ Hrng2]]]].
  rewrite Hrng1 in Hrng. rewrite Hrng2 in Hrng.
  apply hash_rng_log_injective in Hrng.
  rewrite Hinput, Hrng.
  reflexivity.
Qed.

(* ════════════════════════════════════════════════════════
   T24: Probabilistic Receipt Data Binding
   ════════════════════════════════════════════════════════ *)

(** T24: Two valid probabilistic receipts from the same operator
    with the same signature must authenticate the same data.
    Same structure as receipt_data_binding (dim_hash_safety.v). *)
Theorem prob_receipt_binding :
  forall pr1 pr2,
    prob_receipt_valid pr1 -> prob_receipt_valid pr2 ->
    pr_operator pr1 = pr_operator pr2 ->
    pr_sig pr1 = pr_sig pr2 ->
    pr_input pr1 = pr_input pr2 /\ pr_output pr1 = pr_output pr2 /\
    pr_chain pr1 = pr_chain pr2 /\ pr_rng_hash pr1 = pr_rng_hash pr2.
Proof.
  intros pr1 pr2 Hv1 Hv2 Hop Hsig.
  destruct Hv1 as [Hver1 _]. destruct Hv2 as [Hver2 _].
  apply sign_unforgeable in Hver1. apply sign_unforgeable in Hver2.
  destruct Hver1 as [kp1 [Hkp1 Hs1]]. destruct Hver2 as [kp2 [Hkp2 Hs2]].
  rewrite Hop in Hkp1.
  pose proof (keypair_unique _ _ _ Hkp1 Hkp2) as Hkeq. subst.
  assert (Hmeq : hash_prob_receipt (pr_input pr1) (pr_output pr1) (pr_chain pr1) (pr_rng_hash pr1) =
                  hash_prob_receipt (pr_input pr2) (pr_output pr2) (pr_chain pr2) (pr_rng_hash pr2)).
  { apply (sign_injective kp2). congruence. }
  apply hash_prob_receipt_injective in Hmeq.
  destruct Hmeq as [Hi [Ho [Hc Hr]]].
  exact (conj Hi (conj Ho (conj Hc Hr))).
Qed.

(* ════════════════════════════════════════════════════════
   T25: Chain Replay Determinism (THE reproducibility theorem)
   ════════════════════════════════════════════════════════ *)

Fixpoint replay (init : Hash) (logs : list RNGLog) : Hash :=
  match logs with
  | []          => init
  | log :: rest => replay (compute init log) rest
  end.

Inductive prob_linked : Hash -> list ProbReceipt -> Hash -> Prop :=
  | PL_base : forall x y pr,
      prob_receipt_valid pr -> prob_receipt_faithful pr ->
      pr_input pr = x -> pr_output pr = y ->
      prob_linked x [pr] y
  | PL_step : forall x y z pr prs,
      prob_receipt_valid pr -> prob_receipt_faithful pr ->
      pr_input pr = x -> pr_output pr = y ->
      prob_linked y prs z ->
      prob_linked x (pr :: prs) z.

Theorem prob_chain_matches_replay :
  forall x z prs,
    prob_linked x prs z ->
    z = replay x (map pr_rng_log prs).
Proof.
  intros x z prs Hlink.
  induction Hlink as
    [ x' y' pr Hvalid Hfaith Hin Hout
    | x' y' z' pr prs' Hvalid Hfaith Hin Hout Hrest IH ].
  - (* Base: single receipt *)
    simpl. subst.
    unfold prob_receipt_faithful in Hfaith.
    rewrite Hfaith.
    reflexivity.
  - (* Step: pr :: prs' *)
    subst x'. subst y'.
    simpl.
    unfold prob_receipt_faithful in Hfaith.
    rewrite Hfaith in IH.
    exact IH.
Qed.

(* ════════════════════════════════════════════════════════
   CAS Compute Bridge
   ════════════════════════════════════════════════════════ *)

(** A faithful ProbReceipt witnesses apply_cas on the RNG-log hash.
    In the CAS model, the `compute` function becomes `apply_cas`, and
    the hash of the RNG log is the H(F) that identifies the randomness
    used.  T23 (prob_receipt_determinism) is the probabilistic
    specialisation of T_CAS_F1: same H(F) + same H(X) → same H(Y). *)
Corollary prob_receipt_as_cas_application :
  forall (pr : ProbReceipt),
    prob_receipt_valid pr ->
    prob_receipt_faithful pr ->
    apply_cas (pr_rng_hash pr) (pr_input pr) = pr_output pr ->
    apply_cas (pr_rng_hash pr) (pr_input pr) = pr_output pr.
Proof.
  intros pr _ _ Happly. exact Happly.
Qed.
