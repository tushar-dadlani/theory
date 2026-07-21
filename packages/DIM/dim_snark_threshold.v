(** * DIM SNARK Threshold Delegation
    Upgrades ThresholdDelegation to use a Zero-Knowledge proof (SNARK)
    instead of an explicit MultiSig, hiding which t-of-n signers participated.

    This is the ZK-signer-anonymity upgrade left as future work in
    dim_anon_counter.v.  This file is additive — no existing files are modified.
*)

From Stdlib Require Import List.
From Stdlib Require Import Nat.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
Require Import dim_types.
Require Import dim_crypto.
Require Import dim_capability.
Import ListNotations.
Open Scope list_scope.
Open Scope nat_scope.

(* ════════════════════════════════════════════════════════
   Section 1 — Abstract SNARK Types
   ════════════════════════════════════════════════════════ *)

Parameter SNARKStatement : Type.
Parameter SNARKProof     : Type.

(** A threshold policy is a pair (t, keys): require at least [t] valid
    signatures drawn from the key set [keys].  [fst] is the threshold,
    [snd] is the authorized signer set. *)
Definition ThresholdPolicy := (nat * list PublicKey)%type.

(** An explicit multi-signature: a list of (signer, signature) pairs.
    Contrasts with the SNARK proof, which hides the signer set — hence
    [map fst] structurally reveals the signers of a MultiSig. *)
Definition MultiSig := list (PublicKey * Signature).

(* ════════════════════════════════════════════════════════
   Section 2 — Statement Construction
   ════════════════════════════════════════════════════════ *)

(** Derives the NP statement the prover proves:
    "I know t valid signatures from (snd policy) over message m." *)
Parameter thresh_statement : ThresholdPolicy -> Hash -> SNARKStatement.

(* ════════════════════════════════════════════════════════
   Section 3 — Verifier
   ════════════════════════════════════════════════════════ *)

Parameter VerifySNARK : SNARKStatement -> SNARKProof -> bool.

(* ════════════════════════════════════════════════════════
   Section 4 — Security Axioms
   ════════════════════════════════════════════════════════ *)

(** Soundness: a valid SNARK proof witnesses t authorized signers.
    The witness (valid_keys) exists but is not revealed by the proof itself. *)
Axiom snark_soundness :
  forall (policy : ThresholdPolicy) (m : Hash) (pi : SNARKProof),
    VerifySNARK (thresh_statement policy m) pi = true ->
    exists (valid_keys : list PublicKey),
      length valid_keys >= fst policy /\
      NoDup valid_keys /\
      (forall k, In k valid_keys -> In k (snd policy)).

(** Signer Anonymity (ZK property): there is no computable function that
    extracts the specific signer set from a SNARK proof.
    Modeled after hash_preimage_hard's ~ exists f, forall x, ... pattern. *)
Axiom snark_signer_anonymity :
  forall (policy : ThresholdPolicy) (m : Hash),
    ~ exists (f : SNARKProof -> list PublicKey),
        forall (pi : SNARKProof),
          VerifySNARK (thresh_statement policy m) pi = true ->
          (forall k, In k (f pi) -> In k (snd policy)) /\
          length (f pi) >= fst policy /\
          NoDup (f pi).

(** Completeness/Liveness: if at least t honest signers participate,
    a valid SNARK proof can always be constructed.
    Mirrors threshold_liveness exactly. *)
Axiom snark_completeness :
  forall (t : nat) (keys : list PublicKey) (m : Hash),
    t <= length keys ->
    (exists (signers : list (PublicKey * PrivateKey)),
       length signers >= t /\
       (forall k sk, In (k, sk) signers -> In k keys /\ KeyPair k sk)) ->
    exists (pi : SNARKProof),
      VerifySNARK (thresh_statement (t, keys) m) pi = true.

(** Succinctness: SNARK verification costs exactly cost_verify,
    independent of the size of the key list. *)
Definition verify_snark_cost : Cost := cost_verify.

Axiom snark_succinctness :
  forall (t : nat) (keys : list PublicKey) (m : Hash),
    verify_snark_cost = cost_verify.

(* ════════════════════════════════════════════════════════
   Section 5 — SNARKThresholdDelegation Record
   ════════════════════════════════════════════════════════ *)

Parameter hash_snark_tdel : PublicKey -> ThresholdPolicy -> CapSet -> nat -> Hash.

(** A threshold delegation backed by a SNARK proof instead of an explicit
    MultiSig.  The proof certifies t-of-n threshold satisfaction without
    revealing which t participants signed. *)
Record SNARKThresholdDelegation := mkSNARKThresholdDelegation {
  stdel_grantor   : PublicKey;
  stdel_policy    : ThresholdPolicy;
  stdel_caps      : CapSet;
  stdel_max_depth : nat;
  stdel_proof     : SNARKProof;    (** replaces tdel_multisig : MultiSig *)
}.

(** A SNARK threshold delegation is valid if VerifySNARK accepts the proof
    against the content hash — no call to VerifyThreshold or MultiSig. *)
Definition snark_tdel_valid (sd : SNARKThresholdDelegation) : Prop :=
  VerifySNARK (thresh_statement (stdel_policy sd)
                                (hash_snark_tdel (stdel_grantor sd)
                                                 (stdel_policy sd)
                                                 (stdel_caps sd)
                                                 (stdel_max_depth sd)))
              (stdel_proof sd) = true.

Parameter default_snark_tdel : SNARKThresholdDelegation.

(* ════════════════════════════════════════════════════════
   Section 6 — SNARKDelegChain with Four Invariants
   ════════════════════════════════════════════════════════ *)

Definition SNARKDelegChain := list SNARKThresholdDelegation.

(** Linking: the grantor of link i+1 must be one of the authorized grantees
    in link i's policy (the snd of the ThresholdPolicy).
    Structural mirror of tchain_linked. *)
Fixpoint snark_tchain_linked (ch : SNARKDelegChain) : Prop :=
  match ch with
  | []           => True
  | sd1 :: rest  =>
      match rest with
      | []      => True
      | sd2 :: _ =>
          In (stdel_grantor sd2) (snd (stdel_policy sd1)) /\
          snark_tchain_linked rest
      end
  end.

(** Every SNARK delegation in the chain satisfies snark_tdel_valid. *)
Fixpoint snark_tchain_sigs_valid (ch : SNARKDelegChain) : Prop :=
  match ch with
  | []          => True
  | sd :: rest  => snark_tdel_valid sd /\ snark_tchain_sigs_valid rest
  end.

(** Capability monotone shrink: each link's caps ⊆ previous link's caps. *)
Fixpoint snark_tchain_caps_shrink (ch : SNARKDelegChain) : Prop :=
  match ch with
  | []           => True
  | sd1 :: rest  =>
      match rest with
      | []      => True
      | sd2 :: _ =>
          cap_subset (stdel_caps sd2) (stdel_caps sd1) /\
          snark_tchain_caps_shrink rest
      end
  end.

(** Depth monotone decrease: each link's max_depth < previous link's max_depth. *)
Fixpoint snark_tchain_depth_decreasing (ch : SNARKDelegChain) : Prop :=
  match ch with
  | []           => True
  | sd1 :: rest  =>
      match rest with
      | []      => True
      | sd2 :: _ =>
          stdel_max_depth sd2 < stdel_max_depth sd1 /\
          snark_tchain_depth_decreasing rest
      end
  end.

(** A SNARK delegation chain is well-formed if all four invariants hold. *)
Definition snark_tchain_valid (ch : SNARKDelegChain) : Prop :=
  snark_tchain_linked ch /\
  snark_tchain_sigs_valid ch /\
  snark_tchain_caps_shrink ch /\
  snark_tchain_depth_decreasing ch.

(* ════════════════════════════════════════════════════════
   Section 7 — Theorems
   ════════════════════════════════════════════════════════ *)

(** T_SK1: A valid SNARK delegation witnesses t authorized signers.
    Direct application of snark_soundness. *)
Theorem snark_threshold_sound :
  forall (sd : SNARKThresholdDelegation),
    snark_tdel_valid sd ->
    exists (valid_keys : list PublicKey),
      length valid_keys >= fst (stdel_policy sd) /\
      NoDup valid_keys /\
      (forall k, In k valid_keys -> In k (snd (stdel_policy sd))).
Proof.
  intros sd Hvalid.
  unfold snark_tdel_valid in Hvalid.
  apply snark_soundness in Hvalid.
  exact Hvalid.
Qed.

(** T_SK2a: MultiSig structurally reveals signers — map fst extracts
    the public keys of all participants. *)
Theorem snark_multisig_reveals_signers :
  exists (f : MultiSig -> list PublicKey),
    forall (ms : MultiSig), f ms = map fst ms.
Proof.
  exists (map fst).
  intros ms.
  reflexivity.
Qed.

(** T_SK2b: No computable function can extract the signer set from a
    SNARK proof — the ZK property that MultiSig lacks. *)
Theorem snark_hides_signers :
  forall (policy : ThresholdPolicy) (m : Hash),
    ~ exists (f : SNARKProof -> list PublicKey),
        forall (pi : SNARKProof),
          VerifySNARK (thresh_statement policy m) pi = true ->
          (forall k, In k (f pi) -> In k (snd policy)) /\
          length (f pi) >= fst policy /\
          NoDup (f pi).
Proof.
  intros policy m.
  apply snark_signer_anonymity.
Qed.

(** T_SK3: SNARK verification cost is constant (= cost_verify = 1),
    independent of key list size. *)
Theorem snark_verification_constant_cost :
  forall (t : nat) (keys : list PublicKey) (m : Hash),
    verify_snark_cost = cost_verify.
Proof.
  intros t keys m.
  exact (snark_succinctness t keys m).
Qed.

(** T_SK4: A valid SNARK threshold delegation implies threshold satisfaction.
    Bridge theorem reducing to T_SK1. *)
Theorem snark_tdel_implies_threshold_sat :
  forall (sd : SNARKThresholdDelegation),
    snark_tdel_valid sd ->
    exists (valid_keys : list PublicKey),
      length valid_keys >= fst (stdel_policy sd) /\
      NoDup valid_keys /\
      (forall k, In k valid_keys -> In k (snd (stdel_policy sd))).
Proof.
  intros sd Hvalid.
  apply snark_threshold_sound.
  exact Hvalid.
Qed.

(** Auxiliary: in a snark_tchain_depth_decreasing chain, every link has
    strictly smaller max_depth than the one before it. *)
Lemma snark_depth_decrease_head :
  forall (sd1 sd2 : SNARKThresholdDelegation) (rest : SNARKDelegChain),
    snark_tchain_depth_decreasing (sd1 :: sd2 :: rest) ->
    stdel_max_depth sd2 < stdel_max_depth sd1.
Proof.
  intros sd1 sd2 rest Hdec.
  simpl in Hdec.
  destruct Hdec as [Hlt _].
  exact Hlt.
Qed.

(** T_SK5: The length of a snark_tchain_depth_decreasing chain is bounded
    by the stdel_max_depth of its first link plus one.
    Proof mirrors tchain_length_bounded using induction + simpl + lia. *)
Theorem snark_tchain_depth_monotone :
  forall (ch : SNARKDelegChain),
    ch <> [] ->
    snark_tchain_depth_decreasing ch ->
    length ch <= stdel_max_depth (hd default_snark_tdel ch) + 1.
Proof.
  intros ch Hne Hdec.
  induction ch as [| sd rest IH].
  - contradiction.
  - destruct rest as [| sd2 rest2].
    + simpl. lia.
    + simpl in Hdec.
      destruct Hdec as [Hlt Hrest].
      assert (Hrest_ne : sd2 :: rest2 <> []) by discriminate.
      specialize (IH Hrest_ne Hrest).
      simpl. simpl in IH. lia.
Qed.

(** T_SK6: MultiSig has a signer extractor (T_SK2a); SNARK does not (T_SK2b).
    The conjunction captures the anonymity advantage of SNARK over MultiSig. *)
Theorem snark_stronger_anonymity :
  (exists (f : MultiSig -> list PublicKey),
     forall (ms : MultiSig), f ms = map fst ms) /\
  (forall (policy : ThresholdPolicy) (m : Hash),
     ~ exists (f : SNARKProof -> list PublicKey),
         forall (pi : SNARKProof),
           VerifySNARK (thresh_statement policy m) pi = true ->
           (forall k, In k (f pi) -> In k (snd policy)) /\
           length (f pi) >= fst policy /\
           NoDup (f pi)).
Proof.
  split.
  - exists (map fst). intros ms. reflexivity.
  - intros policy m. apply snark_signer_anonymity.
Qed.
