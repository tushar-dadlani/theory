(** * DIM Complexity Bounds
    Formal time-complexity theorems for DIM operations.

    We use a simple cost model: every Sign, Verify, or H call costs
    exactly 1 unit (defined in dim_types.v as cost_hash, cost_sign,
    cost_verify). This models the O(1) wall-clock cost of Ed25519 and
    SHA-256 on modern hardware and lets us state asymptotic bounds
    as concrete equalities.

    Theorems:
      T5  verify_cost_linear     — verifying one receipt costs 1 + |chain|
      T6  provenance_walk_linear — walking k receipts costs k*(1+max_depth)
      T7  transition_cost_const  — writing a receipt costs exactly 2
                                   (one hash, one sign)
      T8  chain_length_bounded   — depth-decreasing chain has length ≤ root depth
      T9  caps_never_grow        — chain_caps_shrink is preserved by prepending
      T10 chain_valid_implies_shrink — chain_valid implies cap containment
                                      from first to last link
*)

From Stdlib Require Import List.
From Stdlib Require Import Nat.
From Stdlib Require Import Arith.
Require Import dim_types.
Require Import dim_crypto.
Require Import dim_capability.
Open Scope list_scope.
Open Scope nat_scope.

(* ════════════════════════════════════════════════════════
   Cost functions
   The cost of an operation is its number of cryptographic
   primitive calls (hash + verify/sign).
   ════════════════════════════════════════════════════════ *)

(** Cost to verify a single delegation link:
    one Verify call = cost_verify. *)
Definition verify_link_cost : Cost := cost_verify.

(** Cost to verify a delegation chain of length n:
    one Verify per link. *)
Definition verify_chain_cost (n : nat) : Cost := n * cost_verify.

(** Cost to verify a full receipt:
    one Verify for the receipt signature
    + one Verify per chain link. *)
Definition verify_receipt_cost (r : Receipt) : Cost :=
  cost_verify + verify_chain_cost (length (r_chain r)).

(** Cost to perform a transition (write a receipt):
    one H call (hash the payload)
    + one Sign call. *)
Definition transition_cost : Cost := cost_hash + cost_sign.

(** Cost to walk a provenance chain of k receipts,
    each with a delegation chain of depth at most d:
    k * (cost_verify + d * cost_verify). *)
Definition provenance_walk_cost (k : nat) (max_d : nat) : Cost :=
  k * (cost_verify + verify_chain_cost max_d).

(* ════════════════════════════════════════════════════════
   Theorem 5: Receipt Verification Cost is Linear in Chain Depth
   ════════════════════════════════════════════════════════ *)

(** T5: The cost to verify receipt r equals 1 + |r_chain r|.
    (Using cost_verify = cost_hash = cost_sign = 1.) *)
Theorem verify_cost_linear :
  forall (r : Receipt),
    verify_receipt_cost r = 1 + length (r_chain r).
Proof.
  intros r.
  unfold verify_receipt_cost, verify_chain_cost.
  unfold cost_verify.
  simpl.
  (* cost_verify = 1, so: 1 + length(chain) * 1 = 1 + length(chain) *)
  rewrite Nat.mul_1_r.
  reflexivity.
Qed.

(* ════════════════════════════════════════════════════════
   Theorem 6: Provenance Walk Cost is Linear in History Length
   ════════════════════════════════════════════════════════ *)

(** T6: Walking k receipts each with chain depth at most d costs
    k * (1 + d). This is O(k*d), but since d is bounded in practice
    (typically ≤ 5), it behaves as O(k). *)
Theorem provenance_walk_linear :
  forall (k d : nat),
    provenance_walk_cost k d = k * (1 + d).
Proof.
  intros k d.
  unfold provenance_walk_cost, verify_chain_cost.
  unfold cost_verify.
  rewrite Nat.mul_1_r.
  reflexivity.
Qed.

(* ════════════════════════════════════════════════════════
   Theorem 7: Transition (Write) Cost is Constant
   ════════════════════════════════════════════════════════ *)

(** T7: Writing a receipt costs exactly 2 cryptographic operations
    (one hash, one sign) — independent of system size, CAS size,
    number of operators, or delegation chain length. *)
Theorem transition_cost_const :
  transition_cost = 2.
Proof.
  unfold transition_cost, cost_hash, cost_sign.
  reflexivity.
Qed.

(* ════════════════════════════════════════════════════════
   Theorem 8: Depth-Decreasing Chain has Bounded Length
   ════════════════════════════════════════════════════════ *)

(** Auxiliary: in a depth-decreasing chain, every link has
    strictly smaller max_depth than the one before it. *)
Lemma depth_decrease_head :
  forall (d1 d2 : Delegation) (rest : DelegChain),
    chain_depth_decreasing (d1 :: d2 :: rest) ->
    del_max_depth d2 < del_max_depth d1.
Proof.
  intros d1 d2 rest Hdec.
  simpl in Hdec.
  destruct Hdec as [Hlt _].
  exact Hlt.
Qed.

(** T8: The length of a depth-decreasing chain is bounded by
    the max_depth of its first link plus one.
    Proof: each step strictly decrements max_depth (nat), so
    the chain cannot be longer than its starting depth + 1. *)
Theorem chain_length_bounded :
  forall (ch : DelegChain),
    ch <> [] ->
    chain_depth_decreasing ch ->
    length ch <= del_max_depth (hd (mkDelegation
        (hd (hd [] []) [])
        (hd (hd [] []) [])
        [] 0 (hd (hd [] []) []))
      ch) + 1.
Proof.
  intros ch Hne Hdec.
  induction ch as [| d rest IH].
  - contradiction.
  - simpl.
    destruct rest as [| d2 rest2].
    + simpl. apply Nat.le_add_r.
    + simpl in Hdec.
      destruct Hdec as [Hlt Hrest].
      simpl.
      (* length (d2::rest2) <= del_max_depth d2 + 1 by IH *)
      assert (Hrest_ne : d2 :: rest2 <> []) by discriminate.
      specialize (IH Hrest_ne Hrest).
      simpl in IH.
      (* del_max_depth d2 < del_max_depth d1, so
         length(d2::rest2) <= d2.depth + 1 <= d1.depth *)
      apply Nat.le_succ_l in Hlt.
      apply (Nat.le_trans _ (del_max_depth d + 1)).
      * apply Nat.le_succ_l.
        apply (Nat.le_trans _ (del_max_depth d2 + 1)).
        -- exact IH.
        -- apply Nat.add_le_add_right.
           apply Nat.lt_le_incl.
           exact Hlt.
      * apply Nat.le_refl.
Qed.

(* ════════════════════════════════════════════════════════
   Theorem 9: Capability Sets Never Grow Along a Chain
   ════════════════════════════════════════════════════════ *)

(** Auxiliary: chain_caps_shrink is preserved under tail. *)
Lemma chain_caps_shrink_tail :
  forall (d : Delegation) (rest : DelegChain),
    chain_caps_shrink (d :: rest) ->
    chain_caps_shrink rest.
Proof.
  intros d rest Hshrink.
  destruct rest as [| d2 rest2].
  - simpl. trivial.
  - simpl in Hshrink.
    destruct Hshrink as [_ Hrest].
    exact Hrest.
Qed.

(** T9: For any link at position i and position j > i in a
    chain_caps_shrink chain, caps[j] ⊆ caps[i].
    We prove the immediate version: caps of last ⊆ caps of first. *)
Theorem caps_never_grow :
  forall (ch : DelegChain),
    chain_caps_shrink ch ->
    forall (d_first d_last : Delegation),
      d_first = hd d_first ch ->
      d_last  = last ch d_last ->
      ch <> [] ->
      cap_subset (del_caps d_last) (del_caps d_first).
Proof.
  induction ch as [| d rest IH].
  - intros _ d_first d_last _ _ Hne. contradiction.
  - intros Hshrink d_first d_last Hfirst Hlast _.
    destruct rest as [| d2 rest2].
    + simpl in Hfirst, Hlast.
      rewrite <- Hfirst, <- Hlast.
      apply cap_subset_refl.
    + simpl in Hshrink.
      destruct Hshrink as [Hd_d2 Hrest].
      simpl in Hfirst. rewrite <- Hfirst.
      simpl in Hlast.
      apply cap_subset_trans with (B := del_caps d2).
      * apply IH.
        -- exact Hrest.
        -- simpl. reflexivity.
        -- exact Hlast.
        -- discriminate.
      * exact Hd_d2.
Qed.

(* ════════════════════════════════════════════════════════
   Theorem 10: chain_valid implies full cap containment
   ════════════════════════════════════════════════════════ *)

(** T10: A fully valid chain (all four invariants) implies that
    the terminal grantee's caps are a subset of the root grantor's caps.
    This is the end-to-end delegation-safety theorem. *)
Theorem chain_valid_implies_cap_containment :
  forall (ch : DelegChain),
    chain_valid ch ->
    forall (d_first d_last : Delegation),
      d_first = hd d_first ch ->
      d_last  = last ch d_last ->
      ch <> [] ->
      cap_subset (del_caps d_last) (del_caps d_first).
Proof.
  intros ch Hvalid d_first d_last Hfirst Hlast Hne.
  unfold chain_valid in Hvalid.
  destruct Hvalid as [_ [_ [Hshrink _]]].
  apply caps_never_grow; assumption.
Qed.
