(** * DIM Capabilities, Delegation, and Receipts
    Updated: stdlib imports fixed; max_depth field added to Delegation
    to support complexity bounds in dim_complexity.v *)

From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Nat.
Require Import dim_types.
Require Import dim_crypto.
Open Scope list_scope.

(* ════════════════════════════════════════════════════════
   Capabilities
   ════════════════════════════════════════════════════════ *)

Definition Capability := (State * Hash)%type.
Definition CapSet     := list Capability.

Definition cap_in (c : Capability) (cs : CapSet) : Prop := In c cs.

Definition cap_subset (A B : CapSet) : Prop :=
  forall c, cap_in c A -> cap_in c B.

Lemma cap_subset_refl : forall (cs : CapSet), cap_subset cs cs.
Proof. intros cs c Hc. exact Hc. Qed.

Lemma cap_subset_trans :
  forall (A B C : CapSet),
    cap_subset A B -> cap_subset B C -> cap_subset A C.
Proof.
  intros A B C HAB HBC c Hc.
  apply HBC. apply HAB. exact Hc.
Qed.

(** A CapSet is empty if it contains no capabilities. *)
Definition cap_empty (cs : CapSet) : Prop := cs = [].

(* ════════════════════════════════════════════════════════
   Delegation
   ════════════════════════════════════════════════════════ *)

Record Delegation := mkDelegation {
  del_grantor   : PublicKey;
  del_grantee   : PublicKey;
  del_caps      : CapSet;
  del_max_depth : nat;      (** max further sub-delegations permitted *)
  del_sig       : Signature;
}.

Parameter hash_del : PublicKey -> PublicKey -> CapSet -> nat -> Hash.

Definition del_sig_valid (d : Delegation) : Prop :=
  Verify (del_grantor d)
         (hash_del (del_grantor d) (del_grantee d)
                   (del_caps d) (del_max_depth d))
         (del_sig d)
  = true.

(* ════════════════════════════════════════════════════════
   Delegation Chain
   ════════════════════════════════════════════════════════ *)

Definition DelegChain := list Delegation.

(** Every grantee in link i must be the grantor in link i+1. *)
Fixpoint chain_linked (ch : DelegChain) : Prop :=
  match ch with
  | []               => True
  | [_]              => True
  | d1 :: d2 :: rest =>
      del_grantee d1 = del_grantor d2 /\
      chain_linked (d2 :: rest)
  end.

(** Every delegation in the chain carries a valid signature. *)
Fixpoint chain_sigs_valid (ch : DelegChain) : Prop :=
  match ch with
  | []        => True
  | d :: rest => del_sig_valid d /\ chain_sigs_valid rest
  end.

(** Capability monotone shrink: each link's caps ⊆ previous link's caps.
    This is the core delegation-safety invariant. *)
Fixpoint chain_caps_shrink (ch : DelegChain) : Prop :=
  match ch with
  | []               => True
  | [_]              => True
  | d1 :: d2 :: rest =>
      cap_subset (del_caps d2) (del_caps d1) /\
      chain_caps_shrink (d2 :: rest)
  end.

(** Depth monotone decrease: each link's max_depth < previous link's max_depth.
    Ensures the chain is finite and terminating. *)
Fixpoint chain_depth_decreasing (ch : DelegChain) : Prop :=
  match ch with
  | []               => True
  | [_]              => True
  | d1 :: d2 :: rest =>
      del_max_depth d2 < del_max_depth d1 /\
      chain_depth_decreasing (d2 :: rest)
  end.

(** A chain is well-formed if all four invariants hold. *)
Definition chain_valid (ch : DelegChain) : Prop :=
  chain_linked ch /\
  chain_sigs_valid ch /\
  chain_caps_shrink ch /\
  chain_depth_decreasing ch.

(* ════════════════════════════════════════════════════════
   Receipt
   ════════════════════════════════════════════════════════ *)

Record Receipt := mkReceipt {
  r_input    : Hash;
  r_output   : Hash;
  r_operator : PublicKey;
  r_chain    : DelegChain;
  r_time     : Timestamp;
  r_sig      : Signature;
}.

Parameter hash_receipt : Hash -> Hash -> DelegChain -> Hash.

Definition receipt_valid (r : Receipt) : Prop :=
  Verify (r_operator r)
         (hash_receipt (r_input r) (r_output r) (r_chain r))
         (r_sig r) = true
  /\ chain_sigs_valid  (r_chain r)
  /\ chain_linked      (r_chain r)
  /\ chain_caps_shrink (r_chain r).

(** Extended validity: also checks depth decrease. *)
Definition receipt_valid_strict (r : Receipt) : Prop :=
  receipt_valid r /\ chain_depth_decreasing (r_chain r).
