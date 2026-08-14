(* ================================================================= *)
(*  ProfiniteInteger.v                                               *)
(*                                                                    *)
(*  THE INFINITE PRIMORIAL as a first-class object: the profinite      *)
(*  integers  Zhat = lim_n Z/(n!)Z = lim_n Z/nZ = prod_p Z_p.          *)
(*                                                                    *)
(*  A point of Zhat is a coherent residue sequence over the FACTORIAL   *)
(*  modulus tower  M n = n!  (cofinal in the divisibility order, since  *)
(*  every m divides m!, so this limit is Zhat = lim Z/nZ):              *)
(*                                                                    *)
(*     a : nat -> nat   with   a n = a (S n) mod (n!)   (redcohF)       *)
(*                                                                    *)
(*  This is the RING face of "(primorial)^oo": as n -> oo the modulus   *)
(*  n! drags every prime to unbounded power.  Same coherent-sequence    *)
(*  recipe as PadicIntegers.v with p^n replaced by n!, so it is         *)
(*  guaranteed axiom-free by the same proofs.  We build the object, the *)
(*  reduction cone, ring operations descending to the limit, the        *)
(*  diagonal embedding Z -> Zhat, and the universal property.           *)
(* ================================================================= *)

From Stdlib Require Import Arith Lia Factorial.

(* the factorial modulus tower *)
Definition M (n : nat) : nat := fact n.

Lemma M_nonzero : forall n, M n <> 0.
Proof. intro n; unfold M; apply fact_neq_0. Qed.

Lemma M_succ : forall n, M (S n) = M n * S n.
Proof. intro n; unfold M; simpl; ring. Qed.

(* nested modulus: n! divides (S n)!, so reducing mod (S n)! then mod n! *)
(* is the same as reducing mod n!.                                        *)
Lemma nested_mod : forall x n, (x mod (M (S n))) mod (M n) = x mod (M n).
Proof.
  intros x n; rewrite M_succ.
  rewrite Nat.Div0.mod_mul_r, (Nat.mul_comm (M n)),
          Nat.Div0.mod_add, Nat.Div0.mod_mod; reflexivity.
Qed.

(* ================================================================= *)
(*  1.  THE OBJECT: coherent residue sequences over the factorial tower *)
(* ================================================================= *)

Definition redcohF (a : nat -> nat) : Prop := forall n, a n = a (S n) mod (M n).

Definition Zhat : Type := { a : nat -> nat | redcohF a }.

Definition digitsW (X : Zhat) : nat -> nat := proj1_sig X.
Definition projW (n : nat) (X : Zhat) : nat := digitsW X n.

(* the reduction cone: proj n commutes with the mod-n! bonding map *)
Lemma projW_cone : forall X n, projW n X = projW (S n) X mod (M n).
Proof. intros X n; exact (proj2_sig X n). Qed.

(* ================================================================= *)
(*  2.  THE RING OPERATIONS, reduced mod n! at each level            *)
(* ================================================================= *)

Definition rzero : nat -> nat := fun _ => 0.
Definition rone  : nat -> nat := fun n => 1 mod (M n).
Definition radd (a b : nat -> nat) : nat -> nat := fun n => (a n + b n) mod (M n).
Definition rmul (a b : nat -> nat) : nat -> nat := fun n => (a n * b n) mod (M n).

Lemma redcohF_zero : redcohF rzero.
Proof. intro n; unfold rzero; rewrite Nat.Div0.mod_0_l; reflexivity. Qed.

Lemma redcohF_one : redcohF rone.
Proof. intro n; unfold rone; rewrite nested_mod; reflexivity. Qed.

Lemma redcohF_add : forall a b, redcohF a -> redcohF b -> redcohF (radd a b).
Proof.
  intros a b Ha Hb n; unfold radd.
  rewrite nested_mod, (Ha n), (Hb n), <- Nat.Div0.add_mod; reflexivity.
Qed.

Lemma redcohF_mul : forall a b, redcohF a -> redcohF b -> redcohF (rmul a b).
Proof.
  intros a b Ha Hb n; unfold rmul.
  rewrite nested_mod, (Ha n), (Hb n), <- Nat.Div0.mul_mod; reflexivity.
Qed.

Definition Wzero : Zhat := exist redcohF rzero redcohF_zero.
Definition Wone  : Zhat := exist redcohF rone redcohF_one.
Definition Wadd (X Y : Zhat) : Zhat :=
  exist redcohF (radd (digitsW X) (digitsW Y)) (redcohF_add _ _ (proj2_sig X) (proj2_sig Y)).
Definition Wmul (X Y : Zhat) : Zhat :=
  exist redcohF (rmul (digitsW X) (digitsW Y)) (redcohF_mul _ _ (proj2_sig X) (proj2_sig Y)).

(* the projections are RING HOMOMORPHISMS to Z/(n!)Z *)
Lemma projW_add : forall X Y n, projW n (Wadd X Y) = (projW n X + projW n Y) mod (M n).
Proof. reflexivity. Qed.
Lemma projW_mul : forall X Y n, projW n (Wmul X Y) = (projW n X * projW n Y) mod (M n).
Proof. reflexivity. Qed.

Lemma radd_comm : forall a b n, radd a b n = radd b a n.
Proof. intros a b n; unfold radd; rewrite Nat.add_comm; reflexivity. Qed.
Lemma rmul_comm : forall a b n, rmul a b n = rmul b a n.
Proof. intros a b n; unfold rmul; rewrite Nat.mul_comm; reflexivity. Qed.

(* ================================================================= *)
(*  3.  THE DIAGONAL EMBEDDING  Z -> Zhat  (dense image)             *)
(* ================================================================= *)

Definition embW (z : nat) : Zhat :=
  exist redcohF (fun n => z mod (M n)) (fun n => eq_sym (nested_mod z n)).

Lemma projW_emb : forall z n, projW n (embW z) = z mod (M n).
Proof. reflexivity. Qed.

(* the embedding is a ring homomorphism into the limit *)
Lemma embW_add : forall x y n,
  projW n (embW (x + y)) = (projW n (embW x) + projW n (embW y)) mod (M n).
Proof. intros x y n; unfold projW, embW, digitsW; cbn [proj1_sig].
  rewrite <- Nat.Div0.add_mod; reflexivity. Qed.
Lemma embW_mul : forall x y n,
  projW n (embW (x * y)) = (projW n (embW x) * projW n (embW y)) mod (M n).
Proof. intros x y n; unfold projW, embW, digitsW; cbn [proj1_sig].
  rewrite <- Nat.Div0.mul_mod; reflexivity. Qed.

(* ================================================================= *)
(*  4.  UNIVERSAL PROPERTY: coherent residue data assembles into Zhat *)
(* ================================================================= *)

Definition Wmediate {A : Type} (fam : forall n, A -> nat)
  (coh : forall z n, fam n z = fam (S n) z mod (M n)) (z : A) : Zhat :=
  exist redcohF (fun n => fam n z) (coh z).

Lemma Wmediate_proj : forall {A} (fam : forall n, A -> nat) coh n z,
  projW n (@Wmediate A fam coh z) = fam n z.
Proof. reflexivity. Qed.

(* cofinality of the factorial tower in (nat, |): every S k divides M (S k), *)
(* so lim_n Z/(n!)Z = lim_m Z/mZ = Zhat.                                     *)
Lemma cofinal : forall k, Nat.divide (S k) (M (S k)).
Proof. intro k; unfold M; exists (fact k); simpl; ring. Qed.

(* ----------------------------------------------------------------- *)
(*  MASTER THEOREM — Zhat as inverse-limit ring, axiom-free          *)
(* ----------------------------------------------------------------- *)

Theorem profinite_integer :
  (* the projection cone commutes with the mod-n! bonding maps *)
  (forall X n, projW n X = projW (S n) X mod (M n))
  (* the ring operations descend to the inverse limit *)
  /\ redcohF rzero /\ redcohF rone
  /\ (forall a b, redcohF a -> redcohF b -> redcohF (radd a b))
  /\ (forall a b, redcohF a -> redcohF b -> redcohF (rmul a b))
  (* the projections are ring homomorphisms *)
  /\ (forall X Y n, projW n (Wadd X Y) = (projW n X + projW n Y) mod (M n))
  /\ (forall X Y n, projW n (Wmul X Y) = (projW n X * projW n Y) mod (M n))
  (* the diagonal Z -> Zhat is a ring homomorphism *)
  /\ (forall x y n, projW n (embW (x + y)) = (projW n (embW x) + projW n (embW y)) mod (M n))
  /\ (forall x y n, projW n (embW (x * y)) = (projW n (embW x) * projW n (embW y)) mod (M n))
  (* universal property: coherent residue data assembles into a limit point *)
  /\ (forall (A : Type) (fam : forall n, A -> nat)
        (coh : forall z n, fam n z = fam (S n) z mod (M n)) n z,
        projW n (Wmediate fam coh z) = fam n z)
  (* the factorial tower is cofinal in divisibility, so this IS lim Z/nZ *)
  /\ (forall k, Nat.divide (S k) (M (S k))).
Proof.
  split; [ exact projW_cone | ].
  split; [ exact redcohF_zero | ].
  split; [ exact redcohF_one | ].
  split; [ exact redcohF_add | ].
  split; [ exact redcohF_mul | ].
  split; [ exact projW_add | ].
  split; [ exact projW_mul | ].
  split; [ exact embW_add | ].
  split; [ exact embW_mul | ].
  split; [ intros A fam coh n z; exact (Wmediate_proj fam coh n z) | ].
  exact cofinal.
Qed.

Print Assumptions profinite_integer.

(* ================================================================= *)
(*  END ProfiniteInteger.v                                           *)
(*  Zhat = lim Z/(n!)Z = Zhat, the profinite-integer RING face of      *)
(*  (primorial)^oo, as coherent residue sequences: reduction cone,     *)
(*  ring ops descending to the limit, ring-hom projections, the        *)
(*  diagonal embedding Z -> Zhat, cofinality, and the universal        *)
(*  property.  ZERO Admitted; axiom-free.                              *)
(* ================================================================= *)
