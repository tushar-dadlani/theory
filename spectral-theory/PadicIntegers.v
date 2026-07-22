(* ================================================================= *)
(*  PadicIntegers.v                                                   *)
(*                                                                    *)
(*  EXTENSION 1: the p-adic integers Z_p as the INVERSE LIMIT of the    *)
(*  tower Z/p^n under mod-p^n reduction -- the genuine p-adic tower,    *)
(*  distinct from ChainTower's order-truncation tower.  Axiom-free.     *)
(*                                                                    *)
(*  Same coherent-sequence recipe as InvLimit.v, but the levels are the *)
(*  residue rings Z/p^n and the bonding maps are the RING quotients     *)
(*  r |-> r mod p^n.  A point of Z_p is a coherent residue sequence:     *)
(*                                                                    *)
(*     a : nat -> nat   with   a n = a (S n) mod p^n   (redcoh)         *)
(*                                                                    *)
(*  We build the object, the reduction projection cone, the ring        *)
(*  operations (zero, one, add, mul) and prove they DESCEND to the limit *)
(*  (coherence-preserving = well-defined mod every p^n), that the        *)
(*  projections are ring homomorphisms, and the UNIVERSAL PROPERTY.      *)
(* ================================================================= *)

From Stdlib Require Import Arith Lia.

Section Zp.

Variable p : nat.
Hypothesis Hp : 2 <= p.

Lemma pn_nonzero : forall n, p ^ n <> 0.
Proof. intro n; apply Nat.pow_nonzero; lia. Qed.

(* the nested-modulus lemma: p^n divides p^(S n), so reducing mod        *)
(* p^(S n) then mod p^n is the same as reducing mod p^n.                *)
Lemma nested_mod : forall x n, (x mod (p ^ S n)) mod (p ^ n) = x mod (p ^ n).
Proof.
  intros x n; replace (p ^ S n) with (p ^ n * p) by (rewrite Nat.pow_succ_r'; ring).
  rewrite Nat.Div0.mod_mul_r, (Nat.mul_comm (p ^ n)),
          Nat.Div0.mod_add, Nat.Div0.mod_mod; reflexivity.
Qed.

(* ================================================================= *)
(*  1.  THE OBJECT: coherent residue sequences                       *)
(* ================================================================= *)

Definition redcoh (a : nat -> nat) : Prop := forall n, a n = a (S n) mod (p ^ n).

Definition Zp : Type := { a : nat -> nat | redcoh a }.

Definition digits (X : Zp) : nat -> nat := proj1_sig X.
Definition projZ (n : nat) (X : Zp) : nat := digits X n.

(* the reduction cone: proj n commutes with the mod-p^n bonding map *)
Lemma projZ_cone : forall X n, projZ n X = projZ (S n) X mod (p ^ n).
Proof. intros X n; exact (proj2_sig X n). Qed.

(* ================================================================= *)
(*  2.  THE RING OPERATIONS, reduced mod p^n at each level           *)
(* ================================================================= *)

Definition rzero : nat -> nat := fun _ => 0.
Definition rone  : nat -> nat := fun n => 1 mod (p ^ n).
Definition radd (a b : nat -> nat) : nat -> nat := fun n => (a n + b n) mod (p ^ n).
Definition rmul (a b : nat -> nat) : nat -> nat := fun n => (a n * b n) mod (p ^ n).

(* each operation DESCENDS to the inverse limit (preserves coherence) *)
Lemma redcoh_zero : redcoh rzero.
Proof. intro n; unfold rzero; rewrite Nat.Div0.mod_0_l; reflexivity. Qed.

Lemma redcoh_one : redcoh rone.
Proof. intro n; unfold rone; rewrite nested_mod; reflexivity. Qed.

Lemma redcoh_add : forall a b, redcoh a -> redcoh b -> redcoh (radd a b).
Proof.
  intros a b Ha Hb n; unfold radd.
  rewrite nested_mod, (Ha n), (Hb n), <- Nat.Div0.add_mod; reflexivity.
Qed.

Lemma redcoh_mul : forall a b, redcoh a -> redcoh b -> redcoh (rmul a b).
Proof.
  intros a b Ha Hb n; unfold rmul.
  rewrite nested_mod, (Ha n), (Hb n), <- Nat.Div0.mul_mod; reflexivity.
Qed.

(* the ring operations packaged as Z_p elements *)
Definition Zzero : Zp := exist redcoh rzero redcoh_zero.
Definition Zone  : Zp := exist redcoh rone redcoh_one.
Definition Zadd (X Y : Zp) : Zp :=
  exist redcoh (radd (digits X) (digits Y)) (redcoh_add _ _ (proj2_sig X) (proj2_sig Y)).
Definition Zmul (X Y : Zp) : Zp :=
  exist redcoh (rmul (digits X) (digits Y)) (redcoh_mul _ _ (proj2_sig X) (proj2_sig Y)).

(* the projections are RING HOMOMORPHISMS to Z/p^n *)
Lemma projZ_add : forall X Y n, projZ n (Zadd X Y) = (projZ n X + projZ n Y) mod (p ^ n).
Proof. reflexivity. Qed.
Lemma projZ_mul : forall X Y n, projZ n (Zmul X Y) = (projZ n X * projZ n Y) mod (p ^ n).
Proof. reflexivity. Qed.

(* commutativity (a sample ring axiom; the rest lift levelwise the same way) *)
Lemma radd_comm : forall a b n, radd a b n = radd b a n.
Proof. intros a b n; unfold radd; rewrite Nat.add_comm; reflexivity. Qed.
Lemma rmul_comm : forall a b n, rmul a b n = rmul b a n.
Proof. intros a b n; unfold rmul; rewrite Nat.mul_comm; reflexivity. Qed.

(* ================================================================= *)
(*  3.  UNIVERSAL PROPERTY: coherent residue data assembles into Z_p  *)
(*      (this IS completeness: a coherent Cauchy tower has a limit)    *)
(* ================================================================= *)

Definition Zmediate {A : Type} (fam : forall n, A -> nat)
  (coh : forall z n, fam n z = fam (S n) z mod (p ^ n)) (z : A) : Zp :=
  exist redcoh (fun n => fam n z) (coh z).

Lemma Zmediate_proj : forall {A} (fam : forall n, A -> nat) coh n z,
  projZ n (@Zmediate A fam coh z) = fam n z.
Proof. reflexivity. Qed.

(* ----------------------------------------------------------------- *)
(*  MASTER THEOREM — Z_p as inverse-limit ring, axiom-free           *)
(* ----------------------------------------------------------------- *)

Theorem padic_integers :
  (* the projection cone commutes with the mod-p^n bonding maps *)
  (forall X n, projZ n X = projZ (S n) X mod (p ^ n))
  (* the ring operations descend to the inverse limit *)
  /\ redcoh rzero /\ redcoh rone
  /\ (forall a b, redcoh a -> redcoh b -> redcoh (radd a b))
  /\ (forall a b, redcoh a -> redcoh b -> redcoh (rmul a b))
  (* the projections are ring homomorphisms *)
  /\ (forall X Y n, projZ n (Zadd X Y) = (projZ n X + projZ n Y) mod (p ^ n))
  /\ (forall X Y n, projZ n (Zmul X Y) = (projZ n X * projZ n Y) mod (p ^ n))
  (* universal property: coherent residue data assembles into a limit point *)
  /\ (forall (A : Type) (fam : forall n, A -> nat)
        (coh : forall z n, fam n z = fam (S n) z mod (p ^ n)) n z,
        projZ n (Zmediate fam coh z) = fam n z).
Proof.
  split; [ exact projZ_cone | ].
  split; [ exact redcoh_zero | ].
  split; [ exact redcoh_one | ].
  split; [ exact redcoh_add | ].
  split; [ exact redcoh_mul | ].
  split; [ exact projZ_add | ].
  split; [ exact projZ_mul
         | intros A fam coh n z; exact (Zmediate_proj fam coh n z) ].
Qed.

End Zp.

Print Assumptions padic_integers.

(* ================================================================= *)
(*  END PadicIntegers.v                                               *)
(*  Z_p = lim Z/p^n as coherent residue sequences, with the reduction   *)
(*  projection cone, ring operations that descend to the limit, ring-   *)
(*  homomorphism projections, and the universal property (= complete-   *)
(*  ness).  ZERO Admitted; Closed under the global context.            *)
(* ================================================================= *)
