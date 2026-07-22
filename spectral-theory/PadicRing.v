(* ================================================================= *)
(*  PadicRing.v                                                       *)
(*                                                                    *)
(*  CONSOLIDATION: the algebraic structure of Z_p (PadicIntegers).     *)
(*  Under pointwise equality Zeq, the p-adic integers form a           *)
(*  COMMUTATIVE SEMIRING (zero, one, add, mul): all the ring identities that     *)
(*  do not involve subtraction are proved here, completing the         *)
(*  "operations descend to the limit" content of PadicIntegers into a   *)
(*  full algebraic characterisation.  Axiom-free.                      *)
(*                                                                    *)
(*  Each identity reduces to the corresponding fact in the level ring   *)
(*  Z/p^n (nat mod p^n), via the Nat.Div0 idempotent-mod lemmas; the    *)
(*  unit laws use that a coherent digit is a genuine residue           *)
(*  (redcoh_lt : a n < p^n, so a n mod p^n = a n).                     *)
(*                                                                    *)
(*  DEFERRED (honest note): Z_p is a full commutative RING -- additive  *)
(*  inverses exist (-a at level n is (p^n - a n) mod p^n) -- but the     *)
(*  coherence of that negation across levels rests on nat TRUNCATED     *)
(*  subtraction and is not proved here; likewise Add Ring registration. *)
(* ================================================================= *)

Require Import PadicIntegers.
From Stdlib Require Import Arith Lia.

Section ZpRing.

Variable p : nat.
Hypothesis Hp : 2 <= p.

(* pointwise equality of p-adic integers *)
Definition Zeq (X Y : Zp p) : Prop := forall n, digits p X n = digits p Y n.

Lemma Zeq_refl  : forall X, Zeq X X.
Proof. intros X n; reflexivity. Qed.
Lemma Zeq_sym   : forall X Y, Zeq X Y -> Zeq Y X.
Proof. intros X Y H n; symmetry; apply H. Qed.
Lemma Zeq_trans : forall X Y Z, Zeq X Y -> Zeq Y Z -> Zeq X Z.
Proof. intros X Y Z H1 H2 n; rewrite H1; apply H2. Qed.

(* a coherent digit is a genuine residue: a n < p^n *)
Lemma redcoh_lt : forall a, redcoh p a -> forall n, a n < p ^ n.
Proof.
  intros a Ha n; rewrite (Ha n); apply Nat.mod_upper_bound, Nat.pow_nonzero; lia.
Qed.

(* the digit-level readouts of the operations (definitional) *)
Lemma digits_zero : forall n, digits p (Zzero p) n = 0.
Proof. reflexivity. Qed.
Lemma digits_one  : forall n, digits p (Zone p) n = 1 mod p ^ n.
Proof. reflexivity. Qed.
Lemma digits_add  : forall X Y n, digits p (Zadd p X Y) n = (digits p X n + digits p Y n) mod p ^ n.
Proof. reflexivity. Qed.
Lemma digits_mul  : forall X Y n, digits p (Zmul p X Y) n = (digits p X n * digits p Y n) mod p ^ n.
Proof. reflexivity. Qed.

(* ================================================================= *)
(*  COMMUTATIVE SEMIRING AXIOMS (under Zeq)                           *)
(* ================================================================= *)

Lemma Zadd_comm : forall X Y, Zeq (Zadd p X Y) (Zadd p Y X).
Proof. intros X Y n; rewrite !digits_add, Nat.add_comm; reflexivity. Qed.

Lemma Zmul_comm : forall X Y, Zeq (Zmul p X Y) (Zmul p Y X).
Proof. intros X Y n; rewrite !digits_mul, Nat.mul_comm; reflexivity. Qed.

Lemma Zadd_assoc : forall X Y Z, Zeq (Zadd p (Zadd p X Y) Z) (Zadd p X (Zadd p Y Z)).
Proof.
  intros X Y Z n; rewrite !digits_add.
  rewrite Nat.Div0.add_mod_idemp_l, Nat.Div0.add_mod_idemp_r, Nat.add_assoc; reflexivity.
Qed.

Lemma Zmul_assoc : forall X Y Z, Zeq (Zmul p (Zmul p X Y) Z) (Zmul p X (Zmul p Y Z)).
Proof.
  intros X Y Z n; rewrite !digits_mul.
  rewrite Nat.Div0.mul_mod_idemp_l, Nat.Div0.mul_mod_idemp_r, Nat.mul_assoc; reflexivity.
Qed.

Lemma Zadd_0_l : forall X, Zeq (Zadd p (Zzero p) X) X.
Proof.
  intros X n; rewrite digits_add, digits_zero, Nat.add_0_l, Nat.mod_small;
    [ reflexivity | apply redcoh_lt; exact (proj2_sig X) ].
Qed.

Lemma Zmul_1_l : forall X, Zeq (Zmul p (Zone p) X) X.
Proof.
  intros X n; rewrite digits_mul, digits_one, Nat.Div0.mul_mod_idemp_l,
    Nat.mul_1_l, Nat.mod_small;
    [ reflexivity | apply redcoh_lt; exact (proj2_sig X) ].
Qed.

Lemma Zmul_0_l : forall X, Zeq (Zmul p (Zzero p) X) (Zzero p).
Proof.
  intros X n; rewrite digits_mul, digits_zero, Nat.mul_0_l, Nat.Div0.mod_0_l;
    reflexivity.
Qed.

Lemma Zdistrib_l : forall X Y Z,
  Zeq (Zmul p X (Zadd p Y Z)) (Zadd p (Zmul p X Y) (Zmul p X Z)).
Proof.
  intros X Y Z n; rewrite !digits_add, !digits_mul, digits_add.
  rewrite Nat.Div0.mul_mod_idemp_r, Nat.mul_add_distr_l, <- Nat.Div0.add_mod; reflexivity.
Qed.

(* ----------------------------------------------------------------- *)
(*  MASTER THEOREM — Z_p is a commutative semiring, axiom-free        *)
(* ----------------------------------------------------------------- *)

Theorem Zp_comm_semiring :
  (forall X, Zeq X X)
  /\ (forall X Y, Zeq X Y -> Zeq Y X)
  /\ (forall X Y Z, Zeq X Y -> Zeq Y Z -> Zeq X Z)
  /\ (forall X Y, Zeq (Zadd p X Y) (Zadd p Y X))
  /\ (forall X Y Z, Zeq (Zadd p (Zadd p X Y) Z) (Zadd p X (Zadd p Y Z)))
  /\ (forall X, Zeq (Zadd p (Zzero p) X) X)
  /\ (forall X Y, Zeq (Zmul p X Y) (Zmul p Y X))
  /\ (forall X Y Z, Zeq (Zmul p (Zmul p X Y) Z) (Zmul p X (Zmul p Y Z)))
  /\ (forall X, Zeq (Zmul p (Zone p) X) X)
  /\ (forall X, Zeq (Zmul p (Zzero p) X) (Zzero p))
  /\ (forall X Y Z, Zeq (Zmul p X (Zadd p Y Z)) (Zadd p (Zmul p X Y) (Zmul p X Z))).
Proof.
  split; [ exact Zeq_refl | ].
  split; [ exact Zeq_sym | ].
  split; [ exact Zeq_trans | ].
  split; [ exact Zadd_comm | ].
  split; [ exact Zadd_assoc | ].
  split; [ exact Zadd_0_l | ].
  split; [ exact Zmul_comm | ].
  split; [ exact Zmul_assoc | ].
  split; [ exact Zmul_1_l | ].
  split; [ exact Zmul_0_l | exact Zdistrib_l ].
Qed.

End ZpRing.

Print Assumptions Zp_comm_semiring.

(* ================================================================= *)
(*  END PadicRing.v                                                   *)
(*  Z_p is a commutative semiring under pointwise equality (zero, one, add, mul);   *)
(*  every axiom reduces to Z/p^n via the Nat.Div0 mod lemmas.          *)
(*  ZERO Admitted; Closed under the global context.                    *)
(* ================================================================= *)
