(* ================================================================= *)
(*  LadderOps.v                                                       *)
(*                                                                    *)
(*  LADDER OPERATORS and DIFFERENTIATION OVER THE LATTICE, over Q,    *)
(*  axiom-free -- the second-quantised view of the primon gas.        *)
(*                                                                    *)
(*  On the occupation-number lattice of one mode, the monomial x^k    *)
(*  is the state of occupation k.  The ladder / calculus operators:    *)
(*                                                                    *)
(*    creation      M : x^k |-> x^{k+1}   (occupation k -> k+1)         *)
(*    annihilation  D : x^k |-> k x^{k-1} (the formal derivative d/dx) *)
(*    number        N : x^k |-> k x^k     (counts occupation)          *)
(*                                                                    *)
(*  Differentiation over the (discrete) lattice IS the annihilation    *)
(*  operator D = d/dx, and the NUMBER operator is  N = x . d/dx  =     *)
(*  M . D.  We prove:                                                 *)
(*    - MD : x * D(x^k) = N(x^k)          (N = x d/dx, termwise)        *)
(*    - weyl : D(M x^k) - M(D x^k) = x^k  (the Weyl relation [D,M]=1)   *)
(*    - deriv_number : x * (d/dx of the partition function) = the      *)
(*      number-weighted sum   sum_k k x^k   (the mean-occupation        *)
(*      generating function, x d/dx Z)                                 *)
(*    - create_mult : creation multiplies the number by the base       *)
(*      (x^{k+1} = x . x^k), i.e. on n = p^k creation is "times p".     *)
(*                                                                    *)
(*  So the arithmetic ladder (multiply / divide by a prime) and the    *)
(*  analytic ladder (x d/dx / d/dx on the generating function) are the *)
(*  same operators, and N counts the occupation = the p-adic valuation.*)
(* ================================================================= *)

Require Import PrimonGas.
From Stdlib Require Import QArith Lqa ZArith List Lia.
Import ListNotations.
Open Scope Q_scope.

(* ================================================================= *)
(*  1.  THE OPERATORS                                                 *)
(* ================================================================= *)

(* on occupation numbers (the lattice points) *)
Definition create     (k : nat) : nat := S k.
Definition annihilate (k : nat) : nat := Nat.pred k.
Definition number     (k : nat) : nat := k.

(* on the monomial coefficients (the generating-function calculus) *)
(* annihilation = formal derivative:  d/dx (x^k) = k x^{k-1}         *)
Definition Dx (x : Q) (k : nat) : Q := inject_Z (Z.of_nat k) * qpow x (Nat.pred k).
(* number operator:  N(x^k) = k x^k                                  *)
Definition Nx (x : Q) (k : nat) : Q := inject_Z (Z.of_nat k) * qpow x k.

(* basic lattice ladder facts *)
Lemma annihilate_create : forall k, annihilate (create k) = k.
Proof. intro k; reflexivity. Qed.

Lemma annihilate_vacuum : annihilate 0%nat = 0%nat.
Proof. reflexivity. Qed.

Lemma number_id : forall k, number k = k.
Proof. reflexivity. Qed.

(* creation multiplies the underlying number by the base:
   x^{k+1} = x * x^k.  With x = p this is  p^{k+1} = p * p^k,
   i.e. creation on n = p^k is "multiply by p". *)
Lemma create_mult : forall x k, qpow x (create k) == x * qpow x k.
Proof. intros x k; reflexivity. Qed.

(* ================================================================= *)
(*  2.  N = x . d/dx  (number operator = base times derivative)      *)
(* ================================================================= *)

Lemma injSk : forall k, inject_Z (Z.of_nat (S k)) == inject_Z (Z.of_nat k) + 1.
Proof.
  intro k; replace (Z.of_nat (S k)) with (Z.of_nat k + 1)%Z by lia.
  rewrite inject_Z_plus; reflexivity.
Qed.

(* the number operator is the base times the annihilation operator *)
Theorem MD : forall x k, x * Dx x k == Nx x k.
Proof.
  intros x k; unfold Dx, Nx; destruct k as [|k'].
  - simpl; ring.
  - simpl (Nat.pred (S k'));
    change (qpow x (S k')) with (x * qpow x k'); ring.
Qed.

(* ================================================================= *)
(*  3.  THE WEYL / CANONICAL COMMUTATION RELATION  [D, M] = 1        *)
(* ================================================================= *)

(* D(M x^k) - M(D x^k) = x^k.  Here M x^k = x^{k+1} = create,          *)
(* D(x^{k+1}) = (k+1) x^k, and M(D x^k) = x * D x^k = N x^k = k x^k.    *)
Theorem weyl : forall x k, Dx x (create k) - x * Dx x k == qpow x k.
Proof.
  intros x k; rewrite (MD x k); unfold Dx, Nx, create.
  simpl (Nat.pred (S k)); rewrite injSk; ring.
Qed.

(* ================================================================= *)
(*  4.  DIFFERENTIATION OF THE PARTITION FUNCTION = NUMBER SUM        *)
(* ================================================================= *)

(* d/dx of the truncated partition function psum = sum_k x^k *)
Definition dsum (x : Q) (K : nat) : Q := qsum (map (Dx x) (seq 0 K)).
(* the number-weighted sum  sum_k k x^k  =  x d/dx Z  (mean occupation) *)
Definition nsum (x : Q) (K : nat) : Q := qsum (map (Nx x) (seq 0 K)).

(* x . d/dx of the partition function is the number-weighted sum:      *)
(* applying x d/dx term by term applies the number operator.           *)
Theorem deriv_number : forall x K, x * dsum x K == nsum x K.
Proof.
  intros x K; unfold nsum, dsum.
  rewrite <- (qsum_map_scale_l nat x (Dx x) (seq 0 K)).
  apply qsum_map_ext; intro k; apply MD.
Qed.

(* ----------------------------------------------------------------- *)
(*  MASTER THEOREM — axiom-free over Q                               *)
(* ----------------------------------------------------------------- *)

Theorem ladder_ops :
  (* the lattice ladder: annihilation undoes creation, vacuum is killed *)
  (forall k, annihilate (create k) = k)
  /\ annihilate 0%nat = 0%nat
  (* creation = multiply the number by the base (times p) *)
  /\ (forall x k, qpow x (create k) == x * qpow x k)
  (* the number operator is base times derivative:  N = x d/dx *)
  /\ (forall x k, x * Dx x k == Nx x k)
  (* the Weyl / canonical commutation relation  [D, M] = 1 *)
  /\ (forall x k, Dx x (create k) - x * Dx x k == qpow x k)
  (* x d/dx of the partition function = number-weighted (mean-occupation) sum *)
  /\ (forall x K, x * dsum x K == nsum x K).
Proof.
  split; [ exact annihilate_create | ].
  split; [ exact annihilate_vacuum | ].
  split; [ exact create_mult | ].
  split; [ exact MD | ].
  split; [ exact weyl | exact deriv_number ].
Qed.

Print Assumptions ladder_ops.

(* ================================================================= *)
(*  END LadderOps.v                                                   *)
(*  Ladder operators on the occupation lattice: annihilation = d/dx    *)
(*  (differentiation over the lattice), number = x d/dx = M.D, Weyl     *)
(*  relation [D,M]=1, and x d/dx Z = the number-weighted sum.          *)
(*  ZERO Admitted; Closed under the global context.                    *)
(* ================================================================= *)
