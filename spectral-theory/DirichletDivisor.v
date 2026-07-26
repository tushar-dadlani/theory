(* ================================================================= *)
(*  DirichletDivisor.v                                              *)
(*                                                                    *)
(*  THE DIVISOR FUNCTIONS τ, σ, σ_k as Dirichlet convolutions, and    *)
(*  their MULTIPLICATIVITY — immediate from DirichletMult.dconv_mult. *)
(*                                                                    *)
(*     τ   = 1 ∗ 1        (number of divisors)                        *)
(*     σ   = id ∗ 1       (sum of divisors)                           *)
(*     σ_k = id_k ∗ 1     (id_k(n) = n^k)                             *)
(*                                                                    *)
(*  Since 1, id, id_k are multiplicative, all three are multiplicative*)
(*  by dconv_mult.  Also gives their standard divisor-sum values.     *)
(*  AXIOM-FREE.                                                       *)
(* ================================================================= *)

From Stdlib Require Import ZArith Arith Lia List.
Import ListNotations.
Require Import HopfGroupTensor Totient DirichletConv DirichletMult.
Open Scope Z_scope.

(* ================================================================= *)
(*  id_k, τ, σ, σ_k                                                   *)
(* ================================================================= *)
Definition didk (k : nat) : nat -> Z := fun n => Z.of_nat (n ^ k).
Definition dtau : nat -> Z := dconv done done.
Definition dsigma : nat -> Z := dconv did done.
Definition dsigmak (k : nat) : nat -> Z := dconv (didk k) done.

(* id_k is (completely) multiplicative *)
Lemma didk_mult : forall k, multiplicative (didk k).
Proof.
  intro k; split.
  - unfold didk; rewrite Nat.pow_1_l; reflexivity.
  - intros m n _ _ _; unfold didk; rewrite Nat.pow_mul_l, Nat2Z.inj_mul; reflexivity.
Qed.

(* ================================================================= *)
(*  MULTIPLICATIVITY                                                  *)
(* ================================================================= *)
Theorem dtau_mult : multiplicative dtau.
Proof. unfold dtau; apply dconv_mult; apply done_mult. Qed.

Theorem dsigma_mult : multiplicative dsigma.
Proof. unfold dsigma; apply dconv_mult; [ apply did_mult | apply done_mult ]. Qed.

Theorem dsigmak_mult : forall k, multiplicative (dsigmak k).
Proof. intro k; unfold dsigmak; apply dconv_mult; [ apply didk_mult | apply done_mult ]. Qed.

(* ================================================================= *)
(*  Standard divisor-sum values                                      *)
(* ================================================================= *)
Lemma sumf_ones : forall {T} (l : list T), sumf l (fun _ => 1%Z) = Z.of_nat (length l).
Proof.
  intros T l; induction l as [|a l IH]; [ reflexivity | ].
  rewrite sumf_cons', IH; cbn [length]; rewrite Nat2Z.inj_succ; lia.
Qed.

(* τ(n) = number of divisors of n *)
Theorem dtau_as_div : forall n, (1 <= n)%nat -> dtau n = Z.of_nat (length (divisors n)).
Proof.
  intros n Hn; unfold dtau; rewrite (dconv_as_div done done n Hn); unfold done.
  transitivity (sumf (divisors n) (fun _ => 1%Z)); [ apply sumf_ext; intros; ring | apply sumf_ones ].
Qed.

(* σ(n) = sum of the divisors of n *)
Theorem dsigma_as_div : forall n, (1 <= n)%nat ->
  dsigma n = sumf (divisors n) (fun d => Z.of_nat d).
Proof.
  intros n Hn; unfold dsigma; rewrite (dconv_as_div did done n Hn); unfold did, done.
  apply sumf_ext; intros; ring.
Qed.

(* σ_k(n) = sum of the k-th powers of the divisors of n *)
Theorem dsigmak_as_div : forall k n, (1 <= n)%nat ->
  dsigmak k n = sumf (divisors n) (fun d => Z.of_nat (d ^ k)).
Proof.
  intros k n Hn; unfold dsigmak; rewrite (dconv_as_div (didk k) done n Hn); unfold didk, done.
  apply sumf_ext; intros; ring.
Qed.

Print Assumptions dtau_mult.
Print Assumptions dsigma_mult.
Print Assumptions dsigmak_mult.

(* ================================================================= *)
(*  END DirichletDivisor.v                                          *)
(*  τ = 1∗1, σ = id∗1, σ_k = id_k∗1, all multiplicative.  Closed      *)
(*  under the global context (axiom-free).                           *)
(* ================================================================= *)
