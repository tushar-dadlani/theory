(* ================================================================= *)
(*  EulerProductAssembly.v  —  the primorial-indexed product of the      *)
(*  per-prime factors, tying prime_infinity_picture to the Euler product.*)
(*                                                                    *)
(*  prime_infinity_picture (PrimeInfinities.v) gave, for each prime p,    *)
(*  the per-prime factor  p/(p-1) = Sum_k (1/p)^k  (the additive sum over *)
(*  the exponent-count reconciling the prime's geometric infinity).      *)
(*                                                                    *)
(*  The Euler-product assembly is the PRODUCT of those factors over       *)
(*  primes, indexed by the prime-COUNT k (the primorial index):          *)
(*                                                                    *)
(*    euler_prod k = prod_{i<k} p_i/(p_i - 1),                          *)
(*                                                                    *)
(*  with, mirroring the primorial's growth primor(S k) = primor k . P k:  *)
(*                                                                    *)
(*    euler_prod (S k) = euler_prod k . (P k/(P k - 1))    (adjoin next   *)
(*                                       prime's factor -- same rung)     *)
(*    euler_prod k . (prod (p_i - 1)) = primorial k        (primorial-    *)
(*                                       relativized identity)            *)
(*    euler_prod k = primorial k / prod (p_i - 1)          (the reduced   *)
(*                                       residue reciprocal density)      *)
(*                                                                    *)
(*  and each rung's factor IS the additive geometric sum (pfactor_geom,   *)
(*  = prime_euler_factor).  This is the s=1 rung of the Euler product     *)
(*  zeta(s) = prod_p 1/(1 - p^{-s}); at s=1 the factor is p/(p-1).        *)
(*                                                                    *)
(*  Axiom-clean.                                                        *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import PrimeInfinities.
Open Scope R_scope.

Section Assembly.
Variable P : nat -> R.                 (* abstract prime enumeration *)
Hypothesis HP : forall i, 2 <= P i.    (* each prime is >= 2 *)

(* the per-prime factor (the s=1 Euler factor, from prime_infinity_picture) *)
Definition pfactor (i : nat) : R := P i / (P i - 1).

(* the primorial-indexed product of the per-prime factors *)
Fixpoint euler_prod (k : nat) : R :=
  match k with 0 => 1 | S k' => euler_prod k' * pfactor k' end.

(* the primorial (product of the first k primes) *)
Fixpoint primorial (k : nat) : R :=
  match k with 0 => 1 | S k' => primorial k' * P k' end.

(* the product of the (p_i - 1)'s = the phi-like denominator *)
Fixpoint denom (k : nat) : R :=
  match k with 0 => 1 | S k' => denom k' * (P k' - 1) end.

(* each rung adjoins the next prime's factor -- mirrors primorial growth *)
Lemma euler_prod_rec : forall k, euler_prod (S k) = euler_prod k * pfactor k.
Proof. reflexivity. Qed.

Lemma primorial_rec : forall k, primorial (S k) = primorial k * P k.
Proof. reflexivity. Qed.

(* the reconciliation, per rung: the factor IS the additive geometric sum *)
Lemma pfactor_geom : forall i,
  Un_cv (fun K => sum_f_R0 (fun k => (/ P i) ^ k) K) (pfactor i).
Proof. intro i. unfold pfactor. apply prime_euler_factor. apply HP. Qed.

Lemma denom_pos : forall k, 0 < denom k.
Proof.
  induction k as [| k IH]; simpl; [ lra | ].
  apply Rmult_lt_0_compat; [ exact IH | pose proof (HP k); lra ].
Qed.

(* the primorial-relativized identity: (prod of factors).(prod of (p-1)) = primorial *)
Theorem euler_prod_denom : forall k, euler_prod k * denom k = primorial k.
Proof.
  induction k as [| k IH]; [ simpl; ring | ].
  cbn [euler_prod primorial denom]. unfold pfactor.
  assert (Hk : P k - 1 <> 0) by (pose proof (HP k); lra).
  replace (euler_prod k * (P k / (P k - 1)) * (denom k * (P k - 1)))
    with (euler_prod k * denom k * P k) by (field; exact Hk).
  rewrite IH. reflexivity.
Qed.

(* hence the product of per-prime factors = primorial / prod(p-1)
   (the reduced-residue reciprocal density) *)
Theorem euler_prod_eq : forall k, euler_prod k = primorial k / denom k.
Proof.
  intro k. rewrite <- euler_prod_denom.
  pose proof (denom_pos k). field; lra.
Qed.

(* ===== the assembly, bundled ===== *)
Theorem euler_assembly :
  (forall k, euler_prod (S k) = euler_prod k * pfactor k)          (* adjoin next prime's factor *)
  /\ (forall k, primorial (S k) = primorial k * P k)              (* primorial grows by same prime *)
  /\ (forall i, Un_cv (fun K => sum_f_R0 (fun k => (/ P i) ^ k) K) (pfactor i)) (* factor = add. geom sum *)
  /\ (forall k, euler_prod k * denom k = primorial k)            (* factors x (p-1)-product = primorial *)
  /\ (forall k, euler_prod k = primorial k / denom k).           (* = primorial / phi-like denom *)
Proof.
  split; [ exact euler_prod_rec | ].
  split; [ exact primorial_rec | ].
  split; [ exact pfactor_geom | ].
  split; [ exact euler_prod_denom | ].
  exact euler_prod_eq.
Qed.

End Assembly.

Print Assumptions euler_prod_denom.
Print Assumptions euler_assembly.
