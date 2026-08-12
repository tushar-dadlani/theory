(* ================================================================= *)
(*  MertensThird.v                                                    *)
(*                                                                    *)
(*  MERTENS' THIRD THEOREM -- the asymptotic that pins the constant   *)
(*  in the Nicolas criterion.  (SCAFFOLD: target stated precisely,     *)
(*  reachable algebraic/positivity pieces proved; the analytic limit   *)
(*  itself is the deferred deep theorem, NOT proved here.)             *)
(*                                                                    *)
(*     prod_{p <= p_k} (1 - 1/p)  ~  e^{-gamma} / ln p_k.              *)
(*                                                                    *)
(*  Equivalently, with N_k the k-th primorial and phi Euler's totient, *)
(*     N_k / phi(N_k)  ~  e^{gamma} * ln p_k.                          *)
(*  Since theta(p_k) = ln N_k and (by PNT) ln ln N_k ~ ln p_k, this is *)
(*  exactly the RHS scale of the Nicolas inequality                    *)
(*     N_k/phi(N_k)  >  e^{gamma} * ln ln N_k                          *)
(*  from NicolasCriterion.v.  Here e^{gamma} = EulerMascheroni.egamma  *)
(*  is the CONSTRUCTED constant, so exp(-gamma) = / egamma.            *)
(*                                                                    *)
(*  What is proved (Qed): the finite Mertens product equals            *)
(*  phi(N_k)/N_k, is positive, and (under primality of the prime list) *)
(*  equals prod (1 - 1/p) via reduced_residue_density.                 *)
(*  What is STATED only: MertensThird / Nicolas_asymptotic, the        *)
(*  convergence to / egamma resp. egamma -- Mertens' deep theorem,     *)
(*  never asserted true.                                              *)
(* ================================================================= *)

From Stdlib Require Import ZArith Znumtheory Arith Lia List Reals Lra.
Require Import Totient PrimorialSpectralTheory.
Require Import NicolasCriterion EulerMascheroni.
Import ListNotations.
Local Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  The finite Mertens product, as phi(N_k)/N_k                       *)
(* ----------------------------------------------------------------- *)

Definition MertProd (k : nat) : R := INR (phi (primorial k)) / INR (primorial k).

Lemma phi_ge_1 : forall n, (1 <= n)%nat -> (1 <= phi n)%nat.
Proof.
  intros n Hn. unfold phi.
  assert (Hin : In 1%nat (filter (fun k => Nat.gcd k n =? 1) (seq 1 n))).
  { apply filter_In. split.
    - apply in_seq; lia.
    - apply Nat.eqb_eq. destruct n; reflexivity. }
  destruct (filter (fun k => Nat.gcd k n =? 1) (seq 1 n)) as [|a l] eqn:E.
  - simpl in Hin; contradiction.
  - simpl; lia.
Qed.

Lemma primorial_pos : forall k, (1 <= primorial k)%nat.
Proof.
  induction k as [|k IH]; [ simpl; lia | ].
  replace (primorial (S k)) with (primorial k * kth_prime (S k))%nat by reflexivity.
  pose proof (kth_prime_ge_2 (S k)); nia.
Qed.

Lemma MertProd_pos : forall k, 0 < MertProd k.
Proof.
  intro k. unfold MertProd. apply Rdiv_lt_0_compat.
  - apply lt_0_INR. pose proof (phi_ge_1 (primorial k) (primorial_pos k)); lia.
  - apply lt_0_INR. pose proof (primorial_pos k); lia.
Qed.

(* Under distinctness + primality of the first k+1 primes, the ratio   *)
(* phi(N_k)/N_k IS the Mertens product prod (1 - 1/p).                  *)
Lemma MertProd_is_product : forall k,
  NoDup (primorial_primes k) ->
  Forall (fun p => prime (Z.of_nat p)) (primorial_primes k) ->
  MertProd k = prodR (map (fun p => (1 - / INR p)%R) (primorial_primes k)).
Proof.
  intros k Hnd Hpr. unfold MertProd. rewrite (primorial_eq_prodl k).
  apply (reduced_residue_density (primorial_primes k) Hnd Hpr).
Qed.

(* ----------------------------------------------------------------- *)
(*  Basic positivity of the scale factor ln p_k                       *)
(* ----------------------------------------------------------------- *)

Lemma ln_kth_prime_pos : forall k, 0 < ln (INR (kth_prime k)).
Proof.
  intro k. rewrite <- ln_1. apply ln_increasing; [ lra | ].
  pose proof (one_lt_INR_ge2 (kth_prime k) (kth_prime_ge_2 k)); lra.
Qed.

(* ----------------------------------------------------------------- *)
(*  D.  Mertens' third theorem, STATED as the target (not proved)     *)
(* ----------------------------------------------------------------- *)

(* prod_{p<=p_k}(1-1/p) * ln p_k  ->  e^{-gamma} = / egamma.           *)
Definition MertensThird : Prop :=
  Un_cv (fun k => MertProd k * ln (INR (kth_prime k))) (/ egamma).

(* The reciprocal, Nicolas-facing form:                                *)
(*   (N_k/phi(N_k)) / ln p_k  ->  e^{gamma} = egamma.                   *)
Definition Nicolas_asymptotic : Prop :=
  Un_cv (fun k => (INR (primorial k) / INR (phi (primorial k)))
                    / ln (INR (kth_prime k))) egamma.

(* These two targets are equivalent (reciprocal), and each is Mertens' *)
(* third theorem in the primorial parametrization.  Proving either is  *)
(* the deferred analytic step: it needs Mertens' second theorem        *)
(* (sum_{p<=x} 1/p = ln ln x + M + o(1)) plus the identification of the *)
(* constant with gamma.  Neither is asserted true here.                *)
