(* ================================================================= *)
(*  ArchimedeanTower.v  —  the ARCHIMEDEAN PLACE as the stationary     *)
(*  limit of the PRIMORIAL LATTICE.                                   *)
(*                                                                    *)
(*  Reframing (per the product-formula-first architecture): the        *)
(*  archimedean place ∞ is NOT primitive — it is the product-formula   *)
(*  dual of the primorial lattice Λ_B = {primes ≤ B}.  For a positive  *)
(*  integer n, its archimedean size |n|_∞ = n is RECONSTRUCTED from     *)
(*  the p-adic data over the primorial cutoff:                        *)
(*                                                                    *)
(*     inject_Z n  ==  / fabs (primes_upto B) ks     (ks factorises n) *)
(*                                                                    *)
(*  where fabs = ∏_{p≤B} |n|_p (ProductFormulaQ).  The key structural  *)
(*  fact is STATIONARITY: this holds at EVERY cutoff B ≥ n and the      *)
(*  reconstructed value is INDEPENDENT of B — primes p ∤ n contribute   *)
(*  |n|_p = 1, so growing the primorial lattice past n adds nothing.   *)
(*  So |n|_∞ is the eventually-stationary value of the primorial tower  *)
(*  — a finite, purely-rational statement, AXIOM-FREE, needing no ℝ.    *)
(*                                                                    *)
(*  This is the DEFINITIONAL layer: the archimedean place from the     *)
(*  primes.  The metric COMPLETION to ℝ/CReal (irrationals, limits)    *)
(*  is a separate layer; the Gaussian / θ / functional equation are    *)
(*  the RESIDUAL analytic structure emergent ON TOP of that            *)
(*  completion — not part of this reconstruction.                     *)
(*                                                                    *)
(*  Extends ProductFormulaQ (generalises product_formula_int from the  *)
(*  single cutoff B = n to the whole tower B ≥ n).  Axiom-free over    *)
(*  Q / Z.                                                            *)
(* ================================================================= *)

Require Import PrimeFactorizationN PrimeFactorizationExists PrimonGas ProductFormulaQ.
From Stdlib Require Import ZArith Znumtheory QArith Lqa Lia List.
Import ListNotations.
Open Scope Q_scope.

(* ----------------------------------------------------------------- *)
(*  Reciprocity: a·b = 1 makes a the reciprocal of b.                *)
(* ----------------------------------------------------------------- *)

Lemma recip_of_pf : forall a b : Q, a * b == 1 -> a == / b.
Proof.
  intros a b H.
  assert (Hb : ~ b == 0) by (intro Hb0; rewrite Hb0, Qmult_0_r in H; lra).
  setoid_replace a with (a * b * / b) by (field; exact Hb).
  rewrite H; field; exact Hb.
Qed.

(* THE reconstruction: the archimedean size is the reciprocal of the   *)
(* p-adic product over any prime list that factorises n.               *)
Lemma fabs_recip : forall ps ks, Forall prime ps -> length ps = length ks ->
  inject_Z (code ps ks) == / fabs ps ks.
Proof. intros ps ks Hpr Hlen; apply recip_of_pf, pf_int; assumption. Qed.

(* ----------------------------------------------------------------- *)
(*  THE PRIMORIAL ARCHIMEDEAN TOWER.                                  *)
(*  For every primorial cutoff B ≥ n, the p-adic product over          *)
(*  primes_upto B reconstructs |n|_∞ = n.                             *)
(* ----------------------------------------------------------------- *)

Theorem archimedean_reconstruct : forall n B, (0 < n)%Z -> (n <= Z.of_nat B)%Z ->
  exists ks,
       length (primes_upto B) = length ks
    /\ code (primes_upto B) ks = n
    /\ inject_Z n * fabs (primes_upto B) ks == 1        (* product formula      *)
    /\ inject_Z n == / fabs (primes_upto B) ks.         (* |n|_∞ reconstructed  *)
Proof.
  intros n B Hn HB.
  assert (Hsm : forall q, prime q -> (q | n)%Z -> In q (primes_upto B)).
  { intros q Hq Hqn; apply primes_upto_complete; [ exact Hq | ].
    apply Z.le_trans with n; [ apply Z.divide_pos_le; [ exact Hn | exact Hqn ] | exact HB ]. }
  destruct (code_surj (primes_upto B) (primes_upto_Forall B) (primes_upto_nodup B) n Hn Hsm)
    as [ks [Hlen Hcode]].
  exists ks; split; [ exact Hlen | split; [ exact Hcode | split ] ].
  - rewrite <- Hcode; apply pf_int; [ apply primes_upto_Forall | exact Hlen ].
  - rewrite <- Hcode; apply fabs_recip; [ apply primes_upto_Forall | exact Hlen ].
Qed.

(* ----------------------------------------------------------------- *)
(*  STATIONARITY: the reconstructed archimedean value is independent   *)
(*  of the primorial cutoff — the tower is eventually constant at      *)
(*  |n|_∞.  (Both reconstructions equal inject_Z n.)                   *)
(* ----------------------------------------------------------------- *)

Corollary archimedean_stationary : forall n B1 B2, (0 < n)%Z ->
  (n <= Z.of_nat B1)%Z -> (n <= Z.of_nat B2)%Z ->
  exists ks1 ks2,
       code (primes_upto B1) ks1 = n
    /\ code (primes_upto B2) ks2 = n
    /\ / fabs (primes_upto B1) ks1 == / fabs (primes_upto B2) ks2.
Proof.
  intros n B1 B2 Hn H1 H2.
  destruct (archimedean_reconstruct n B1 Hn H1) as [ks1 [_ [Hc1 [_ He1]]]].
  destruct (archimedean_reconstruct n B2 Hn H2) as [ks2 [_ [Hc2 [_ He2]]]].
  exists ks1, ks2; split; [ exact Hc1 | split; [ exact Hc2 | ] ].
  rewrite <- He1, <- He2; reflexivity.
Qed.

(* the archimedean value is literally the stationary reconstruction    *)
Corollary archimedean_value : forall n B, (0 < n)%Z -> (n <= Z.of_nat B)%Z ->
  exists ks, code (primes_upto B) ks = n /\ / fabs (primes_upto B) ks == inject_Z n.
Proof.
  intros n B Hn HB.
  destruct (archimedean_reconstruct n B Hn HB) as [ks [_ [Hc [_ He]]]].
  exists ks; split; [ exact Hc | rewrite <- He; reflexivity ].
Qed.

Print Assumptions archimedean_reconstruct.
Print Assumptions archimedean_stationary.

(* ================================================================= *)
(*  END ArchimedeanTower.v                                           *)
(*  |n|_∞ = / (∏_{p≤B} |n|_p) at every primorial cutoff B ≥ n, and     *)
(*  the value is cutoff-independent: the archimedean place is the      *)
(*  stationary limit of the primorial lattice, defined FROM the        *)
(*  primes, axiom-free over Q.  The completion to ℝ/CReal — and the    *)
(*  residual Gaussian on top of it — is the next, separate layer.     *)
(* ================================================================= *)
