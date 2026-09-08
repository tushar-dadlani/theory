(* ================================================================= *)
(*  CTwistEuler341.v  --  the 3-4-1 inequality for L-functions.        *)
(*                                                                    *)
(*      1 <= |L(a,chi_0)|^3 |L(a+ib,chi)|^4 |L(a+2ib,chi^2)|           *)
(*                                                    for a > 1.      *)
(*                                                                    *)
(*  The L-analogue of ThreeFourOne.tfo_zeta, assembled from            *)
(*  CTwist341.tper_prime (the per-prime inequality) over the finite    *)
(*  Euler products, then passed to the limit by                        *)
(*  CTwistedEuler.dirichlet_L_euler_product -- which plays exactly the *)
(*  role CEulerProductFull.EF_cv plays for zeta.                       *)
(*                                                                    *)
(*  The interfaces line up definitionally: CTwistedEuler.LF is         *)
(*  Cwprod (map efchi ...) with efchi q = (1 - Fchi q)^{-1}, and       *)
(*  CTwist341.tz1 p g A a b q IS Fchi p g A (mkC a b) q, so            *)
(*  Cmod (efchi q) = tQ (tz1 ... q) with nothing to prove but          *)
(*  Cmod_inv.                                                          *)
(*                                                                    *)
(*  SCOPE.  This does NOT yet give L(1+it,chi) <> 0.  The sequence     *)
(*  argument of ZetaLineNonzero needs |L(a+it0,chi)| <= C (a-1) at a   *)
(*  putative zero, i.e. L DIFFERENTIABLE at 1+it0 -- and CLSeries is   *)
(*  gated at Re s > 1.  Non-vanishing on the line is blocked behind    *)
(*  the continuation of L past Re s = 1, not behind the 3-4-1.         *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia ZArith Znumtheory List.
Require Import ComplexField Cmodulus CexpFull CPowMul CSeries CDeriv
        RootsOfUnity ZmodOrder DirichletModP EulerProductR EulerProductZeta
        CEulerProductZeta ZetaStripBound ThreeFourOne
        CharModulus CTwistedCoeff CLSeries CTwistedEuler
        CTwistPerPrime CTwist341.
Import ListNotations.
Open Scope R_scope.

(* the finite twisted Euler product, as a real number *)
Definition tEF (f : Z -> C) (N : nat) : R :=
  fold_right Rmult 1 (map (fun q => tQ (f q)) (primes_upto (S N))).

Lemma tEF_eq : forall p g A s N, 1 < Re s ->
  tEF (Fchi p g A s) N = Cmod (LF p g A s N).
Proof.
  intros p g A s N Hs. unfold tEF, LF.
  rewrite Cmod_Cwprod, map_map.
  apply f_equal, map_ext_in; intros q Hq.
  assert (Hq2 : 2 <= IZR q).
  { apply IZR_le. pose proof (primes_upto_prime (S N) q Hq) as Hpr.
    destruct Hpr; lia. }
  unfold tQ, efchi. symmetry.
  apply Cmod_inv. apply tden_ne0; assumption.
Qed.

(* the finite product inequality *)
Lemma tfinite_ineq : forall p g A a b N, 1 < a ->
  1 <= (tEF (Fchi p g 0 (mkC a 0)) N) ^ 3
       * (tEF (Fchi p g A (mkC a b)) N) ^ 4
       * (tEF (Fchi p g (2 * A) (mkC a (2 * b))) N).
Proof.
  intros p g A a b N Ha.
  assert (Hprod :
    1 <= fold_right Rmult 1
           (map (fun q => (tQ (tz0 p g a q)) ^ 3
                          * (tQ (tz1 p g A a b q)) ^ 4
                          * (tQ (tz2 p g A a b q)))
                (primes_upto (S N)))).
  { apply Rle_trans with
      (fold_right Rmult 1 (map (fun _ : Z => 1) (primes_upto (S N)))).
    - rewrite Rprod_ones; apply Rle_refl.
    - apply Rprod_map_le; intros q Hq; split; [ lra | ].
      apply tper_prime; [ exact Ha | ].
      apply IZR_le. pose proof (primes_upto_prime (S N) q Hq) as Hpr.
      destruct Hpr; lia. }
  rewrite (Rprod_mult (fun q => (tQ (tz0 p g a q)) ^ 3
                                * (tQ (tz1 p g A a b q)) ^ 4)
                      (fun q => tQ (tz2 p g A a b q))) in Hprod.
  rewrite (Rprod_mult (fun q => (tQ (tz0 p g a q)) ^ 3)
                      (fun q => (tQ (tz1 p g A a b q)) ^ 4)) in Hprod.
  rewrite (Rprod_pow (fun q => tQ (tz0 p g a q)) 3) in Hprod.
  rewrite (Rprod_pow (fun q => tQ (tz1 p g A a b q)) 4) in Hprod.
  unfold tEF. exact Hprod.
Qed.

(* ================================================================= *)
(*  THE 3-4-1 INEQUALITY FOR L-FUNCTIONS                              *)
(* ================================================================= *)
Theorem tfo_L : forall p g A a b,
  prime (Z.of_nat p) -> (1 <= g <= p - 1)%nat -> ord p g = (p - 1)%nat ->
  1 < a ->
  forall L0 L1 L2,
    Cseries_cv (Lterm p g 0 (mkC a 0)) L0 ->
    Cseries_cv (Lterm p g A (mkC a b)) L1 ->
    Cseries_cv (Lterm p g (2 * A) (mkC a (2 * b))) L2 ->
    1 <= (Cmod L0) ^ 3 * (Cmod L1) ^ 4 * (Cmod L2).
Proof.
  intros p g A a b Hp Hg Hord Ha L0 L1 L2 H0 H1 H2.
  assert (Hs0 : 1 < Re (mkC a 0)) by (cbn; lra).
  assert (Hs1 : 1 < Re (mkC a b)) by (cbn; lra).
  assert (Hs2 : 1 < Re (mkC a (2 * b))) by (cbn; lra).
  apply Rle_cv_lim with
    (Un := fun _ : nat => 1)
    (Vn := fun N => (tEF (Fchi p g 0 (mkC a 0)) N) ^ 3
                    * (tEF (Fchi p g A (mkC a b)) N) ^ 4
                    * (tEF (Fchi p g (2 * A) (mkC a (2 * b))) N)).
  - intro N; apply tfinite_ineq; exact Ha.
  - apply Un_cv_const.
  - apply (Un_cv_ext_loc
             (fun N => (Cmod (LF p g 0 (mkC a 0) N)) ^ 3
                       * (Cmod (LF p g A (mkC a b) N)) ^ 4
                       * (Cmod (LF p g (2 * A) (mkC a (2 * b)) N)))).
    + intro N. rewrite !tEF_eq by assumption. reflexivity.
    + apply CV_mult; [ apply CV_mult | ].
      * apply Un_cv_pow, CUn_cv_Cmod.
        exact (dirichlet_L_euler_product p g 0 Hp Hg Hord _ Hs0 L0 H0).
      * apply Un_cv_pow, CUn_cv_Cmod.
        exact (dirichlet_L_euler_product p g A Hp Hg Hord _ Hs1 L1 H1).
      * apply CUn_cv_Cmod.
        exact (dirichlet_L_euler_product p g (2 * A) Hp Hg Hord _ Hs2 L2 H2).
Qed.

(* ----------------------------------------------------------------- *)
(*  non-vacuity: every factor in the product is a genuine finite       *)
(*  positive real, so the bound constrains real quantities             *)
(* ----------------------------------------------------------------- *)
Lemma tQ_factor_pos : forall p g A s q, 1 < Re s -> 2 <= IZR q ->
  0 < tQ (Fchi p g A s q).
Proof.
  intros p g A s q Hs Hq. unfold tQ.
  apply Rinv_0_lt_compat, Cmod_pos_ne0.
  apply tden_ne0; assumption.
Qed.

Print Assumptions tfo_L.

(* ================================================================= *)
(*  END CTwistEuler341.v                                              *)
(* ================================================================= *)
