(* ================================================================= *)
(*  UniformIntegralSwap.v  —  the integral of a uniform limit is the    *)
(*  limit of the integrals.                                             *)
(*                                                                    *)
(*  If  fn -> g  UNIFORMLY on [a,b]  and every fn (and g) is Riemann-    *)
(*  integrable there, then  RiemannInt fn -> RiemannInt g.              *)
(*                                                                    *)
(*  This is the missing real-analysis tool on the critical path to the  *)
(*  HADAMARD-PRODUCT keystone: the Jensen integral                      *)
(*    int_0^{2pi} ln|1 - r e^{i theta}| d theta = 0   (|r|<1)          *)
(*  is proved by integrating the log-kernel Fourier series             *)
(*  (LogGeomSeries.log_geom_series) term by term (each harmonic         *)
(*  integrates to 0, JensenOrthogonality.cos_int_2PI) and SWAPPING the  *)
(*  limit past the integral -- which needs exactly this theorem.        *)
(*  Stdlib has no such lemma; this supplies it.                         *)
(*                                                                    *)
(*  Proof: |int fn - int g| = |int (fn - g)| <= int |fn - g| <=         *)
(*  (b-a).eps, via RiemannInt_P13 (linearity), P16/P17 (|int|<=int|.|), *)
(*  P19 (monotonicity) and P15 (constant integral).  Axiom-clean.       *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Open Scope R_scope.

(* uniform convergence on [a,b], plain-R form (<= eps) *)
Definition Unif_conv (fn : nat -> R -> R) (g : R -> R) (a b : R) : Prop :=
  forall eps, 0 < eps -> exists N, forall n, (N <= n)%nat ->
    forall x, a <= x <= b -> Rabs (fn n x - g x) <= eps.

Theorem RiemannInt_unif_limit :
  forall (fn : nat -> R -> R) (g : R -> R) (a b : R) (Hab : a <= b)
         (prn : forall n, Riemann_integrable (fn n) a b)
         (prg : Riemann_integrable g a b),
  Unif_conv fn g a b ->
  Un_cv (fun n => RiemannInt (prn n)) (RiemannInt prg).
Proof.
  intros fn g a b Hab prn prg Hunif eps Heps.
  assert (Hden : 0 < 2 * (b - a) + 1) by lra.
  set (d := eps / (2 * (b - a) + 1)).
  assert (Hd : 0 < d) by (unfold d; apply Rdiv_lt_0_compat; assumption).
  destruct (Hunif d Hd) as [N HN].
  exists N. intros n Hn. unfold R_dist.
  set (prd := RiemannInt_P10 (-1) (prn n) prg).
  set (prabs := RiemannInt_P16 prd).
  set (preps := RiemannInt_P14 a b d).
  assert (Heq : RiemannInt (prn n) - RiemannInt prg = RiemannInt prd).
  { rewrite (RiemannInt_P13 (prn n) prg prd). ring. }
  rewrite Heq.
  apply Rle_lt_trans with (RiemannInt preps).
  - eapply Rle_trans; [ apply (RiemannInt_P17 prd prabs Hab) | ].
    apply (RiemannInt_P19 prabs preps Hab).
    intros x Hx. cbv beta. unfold fct_cte.
    replace (fn n x + -1 * g x) with (fn n x - g x) by ring.
    apply HN; [ exact Hn | lra ].
  - rewrite (RiemannInt_P15 preps). unfold d.
    apply Rlt_le_trans with (eps / (2 * (b - a) + 1) * (2 * (b - a) + 1)).
    + apply Rmult_lt_compat_l; [ apply Rdiv_lt_0_compat; assumption | lra ].
    + right. field. lra.
Qed.

Print Assumptions RiemannInt_unif_limit.
