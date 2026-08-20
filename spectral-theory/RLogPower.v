(* ================================================================= *)
(*  RLogPower.v  —  ln beaten by a fourth root, and what follows.      *)
(*                                                                    *)
(*    ln_le_lin   : ln x <= x - 1                                      *)
(*    ln_le_4root : ln x <= 4 . sqrt (sqrt x)                          *)
(*    ln_sq_le    : (ln x)^2 <= 16 . sqrt x            (x >= 1)        *)
(*    r_ln2_subquad : r . (ln x)^2 <= eps . r^2  eventually            *)
(*                                                                    *)
(*  SubQuadLog needs ln |H| = o(r^2), and every term of the bound is   *)
(*  O(r ln^2 r).  Closing that gap needs ln to be beaten by a POWER,   *)
(*  and ln x <= x - 1 alone is useless -- it gives ln^2 r <= r^2, not  *)
(*  o(r).  Applying it at the fourth root instead does it: writing     *)
(*  x = y^4 gives ln x = 4 ln y <= 4(y-1) <= 4 y, so ln^2 x <= 16 y^2  *)
(*  = 16 sqrt x, and r sqrt r = r^{3/2} is comfortably o(r^2).         *)
(*                                                                    *)
(*  Only sqrt is used -- no Rpower, no fractional exponents -- which   *)
(*  keeps this in the same elementary register as the rest of the      *)
(*  chain.  Axiom-clean.                                               *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra.
Open Scope R_scope.

Lemma ln_mono_le : forall x y, 0 < x -> x <= y -> ln x <= ln y.
Proof.
  intros x y Hx Hxy.
  destruct (Rle_lt_or_eq_dec x y Hxy) as [Hlt | Heq];
    [ left; apply ln_increasing; assumption | rewrite Heq; apply Rle_refl ].
Qed.

Lemma ln_le_lin : forall x, 0 < x -> ln x <= x - 1.
Proof.
  intros x Hx.
  pose proof (exp_ineq1_le (x - 1)) as H.
  replace (1 + (x - 1)) with x in H by ring.
  apply Rle_trans with (ln (exp (x - 1)));
    [ apply ln_mono_le; assumption | rewrite ln_exp; lra ].
Qed.

Lemma sqrt_quad : forall x, 0 <= x -> sqrt (sqrt x) * sqrt (sqrt x) = sqrt x.
Proof. intros x Hx. apply sqrt_sqrt, sqrt_pos. Qed.

Lemma ln_le_4root : forall x, 0 < x -> ln x <= 4 * sqrt (sqrt x).
Proof.
  intros x Hx.
  set (y := sqrt (sqrt x)).
  assert (Hy0 : 0 <= y) by (unfold y; apply sqrt_pos).
  assert (Hyx : y * y * (y * y) = x).
  { unfold y. rewrite (sqrt_quad x ltac:(lra)).
    apply sqrt_sqrt; lra. }
  assert (Hy : 0 < y).
  { destruct Hy0 as [H | H]; [ exact H | exfalso; rewrite <- H in Hyx; lra ]. }
  (* ln x = 4 ln y *)
  assert (Hln : ln x = 4 * ln y).
  { assert (Hyy : 0 < y * y) by nra.
    rewrite <- Hyx.
    rewrite (ln_mult (y * y) (y * y) Hyy Hyy).
    rewrite (ln_mult y y Hy Hy). ring. }
  pose proof (ln_le_lin y Hy). lra.
Qed.

Lemma ln_nonneg : forall x, 1 <= x -> 0 <= ln x.
Proof.
  intros x Hx. rewrite <- ln_1. apply ln_mono_le; lra.
Qed.

Lemma ln_sq_le : forall x, 1 <= x -> (ln x) ^ 2 <= 16 * sqrt x.
Proof.
  intros x Hx.
  pose proof (ln_le_4root x ltac:(lra)) as H4.
  pose proof (ln_nonneg x Hx) as H0.
  pose proof (sqrt_pos (sqrt x)) as Hs.
  assert (Hq : sqrt (sqrt x) * sqrt (sqrt x) = sqrt x)
    by (apply sqrt_quad; lra).
  nra.
Qed.

(* the o(r^2) closer, in the exact shape SubQuadLog consumes *)
Lemma r_ln2_subquad : forall (c eps : R), 0 < c -> 0 < eps ->
  exists R0, 0 < R0 /\
    forall r, R0 <= r -> c * (r * (ln r) ^ 2) <= eps * r ^ 2.
Proof.
  intros c eps Hc Heps.
  exists (Rmax 1 ((16 * c / eps) ^ 2)).
  split; [ apply Rlt_le_trans with 1; [ lra | apply Rmax_l ] | ].
  intros r Hr.
  assert (Hr1 : 1 <= r) by (apply Rle_trans with (Rmax 1 ((16 * c / eps) ^ 2));
                            [ apply Rmax_l | exact Hr ]).
  assert (Hr2 : (16 * c / eps) ^ 2 <= r)
    by (apply Rle_trans with (Rmax 1 ((16 * c / eps) ^ 2));
        [ apply Rmax_r | exact Hr ]).
  pose proof (ln_sq_le r Hr1) as Hln.
  pose proof (sqrt_pos r) as Hs0.
  assert (Hsq : sqrt r * sqrt r = r) by (apply sqrt_sqrt; lra).
  (* 16 c / eps <= sqrt r *)
  assert (Hroot : 16 * c / eps <= sqrt r).
  { assert (Hpos : 0 <= 16 * c / eps)
      by (apply Rle_mult_inv_pos; lra).
    nra. }
  (* c r ln^2 r <= 16 c r sqrt r <= eps r^2 *)
  assert (Hstep : c * (r * (ln r) ^ 2) <= c * (r * (16 * sqrt r)))
    by (apply Rmult_le_compat_l; [ lra | apply Rmult_le_compat_l; lra ]).
  assert (Hfin : c * (r * (16 * sqrt r)) <= eps * r ^ 2).
  { replace (eps * r ^ 2) with (eps * (r * (sqrt r * sqrt r))) by (rewrite Hsq; ring).
    assert (H16 : 16 * c <= eps * sqrt r).
    { apply (Rmult_le_reg_r (/ eps)); [ apply Rinv_0_lt_compat; lra | ].
      replace (eps * sqrt r * / eps) with (sqrt r) by (field; lra).
      replace (16 * c * / eps) with (16 * c / eps) by (unfold Rdiv; ring).
      exact Hroot. }
    assert (Hrs : 0 <= r * sqrt r) by nra.
    assert (Hmul : 16 * c * (r * sqrt r) <= eps * sqrt r * (r * sqrt r))
      by (apply Rmult_le_compat_r; assumption).
    nra. }
  lra.
Qed.

Print Assumptions ln_le_4root.
Print Assumptions r_ln2_subquad.
