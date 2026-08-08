(* ================================================================= *)
(*  CUnifCont.v  —  Milestone C, brick C2d Block A: the 2D uniform      *)
(*  continuity of Fp∘arc, uniform in θ over the compact [0,2π].          *)
(*                                                                    *)
(*  This discharges the Harc_uc hypothesis of CCauchyFormula.  Proof by  *)
(*  a finite open cover of [0,2π] (compact_P3), mirroring Rtopology's    *)
(*  Heine: the cover radius at each θ* is the lub of "good box radii",   *)
(*  which is choice-free (canonical), keeping the four-axiom budget.     *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia Rtopology.
Require Import ComplexField Cmodulus CSeries CPathIntegral.
Open Scope R_scope.

(* ---- Lipschitz bounds for sin and cos (|f'| <= 1) ---- *)
Lemma deriv_lip1 : forall (f f' : R -> R),
  (forall c, derivable_pt_lim f c (f' c)) ->
  (forall c, Rabs (f' c) <= 1) ->
  forall x y, Rabs (f x - f y) <= Rabs (x - y).
Proof.
  intros f f' Hd Hb x y.
  destruct (Rtotal_order x y) as [Hlt | [Heq | Hgt]].
  - destruct (MVT_cor2 f f' x y Hlt (fun c _ => Hd c)) as [c [Hc _]].
    rewrite Rabs_minus_sym, Hc, Rabs_mult, (Rabs_minus_sym y x).
    apply Rle_trans with (1 * Rabs (x - y));
      [ apply Rmult_le_compat_r; [ apply Rabs_pos | apply Hb ] | lra ].
  - subst; replace (f y - f y) with 0 by ring; replace (y - y) with 0 by ring;
      rewrite Rabs_R0; apply Rle_refl.
  - destruct (MVT_cor2 f f' y x Hgt (fun c _ => Hd c)) as [c [Hc _]].
    rewrite Hc, Rabs_mult.
    apply Rle_trans with (1 * Rabs (x - y));
      [ apply Rmult_le_compat_r; [ apply Rabs_pos | apply Hb ] | lra ].
Qed.

Lemma cos_lip : forall x y, Rabs (cos x - cos y) <= Rabs (x - y).
Proof.
  apply (deriv_lip1 cos (fun c => - sin c)).
  - intro c; apply derivable_pt_lim_cos.
  - intro c; rewrite Rabs_Ropp; apply Rabs_le; pose proof (SIN_bound c); lra.
Qed.

Lemma sin_lip : forall x y, Rabs (sin x - sin y) <= Rabs (x - y).
Proof.
  apply (deriv_lip1 sin cos).
  - intro c; apply derivable_pt_lim_sin.
  - intro c; apply Rabs_le; pose proof (COS_bound c); lra.
Qed.

(* ---- arc is jointly continuous in (ρ,θ) ---- *)
Lemma arc_joint_cont : forall r0 t0 eps, 0 < eps -> exists b, 0 < b /\
  forall rho t, Rabs (rho - r0) < b -> Rabs (t - t0) < b ->
    Cmod (Cminus (arc rho t) (arc r0 t0)) < eps.
Proof.
  intros r0 t0 eps Heps.
  exists (eps / (2 * (1 + Rabs r0))).
  assert (Hpos : 0 < 2 * (1 + Rabs r0)) by (pose proof (Rabs_pos r0); lra).
  split; [ apply Rdiv_lt_0_compat; lra | ].
  intros rho t Hr Ht.
  set (b := eps / (2 * (1 + Rabs r0))) in *.
  eapply Rle_lt_trans; [ apply Cmod_le_sum | ].
  unfold arc, Cminus; cbn [Re Im].
  (* |ρcos t − r0 cos t0| + |ρ sin t − r0 sin t0| < eps *)
  assert (Hb1 : Rabs (rho * cos t - r0 * cos t0) <= Rabs (rho - r0) + Rabs r0 * Rabs (t - t0)).
  { replace (rho * cos t - r0 * cos t0)
       with ((rho - r0) * cos t + r0 * (cos t - cos t0)) by ring.
    eapply Rle_trans; [ apply Rabs_triang | ].
    apply Rplus_le_compat.
    - rewrite Rabs_mult; rewrite <- (Rmult_1_r (Rabs (rho - r0))) at 2.
      apply Rmult_le_compat_l; [ apply Rabs_pos | apply Rabs_le; pose proof (COS_bound t); lra ].
    - rewrite Rabs_mult; apply Rmult_le_compat_l; [ apply Rabs_pos | apply cos_lip ]. }
  assert (Hb2 : Rabs (rho * sin t - r0 * sin t0) <= Rabs (rho - r0) + Rabs r0 * Rabs (t - t0)).
  { replace (rho * sin t - r0 * sin t0)
       with ((rho - r0) * sin t + r0 * (sin t - sin t0)) by ring.
    eapply Rle_trans; [ apply Rabs_triang | ].
    apply Rplus_le_compat.
    - rewrite Rabs_mult; rewrite <- (Rmult_1_r (Rabs (rho - r0))) at 2.
      apply Rmult_le_compat_l; [ apply Rabs_pos | apply Rabs_le; pose proof (SIN_bound t); lra ].
    - rewrite Rabs_mult; apply Rmult_le_compat_l; [ apply Rabs_pos | apply sin_lip ]. }
  pose proof (Rabs_pos r0).
  apply Rle_lt_trans with (2 * (Rabs (rho - r0) + Rabs r0 * Rabs (t - t0))); [ lra | ].
  (* both |ρ−r0|,|t−t0| < b, and 2*(b + |r0|*b) = 2*(1+|r0|)*b <= 2*(2+|r0|)*b = eps *)
  apply Rlt_le_trans with (2 * (b + Rabs r0 * b)).
  - apply Rmult_lt_compat_l; [ lra | ].
    apply Rplus_lt_le_compat; [ exact Hr | ].
    apply Rmult_le_compat_l; [ exact H | left; exact Ht ].
  - unfold b; apply Req_le; field; lra.
Qed.

(* ================================================================= *)
(*  END (part 1) — Lipschitz + joint continuity.  Cover argument next.  *)
(* ================================================================= *)
