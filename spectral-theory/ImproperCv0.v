(* ================================================================= *)
(*  ImproperCv0.v  —  Riemann FE milestone R2a, file 2:             *)
(*  a near-0 improper-integral toolkit  ∫₀^1 f = lim_{ε→0⁺} ∫_ε^1 f.  *)
(*                                                                    *)
(*  The mirror of ImproperCv1 (∫₁^∞), but the integrand is SINGULAR   *)
(*  at 0 (e.g. t^{a-1}, a<1), so the `Rmax 1` clamp is unusable and    *)
(*  the integrability hypothesis must be positivity-gated:            *)
(*     Hf : forall x y, 0 < x -> x <= y -> Riemann_integrable f x y.   *)
(*  We keep the partial integral TOTAL with an Rlt_dec/Rle_dec guard   *)
(*  (as with Psi), so no proof witnesses thread through the predicate. *)
(*  Existence reuses GaussImproper.monotone_seq_transfer verbatim via  *)
(*  the reciprocal reparametrization ε ↦ 1/ε (∫_ε^1 is nondecreasing   *)
(*  as ε↓, i.e. as 1/ε↑).                                             *)
(*  No new axioms (classical Reals only).                            *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import GaussImproper ImproperCv1.
Open Scope R_scope.

(* --- reciprocal limit helpers --- *)

Lemma cv_infty_recip : forall e, (forall k, 0 < e k) -> Un_cv e 0 -> cv_infty (fun k => / e k).
Proof.
  intros e He Hcv M; destruct (Rle_or_lt M 0) as [HM | HM].
  - exists 0%nat; intros k _; pose proof (Rinv_0_lt_compat (e k) (He k)); lra.
  - destruct (Hcv (/ M) (Rinv_0_lt_compat M HM)) as [N HN]; exists N; intros k Hk.
    specialize (HN k Hk); unfold R_dist in HN; rewrite Rminus_0_r in HN.
    rewrite Rabs_right in HN by (apply Rle_ge; left; apply He).
    apply Rmult_lt_reg_r with (e k); [ apply He | ].
    rewrite Rinv_l by (apply Rgt_not_eq; apply He).
    apply Rlt_le_trans with (M * / M); [ apply Rmult_lt_compat_l; [ exact HM | exact HN ] | ].
    rewrite Rinv_r; [ apply Rle_refl | apply Rgt_not_eq; exact HM ].
Qed.

Lemma Un_cv_recip_0 : forall u, (forall k, 0 < u k) -> cv_infty u -> Un_cv (fun k => / u k) 0.
Proof.
  intros u Hu Hinf eps Heps; destruct (Hinf (/ eps)) as [N HN]; exists N; intros k Hk.
  specialize (HN k Hk); unfold R_dist; rewrite Rminus_0_r.
  rewrite Rabs_right by (apply Rle_ge; left; apply Rinv_0_lt_compat; apply Hu).
  apply Rmult_lt_reg_r with (u k); [ apply Hu | ].
  rewrite Rinv_l by (apply Rgt_not_eq; apply Hu).
  rewrite <- (Rinv_r eps) by (apply Rgt_not_eq; exact Heps).
  apply Rmult_lt_compat_l; [ exact Heps | exact HN ].
Qed.

Lemma inv_ge_1 : forall x, 0 < x -> x <= 1 -> 1 <= / x.
Proof. intros x Hx Hx1; rewrite <- Rinv_1; apply Rinv_le_contravar; [ exact Hx | exact Hx1 ]. Qed.

Lemma inv_le_1 : forall x, 1 <= x -> / x <= 1.
Proof. intros x Hx; rewrite <- Rinv_1; apply Rinv_le_contravar; [ lra | exact Hx ]. Qed.

(* --- the total partial integral ∫_ε^1 f and the improper predicate --- *)

Definition rint01 (f : R -> R) (Hf : forall x y, 0 < x -> x <= y -> Riemann_integrable f x y)
  (e : R) : R :=
  match Rlt_dec 0 e with
  | left He => match Rle_dec e 1 with left He1 => RiemannInt (Hf e 1 He He1) | right _ => 0 end
  | right _ => 0
  end.

Lemma rint01_val : forall f Hf e (He : 0 < e) (He1 : e <= 1),
  rint01 f Hf e = RiemannInt (Hf e 1 He He1).
Proof.
  intros f Hf e He He1; unfold rint01.
  destruct (Rlt_dec 0 e) as [H | H]; [ | exfalso; lra ].
  destruct (Rle_dec e 1) as [H1 | H1];
    [ apply RiemannInt_P5 | exfalso; lra ].
Qed.

Definition ImproperCv0 (f : R -> R) (Hf : forall x y, 0 < x -> x <= y -> Riemann_integrable f x y)
  (I : R) : Prop :=
  forall (e : nat -> R), (forall k, 0 < e k) -> (forall k, e k <= 1) -> Un_cv e 0 ->
    Un_cv (fun k => rint01 f Hf (e k)) I.

(* ∫_ε^1 f is nonincreasing in ε (for f ≥ 0 on (0,1]). *)
Lemma rint01_mono : forall f Hf, (forall x, 0 < x -> x <= 1 -> 0 <= f x) ->
  forall y x, 0 < y -> y <= x -> x <= 1 -> rint01 f Hf x <= rint01 f Hf y.
Proof.
  intros f Hf Hpos y x Hy Hyx Hx1.
  assert (Hxpos : 0 < x) by lra.
  set (Hy1 := Rle_trans y x 1 Hyx Hx1).
  rewrite (rint01_val f Hf x Hxpos Hx1), (rint01_val f Hf y Hy Hy1).
  assert (Hyx0 : 0 <= RiemannInt (Hf y x Hy Hyx)).
  { pose proof (RiemannInt_P15 (RiemannInt_P14 y x 0)) as Hz.
    apply Rle_trans with (RiemannInt (RiemannInt_P14 y x 0)).
    - rewrite Hz; ring_simplify; apply Rle_refl.
    - apply RiemannInt_P19; [ exact Hyx | intros t Ht; unfold fct_cte; apply Hpos; lra ]. }
  pose proof (RiemannInt_P26 (Hf y x Hy Hyx) (Hf x 1 Hxpos Hx1) (Hf y 1 Hy Hy1)) as Hadd; lra.
Qed.

(* --- well-definedness via the reciprocal reparam --- *)

Theorem improper_welldef0 : forall f Hf, (forall x, 0 < x -> x <= 1 -> 0 <= f x) ->
  forall (a : nat -> R) (I : R),
    (forall k, 0 < a k) -> (forall k, a k <= 1) -> Un_cv a 0 ->
    Un_cv (fun k => rint01 f Hf (a k)) I -> ImproperCv0 f Hf I.
Proof.
  intros f Hf Hpos a I Ha0 Ha1 Hacv HaI e He0 He1 Hecv.
  set (F := fun x => rint01 f Hf (/ Rmax 1 x)).
  assert (Fmono : forall x y, 0 <= x -> x <= y -> F x <= F y).
  { intros x y Hx Hxy; unfold F.
    assert (Hmx : 1 <= Rmax 1 x) by apply Rmax_l.
    assert (Hmy : 1 <= Rmax 1 y) by apply Rmax_l.
    assert (Hmxy : Rmax 1 x <= Rmax 1 y)
      by (apply Rmax_lub; [ apply Rmax_l | apply Rle_trans with y; [ exact Hxy | apply Rmax_r ] ]).
    apply (rint01_mono f Hf Hpos (/ Rmax 1 y) (/ Rmax 1 x)).
    - apply Rinv_0_lt_compat; lra.
    - apply Rinv_le_contravar; [ lra | exact Hmxy ].
    - apply inv_le_1; exact Hmx. }
  assert (Hrep : forall (s : nat -> R), (forall k, 0 < s k) -> (forall k, s k <= 1) ->
                 forall k, F (/ s k) = rint01 f Hf (s k)).
  { intros s Hs0 Hs1 k; unfold F.
    rewrite Rmax_right by (apply inv_ge_1; [ apply Hs0 | apply Hs1 ]).
    rewrite Rinv_inv; reflexivity. }
  apply (Un_cv_ext (fun k => F (/ e k))).
  - intro k; apply Hrep; assumption.
  - apply (monotone_seq_transfer F I Fmono (fun k => / a k)
             (fun k => Rlt_le _ _ (Rinv_0_lt_compat _ (Ha0 k))) (cv_infty_recip a Ha0 Hacv)).
    + apply (Un_cv_ext (fun k => rint01 f Hf (a k))); [ | exact HaI ].
      intro k; symmetry; apply Hrep; assumption.
    + intro k; apply Rlt_le; apply Rinv_0_lt_compat; apply He0.
    + apply cv_infty_recip; assumption.
Qed.

(* --- existence from a uniform bound --- *)

Theorem improper_bounded_cv0 : forall f Hf, (forall x, 0 < x -> x <= 1 -> 0 <= f x) ->
  (exists M, forall x, 0 < x -> x <= 1 -> rint01 f Hf x <= M) ->
  { I : R | ImproperCv0 f Hf I }.
Proof.
  intros f Hf Hpos Hbnd.
  set (a := fun n => / (1 + INR n)).
  assert (Ha0 : forall k, 0 < a k)
    by (intro k; unfold a; apply Rinv_0_lt_compat; pose proof (pos_INR k); lra).
  assert (Ha1 : forall k, a k <= 1)
    by (intro k; unfold a; apply inv_le_1; pose proof (pos_INR k); lra).
  assert (Hacv : Un_cv a 0)
    by (unfold a; apply Un_cv_recip_0;
        [ intro k; pose proof (pos_INR k); lra | apply cv_infty_1_INR ]).
  assert (Hgrow : Un_growing (fun n => rint01 f Hf (a n))).
  { intro n; apply (rint01_mono f Hf Hpos (a (S n)) (a n)); [ apply Ha0 | | apply Ha1 ].
    unfold a; apply Rinv_le_contravar; [ pose proof (pos_INR n); lra | rewrite S_INR; lra ]. }
  assert (Hub : has_ub (fun n => rint01 f Hf (a n))).
  { destruct Hbnd as [M HM]; unfold has_ub, EUn, bound, is_upper_bound;
      exists M; intros r [n ->]; apply HM; [ apply Ha0 | apply Ha1 ]. }
  destruct (growing_cv (fun n => rint01 f Hf (a n)) Hgrow Hub) as [I HI].
  exists I; apply (improper_welldef0 f Hf Hpos a I Ha0 Ha1 Hacv HI).
Qed.

(* --- linearity and extensionality --- *)

Theorem improper_linear0 : forall f g l Hf Hg Hfg If Ig,
  ImproperCv0 f Hf If -> ImproperCv0 g Hg Ig ->
  ImproperCv0 (fun x => f x + l * g x) Hfg (If + l * Ig).
Proof.
  intros f g l Hf Hg Hfg If Ig HF HG e He0 He1 Hecv.
  apply (Un_cv_ext (fun k => rint01 f Hf (e k) + l * rint01 g Hg (e k))).
  - intro k; rewrite (rint01_val f Hf (e k) (He0 k) (He1 k)),
      (rint01_val g Hg (e k) (He0 k) (He1 k)),
      (rint01_val (fun x => f x + l * g x) Hfg (e k) (He0 k) (He1 k)).
    symmetry; apply (RiemannInt_P13 (Hf (e k) 1 (He0 k) (He1 k)) (Hg (e k) 1 (He0 k) (He1 k))).
  - apply CV_plus; [ apply HF; assumption | ].
    apply (CV_mult (fun _ => l) (fun k => rint01 g Hg (e k)) l Ig);
      [ apply Un_cv_const | apply HG; assumption ].
Qed.

Theorem improper_ext0 : forall f g Hf Hg I,
  (forall x, 0 < x -> x <= 1 -> f x = g x) -> ImproperCv0 f Hf I -> ImproperCv0 g Hg I.
Proof.
  intros f g Hf Hg I Heq HF e He0 He1 Hecv.
  apply (Un_cv_ext (fun k => rint01 f Hf (e k))); [ | apply HF; assumption ].
  intro k; rewrite (rint01_val f Hf (e k) (He0 k) (He1 k)),
    (rint01_val g Hg (e k) (He0 k) (He1 k)).
  apply RiemannInt_P18; [ apply He1 | intros x Hx; pose proof (He0 k); apply Heq; lra ].
Qed.

Print Assumptions improper_bounded_cv0.
Print Assumptions improper_linear0.

(* ================================================================= *)
(*  END ImproperCv0.v                                                *)
(*  ∫₀^1 toolkit: existence (bounded-monotone), linearity, extensionality. *)
(* ================================================================= *)
