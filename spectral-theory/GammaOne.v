(* ================================================================= *)
(*  GammaOne.v  —  Γ(1) = 1.                                           *)
(*                                                                    *)
(*  Γ(1) = ∫₀^∞ e^{−t} dt = 1, evaluated directly:                    *)
(*    gnear 1 1 = ∫₀^1 e^{−t} = 1 − e^{−1}   (FTC + ε→0),              *)
(*    gtail 1 1 = ∫₁^∞ e^{−t} = e^{−1}       (FTC + A→∞),              *)
(*  antiderivative −e^{−t}; the boundary terms e^{−ε}→1 and e^{−A}→0. *)
(*  This discharges the Γ(1)=1 hypothesis of ZetaValues.zeta_neg1.    *)
(*  No new axioms (classical Reals only).                            *)
(* ================================================================= *)

From Stdlib Require Import Reals Rpower Lra Lia.
Require Import GammaReal ImproperCv0 ImproperCv1 ContinuousCoV GammaFunction MellinElem.
Open Scope R_scope.

(* --- the kernels collapse to e^{−t} --- *)

Lemma gnk11 : forall x, 0 < x -> gnk 1 1 x = exp (- x).
Proof.
  intros x Hx; unfold gnk; replace (1 - 1) with 0 by ring;
    rewrite (Rpower_O x Hx); replace (1 * x) with x by ring; ring.
Qed.

Lemma gtk11 : forall u, 1 <= u -> gtk 1 1 u = exp (- u).
Proof.
  intros u Hu; unfold gtk; rewrite (clamp_id u Hu); replace (1 - 1) with 0 by ring;
    rewrite (Rpower_O u ltac:(lra)); replace (1 * u) with u by ring; ring.
Qed.

(* --- antiderivative:  d/dt (−e^{−t}) = e^{−t} --- *)

Lemma dexp : forall x, derivable_pt_lim (fun t => - exp (- t)) x (exp (- x)).
Proof.
  intro x.
  pose proof (derivable_pt_lim_comp (fun t => - t) exp x (-1) (exp (- x))
                (derivable_pt_lim_opp (fun t => t) x 1 (derivable_pt_lim_id x))
                (derivable_pt_lim_exp (- x))) as Hc.
  pose proof (derivable_pt_lim_opp (fun t => exp (- t)) x (exp (- x) * -1) Hc) as Ho.
  replace (exp (- x)) with (- (exp (- x) * -1)) by ring; exact Ho.
Qed.

(* --- the finite integrals via FTC --- *)

Lemma near_int_val : forall a (Ha : 0 < a) (Ha1 : a <= 1),
  RiemannInt (Hf_near 1 1 a 1 Ha Ha1) = exp (- a) - exp (- 1).
Proof.
  intros a Ha Ha1.
  assert (Hanti : antiderivative (gnk 1 1) (fun t => - exp (- t)) a 1).
  { split; [ | exact Ha1 ].
    intros x Hx.
    assert (Hd : derivable_pt_lim (fun t => - exp (- t)) x (gnk 1 1 x))
      by (rewrite (gnk11 x ltac:(lra)); apply dexp).
    exists (exist (fun l => derivable_pt_lim (fun t => - exp (- t)) x l) (gnk 1 1 x) Hd);
      reflexivity. }
  rewrite (FTC_antideriv (gnk 1 1) (fun t => - exp (- t)) a 1 Ha1
             (fun x Hx => cont_gnk 1 1 x ltac:(lra)) (Hf_near 1 1 a 1 Ha Ha1) Hanti); replace (- (1)) with (-1) by ring; ring.
Qed.

Lemma tail_int_val : forall A (HA : 1 <= A),
  RiemannInt (gtk_int 1 1 1 A) = exp (- 1) - exp (- A).
Proof.
  intros A HA.
  assert (Hanti : antiderivative (gtk 1 1) (fun t => - exp (- t)) 1 A).
  { split; [ | exact HA ].
    intros x Hx.
    assert (Hd : derivable_pt_lim (fun t => - exp (- t)) x (gtk 1 1 x))
      by (rewrite (gtk11 x ltac:(lra)); apply dexp).
    exists (exist (fun l => derivable_pt_lim (fun t => - exp (- t)) x l) (gtk 1 1 x) Hd);
      reflexivity. }
  rewrite (FTC_antideriv (gtk 1 1) (fun t => - exp (- t)) 1 A HA
             (fun x _ => cont_gtk 1 1 x) (gtk_int 1 1 1 A) Hanti); replace (- (1)) with (-1) by ring; ring.
Qed.

(* --- boundary limits --- *)

Lemma exp_neg_cv1 : forall e, Un_cv e 0 -> Un_cv (fun k => exp (- e k)) 1.
Proof.
  intros e He.
  replace 1 with (exp 0) by (rewrite exp_0; reflexivity).
  apply (continuity_seq exp (fun k => - e k) 0);
    [ apply derivable_continuous_pt; apply derivable_pt_exp | ].
  intros eps Heps; destruct (He eps Heps) as [N HN]; exists N; intros n Hn.
  unfold R_dist in *; replace (- e n - 0) with (- (e n - 0)) by ring;
    rewrite Rabs_Ropp; apply HN; exact Hn.
Qed.

Lemma exp_neg_infty_cv0 : forall A, (forall k, 1 <= A k) -> cv_infty A ->
  Un_cv (fun k => exp (- A k)) 0.
Proof.
  intros A HA Hinf.
  apply (Un_cv_squeeze0 (fun k => exp (- A k)) (fun k => / A k)).
  - exists 0%nat; intros k _.
    assert (Hkpos : 0 < A k) by (pose proof (HA k); lra).
    split; [ left; apply exp_pos | ].
    rewrite exp_Ropp; apply Rinv_le_contravar; [ exact Hkpos | ].
    assert (Hle : A k <= exp (A k))
      by (pose proof (exp_lb2 0 (A k) ltac:(lra)) as Hlb; simpl in Hlb; lra).
    exact Hle.
  - apply Un_cv_recip_0; [ intro k; pose proof (HA k); lra | exact Hinf ].
Qed.

(* --- gnear 1 1 = 1 − e^{−1}   and   gtail 1 1 = e^{−1} --- *)

Lemma gnear_1 : forall (H : 0 < 1) (Hc : 0 < 1), gnear 1 1 H Hc = 1 - exp (- 1).
Proof.
  intros H Hc.
  set (e := fun k => / (1 + INR k)).
  assert (He0 : forall k, 0 < e k)
    by (intro k; unfold e; apply Rinv_0_lt_compat; pose proof (pos_INR k); lra).
  assert (He1 : forall k, e k <= 1) by (intro k; unfold e; apply inv_le_1; pose proof (pos_INR k); lra).
  assert (Hecv : Un_cv e 0)
    by (unfold e; apply Un_cv_recip_0; [ intro k; pose proof (pos_INR k); lra | apply cv_infty_1_INR ]).
  apply (UL_sequence (fun k => rint01 (gnk 1 1) (Hf_near 1 1) (e k))).
  - exact (proj2_sig (gnear_sig 1 1 H Hc) e He0 He1 Hecv).
  - apply (Un_cv_ext (fun k => exp (- e k) - exp (- 1))
                     (fun k => rint01 (gnk 1 1) (Hf_near 1 1) (e k))).
    + intro k; rewrite (rint01_val (gnk 1 1) (Hf_near 1 1) (e k) (He0 k) (He1 k)),
        (near_int_val (e k) (He0 k) (He1 k)); reflexivity.
    + apply (CV_minus (fun k => exp (- e k)) (fun _ => exp (- 1)) 1 (exp (- 1)));
        [ apply exp_neg_cv1; exact Hecv | apply Un_cv_const ].
Qed.

Lemma gtail_1 : forall (Hc : 0 < 1), gtail 1 1 Hc = exp (- 1).
Proof.
  intro Hc.
  set (A := fun k => 1 + INR k).
  assert (HA1 : forall k, 1 <= A k) by (intro k; unfold A; pose proof (pos_INR k); lra).
  assert (HAinf : cv_infty A) by (unfold A; apply cv_infty_1_INR).
  apply (UL_sequence (fun k => pint1 (gtk 1 1) (gtk_int 1 1) (A k))).
  - exact (proj2_sig (gtail_sig 1 1 Hc) A HA1 HAinf).
  - apply (Un_cv_ext (fun k => exp (- 1) - exp (- A k))
                     (fun k => pint1 (gtk 1 1) (gtk_int 1 1) (A k))).
    + intro k; unfold pint1; rewrite (tail_int_val (A k) (HA1 k)); reflexivity.
    + pose proof (CV_minus (fun _ => exp (- 1)) (fun k => exp (- A k)) (exp (- 1)) 0
                    (Un_cv_const (exp (- 1))) (exp_neg_infty_cv0 A HA1 HAinf)) as HCV.
      rewrite Rminus_0_r in HCV; exact HCV.
Qed.

(* --- Γ(1) = 1 --- *)

Theorem Gam_1 : forall (H : 0 < 1), Gam 1 H = 1.
Proof.
  intro H; unfold Gam, mellin.
  rewrite (gnear_1 H Rlt_0_1), (gtail_1 Rlt_0_1); ring.
Qed.

Print Assumptions Gam_1.

(* ================================================================= *)
(*  END GammaOne.v.  Γ(1) = ∫₀^∞ e^{−t} = 1.                          *)
(* ================================================================= *)
