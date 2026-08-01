(* ================================================================= *)
(*  GammaHalf.v  —  Γ(1/2) = √π,  hence ζ(−1) = −1/12 unconditionally.*)
(*                                                                    *)
(*  Substitute t = x² in Γ(1/2) = ∫₀^∞ t^{−1/2} e^{−t} dt:            *)
(*     t^{−1/2} e^{−t} · (dt = 2x dx)  ↦  2 e^{−x²}                    *)
(*  (gg_eq).  cov_local turns each finite piece ∫_{a²}^{b²} of the     *)
(*  Γ-integrand into 2∫_a^b e^{−x²} (cov_half).  Passing to the        *)
(*  improper limits, the ∫₀^1 e^{−x²} piece cancels between gnear and  *)
(*  gtail, leaving 2·(∫₀^∞ e^{−x²}) = 2·(√π/2) = √π (GaussFull /       *)
(*  GaussValue.gauss_improper).  The sequences are chosen as perfect    *)
(*  squares so no √·² transport is needed.                            *)
(*  Combined with ZetaValues.zeta_neg1, ζ_ext(−1) = −1/12 outright.    *)
(*  No new axioms (classical Reals only).                            *)
(* ================================================================= *)

From Stdlib Require Import Reals Rpower Lra Lia.
Require Import GammaReal ImproperCv0 ImproperCv1 GammaFunction LocalCoV MellinElem
        GaussValue GaussImproper XiTwoSided ZetaValues.
Open Scope R_scope.

(* --- elementary facts --- *)

Lemma exp_sq_le1 : forall x, exp_sq x <= 1.
Proof.
  intro x; unfold exp_sq; rewrite <- exp_0.
  assert (H : - x ^ 2 <= 0) by (replace (x ^ 2) with (Rsqr x) by (unfold Rsqr; ring);
    pose proof (Rle_0_sqr x); lra).
  destruct H as [Hlt | Heq]; [ apply Rlt_le; apply exp_increasing; exact Hlt | rewrite Heq; apply Rle_refl ].
Qed.

Lemma dsq : forall t, derivable_pt_lim (fun x => x ^ 2) t (2 * t).
Proof.
  intro t; replace (2 * t) with (INR 2 * t ^ 1) by (simpl; ring);
    apply (derivable_pt_lim_pow t 2).
Qed.

Lemma cont_2x : forall t, continuity_pt (fun x => 2 * x) t.
Proof.
  intro t; apply (continuity_pt_scal (fun x => x) 2 t);
    apply derivable_continuous_pt; apply derivable_pt_id.
Qed.

Lemma gg_eq : forall x, 0 < x -> gnk (1 / 2) 1 (x ^ 2) * (2 * x) = 2 * exp_sq x.
Proof.
  intros x Hx; unfold gnk, exp_sq.
  assert (HR : Rpower (x ^ 2) (1 / 2 - 1) = / x).
  { replace (1 / 2 - 1) with (- / 2) by lra; rewrite Rpower_Ropp.
    assert (Hx2 : 0 < x ^ 2) by (apply pow_lt; exact Hx).
    rewrite (Rpower_sqrt (x ^ 2) Hx2).
    replace (x ^ 2) with (Rsqr x) by (unfold Rsqr; ring).
    rewrite (sqrt_Rsqr x (Rlt_le _ _ Hx)); reflexivity. }
  rewrite HR; replace (1 * x ^ 2) with (x ^ 2) by ring; field; apply Rgt_not_eq; exact Hx.
Qed.

Lemma cont_gg : forall t, 0 < t -> continuity_pt (fun t => gnk (1 / 2) 1 (t ^ 2) * (2 * t)) t.
Proof.
  intros t Ht; apply continuity_pt_mult; [ | apply cont_2x ].
  apply (continuity_pt_comp (fun x => x ^ 2) (gnk (1 / 2) 1) t).
  - apply derivable_continuous_pt; exists (2 * t); apply dsq.
  - apply cont_gnk; apply pow_lt; exact Ht.
Qed.

Lemma gtk_eq_gnk : forall u, 1 <= u -> gtk (1 / 2) 1 u = gnk (1 / 2) 1 u.
Proof. intros u Hu; unfold gtk, gnk; rewrite (clamp_id u Hu); reflexivity. Qed.

Lemma cv_infty_ge : forall (u v : nat -> R), (forall k, u k <= v k) -> cv_infty u -> cv_infty v.
Proof.
  intros u v Huv Hu M; destruct (Hu M) as [N HN]; exists N; intros n Hn;
    apply Rlt_le_trans with (u n); [ apply HN; exact Hn | apply Huv ].
Qed.

(* --- the change of variables t = x² on a finite piece --- *)

Lemma cov_half : forall (a b lo hi : R) (Ha : 0 < a) (Hab : a <= b),
  lo = a ^ 2 -> hi = b ^ 2 ->
  forall (prR : Riemann_integrable (gnk (1 / 2) 1) lo hi),
  RiemannInt prR = 2 * RiemannInt (exp_sq_int a b).
Proof.
  intros a b lo hi Ha Hab Hlo Hhi.
  rewrite Hlo, Hhi; intro prR.
  assert (prL : Riemann_integrable (fun t => gnk (1 / 2) 1 (t ^ 2) * (2 * t)) a b)
    by (apply continuity_implies_RiemannInt; [ exact Hab | intros t Ht; apply cont_gg; lra ]).
  assert (E : RiemannInt prL = RiemannInt prR).
  { apply (cov_local (fun x => x ^ 2) (fun x => 2 * x) (gnk (1 / 2) 1) a b Hab).
    - intros t _; apply dsq.
    - intros t _; apply cont_2x.
    - intros t Ht; cbv beta; split; nra.
    - intros u Hu; cbv beta in Hu; apply cont_gnk;
        assert (Ha2 : 0 < a ^ 2) by (apply pow_lt; exact Ha); lra. }
  rewrite <- E.
  assert (g2int : Riemann_integrable (fun x => fct_cte 0 x + 2 * exp_sq x) a b).
  { apply continuity_implies_RiemannInt; [ exact Hab | intros t _;
      apply continuity_pt_plus; [ apply continuity_pt_const; intros p q; reflexivity
                                | apply continuity_pt_scal; apply cont_exp_sq ] ]. }
  assert (H18 : forall x, a < x < b -> gnk (1 / 2) 1 (x ^ 2) * (2 * x) = fct_cte 0 x + 2 * exp_sq x)
    by (intros x Hx; unfold fct_cte; rewrite (gg_eq x ltac:(lra)); ring).
  rewrite (RiemannInt_P18 prL g2int Hab H18).
  rewrite (RiemannInt_P13 (RiemannInt_P14 a b 0) (exp_sq_int a b) g2int).
  rewrite (RiemannInt_P15 (RiemannInt_P14 a b 0)); ring.
Qed.

(* --- the near piece:  gnear (1/2) 1 = 2·∫₀^1 e^{−x²} --- *)

Lemma int_lower_cv : forall c, (forall k, 0 <= c k) -> (forall k, c k <= 1) -> Un_cv c 0 ->
  Un_cv (fun k => RiemannInt (exp_sq_int (c k) 1)) (RiemannInt (exp_sq_int 0 1)).
Proof.
  intros c Hc0 Hc1 Hcv eps Heps.
  destruct (Hcv eps Heps) as [N HN]; exists N; intros n Hn.
  assert (Hch : RiemannInt (exp_sq_int 0 (c n)) + RiemannInt (exp_sq_int (c n) 1)
                = RiemannInt (exp_sq_int 0 1)) by (apply RiemannInt_P26).
  assert (Hnn : 0 <= RiemannInt (exp_sq_int 0 (c n))).
  { apply Rle_trans with (RiemannInt (RiemannInt_P14 0 (c n) 0)).
    - rewrite (RiemannInt_P15 (RiemannInt_P14 0 (c n) 0)); ring_simplify; apply Rle_refl.
    - apply RiemannInt_P19; [ apply Hc0 | intros t _; unfold fct_cte; left; apply exp_pos ]. }
  assert (Hub : RiemannInt (exp_sq_int 0 (c n)) <= c n).
  { apply Rle_trans with (RiemannInt (RiemannInt_P14 0 (c n) 1)).
    - apply RiemannInt_P19; [ apply Hc0 | intros t _; unfold fct_cte; apply exp_sq_le1 ].
    - rewrite (RiemannInt_P15 (RiemannInt_P14 0 (c n) 1));
        replace (c n - 0) with (c n) by ring; rewrite Rmult_1_l; apply Rle_refl. }
  pose proof (HN n Hn) as Hcn; unfold R_dist in Hcn;
    replace (c n - 0) with (c n) in Hcn by ring;
    rewrite Rabs_right in Hcn by (apply Rle_ge; apply Hc0).
  unfold R_dist;
    replace (RiemannInt (exp_sq_int (c n) 1) - RiemannInt (exp_sq_int 0 1))
      with (- RiemannInt (exp_sq_int 0 (c n))) by lra.
  rewrite Rabs_Ropp, Rabs_right by (apply Rle_ge; exact Hnn); lra.
Qed.

Lemma gnear_half : forall (H : 0 < 1 / 2) (Hc : 0 < 1),
  gnear (1 / 2) 1 H Hc = 2 * RiemannInt (exp_sq_int 0 1).
Proof.
  intros H Hc.
  set (a := fun k => / (1 + INR k)).
  set (e := fun k => (a k) ^ 2).
  assert (Ha0 : forall k, 0 < a k)
    by (intro k; unfold a; apply Rinv_0_lt_compat; pose proof (pos_INR k); lra).
  assert (Ha1 : forall k, a k <= 1) by (intro k; unfold a; apply inv_le_1; pose proof (pos_INR k); lra).
  assert (He0 : forall k, 0 < e k) by (intro k; unfold e; apply pow_lt; apply Ha0).
  assert (He1 : forall k, e k <= 1)
    by (intro k; unfold e; pose proof (Ha0 k); pose proof (Ha1 k); nra).
  assert (Hacv : Un_cv a 0)
    by (unfold a; apply Un_cv_recip_0; [ intro k; pose proof (pos_INR k); lra | apply cv_infty_1_INR ]).
  assert (Hecv : Un_cv e 0).
  { apply (Un_cv_squeeze0 e a); [ | exact Hacv ].
    exists 0%nat; intros k _; split; [ left; apply He0 | ];
      unfold e; pose proof (Ha0 k); pose proof (Ha1 k); nra. }
  apply (UL_sequence (fun k => rint01 (gnk (1 / 2) 1) (Hf_near (1 / 2) 1) (e k))).
  - exact (proj2_sig (gnear_sig (1 / 2) 1 H Hc) e He0 He1 Hecv).
  - apply (Un_cv_ext (fun k => 2 * RiemannInt (exp_sq_int (a k) 1))
                     (fun k => rint01 (gnk (1 / 2) 1) (Hf_near (1 / 2) 1) (e k))).
    + intro k; rewrite (rint01_val (gnk (1 / 2) 1) (Hf_near (1 / 2) 1) (e k) (He0 k) (He1 k)).
      symmetry; apply (cov_half (a k) 1 (e k) 1 (Ha0 k) (Ha1 k) eq_refl ltac:(ring)
                         (Hf_near (1 / 2) 1 (e k) 1 (He0 k) (He1 k))).
    + apply (CV_mult (fun _ => 2) (fun k => RiemannInt (exp_sq_int (a k) 1)) 2
               (RiemannInt (exp_sq_int 0 1)));
        [ apply Un_cv_const | apply int_lower_cv; [ intro k; left; apply Ha0 | exact Ha1 | exact Hacv ] ].
Qed.

(* --- the tail piece:  gtail (1/2) 1 = √π − 2·∫₀^1 e^{−x²} --- *)

Lemma gtail_half : forall (Hc : 0 < 1),
  gtail (1 / 2) 1 Hc = sqrt PI - 2 * RiemannInt (exp_sq_int 0 1).
Proof.
  intro Hc.
  set (b := fun k => 1 + INR k).
  set (A := fun k => (b k) ^ 2).
  assert (Hb1 : forall k, 1 <= b k) by (intro k; unfold b; pose proof (pos_INR k); lra).
  assert (Hb0 : forall k, 0 <= b k) by (intro k; pose proof (Hb1 k); lra).
  assert (HA1 : forall k, 1 <= A k) by (intro k; unfold A; pose proof (Hb1 k); nra).
  assert (HAinf : cv_infty A).
  { apply (cv_infty_ge b A); [ intro k; unfold A; pose proof (Hb1 k); nra | ].
    unfold b; apply cv_infty_1_INR. }
  apply (UL_sequence (fun k => pint1 (gtk (1 / 2) 1) (gtk_int (1 / 2) 1) (A k))).
  - exact (proj2_sig (gtail_sig (1 / 2) 1 Hc) A HA1 HAinf).
  - apply (Un_cv_ext (fun k => 2 * RiemannInt (exp_sq_int 1 (b k)))
                     (fun k => pint1 (gtk (1 / 2) 1) (gtk_int (1 / 2) 1) (A k))).
    + intro k; unfold pint1.
      rewrite (RiemannInt_P18 (gtk_int (1 / 2) 1 1 (A k))
                 (Hf_near (1 / 2) 1 1 (A k) Rlt_0_1 (HA1 k)) (HA1 k)
                 (fun x Hx => gtk_eq_gnk x ltac:(lra))).
      symmetry; apply (cov_half 1 (b k) 1 (A k) Rlt_0_1 (Hb1 k) ltac:(ring) eq_refl
                         (Hf_near (1 / 2) 1 1 (A k) Rlt_0_1 (HA1 k))).
    + apply (Un_cv_ext
               (fun k => 2 * RiemannInt (exp_sq_int 0 (b k)) - 2 * RiemannInt (exp_sq_int 0 1))
               (fun k => 2 * RiemannInt (exp_sq_int 1 (b k)))).
      * intro k;
          pose proof (RiemannInt_P26 (exp_sq_int 0 1) (exp_sq_int 1 (b k)) (exp_sq_int 0 (b k))) as Hch;
          lra.
      * apply (CV_minus (fun k => 2 * RiemannInt (exp_sq_int 0 (b k)))
                 (fun _ => 2 * RiemannInt (exp_sq_int 0 1)) (sqrt PI) (2 * RiemannInt (exp_sq_int 0 1)));
          [ | apply Un_cv_const ].
        replace (sqrt PI) with (2 * (sqrt PI / 2)) by lra.
        apply (CV_mult (fun _ => 2) (fun k => RiemannInt (exp_sq_int 0 (b k))) 2 (sqrt PI / 2));
          [ apply Un_cv_const | ].
        exact (gauss_improper b Hb0 (ltac:(unfold b; apply cv_infty_1_INR))).
Qed.

(* --- Γ(1/2) = √π --- *)

Theorem Gam_half : forall (H : 0 < 1 / 2), Gam (1 / 2) H = sqrt PI.
Proof.
  intro H; unfold Gam, mellin; rewrite (gnear_half H Rlt_0_1), (gtail_half Rlt_0_1); ring.
Qed.

Theorem Gam_half_Rpower : forall (H : 0 < 1 / 2), Gam (1 / 2) H = Rpower PI (1 / 2).
Proof.
  intro H; rewrite (Gam_half H), <- (Rpower_sqrt PI PI_RGT_0); f_equal; lra.
Qed.

(* --- the payoff:  ζ_ext(−1) = −1/12, unconditionally --- *)

Theorem zeta_neg1_unconditional : zeta_ext (-1) = - (1 / 12).
Proof.
  assert (Hh : 0 < 1 / 2) by lra.
  exact (zeta_neg1 Hh (Gam_half_Rpower Hh)).
Qed.

Print Assumptions Gam_half.
Print Assumptions zeta_neg1_unconditional.

(* ================================================================= *)
(*  END GammaHalf.v.  Γ(1/2)=√π; ζ(−1)=−1/12 with no hypotheses.       *)
(* ================================================================= *)
