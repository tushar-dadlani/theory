(* ================================================================= *)
(*  FourierSincC1.v  —  the C¹ upgrade of the removable-singularity    *)
(*  core sinc, via its integral representation.                       *)
(*                                                                    *)
(*  sinc w = ∫₀¹ cos(w s) ds  (= sin w / w for w≠0, = 1 at 0).         *)
(*  This representation gives C¹ for free:                             *)
(*    • derivative  sinc'(w) = ∫₀¹ −s·sin(w s) ds  (leibniz_interval,  *)
(*      remainder bound from the cos-Taylor bound, B(s)=s²);           *)
(*    • sinc'(0) = 0  (the integrand vanishes at w=0);                 *)
(*    • sinc' is continuous — it is Lipschitz in w (sin_lipschitz      *)
(*      under the integral, constant ∫₀¹ s²).                          *)
(*  Packaged as the global C1_fun  sincC1.                            *)
(*                                                                    *)
(*  No third-order Taylor estimate is needed anywhere — the integral   *)
(*  representation absorbs it.  No new axioms (classical Reals only).  *)
(* ================================================================= *)

From Stdlib Require Import Reals Ranalysis5 FunctionalExtensionality Lra Lia.
Require Import FourierSincCore GaussTaylor GaussFull GaussPiValue ContinuousCoV LeibnizInterval.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  Continuity and integrability of the two integrands.              *)
(* ----------------------------------------------------------------- *)

Lemma cont_cos_lin : forall v, continuity (fun s => cos (v * s)).
Proof.
  intros v s; apply (continuity_pt_comp (fun s => v * s) cos s).
  - apply (continuity_pt_scal (fun z => z) v s);
      apply derivable_continuous_pt; exists 1; apply derivable_pt_lim_id.
  - apply continuity_cos.
Qed.

Lemma cont_dsin_lin : forall w, continuity (fun s => - (s * sin (w * s))).
Proof.
  intros w s; apply continuity_pt_opp; apply continuity_pt_mult.
  - apply derivable_continuous_pt; exists 1; apply derivable_pt_lim_id.
  - apply (continuity_pt_comp (fun s => w * s) sin s).
    + apply (continuity_pt_scal (fun z => z) w s);
        apply derivable_continuous_pt; exists 1; apply derivable_pt_lim_id.
    + apply continuity_sin.
Qed.

Lemma cont_sq : continuity (fun s : R => s ^ 2).
Proof.
  intros s; apply (continuity_pt_mult (fun z => z) (fun z => z * 1) s).
  - apply derivable_continuous_pt; exists 1; apply derivable_pt_lim_id.
  - apply continuity_pt_mult;
      [ apply derivable_continuous_pt; exists 1; apply derivable_pt_lim_id
      | apply continuity_pt_const; intros a b; reflexivity ].
Qed.

Lemma pr_cos : forall v, Riemann_integrable (fun s => cos (v * s)) 0 1.
Proof. intro v; apply continuity_implies_RiemannInt; [ apply Rle_0_1 | intros x _; apply cont_cos_lin ]. Qed.
Lemma pr_dsin : forall w, Riemann_integrable (fun s => - (s * sin (w * s))) 0 1.
Proof. intro w; apply continuity_implies_RiemannInt; [ apply Rle_0_1 | intros x _; apply cont_dsin_lin ]. Qed.
Lemma pr_sq : Riemann_integrable (fun s => s ^ 2) 0 1.
Proof. apply continuity_implies_RiemannInt; [ apply Rle_0_1 | intros x _; apply cont_sq ]. Qed.

(* ----------------------------------------------------------------- *)
(*  sinc as the integral of cos(w·).                                 *)
(* ----------------------------------------------------------------- *)

Lemma sinc_int : forall w, RiemannInt (pr_cos w) = sinc w.
Proof.
  intro w; destruct (Req_dec w 0) as [-> | Hw].
  - rewrite sinc_0.
    assert (Heq : RiemannInt (pr_cos 0) = RiemannInt (RiemannInt_P14 0 1 1)).
    { apply RiemannInt_P18; [ apply Rle_0_1 | intros x _; unfold fct_cte;
        rewrite Rmult_0_l, cos_0; reflexivity ]. }
    rewrite Heq, RiemannInt_P15; ring.
  - assert (Hanti : antiderivative (fun s => cos (w * s)) (fun s => / w * sin (w * s)) 0 1).
    { split; [ | apply Rle_0_1 ]. intros s Hs.
      pose proof (derivable_pt_lim_scal (fun s0 => s0) w s 1 (derivable_pt_lim_id s)) as Hlin.
      pose proof (derivable_pt_lim_comp (fun s0 => w * s0) sin s (w * 1) (cos (w * s))
                    Hlin (derivable_pt_lim_sin (w * s))) as Hc.
      pose proof (derivable_pt_lim_scal (fun s0 => sin (w * s0)) (/ w) s
                    (cos (w * s) * (w * 1)) Hc) as Hs2.
      replace (/ w * (cos (w * s) * (w * 1))) with (cos (w * s)) in Hs2 by (field; exact Hw).
      exists (exist _ (cos (w * s)) Hs2); reflexivity. }
    rewrite (FTC_antideriv (fun s => cos (w * s)) (fun s => / w * sin (w * s)) 0 1 Rle_0_1
               (fun x _ => cont_cos_lin w x) (pr_cos w) Hanti).
    unfold sinc; destruct (Req_dec_T w 0) as [-> | _]; [ contradiction | ].
    replace (w * 1) with w by ring; replace (w * 0) with 0 by ring;
      rewrite sin_0; field; exact Hw.
Qed.

(* ----------------------------------------------------------------- *)
(*  sinc is differentiable with sinc'(w) = ∫₀¹ −s·sin(w s) ds.        *)
(* ----------------------------------------------------------------- *)

Definition sincderiv (w : R) : R := RiemannInt (pr_dsin w).

Lemma sinc_deriv : forall w, derivable_pt_lim sinc w (sincderiv w).
Proof.
  intro w; unfold sincderiv.
  assert (Hleib : derivable_pt_lim (fun v => RiemannInt (pr_cos v)) w (RiemannInt (pr_dsin w))).
  { apply (leibniz_interval (fun v s => cos (v * s)) (fun w s => - (s * sin (w * s)))
             (fun s => s ^ 2) 0 1 w Rle_0_1).
    - intro v; apply cont_cos_lin.
    - apply cont_dsin_lin.
    - apply cont_sq.
    - intros h x Hx.
      replace (cos ((w + h) * x) - cos (w * x) - h * - (x * sin (w * x)))
        with (cos (w * x + h * x) - cos (w * x) + h * x * sin (w * x))
        by (replace ((w + h) * x) with (w * x + h * x) by ring; ring).
      apply Rle_trans with ((h * x) ^ 2); [ apply (cos_taylor_bound (w * x) (h * x)) | ].
      apply Req_le; ring. }
  assert (Hext : (fun v => RiemannInt (pr_cos v)) = sinc)
    by (apply functional_extensionality; intro v; apply sinc_int).
  rewrite Hext in Hleib; exact Hleib.
Qed.

Lemma sincderiv_0 : sincderiv 0 = 0.
Proof.
  unfold sincderiv.
  assert (Heq : RiemannInt (pr_dsin 0) = RiemannInt (RiemannInt_P14 0 1 0)).
  { apply RiemannInt_P18; [ apply Rle_0_1 | intros x _; unfold fct_cte;
      rewrite Rmult_0_l, sin_0; ring ]. }
  rewrite Heq, RiemannInt_P15; ring.
Qed.

(* ----------------------------------------------------------------- *)
(*  sinc' is continuous:  it is Lipschitz in the parameter.          *)
(* ----------------------------------------------------------------- *)

Lemma lipschitz_continuity : forall (f : R -> R) (y K : R), 0 <= K ->
  (forall x, Rabs (f x - f y) <= K * Rabs (x - y)) -> continuity_pt f y.
Proof.
  intros f y K HK Hlip eps He.
  exists (eps / (K + 1)); split; [ apply Rdiv_lt_0_compat; lra | ].
  intros x [_ Hdist]; unfold R_dist in *; simpl in *.
  apply Rle_lt_trans with (K * Rabs (x - y)); [ apply Hlip | ].
  apply Rle_lt_trans with ((K + 1) * Rabs (x - y));
    [ apply Rmult_le_compat_r; [ apply Rabs_pos | lra ] | ].
  pose proof (Rmult_lt_compat_l (K + 1) (Rabs (x - y)) (eps / (K + 1)) ltac:(lra) Hdist) as Hm.
  replace ((K + 1) * (eps / (K + 1))) with eps in Hm by (field; lra); exact Hm.
Qed.

Lemma sincderiv_lip : forall w1 w2,
  Rabs (sincderiv w1 - sincderiv w2) <= RiemannInt pr_sq * Rabs (w1 - w2).
Proof.
  intros w1 w2; unfold sincderiv.
  set (dd := fun s => - (s * sin (w1 * s)) - - (s * sin (w2 * s))).
  assert (prdd : Riemann_integrable dd 0 1)
    by (apply continuity_implies_RiemannInt; [ apply Rle_0_1 | intros x _; unfold dd;
        apply continuity_pt_minus; apply cont_dsin_lin ]).
  assert (Hlin : RiemannInt (pr_dsin w1) - RiemannInt (pr_dsin w2) = RiemannInt prdd).
  { assert (prg : Riemann_integrable
                    (fun s => - (s * sin (w1 * s)) + (-1) * - (s * sin (w2 * s))) 0 1)
      by (apply continuity_implies_RiemannInt; [ apply Rle_0_1 | intros x _;
          apply continuity_pt_plus; [ apply cont_dsin_lin
          | apply (continuity_pt_scal (fun s => - (s * sin (w2 * s))) (-1) x); apply cont_dsin_lin ] ]).
    pose proof (RiemannInt_P13 (pr_dsin w1) (pr_dsin w2) prg) as HP.
    assert (Hdg : RiemannInt prdd = RiemannInt prg)
      by (apply RiemannInt_P18; [ apply Rle_0_1 | intros x _; unfold dd; ring ]).
    rewrite Hdg, HP; ring. }
  assert (prTM : Riemann_integrable (fun s => Rabs (w1 - w2) * s ^ 2) 0 1)
    by (apply continuity_implies_RiemannInt; [ apply Rle_0_1 | intros x _;
        apply (continuity_pt_scal (fun s => s ^ 2) (Rabs (w1 - w2)) x); apply cont_sq ]).
  rewrite Hlin.
  apply Rle_trans with (RiemannInt (RiemannInt_P16 prdd)); [ apply RiemannInt_P17; apply Rle_0_1 | ].
  apply Rle_trans with (RiemannInt prTM).
  - apply RiemannInt_P19; [ apply Rle_0_1 | intros x [Hx0 Hx1]; unfold dd ].
    replace (- (x * sin (w1 * x)) - - (x * sin (w2 * x)))
      with (- x * (sin (w1 * x) - sin (w2 * x))) by ring.
    rewrite Rabs_mult.
    apply Rle_trans with (Rabs (- x) * Rabs (w1 * x - w2 * x)).
    + apply Rmult_le_compat_l; [ apply Rabs_pos | apply sin_lipschitz ].
    + rewrite Rabs_Ropp.
      replace (w1 * x - w2 * x) with ((w1 - w2) * x) by ring.
      rewrite Rabs_mult.
      rewrite (Rabs_right x) by (apply Rle_ge; lra).
      replace (Rabs (w1 - w2) * x ^ 2) with (x * (Rabs (w1 - w2) * x)) by ring.
      apply Rmult_le_compat_l; [ lra | apply Rle_refl ].
  - rewrite (RInt_scal_cont (fun s => s ^ 2) (Rabs (w1 - w2)) 0 1 Rle_0_1 cont_sq pr_sq prTM).
    apply Req_le; ring.
Qed.

Lemma sincderiv_cont : continuity sincderiv.
Proof.
  intro y; apply (lipschitz_continuity sincderiv y (RiemannInt pr_sq)).
  - apply (nonneg_int (fun s => s ^ 2) 0 1 pr_sq); [ apply Rle_0_1 | intros x _;
      rewrite <- Rsqr_pow2; apply Rle_0_sqr ].
  - intro x; apply sincderiv_lip.
Qed.

(* ----------------------------------------------------------------- *)
(*  The global C1_fun.                                               *)
(* ----------------------------------------------------------------- *)

Definition sincC1 : C1_fun :=
  mkC1 (c1 := sinc)
       (diff0 := fun w => exist _ (sincderiv w) (sinc_deriv w))
       sincderiv_cont.

Lemma sincC1_val : forall w, sincC1 w = sinc w.
Proof. reflexivity. Qed.

Lemma sincC1_der : forall w, derive sincC1 (diff0 sincC1) w = sincderiv w.
Proof. reflexivity. Qed.

Print Assumptions sincC1.

(* ================================================================= *)
(*  END FourierSincC1.v                                              *)
(*  sinc is a global C1_fun (sincC1) with derivative                 *)
(*  sincderiv w = ∫₀¹ −s sin(w s) ds, sincderiv 0 = 0, sincderiv      *)
(*  continuous.  Feeds the localiser reciprocal factor 1/sinc.       *)
(* ================================================================= *)
