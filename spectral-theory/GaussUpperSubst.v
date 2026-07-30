(* ================================================================= *)
(*  GaussUpperSubst.v  —  Gaussian part-A stack, step 5b (upper flank):*)
(*  ∫₀^√n e^{−x²} ≤ √n·W_{2n−2}, via the substitution x = √n·tan θ.    *)
(*                                                                    *)
(*  Pointwise e^{−x²} ≤ (1+x²/n)⁻ⁿ (gauss_upper_pt), so                *)
(*    ∫₀^√n e^{−x²} ≤ ∫₀^√n (1+x²/n)⁻ⁿ.                                *)
(*  The substitution x = √n·tan θ (g = √n·sin/cos, LOCAL C¹ on [0,π/4], *)
(*  cov_local) turns the integrand into √n·cos^{2n−2}θ, since           *)
(*  1+tan²=1/cos² and dx = √n·sec²θ dθ.  θ runs 0→π/4 (x: 0→√n), and    *)
(*    ∫₀^{π/4} √n·cos^{2n−2} ≤ ∫₀^{π/2} √n·cos^{2n−2} = √n·W_{2n−2}.     *)
(*                                                                    *)
(*  So the whole upper flank is bounded by √n·W_{2n−2} on BOUNDED       *)
(*  intervals — no improper integral needed here (the ∞ only enters     *)
(*  when we let n→∞).  No new axioms (classical Reals only).           *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import WallisIntegral GaussSubst GaussWallis GaussSqueeze LocalCoV.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  cos > 0 on [0,π/4], and sin ≤ cos there.                         *)
(* ----------------------------------------------------------------- *)

Lemma cos_pos_pi4 : forall t, 0 <= t <= PI / 4 -> 0 < cos t.
Proof.
  intros t [H0 H4]; apply cos_gt_0;
    [ pose proof PI2_RGT_0; lra | pose proof PI4_RLT_PI2; lra ].
Qed.

Lemma sin_le_cos_pi4 : forall t, 0 <= t <= PI / 4 -> sin t <= cos t.
Proof.
  intros t [H0 H4].
  assert (Hs : 0 <= sin t) by (apply sin_ge_0; [ lra | pose proof PI_RGT_0; lra ]).
  assert (Hc : 0 <= cos t)
    by (apply cos_ge_0; [ pose proof PI2_RGT_0; lra | pose proof PI4_RLT_PI2; lra ]).
  apply Rsqr_incr_0; [ | exact Hs | exact Hc ].
  pose proof (cos_2a t) as H2.
  assert (Hcos2t : 0 <= cos (2 * t)) by (apply cos_ge_0; [ pose proof PI2_RGT_0; lra | lra ]).
  rewrite H2 in Hcos2t; unfold Rsqr; lra.
Qed.

(* ----------------------------------------------------------------- *)
(*  The substitution g θ = √n·tan θ and its integrand fU.            *)
(* ----------------------------------------------------------------- *)

Definition fU (n : nat) : R -> R := fun u => / (1 + u ^ 2 / INR n) ^ n.
Definition gU (n : nat) : R -> R := mult_real_fct (sqrt (INR n)) (div_fct sin cos).
Definition gU' (n : nat) : R -> R := mult_real_fct (sqrt (INR n)) (fun s => / (cos s) ^ 2).

Lemma gU_val : forall n t, gU n t = sqrt (INR n) * (sin t / cos t).
Proof. reflexivity. Qed.

Lemma gU0 : forall n, gU n 0 = 0.
Proof.
  intro n; rewrite gU_val, sin_0; unfold Rdiv; rewrite Rmult_0_l, Rmult_0_r; reflexivity.
Qed.

Lemma gUpi4 : forall n, gU n (PI / 4) = sqrt (INR n).
Proof.
  intro n; rewrite gU_val.
  replace (sin (PI / 4) / cos (PI / 4)) with (tan (PI / 4)) by (unfold tan; reflexivity).
  rewrite tan_PI4; ring.
Qed.

Lemma gU_deriv : forall n t, cos t <> 0 -> derivable_pt_lim (gU n) t (gU' n t).
Proof.
  intros n t Hc.
  pose proof (derivable_pt_lim_div sin cos t (cos t) (- sin t)
                (derivable_pt_lim_sin t) (derivable_pt_lim_cos t) Hc) as Hd.
  assert (Hval : (cos t * cos t - (- sin t) * sin t) / (cos t)² = / (cos t) ^ 2).
  { pose proof (sin2_cos2 t) as HS; unfold Rsqr in HS |- *.
    replace (cos t * cos t - (- sin t) * sin t) with 1 by nra.
    field; exact Hc. }
  rewrite Hval in Hd.
  exact (derivable_pt_lim_scal _ (sqrt (INR n)) t _ Hd).
Qed.

Lemma cont_gU' : forall n t, cos t <> 0 -> continuity_pt (gU' n) t.
Proof.
  intros n t Hc.
  apply (continuity_pt_scal (fun s => / (cos s) ^ 2) (sqrt (INR n)) t).
  apply (continuity_pt_inv (fun s => (cos s) ^ 2) t).
  - apply cont_cos_pow.
  - apply pow_nonzero; exact Hc.
Qed.

Lemma cont_fU : forall n, 0 < INR n -> continuity (fU n).
Proof.
  intros n Hn t; unfold fU.
  apply (continuity_pt_inv (fun u => (1 + u ^ 2 / INR n) ^ n) t).
  - apply (cont_pow (fun u => 1 + u ^ 2 / INR n) n).
    intro u; apply continuity_pt_plus.
    + apply continuity_pt_const; intros a b; reflexivity.
    + apply (continuity_pt_mult (fun u => u ^ 2) (fun _ => / INR n) u).
      * apply (cont_pow (fun u => u) 2); apply cont_id.
      * apply continuity_pt_const; intros a b; reflexivity.
  - apply pow_nonzero.
    assert (0 <= t ^ 2) by nra.
    assert (0 < / INR n) by (apply Rinv_0_lt_compat; exact Hn).
    apply Rgt_not_eq; unfold Rdiv; nra.
Qed.

(* ----------------------------------------------------------------- *)
(*  Range and pointwise integrand collapse.                          *)
(* ----------------------------------------------------------------- *)

Lemma gU_range : forall n t, 0 <= t <= PI / 4 -> 0 <= gU n t <= sqrt (INR n).
Proof.
  intros n t Ht; destruct Ht as [H0 H4].
  assert (Hc : 0 < cos t) by (apply cos_pos_pi4; lra).
  assert (Hs : 0 <= sin t) by (apply sin_ge_0; [ lra | pose proof PI_RGT_0; lra ]).
  assert (Hsc : sin t <= cos t) by (apply sin_le_cos_pi4; lra).
  assert (Hsn0 : 0 <= sqrt (INR n)) by apply sqrt_pos.
  rewrite gU_val; split.
  - apply Rmult_le_pos; [ exact Hsn0 | ].
    unfold Rdiv; apply Rmult_le_pos; [ exact Hs | left; apply Rinv_0_lt_compat; exact Hc ].
  - apply Rle_trans with (sqrt (INR n) * 1); [ | rewrite Rmult_1_r; apply Rle_refl ].
    apply Rmult_le_compat_l; [ exact Hsn0 | ].
    apply Rmult_le_reg_r with (cos t); [ exact Hc | ].
    rewrite Rmult_1_l; unfold Rdiv; rewrite Rmult_assoc, Rinv_l, Rmult_1_r;
      [ exact Hsc | apply Rgt_not_eq; exact Hc ].
Qed.

Lemma upper_integrand_eq : forall n, (1 <= n)%nat -> 0 < INR n ->
  forall t, 0 < cos t ->
  fU n (gU n t) * gU' n t = sqrt (INR n) * (cos t) ^ (2 * (n - 1)).
Proof.
  intros n Hn1 Hn t Hc.
  assert (Hcne : cos t <> 0) by (apply Rgt_not_eq; exact Hc).
  assert (Hc2ne : (cos t) ^ 2 <> 0) by (apply pow_nonzero; exact Hcne).
  assert (Hnne : INR n <> 0) by (apply Rgt_not_eq; exact Hn).
  assert (Hsnne : sqrt (INR n) <> 0) by (apply Rgt_not_eq; apply sqrt_lt_R0; lra).
  assert (Hsn : sqrt (INR n) * sqrt (INR n) = INR n) by (apply sqrt_sqrt; lra).
  (* fU n (gU n t) = (cos t)^(2n) *)
  assert (HfU : fU n (gU n t) = (cos t) ^ (2 * n)).
  { rewrite gU_val; unfold fU.
    assert (Hb : 1 + (sqrt (INR n) * (sin t / cos t)) ^ 2 / INR n = / (cos t) ^ 2).
    { pose proof (sin2_cos2 t) as HS; unfold Rsqr in HS.
      replace ((sqrt (INR n) * (sin t / cos t)) ^ 2)
        with (sqrt (INR n) * sqrt (INR n) * ((sin t) ^ 2) / (cos t) ^ 2)
        by (field; exact Hcne).
      rewrite Hsn.
      apply Rmult_eq_reg_r with ((cos t) ^ 2); [ | exact Hc2ne ].
      rewrite Rinv_l by exact Hc2ne.
      replace ((1 + INR n * (sin t) ^ 2 / (cos t) ^ 2 / INR n) * (cos t) ^ 2)
        with ((cos t) ^ 2 + (sin t) ^ 2)
        by (field; repeat split; try exact Hcne; try exact Hnne).
      replace ((cos t) ^ 2) with (cos t * cos t) by ring.
      replace ((sin t) ^ 2) with (sin t * sin t) by ring.
      lra. }
    rewrite Hb, (pow_inv ((cos t) ^ 2) n), Rinv_inv, <- pow_mult; reflexivity. }
  rewrite HfU; unfold gU'; unfold mult_real_fct.
  (* (cos t)^(2n) * (√n * /(cos t)^2) = √n * (cos t)^(2(n-1)) *)
  replace (2 * n)%nat with (2 * (n - 1) + 2)%nat by lia.
  rewrite pow_add; field; exact Hcne.
Qed.

(* ----------------------------------------------------------------- *)
(*  THE UPPER BOUND:  ∫₀^√n e^{−x²} ≤ √n·W_{2n−2}.                    *)
(* ----------------------------------------------------------------- *)

Theorem gauss_upper_bound : forall n, (1 <= n)%nat ->
  forall (prE : Riemann_integrable (fun x => exp (- x ^ 2)) 0 (sqrt (INR n))),
  RiemannInt prE <= sqrt (INR n) * Wallis (2 * (n - 1)).
Proof.
  intros n Hn1 prE.
  assert (Hn : 0 < INR n) by (apply lt_0_INR; lia).
  assert (Hsn0 : 0 <= sqrt (INR n)) by apply sqrt_pos.
  assert (Hpi4 : (0 : R) <= PI / 4) by (pose proof PI4_RGT_0; lra).
  assert (Hpi2 : (0 : R) <= PI / 2) by (pose proof PI2_RGT_0; lra).
  assert (H42 : PI / 4 <= PI / 2) by (pose proof PI4_RLT_PI2; lra).
  (* integrands *)
  assert (prU : Riemann_integrable (fU n) 0 (sqrt (INR n)))
    by (apply continuity_implies_RiemannInt; [ exact Hsn0 | intros u _; apply (cont_fU n Hn) ]).
  assert (prTheta : Riemann_integrable (fun t => fU n (gU n t) * gU' n t) 0 (PI / 4)).
  { apply continuity_implies_RiemannInt; [ exact Hpi4 | intros t Ht ].
    apply continuity_pt_mult.
    - apply (continuity_pt_comp (gU n) (fU n) t);
        [ apply derivable_continuous_pt; exists (gU' n t); apply gU_deriv;
          apply Rgt_not_eq; apply cos_pos_pi4; lra
        | apply (cont_fU n Hn) ].
    - apply cont_gU'; apply Rgt_not_eq; apply cos_pos_pi4; lra. }
  assert (prN4 : Riemann_integrable (fun t => sqrt (INR n) * (cos t) ^ (2 * (n - 1))) 0 (PI / 4))
    by (apply continuity_implies_RiemannInt; [ exact Hpi4 | intros t _;
        apply (continuity_pt_scal (fun s => (cos s) ^ (2 * (n - 1))) (sqrt (INR n)) t); apply cont_cos_pow ]).
  assert (prN2 : Riemann_integrable (fun t => sqrt (INR n) * (cos t) ^ (2 * (n - 1))) 0 (PI / 2))
    by (apply continuity_implies_RiemannInt; [ exact Hpi2 | intros t _;
        apply (continuity_pt_scal (fun s => (cos s) ^ (2 * (n - 1))) (sqrt (INR n)) t); apply cont_cos_pow ]).
  assert (prCos2 : Riemann_integrable (fun t => (cos t) ^ (2 * (n - 1))) 0 (PI / 2))
    by (apply continuity_implies_RiemannInt; [ exact Hpi2 | intros t _; apply cont_cos_pow ]).
  assert (prR : Riemann_integrable (fU n) (gU n 0) (gU n (PI / 4)))
    by (rewrite gU0, gUpi4; apply continuity_implies_RiemannInt;
        [ exact Hsn0 | intros u _; apply (cont_fU n Hn) ]).
  (* Step A: e^{-x²} ≤ fU on [0,√n] *)
  assert (HA : RiemannInt prE <= RiemannInt prU)
    by (apply RiemannInt_P19; [ exact Hsn0 | intros x _; apply gauss_upper_pt; exact Hn ]).
  (* connect prR (bounds gU0,gUπ4) to prU (bounds 0,√n) *)
  assert (HRU : RiemannInt prR = RiemannInt prU)
    by (revert prR; rewrite gU0, gUpi4; intro prR; apply RiemannInt_P5).
  (* cov_local *)
  assert (Hderiv : forall t, 0 <= t <= PI / 4 -> derivable_pt_lim (gU n) t (gU' n t))
    by (intros t Ht; apply gU_deriv; apply Rgt_not_eq; apply cos_pos_pi4; exact Ht).
  assert (Hcont' : forall t, 0 <= t <= PI / 4 -> continuity_pt (gU' n) t)
    by (intros t Ht; apply cont_gU'; apply Rgt_not_eq; apply cos_pos_pi4; exact Ht).
  assert (Hmap : forall t, 0 <= t <= PI / 4 -> gU n 0 <= gU n t <= gU n (PI / 4))
    by (intros t Ht; rewrite gU0, gUpi4; apply gU_range; exact Ht).
  assert (Hfc : forall u, gU n 0 <= u <= gU n (PI / 4) -> continuity_pt (fU n) u)
    by (intros u _; apply (cont_fU n Hn)).
  pose proof (cov_local (gU n) (gU' n) (fU n) 0 (PI / 4) Hpi4
                Hderiv Hcont' Hmap Hfc prTheta prR) as Hcov.
  (* pointwise collapse to √n cos^{2(n-1)} *)
  assert (HP18 : RiemannInt prTheta = RiemannInt prN4).
  { apply RiemannInt_P18; [ exact Hpi4 | intros t [Ht1 Ht2] ].
    apply upper_integrand_eq; [ exact Hn1 | exact Hn | apply cos_pos_pi4; lra ]. }
  (* Step C: extend [0,π/4] to [0,π/2] *)
  assert (HC : RiemannInt prN4 <= RiemannInt prN2).
  { assert (prMid : Riemann_integrable (fun t => sqrt (INR n) * (cos t) ^ (2 * (n - 1))) (PI / 4) (PI / 2))
      by (apply continuity_implies_RiemannInt; [ exact H42 | intros t _;
          apply (continuity_pt_scal (fun s => (cos s) ^ (2 * (n - 1))) (sqrt (INR n)) t); apply cont_cos_pow ]).
    assert (Hmid0 : 0 <= RiemannInt prMid).
    { apply Rle_trans with (RiemannInt (RiemannInt_P14 (PI / 4) (PI / 2) 0)).
      - rewrite (RiemannInt_P15 (RiemannInt_P14 (PI / 4) (PI / 2) 0)); ring_simplify; apply Rle_refl.
      - apply RiemannInt_P19; [ exact H42 | intros t Ht; unfold fct_cte ].
        apply Rmult_le_pos; [ exact Hsn0 | apply pow_le; apply cos_ge_0;
          [ pose proof PI2_RGT_0; lra | lra ] ]. }
    pose proof (RiemannInt_P26 prN4 prMid prN2) as Hadd; lra. }
  (* Step D: ∫₀^{π/2} √n cos^{2(n-1)} = √n W_{2(n-1)} *)
  assert (HD : RiemannInt prN2 = sqrt (INR n) * Wallis (2 * (n - 1))).
  { rewrite (int_scal (fun t => (cos t) ^ (2 * (n - 1))) (sqrt (INR n))
               (cont_cos_pow (2 * (n - 1))) prCos2 prN2).
    rewrite (cos_pow_int (2 * (n - 1)) prCos2); reflexivity. }
  (* assemble the chain *)
  apply Rle_trans with (RiemannInt prU); [ exact HA | ].
  rewrite <- HRU, <- Hcov, HP18.
  apply Rle_trans with (RiemannInt prN2); [ exact HC | rewrite HD; apply Rle_refl ].
Qed.

Print Assumptions gauss_upper_bound.

(* ================================================================= *)
(*  END GaussUpperSubst.v                                            *)
(*  ∫₀^√n e^{−x²} ≤ √n·W_{2n−2}, on BOUNDED intervals via x = √n·tan θ  *)
(*  (cov_local, since tan is not a global C1_fun).  Paired with the    *)
(*  lower bound √n·W_{2n+1} ≤ ∫₀^√n e^{−x²}, both flanks are Wallis     *)
(*  products → √π/2 — the squeeze.                                    *)
(* ================================================================= *)
