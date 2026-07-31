(* ================================================================= *)
(*  GaussLeibniz.v  —  Leibniz-gap Phase 2b: the bounded parameter-    *)
(*  Leibniz rule.                                                     *)
(*                                                                    *)
(*    leibniz_bounded :                                               *)
(*      d/dξ ∫_{−A}^A e^{−πx²}cos(2πxξ) dx = ∫_{−A}^A −2πx e^{−πx²}sin(2πxξ) dx *)
(*                                                                    *)
(*  i.e. derivable_pt_lim (ξ ↦ ∫fcos ξ) ξ (∫fsin ξ) on any compact     *)
(*  [−A,A].  Proof: the difference quotient equals (1/t)∫dq where       *)
(*  dq x = fcos(ξ+t) x − fcos ξ x − t·fsin ξ x; by the cos Taylor        *)
(*  bound (GaussTaylor) |dq x| ≤ e^{−πx²}(2πx)²·t² = t²·mbound x, so     *)
(*  |∫dq| ≤ t²·M with M = ∫mbound a fixed constant (RiemannInt_P17/P19  *)
(*  + RInt_scal_cont).  Hence |diff-quotient − ∫fsin| = |∫dq|/|t| ≤     *)
(*  M|t| → 0.  The RiemannInt linearity ∫dq = ∫fcos(ξ+t) − ∫fcos ξ −    *)
(*  t∫fsin ξ is two applications of RiemannInt_P13.                    *)
(*                                                                    *)
(*  No general 2-D Heine — the t² from cos_taylor_bound does the work. *)
(*  No new axioms (classical Reals only).                             *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import GaussSubst GaussFull GaussPiValue GaussTransform GaussDerivValue GaussTaylor.
Open Scope R_scope.

Theorem leibniz_bounded : forall A xi, 0 <= A ->
  derivable_pt_lim (fun s => RiemannInt (fcos_int s (- A) A)) xi (RiemannInt (fsin_int xi (- A) A)).
Proof.
  intros A xi HA.
  assert (HAA : - A <= A) by lra.
  set (l := RiemannInt (fsin_int xi (- A) A)).
  (* the fixed constant M = ∫_{-A}^A e^{-πx²}(2πx)² *)
  set (mbound := fun x => exp_pi x * (2 * PI * x) ^ 2).
  assert (contm : continuity mbound).
  { intro x; unfold mbound; apply continuity_pt_mult; [ apply cont_exp_pi | ].
    apply (cont_pow (fun y => 2 * PI * y) 2); intro y;
      apply (continuity_pt_scal (fun z => z) (2 * PI) y); apply cont_id. }
  assert (prM : Riemann_integrable mbound (- A) A)
    by (apply continuity_implies_RiemannInt; [ exact HAA | intros x _; apply contm ]).
  set (M := RiemannInt prM).
  assert (HM0 : 0 <= M).
  { unfold M; apply (nonneg_int mbound (- A) A prM); [ exact HAA | intros x _; unfold mbound ].
    apply Rmult_le_pos; [ left; unfold exp_pi; apply exp_pos | nra ]. }
  intros eps He.
  assert (Hd0 : 0 < eps / (M + 1)) by (apply Rdiv_lt_0_compat; lra).
  exists (mkposreal (eps / (M + 1)) Hd0).
  intros t Ht0 Htd; simpl in Htd; cbv beta.
  set (Fp := RiemannInt (fcos_int (xi + t) (- A) A)).
  set (Fm := RiemannInt (fcos_int xi (- A) A)).
  (* the integrand of the difference and its integrability *)
  set (dq := fun x => fcos (xi + t) x - fcos xi x - t * fsin xi x).
  assert (contdq : continuity dq).
  { intro x; unfold dq; apply continuity_pt_minus;
      [ apply continuity_pt_minus; [ apply cont_fcos | apply cont_fcos ] | ].
    apply (continuity_pt_scal (fsin xi) t x); apply cont_fsin. }
  assert (prdq : Riemann_integrable dq (- A) A)
    by (apply continuity_implies_RiemannInt; [ exact HAA | intros x _; apply contdq ]).
  (* pointwise Taylor bound *)
  assert (Hpt : forall x, Rabs (dq x) <= t ^ 2 * mbound x).
  { intro x; unfold dq, fcos, fsin, mbound.
    replace (exp_pi x * cos (2 * PI * x * (xi + t)) - exp_pi x * cos (2 * PI * x * xi)
             - t * (- (2 * PI * x * exp_pi x) * sin (2 * PI * x * xi)))
      with (exp_pi x * (cos (2 * PI * x * xi + 2 * PI * x * t) - cos (2 * PI * x * xi)
                        + 2 * PI * x * t * sin (2 * PI * x * xi))).
    2:{ replace (2 * PI * x * (xi + t)) with (2 * PI * x * xi + 2 * PI * x * t) by ring; ring. }
    rewrite Rabs_mult, (Rabs_pos_eq (exp_pi x)) by (left; unfold exp_pi; apply exp_pos).
    apply Rle_trans with (exp_pi x * (2 * PI * x * t) ^ 2).
    - apply Rmult_le_compat_l; [ left; unfold exp_pi; apply exp_pos | ].
      apply (cos_taylor_bound (2 * PI * x * xi) (2 * PI * x * t)).
    - apply Req_le; ring. }
  (* |∫dq| ≤ t² M *)
  assert (prTM : Riemann_integrable (fun x => t ^ 2 * mbound x) (- A) A)
    by (apply continuity_implies_RiemannInt; [ exact HAA | intros x _;
        apply (continuity_pt_scal mbound (t ^ 2) x); apply contm ]).
  assert (Hdq_bound : Rabs (RiemannInt prdq) <= t ^ 2 * M).
  { apply Rle_trans with (RiemannInt (RiemannInt_P16 prdq)); [ apply RiemannInt_P17; exact HAA | ].
    apply Rle_trans with (RiemannInt prTM).
    - apply RiemannInt_P19; [ exact HAA | intros x _; apply Hpt ].
    - rewrite (RInt_scal_cont mbound (t ^ 2) (- A) A HAA contm prM prTM); apply Rle_refl. }
  (* RiemannInt linearity: ∫dq = Fp − Fm − t·l *)
  assert (Hdq_val : RiemannInt prdq = Fp - Fm - t * l).
  { assert (prg1 : Riemann_integrable (fun x => fcos (xi + t) x + (-1) * fcos xi x) (- A) A).
    { apply continuity_implies_RiemannInt; [ exact HAA | intros x _; apply continuity_pt_plus;
        [ apply cont_fcos | apply (continuity_pt_scal (fcos xi) (-1) x); apply cont_fcos ] ]. }
    assert (prg2 : Riemann_integrable
                     (fun x => (fun y => fcos (xi + t) y + (-1) * fcos xi y) x + (- t) * fsin xi x) (- A) A).
    { apply continuity_implies_RiemannInt; [ exact HAA | intros x _; apply continuity_pt_plus;
        [ apply continuity_pt_plus; [ apply cont_fcos | apply (continuity_pt_scal (fcos xi) (-1) x); apply cont_fcos ]
        | apply (continuity_pt_scal (fsin xi) (- t) x); apply cont_fsin ] ]. }
    pose proof (RiemannInt_P13 (fcos_int (xi + t) (- A) A) (fcos_int xi (- A) A) prg1) as HP1.
    pose proof (RiemannInt_P13 prg1 (fsin_int xi (- A) A) prg2) as HP2.
    assert (Hdg2 : RiemannInt prdq = RiemannInt prg2)
      by (apply RiemannInt_P18; [ exact HAA | intros x _; unfold dq; ring ]).
    unfold Fp, Fm, l; rewrite Hdg2, HP2, HP1; ring. }
  (* assemble *)
  assert (Hq : (Fp - Fm) / t - l = RiemannInt prdq / t)
    by (rewrite Hdq_val; field; exact Ht0).
  rewrite Hq.
  apply Rle_lt_trans with (Rabs t * M).
  - apply Rmult_le_reg_r with (Rabs t); [ apply Rabs_pos_lt; exact Ht0 | ].
    rewrite <- Rabs_mult.
    replace (RiemannInt prdq / t * t) with (RiemannInt prdq) by (field; exact Ht0).
    apply Rle_trans with (t ^ 2 * M); [ exact Hdq_bound | ].
    apply Req_le; replace (t ^ 2) with (Rabs t * Rabs t)
      by (rewrite <- Rabs_mult, Rabs_pos_eq by nra; ring); ring.
  - apply Rle_lt_trans with (Rabs t * (M + 1)).
    + apply Rmult_le_compat_l; [ apply Rabs_pos | lra ].
    + pose proof (Rmult_lt_compat_r (M + 1) (Rabs t) (eps / (M + 1)) ltac:(lra) Htd) as Hmm.
      replace (eps / (M + 1) * (M + 1)) with eps in Hmm by (field; lra); exact Hmm.
Qed.

Print Assumptions leibniz_bounded.

(* ================================================================= *)
(*  END GaussLeibniz.v (Phase 2b)                                   *)
(*  d/dξ ∫_{−A}^A e^{−πx²}cos(2πxξ) = ∫_{−A}^A −2πx e^{−πx²}sin(2πxξ).    *)
(*  Phase 2 is complete.  Feeding fn = S_transform, fn' = S_deriv       *)
(*  (via A = INR k) into derivable_pt_lim_CVU with the CVU bound        *)
(*  g_deriv_cvu (Phase 1) is Phase 3.                                  *)
(* ================================================================= *)
