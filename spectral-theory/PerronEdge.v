(* ================================================================= *)
(*  PerronEdge.v  —  Perron A1d: the horizontal-edge estimate.           *)
(*                                                                    *)
(*  int_kRpower_Ld : ∫₀¹ k·y^{Ld p q u} du = k·(y^q − y^p)/((q−p)·ln y)    *)
(*    (FTC with antiderivative k·y^{Ld u}/((q−p)ln y)).                   *)
(*                                                                    *)
(*  horiz_edge_bound : the y^s/s integral over a horizontal edge          *)
(*    mkC p b → mkC q b  is  ≤ 2·|y^q − y^p|/(|b|·ln y)                    *)
(*    (Cintf_mod_le2 + the integral above + the pointwise bound            *)
(*    |y^s/s|·|seg'| ≤ y^{Re s}/|b|·|q−p|).  Axiom-clean.                  *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import ComplexField Cmodulus CDeriv CImproperIntegral CIntegral2 CSegInt
        CPathIntegral CexpFull ContinuousCoV RectWinding PerronBound PerronKernel.
Open Scope R_scope.

Lemma Rpower_Ld_deriv : forall y p q x, 0 < y ->
  derivable_pt_lim (fun u => Rpower y (Ld p q u)) x
                   (ln y * Rpower y (Ld p q x) * (q - p)).
Proof.
  intros y p q x Hy.
  replace (ln y * Rpower y (Ld p q x) * (q - p))
    with ((ln y * Rpower y (Ld p q x)) * (q - p)) by ring.
  apply (derivable_pt_lim_comp (Ld p q) (Rpower y) x (q - p) (ln y * Rpower y (Ld p q x)));
    [ apply Ld_deriv | apply Rpower_exp_deriv; exact Hy ].
Qed.

Lemma int_kRpower_Ld : forall y p q k (Hy : 0 < y) (Hln : ln y <> 0) (Hpq : q - p <> 0)
  (pr : Riemann_integrable (fun u => k * Rpower y (Ld p q u)) 0 1),
  RiemannInt pr = k * ((Rpower y q - Rpower y p) / ((q - p) * ln y)).
Proof.
  intros y p q k Hy Hln Hpq pr.
  assert (Hanti : antiderivative (fun u => k * Rpower y (Ld p q u))
                    (fun u => k / ((q - p) * ln y) * Rpower y (Ld p q u)) 0 1).
  { split; [ | lra ]. intros x Hx.
    assert (HGd : derivable_pt_lim (fun u => k / ((q - p) * ln y) * Rpower y (Ld p q u)) x
                    (k * Rpower y (Ld p q x))).
    { replace (k * Rpower y (Ld p q x))
        with (k / ((q - p) * ln y) * (ln y * Rpower y (Ld p q x) * (q - p)))
        by (field; split; assumption).
      apply derivable_pt_lim_scal, Rpower_Ld_deriv; exact Hy. }
    exists (exist (fun l => derivable_pt_lim
              (fun u => k / ((q - p) * ln y) * Rpower y (Ld p q u)) x l)
              (k * Rpower y (Ld p q x)) HGd).
    unfold derive_pt; simpl; reflexivity. }
  rewrite (FTC_antideriv (fun u => k * Rpower y (Ld p q u))
             (fun u => k / ((q - p) * ln y) * Rpower y (Ld p q u)) 0 1 Rle_0_1
             (fun x _ => derivable_continuous_pt _ x (exist _ _
                (derivable_pt_lim_scal _ k x _ (Rpower_Ld_deriv y p q x Hy)))) pr Hanti).
  rewrite Ld_0, Ld_1; field; split; assumption.
Qed.

(* small Cmod helpers *)
Lemma mkC_Im_ne0 : forall a b, b <> 0 -> mkC a b <> C0.
Proof. intros a b Hb H; apply Hb; apply (f_equal Im) in H; cbn in H; exact H. Qed.

Lemma Ccont_Cmod : forall f, Ccont f -> forall x, continuity_pt (fun u => Cmod (f u)) x.
Proof.
  intros f Hf x; apply (continuity_pt_comp (fun u => Cnorm2 (f u)) sqrt x);
    [ apply Ccont_Cnorm2_comp; exact Hf | apply continuity_pt_sqrt, Cnorm2_nonneg ].
Qed.

(* monotonicity sign of Rpower for y>1 *)
Lemma Rpower_diff_sign : forall y p q, 1 < y ->
  0 <= (q - p) * (Rpower y q - Rpower y p).
Proof.
  intros y p q Hy1.
  assert (Hlny : 0 < ln y) by (rewrite <- ln_1; apply ln_increasing; lra).
  destruct (Rtotal_order q p) as [Hlt | [Heq | Hgt]].
  - assert (Rpower y q < Rpower y p)
      by (unfold Rpower; apply exp_increasing, Rmult_lt_compat_r; assumption).
    nra.
  - subst; nra.
  - assert (Rpower y p < Rpower y q)
      by (unfold Rpower; apply exp_increasing, Rmult_lt_compat_r; assumption).
    nra.
Qed.

Theorem horiz_edge_bound : forall y p q b (Hy1 : 1 < y) (Hb : b <> 0) (Hpq : q <> p)
  (HfF : Ccont (fun u => Cmul (Cmul (Cpw y (seg (mkC p b) (mkC q b) u))
                    (Cinv (seg (mkC p b) (mkC q b) u))) (seg' (mkC p b) (mkC q b) u))),
  Cmod (pathint (seg (mkC p b) (mkC q b)) (seg' (mkC p b) (mkC q b))
                (fun z => Cmul (Cpw y z) (Cinv z)) HfF 0 1)
  <= 2 * (Rabs (Rpower y q - Rpower y p) / (Rabs b * ln y)).
Proof.
  intros y p q b Hy1 Hb Hpq HfF.
  assert (Hy : 0 < y) by lra.
  assert (Hlny : 0 < ln y) by (rewrite <- ln_1; apply ln_increasing; lra).
  assert (Hab : Rabs b > 0) by (apply Rabs_pos_lt; exact Hb).
  set (k := Rabs (q - p) / Rabs b).
  assert (Hcm : Riemann_integrable
                  (fun u => Cmod (Cmul (Cmul (Cpw y (seg (mkC p b) (mkC q b) u))
                    (Cinv (seg (mkC p b) (mkC q b) u))) (seg' (mkC p b) (mkC q b) u))) 0 1)
    by (apply continuity_implies_RiemannInt; [ lra | intros x _; apply Ccont_Cmod; exact HfF ]).
  assert (Hbd : Riemann_integrable (fun u => k * Rpower y (Ld p q u)) 0 1).
  { apply continuity_implies_RiemannInt; [ lra | intros x _ ].
    apply (continuity_pt_mult (fun _ => k) (fun u => Rpower y (Ld p q u)) x);
      [ apply continuity_pt_const; intros a c; reflexivity
      | apply derivable_continuous_pt; exists (ln y * Rpower y (Ld p q x) * (q - p));
        apply Rpower_Ld_deriv; exact Hy ]. }
  (* pointwise:  Cmod(integrand) ≤ k · y^{Ld u} *)
  assert (Hpt : forall u, 0 < u < 1 ->
    Cmod (Cmul (Cmul (Cpw y (seg (mkC p b) (mkC q b) u))
          (Cinv (seg (mkC p b) (mkC q b) u))) (seg' (mkC p b) (mkC q b) u))
    <= k * Rpower y (Ld p q u)).
  { intros u _; rewrite segh, segh', !Cmod_mul, (Cpw_mod y (mkC (Ld p q u) b)); cbn [Re].
    rewrite (Cmod_inv (mkC (Ld p q u) b) (mkC_Im_ne0 _ _ Hb)).
    replace (Cmod (mkC (q - p) 0)) with (Rabs (q - p))
      by (change (mkC (q - p) 0) with (RtoC (q - p)); rewrite Cmod_RtoC; reflexivity).
    assert (Hge : Rabs b <= Cmod (mkC (Ld p q u) b))
      by (pose proof (Cmod_Im (mkC (Ld p q u) b)) as H; cbn in H; exact H).
    assert (Hcp : 0 < Cmod (mkC (Ld p q u) b)) by lra.
    assert (Hinv : / Cmod (mkC (Ld p q u) b) <= / Rabs b)
      by (apply Rinv_le_contravar; [ exact Hab | exact Hge ]).
    assert (Hrp : 0 <= Rpower y (Ld p q u)) by (left; apply exp_pos).
    apply Rle_trans with (Rpower y (Ld p q u) * / Rabs b * Rabs (q - p)).
    - apply Rmult_le_compat_r; [ apply Rabs_pos | apply Rmult_le_compat_l; [ exact Hrp | exact Hinv ] ].
    - apply Req_le; unfold k; field; lra. }
  (* assemble *)
  unfold pathint.
  eapply Rle_trans; [ apply (Cintf_mod_le2 _ HfF 0 1 Hcm Rle_0_1) | ].
  apply Rmult_le_compat_l; [ lra | ].
  eapply Rle_trans; [ apply (RiemannInt_P19 Hcm Hbd Rle_0_1 Hpt) | ].
  rewrite (int_kRpower_Ld y p q k Hy ltac:(lra) ltac:(lra) Hbd).
  apply Req_le.
  assert (Hsgn : Rabs (q - p) * (Rpower y q - Rpower y p)
                 = Rabs (Rpower y q - Rpower y p) * (q - p)).
  { pose proof (Rpower_diff_sign y p q Hy1);
      unfold Rabs; destruct (Rcase_abs (q - p)); destruct (Rcase_abs (Rpower y q - Rpower y p)); nra. }
  unfold k.
  replace (Rabs (q - p) / Rabs b * ((Rpower y q - Rpower y p) / ((q - p) * ln y)))
    with ((Rabs (q - p) * (Rpower y q - Rpower y p)) / (Rabs b * (q - p) * ln y))
    by (field; repeat split; try lra; intro Hc; apply Hpq; lra).
  rewrite Hsgn.
  field; repeat split; try lra; intro Hc; apply Hpq; lra.
Qed.

Print Assumptions horiz_edge_bound.

(* ================================================================= *)
(*  END PerronEdge.v — the horizontal-edge decay bound.                  *)
(* ================================================================= *)
