(* ================================================================= *)
(*  CClampedTower.v  (identity-theorem plan, FE chain brick 5 — cont)   *)
(*                                                                    *)
(*  The clamped scaled function  Gclamp F z0 eps w = F(z0 + eps.clamp w)  *)
(*  where clamp = clampw 11 C0 confines its argument to |v| <= 5.5.      *)
(*  With 6 eps < Re z0 the argument z0 + eps.clamp w stays in {Re>0},    *)
(*  so its CcontC / pointwise continuity are built from the pointwise    *)
(*  continuity of a MEROMORPHIC F on {Re>0} (ptcont_path), NOT a false   *)
(*  global CcontC.  On |w| < 5 the clamp is the identity, so Gclamp is    *)
(*  holomorphic there and equals F(z0 + eps w) -- exactly what the tower  *)
(*  and identity endpoints consume.                                     *)
(*                                                                    *)
(*  Axioms: standard classical-Reals only.                            *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra.
Require Import ComplexField Cmodulus Holomorphic CDeriv CIntegral2 CSegInt
        CPathIntegral PerronRemovable CCauchyAnalytic CClampCont CPtcontPath.
Open Scope R_scope.

Definition Gclamp (F : C -> C) (z0 : C) (eps : R) (w : C) : C :=
  F (Cadd (Cmul (RtoC eps) (clampw 11 C0 w)) z0).

Section ClampedTower.
Variable F : C -> C.
Variable z0 : C.
Variable eps : R.
Hypothesis Heps : 0 < eps.
Hypothesis H6 : 6 * eps < Re z0.
Hypothesis HFptc : forall z, 0 < Re z -> forall e, 0 < e -> exists del, 0 < del /\
  forall z', Cmod (Cminus z' z) < del -> Cmod (Cminus (F z') (F z)) < e.
Hypothesis HFhol : forall z, 0 < Re z -> exists d, is_Cderiv F z d.

Lemma clampw_mod55 : forall w, Cmod (clampw 11 C0 w) <= 11 / 2.
Proof.
  intro w. pose proof (clampw_mod 11 C0 ltac:(lra) w) as Hcm.
  unfold rho in Hcm. rewrite (proj2 (Cmod0 C0) eq_refl) in Hcm. lra.
Qed.

Lemma Gclamp_pt_pos : forall w,
  0 < Re (Cadd (Cmul (RtoC eps) (clampw 11 C0 w)) z0).
Proof.
  intro w.
  replace (Re (Cadd (Cmul (RtoC eps) (clampw 11 C0 w)) z0))
    with (eps * Re (clampw 11 C0 w) + Re z0)
    by (unfold Cadd, Cmul, RtoC; cbn [Re Im]; ring).
  pose proof (Rabs_Re_le_Cmod (clampw 11 C0 w)) as HRe.
  pose proof (clampw_mod55 w) as Hcm.
  pose proof (Rle_abs (- Re (clampw 11 C0 w))) as Hra2. rewrite Rabs_Ropp in Hra2.
  nra.
Qed.

Lemma Gclamp_cc : CcontC (Gclamp F z0 eps).
Proof.
  intros gam Hgam. unfold Gclamp.
  apply (ptcont_path F (fun u => Cadd (Cmul (RtoC eps) (clampw 11 C0 (gam u))) z0)).
  - apply Ccont_add; [ apply Ccont_scal | apply Ccont_const ].
    apply (ptcont_path (clampw 11 C0) gam Hgam).
    intros u e He. exact (clampw_ptcont 11 C0 ltac:(lra) (gam u) e He).
  - intros u e He. exact (HFptc _ (Gclamp_pt_pos (gam u)) e He).
Qed.

Lemma Gclamp_val : forall w, Cmod w < 5 ->
  Gclamp F z0 eps w = F (Cadd (Cmul (RtoC eps) w) z0).
Proof.
  intros w Hw. unfold Gclamp.
  replace (clampw 11 C0 w) with w; [ reflexivity | ].
  symmetry. apply clampw_id. rewrite (proj2 (Cmod0 C0) eq_refl).
  replace (Cminus w C0) with w by ring. lra.
Qed.

Lemma Gclamp_hol : forall w, Cmod w < 4 + 1 -> exists d, is_Cderiv (Gclamp F z0 eps) w d.
Proof.
  intros w Hw.
  assert (Hpt' : 0 < Re (Cadd (Cmul (RtoC eps) w) z0)).
  { replace (Re (Cadd (Cmul (RtoC eps) w) z0)) with (eps * Re w + Re z0)
      by (unfold Cadd, Cmul, RtoC; cbn [Re Im]; ring).
    pose proof (Rabs_Re_le_Cmod w) as HRe.
    pose proof (Rle_abs (- Re w)) as Hra2. rewrite Rabs_Ropp in Hra2.
    pose proof (Rabs_pos (Re w)). nra. }
  destruct (HFhol (Cadd (Cmul (RtoC eps) w) z0) Hpt') as [dF HdF].
  exists (Cmul (RtoC eps) dF).
  apply (is_Cderiv_congr (Gclamp F z0 eps) (fun w' => F (Cadd (Cmul (RtoC eps) w') z0))
           w (Cmul (RtoC eps) dF) (11 / 2 - Cmod w)).
  - pose proof (Cmod_nonneg w); lra.
  - intros w' Hw'. unfold Gclamp.
    replace (clampw 11 C0 w') with w'; [ reflexivity | ].
    symmetry. apply clampw_id. rewrite (proj2 (Cmod0 C0) eq_refl).
    replace (Cminus w' C0) with w' by ring.
    assert (Cmod w' <= Cmod (Cminus w' w) + Cmod w)
      by (replace w' with (Cadd (Cminus w' w) w) at 1 by ring; apply Cmod_triangle).
    lra.
  - exact (Cderiv_comp_affine F (RtoC eps) z0 w dF HdF).
Qed.

Lemma Gclamp_ptc : forall w2 e, 0 < e -> exists del, 0 < del /\
  forall w, Cmod (Cminus w w2) < del ->
    Cmod (Cminus (Gclamp F z0 eps w) (Gclamp F z0 eps w2)) < e.
Proof.
  intros w2 e He.
  destruct (HFptc _ (Gclamp_pt_pos w2) e He) as [delF [HdelF Hb]].
  exists (delF / (2 * eps)). split; [ apply Rdiv_lt_0_compat; lra | ].
  intros w Hw. unfold Gclamp. apply Hb.
  replace (Cminus (Cadd (Cmul (RtoC eps) (clampw 11 C0 w)) z0)
                  (Cadd (Cmul (RtoC eps) (clampw 11 C0 w2)) z0))
    with (Cmul (RtoC eps) (Cminus (clampw 11 C0 w) (clampw 11 C0 w2))) by ring.
  rewrite Cmod_mul, Cmod_RtoC, (Rabs_right eps) by lra.
  eapply Rle_lt_trans;
    [ apply Rmult_le_compat_l; [ lra | apply (clampw_lipschitz 11 C0 w w2); lra ] | ].
  apply Rlt_le_trans with (eps * (2 * (delF / (2 * eps))));
    [ apply Rmult_lt_compat_l; [ lra | ] | apply Req_le; field; lra ].
  apply Rmult_lt_compat_l; [ lra | exact Hw ].
Qed.

End ClampedTower.

Print Assumptions Gclamp_cc.
Print Assumptions Gclamp_hol.
Print Assumptions Gclamp_ptc.
