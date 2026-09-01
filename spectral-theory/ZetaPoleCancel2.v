(* ================================================================= *)
(*  ZetaPoleCancel2.v  --  blocker C0, finished.                      *)
(*                                                                    *)
(*  PhiMinus = -B'/B is holomorphic on {Re s > 0} INCLUDING s = 1.     *)
(*                                                                    *)
(*  Why a second file is needed rather than a patch to ZetaPoleCancel: *)
(*  ZetaFn.zF is DEFINED to be C0 at s = 1 (its Ceq_dec2 branch), so   *)
(*      ZetaPoleCancel.Bfn C1 = Cmul C0 C0 = C0,                      *)
(*  and PhiMinus C1 = Copp (Cmul (Bderiv C1) (Cinv C0)) is garbage.    *)
(*  The correct extension already exists: CZetaRegular6.BfnT, with     *)
(*      BfnT_at1 : BfnT C1 = C1,                                       *)
(*      BfnT_eq  : BfnT s = (s-1) * zF s   on Re s > 0, s <> 1,        *)
(*      BfnT_holo: holomorphic on ALL of Re s > 0.                     *)
(*  So C0 is a rewiring, not an analysis problem.  This file does the  *)
(*  rewiring and supplies the one genuinely missing ingredient: a      *)
(*  HOLOMORPHIC derivative for BfnT at s = 1 (PhiMinus = -B'/B needs   *)
(*  B' differentiable, and ZetaPoleCancel.Bderiv2 is unavailable at 1).*)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import ComplexField Cmodulus Holomorphic CDeriv CHoloCalculus
        CDerivUnique CCutoff CGcutCont CDerivHoloDisk
        CZeta ZetaFn ZetaDeriv ZetaPoleCancel
        CZetaRegular CZetaRegular2 CZetaRegular6.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  Small geometric helpers                                           *)
(* ----------------------------------------------------------------- *)

Lemma Rabs_Re_le2 : forall c, Rabs (Re c) <= Cmod c.
Proof.
  intro c. unfold Cmod, Cnorm2.
  rewrite <- (sqrt_Rsqr_abs (Re c)). apply sqrt_le_1_alt.
  unfold Rsqr. pose proof (Rle_0_sqr (Im c)). unfold Rsqr in *. lra.
Qed.

Lemma Cmod_minus_sym : forall a b, Cmod (Cminus a b) = Cmod (Cminus b a).
Proof.
  intros a b. unfold Cmod, Cnorm2, Cminus, Copp, Cadd; cbn [Re Im].
  f_equal. ring.
Qed.

Lemma C1_ne_C0 : C1 <> C0.
Proof. intro Hc. apply (f_equal Re) in Hc. cbn in Hc. lra. Qed.

Lemma Cmod_pos_ne : forall c, c <> C0 -> 0 < Cmod c.
Proof.
  intros c Hc. pose proof (Cmod_nonneg c) as H.
  assert (Cmod c <> 0) by (intro Hz; apply Hc; apply (proj1 (Cmod0 c)); exact Hz).
  lra.
Qed.

Lemma ne_C1_sub : forall z, z <> C1 -> Cminus C1 z <> C0.
Proof.
  intros z Hne Hc. apply Hne. apply Ceq.
  - apply (f_equal Re) in Hc; cbn in Hc; cbn; lra.
  - apply (f_equal Im) in Hc; cbn in Hc; cbn; lra.
Qed.

Lemma ne_C1_sub' : forall z, z <> C1 -> Cminus z C1 <> C0.
Proof.
  intros z Hne Hc. apply Hne. apply Ceq.
  - apply (f_equal Re) in Hc; cbn in Hc; cbn; lra.
  - apply (f_equal Im) in Hc; cbn in Hc; cbn; lra.
Qed.

(* ----------------------------------------------------------------- *)
(*  M1.  The two B's agree off 1, and BfnT is nonzero near 1.         *)
(* ----------------------------------------------------------------- *)

Lemma Bfn_BfnT_off1 : forall s, 0 < Re s -> Cminus C1 s <> C0 ->
  ZetaPoleCancel.Bfn s = BfnT s.
Proof.
  intros s H0 H1. unfold ZetaPoleCancel.Bfn. symmetry. exact (BfnT_eq s H0 H1).
Qed.

Theorem BfnT_ne0_near1 :
  exists r, 0 < r /\ forall w, Cmod (Cminus w C1) < r -> BfnT w <> C0.
Proof.
  assert (Hval : BfnT C1 <> C0) by (rewrite BfnT_at1; exact C1_ne_C0).
  destruct (Cderiv_nonzero_nbhd BfnT C1 (RtoC ellsum) BfnT_deriv1 Hval)
    as [del [Hdel Hnb]].
  exists del. split; [ exact Hdel | ].
  intros w Hw.
  replace w with (Cadd C1 (Cminus w C1)) by (apply Ceq; cbn; ring).
  apply Hnb. exact Hw.
Qed.

(* ----------------------------------------------------------------- *)
(*  M2a.  The total derivative function, and that it IS the derivative *)
(* ----------------------------------------------------------------- *)

Definition BderivT (s : C) : C :=
  match CZetaRegular.Ceq_dec s C1 with
  | left _  => RtoC ellsum
  | right _ => Bderiv s
  end.

Lemma BderivT_at1 : BderivT C1 = RtoC ellsum.
Proof.
  unfold BderivT. destruct (CZetaRegular.Ceq_dec C1 C1) as [He | Hne].
  - reflexivity.
  - exfalso; apply Hne; reflexivity.
Qed.

Lemma BderivT_off1 : forall s, s <> C1 -> BderivT s = Bderiv s.
Proof.
  intros s Hs. unfold BderivT.
  destruct (CZetaRegular.Ceq_dec s C1) as [He | Hne].
  - exfalso; apply Hs; exact He.
  - reflexivity.
Qed.

Theorem BderivT_spec : forall z, 0 < Re z -> is_Cderiv BfnT z (BderivT z).
Proof.
  intros z Hz.
  destruct (CZetaRegular.Ceq_dec z C1) as [He | Hne].
  - subst z. rewrite BderivT_at1. exact BfnT_deriv1.
  - rewrite (BderivT_off1 z Hne).
    assert (H1 : Cminus C1 z <> C0) by (apply ne_C1_sub; exact Hne).
    assert (Hcm : 0 < Cmod (Cminus z C1))
      by (apply Cmod_pos_ne; apply ne_C1_sub'; exact Hne).
    assert (Hr : 0 < Rmin (Re z) (Cmod (Cminus z C1)))
      by (apply Rmin_glb_lt; assumption).
    apply (is_Cderiv_congr_local BfnT ZetaPoleCancel.Bfn z (Bderiv z)
             (Rmin (Re z) (Cmod (Cminus z C1))) Hr).
    + intros w Hw.
      pose proof (Rmin_l (Re z) (Cmod (Cminus z C1))) as Hm1.
      pose proof (Rmin_r (Re z) (Cmod (Cminus z C1))) as Hm2.
      assert (HwRe : 0 < Re w).
      { pose proof (Rabs_Re_le2 (Cminus w z)) as Hb.
        assert (Hlt : Rabs (Re (Cminus w z)) < Re z) by lra.
        apply Rabs_def2 in Hlt. cbn in Hlt. lra. }
      assert (HwNe : Cminus C1 w <> C0).
      { apply ne_C1_sub. intro Hc. subst w.
        rewrite Cmod_minus_sym in Hw. lra. }
      symmetry. exact (Bfn_BfnT_off1 w HwRe HwNe).
    + apply B_deriv. split; assumption.
Qed.

(* ----------------------------------------------------------------- *)
(*  M2b.  BderivT is holomorphic away from 1 (existing machinery).     *)
(* ----------------------------------------------------------------- *)

Lemma BderivT_holo_off1 : forall z, 0 < Re z -> z <> C1 ->
  exists d, is_Cderiv BderivT z d.
Proof.
  intros z Hz Hne.
  assert (H1 : Cminus C1 z <> C0) by (apply ne_C1_sub; exact Hne).
  assert (Hcm : 0 < Cmod (Cminus z C1))
    by (apply Cmod_pos_ne; apply ne_C1_sub'; exact Hne).
  exists (Bderiv2 z Hz H1).
  apply (is_Cderiv_ext_local BderivT Bderiv z (Bderiv2 z Hz H1)
           (Cmod (Cminus z C1)) Hcm).
  - intros w Hw. apply BderivT_off1.
    intro Hc. subst w. rewrite Cmod_minus_sym in Hw. lra.
  - apply Bderiv_deriv.
Qed.

(* ----------------------------------------------------------------- *)
(*  M2c.  BderivT is holomorphic AT 1.                                *)
(*                                                                    *)
(*  Three obstacles, each dodged by an existing tool:                  *)
(*    - CDerivHoloDisk works on disks centred at the ORIGIN            *)
(*        -> affine rescale  w |-> 1 + w/10  (Cderiv_comp_affine)      *)
(*    - it demands holomorphy on radius 2*R2+1                         *)
(*        -> the 1/10 rescale buys the room                            *)
(*    - it demands GLOBAL pointwise continuity, but BfnT is C0 on      *)
(*      Re s <= 0                                                      *)
(*        -> radial cutoff (CGcutCont.gcut)                            *)
(* ----------------------------------------------------------------- *)

Definition Vres (w : C) : C := BfnT (Cadd (Cmul (RtoC (/ 10)) w) C1).
Definition Vcut : C -> C := gcut Vres 3 4.
Definition wmap (s : C) : C :=
  Cadd (Cmul (RtoC 10) s) (Copp (Cmul (RtoC 10) C1)).

Lemma wmap_alt : forall s, wmap s = Cmul (RtoC 10) (Cminus s C1).
Proof. intro s. unfold wmap. apply Ceq; cbn; ring. Qed.

Lemma wmap_mod : forall s, Cmod (wmap s) = 10 * Cmod (Cminus s C1).
Proof.
  intro s. rewrite wmap_alt, Cmod_mul, Cmod_RtoC, Rabs_right by lra. reflexivity.
Qed.

Lemma wmap_back : forall s, Cadd (Cmul (RtoC (/ 10)) (wmap s)) C1 = s.
Proof. intro s. unfold wmap. apply Ceq; cbn; field. Qed.

Lemma Vres_holo : forall w, Cmod w < 10 -> exists d, is_Cderiv Vres w d.
Proof.
  intros w Hw.
  assert (HRe : 0 < Re (Cadd (Cmul (RtoC (/ 10)) w) C1)).
  { pose proof (Rabs_Re_le2 w) as Hb.
    assert (Ha : Rabs (Re w) < 10) by lra.
    apply Rabs_def2 in Ha. cbn. lra. }
  destruct (BfnT_holo _ HRe) as [d Hd].
  exists (Cmul (RtoC (/ 10)) d).
  exact (Cderiv_comp_affine BfnT (RtoC (/ 10)) C1 w d Hd).
Qed.

Lemma Vcut_eq : forall w, Cmod w < 3 -> Vcut w = Vres w.
Proof. intros w Hw. apply (gcut_one Vres 3 4 ltac:(lra) w Hw). Qed.

Lemma Vcut_holo : forall w, Cmod w < 3 -> exists d, is_Cderiv Vcut w d.
Proof.
  intros w Hw.
  apply (gcut_holo Vres 3 4 10 ltac:(lra) ltac:(lra) Vres_holo w Hw).
Qed.

Lemma Vcut_ptcont : forall z eps, 0 < eps -> exists del, 0 < del /\
  forall z', Cmod (Cminus z' z) < del -> Cmod (Cminus (Vcut z') (Vcut z)) < eps.
Proof.
  intros z eps He.
  apply (gcut_cmod_cont Vres 3 4 10 ltac:(lra) ltac:(lra) Vres_holo z eps He).
Qed.

(* the derivative of Vres transported off the cutoff *)
Lemma Vres_deriv_of_Vcut : forall (Vp : C -> C),
  (forall w, Cmod w < 1 -> is_Cderiv Vcut w (Vp w)) ->
  forall w, Cmod w < 1 -> is_Cderiv Vres w (Vp w).
Proof.
  intros Vp HVp w Hw.
  apply (is_Cderiv_ext_local Vres Vcut w (Vp w) (3 - Cmod w) ltac:(lra)).
  - intros v Hv.
    assert (Hvm : Cmod v < 3).
    { pose proof (Cmod_triangle (Cminus v w) w) as Ht.
      replace (Cadd (Cminus v w) w) with v in Ht by (apply Ceq; cbn; ring).
      lra. }
    symmetry. exact (Vcut_eq v Hvm).
  - exact (HVp w Hw).
Qed.

(* the pull-back identity: BderivT s = 10 * Vp (wmap s) near s = 1 *)
Lemma BderivT_eq_Vp : forall (Vp : C -> C),
  (forall w, Cmod w < 1 -> is_Cderiv Vcut w (Vp w)) ->
  forall s, Cmod (Cminus s C1) < / 10 ->
  BderivT s = Cmul (RtoC 10) (Vp (wmap s)).
Proof.
  intros Vp HVp s Hs.
  assert (Hwm : Cmod (wmap s) < 1) by (rewrite wmap_mod; lra).
  (* Re s > 0, from |s-1| < 1/10 *)
  assert (HsRe : 0 < Re s).
  { pose proof (Rabs_Re_le2 (Cminus s C1)) as Hb.
    assert (Ha : Rabs (Re (Cminus s C1)) < / 10) by lra.
    apply Rabs_def2 in Ha. cbn in Ha. lra. }
  (* the chain rule gives the OTHER derivative of Vres at wmap s *)
  assert (Hchain : is_Cderiv Vres (wmap s) (Cmul (RtoC (/ 10)) (BderivT s))).
  { unfold Vres.
    assert (Hpt : is_Cderiv BfnT (Cadd (Cmul (RtoC (/ 10)) (wmap s)) C1)
                    (BderivT s)).
    { rewrite (wmap_back s). exact (BderivT_spec s HsRe). }
    exact (Cderiv_comp_affine BfnT (RtoC (/ 10)) C1 (wmap s) (BderivT s) Hpt). }
  pose proof (Vres_deriv_of_Vcut Vp HVp (wmap s) Hwm) as Hother.
  pose proof (is_Cderiv_unique Vres (wmap s) _ _ Hother Hchain) as Heq.
  rewrite Heq. apply Ceq; cbn; field.
Qed.

Theorem BderivT_holo_at1 : exists d, is_Cderiv BderivT C1 d.
Proof.
  destruct (holo_deriv_fun_radius Vcut 1 ltac:(lra) Vcut_ptcont
              (fun z Hz => Vcut_holo z ltac:(lra))) as [Vp [HVp1 HVp2]].
  destruct (HVp2 C0 ltac:(rewrite (proj2 (Cmod0 C0) eq_refl); lra)) as [dVp HdVp].
  assert (HVp' : is_Cderiv Vp (Cadd (Cmul (RtoC 10) C1) (Copp (Cmul (RtoC 10) C1))) dVp).
  { replace (Cadd (Cmul (RtoC 10) C1) (Copp (Cmul (RtoC 10) C1))) with C0
      by (apply Ceq; cbn; ring).
    exact HdVp. }
  pose proof (Cderiv_comp_affine Vp (RtoC 10) (Copp (Cmul (RtoC 10) C1))
                C1 dVp HVp') as HGd.
  pose proof (Cderiv_mul (fun _ : C => RtoC 10) (fun w => Vp (wmap w)) C1
                C0 (Cmul (RtoC 10) dVp) (Cderiv_const (RtoC 10) C1) HGd) as HWd.
  eexists.
  apply (is_Cderiv_ext_local BderivT (fun w => Cmul (RtoC 10) (Vp (wmap w)))
           C1 _ (/ 10) ltac:(lra)).
  - intros w Hw. exact (BderivT_eq_Vp Vp HVp1 w Hw).
  - exact HWd.
Qed.

Theorem BderivT_holo : forall z, 0 < Re z -> exists d, is_Cderiv BderivT z d.
Proof.
  intros z Hz.
  destruct (CZetaRegular.Ceq_dec z C1) as [He | Hne].
  - subst z. exact BderivT_holo_at1.
  - exact (BderivT_holo_off1 z Hz Hne).
Qed.

(* ================================================================= *)
(*  M3.  PhiMinusT -- the 1-inclusive replacement for PhiMinus.        *)
(* ================================================================= *)

Definition PhiMinusT (s : C) : C := Copp (Cmul (BderivT s) (Cinv (BfnT s))).

Theorem phi_minusT_holo : forall z, 0 < Re z -> BfnT z <> C0 ->
  exists d, is_Cderiv PhiMinusT z d.
Proof.
  intros z Hz Hne.
  destruct (BderivT_holo z Hz) as [d2 Hd2].
  pose proof (BderivT_spec z Hz) as Hd1.
  eexists. unfold PhiMinusT. apply Cderiv_opp.
  exact (Cderiv_div BderivT BfnT z d2 (BderivT z) Hd2 Hd1 Hne).
Qed.

(* the point the old PhiMinus could not even be stated at *)
Theorem phi_minusT_at1 : exists d, is_Cderiv PhiMinusT C1 d.
Proof.
  apply phi_minusT_holo.
  - cbn. lra.
  - rewrite BfnT_at1. exact C1_ne_C0.
Qed.

(* holomorphic on a whole neighbourhood of 1 -- what Newman consumes *)
Theorem phi_minusT_holo_near1 :
  exists r, 0 < r /\ forall w, Cmod (Cminus w C1) < r ->
    exists d, is_Cderiv PhiMinusT w d.
Proof.
  destruct BfnT_ne0_near1 as [r0 [Hr0 Hne]].
  exists (Rmin r0 1). split; [ apply Rmin_glb_lt; lra | ].
  intros w Hw.
  pose proof (Rmin_l r0 1) as Hm1. pose proof (Rmin_r r0 1) as Hm2.
  assert (HwRe : 0 < Re w).
  { pose proof (Rabs_Re_le2 (Cminus w C1)) as Hb.
    assert (Ha : Rabs (Re (Cminus w C1)) < 1) by lra.
    apply Rabs_def2 in Ha. cbn in Ha. lra. }
  apply phi_minusT_holo; [ exact HwRe | apply Hne; lra ].
Qed.

(* nothing downstream regresses: the two agree wherever the old one is
   meaningful *)
Theorem phi_minusT_eq : forall s, 0 < Re s -> Cminus C1 s <> C0 ->
  PhiMinusT s = PhiMinus s.
Proof.
  intros s H0 H1.
  assert (Hs1 : s <> C1)
    by (intro Hc; subst s; apply H1; apply Ceq; cbn; ring).
  unfold PhiMinusT, PhiMinus.
  rewrite (BderivT_off1 s Hs1), <- (Bfn_BfnT_off1 s H0 H1).
  reflexivity.
Qed.

(* --------------------------------------------------------------- *)
(*  The rewiring is not vacuous: the OLD B is wrong exactly at 1,     *)
(*  because ZetaFn.zF is DEFINED to be C0 there.                      *)
(* --------------------------------------------------------------- *)

Theorem old_Bfn_broken_at1 : ZetaPoleCancel.Bfn C1 = C0 /\ BfnT C1 <> C0.
Proof.
  split.
  - unfold ZetaPoleCancel.Bfn.
    replace (Cminus C1 C1) with C0 by (apply Ceq; cbn; ring).
    apply Ceq; cbn; ring.
  - rewrite BfnT_at1. exact C1_ne_C0.
Qed.

Print Assumptions old_Bfn_broken_at1.
Print Assumptions BderivT_spec.
Print Assumptions BderivT_holo.
Print Assumptions phi_minusT_holo.
Print Assumptions phi_minusT_at1.
Print Assumptions phi_minusT_eq.
