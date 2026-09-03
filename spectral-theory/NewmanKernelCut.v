(* ================================================================= *)
(*  NewmanKernelCut.v  --  Zagier's kernel, cut off near its pole.     *)
(*                                                                    *)
(*  The contour-deformation step of E6 (chord -> far-left arc for the  *)
(*  entire g_T factor) needs a PRIMITIVE, and CPrimConv.PrimC demands  *)
(*  GLOBAL continuity (CcontC) of the integrand -- the same structural *)
(*  demand that forced NewmanCutoff.gtrunc on gext.  The integrand     *)
(*  here is g_T(z) e^{zT} K_R(z), entire except for K_R's pole at 0.   *)
(*                                                                    *)
(*  So cut the kernel: multiply the 1/z summand by a radial cutoff     *)
(*  vanishing on |z| <= d/4 and equal to 1 on |z| >= d/2.  The result  *)
(*  is globally pointwise continuous (NewmanCutoff.cutprod_ptcont --   *)
(*  at 0 the cutoff vanishes identically nearby, which is exactly its  *)
(*  dichotomy), agrees with newman_kernel off the disc |z| < d/2, and  *)
(*  is holomorphic there.  The deformation region {Re z < -d/2} misses *)
(*  the pole, so nothing is lost.                                     *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import ComplexField Cmodulus Holomorphic CDeriv CHoloCalculus
        CCutoff CSegInt CGcutCont CRemovableExt PerronRemovable CNewmanKernel
        NewmanCutoff NewmanContour.
Open Scope R_scope.

Lemma PtcontC_add : forall f g, PtcontC f -> PtcontC g ->
  PtcontC (fun z => Cadd (f z) (g z)).
Proof.
  intros f g Hf Hg z0 eps Heps.
  destruct (Hf z0 (eps / 2) ltac:(lra)) as [d1 [Hd1 H1]].
  destruct (Hg z0 (eps / 2) ltac:(lra)) as [d2 [Hd2 H2]].
  exists (Rmin d1 d2); split; [ apply Rmin_pos; assumption | ].
  intros w Hw.
  assert (Hw1 : Cmod (Cminus w z0) < d1)
    by (eapply Rlt_le_trans; [ exact Hw | apply Rmin_l ]).
  assert (Hw2 : Cmod (Cminus w z0) < d2)
    by (eapply Rlt_le_trans; [ exact Hw | apply Rmin_r ]).
  replace (Cminus (Cadd (f w) (g w)) (Cadd (f z0) (g z0)))
    with (Cadd (Cminus (f w) (f z0)) (Cminus (g w) (g z0))) by ring.
  eapply Rle_lt_trans; [ apply Cmod_triangle | ].
  assert (H1' := H1 w Hw1); assert (H2' := H2 w Hw2); lra.
Qed.

(* ----------------------------------------------------------------- *)
(*  The radial cutoff: 0 on |z| <= d/4, 1 on |z| >= d/2.               *)
(* ----------------------------------------------------------------- *)

Definition chir (d : R) (z : C) : R := 1 - psi (d / 4) (d / 2) (Cmod z).

Lemma chir_bounds : forall d z, 0 <= chir d z <= 1.
Proof.
  intros d z; unfold chir;
    pose proof (psi_bounds (d / 4) (d / 2) (Cmod z)); lra.
Qed.

Lemma chir_one : forall d z, 0 < d -> d / 2 <= Cmod z -> chir d z = 1.
Proof.
  intros d z Hd Hz; unfold chir.
  rewrite (psi_zero (d / 4) (d / 2) (Cmod z) ltac:(lra) Hz); ring.
Qed.

Lemma chir_zero : forall d z, 0 < d -> Cmod z <= d / 4 -> chir d z = 0.
Proof.
  intros d z Hd Hz; unfold chir.
  rewrite (psi_one (d / 4) (d / 2) (Cmod z) ltac:(lra) Hz); ring.
Qed.

Lemma chir_ptcont : forall d, 0 < d -> PtcontR (chir d).
Proof.
  intros d Hd z0 eps Heps.
  assert (HL : 0 < 4 / d) by (apply Rdiv_lt_0_compat; lra).
  exists (eps / (4 / d)); split; [ apply Rdiv_lt_0_compat; lra | ].
  intros w Hw.
  assert (Hlip : Rabs (chir d w - chir d z0) <= 4 / d * Cmod (Cminus w z0)).
  { unfold chir.
    replace (1 - psi (d / 4) (d / 2) (Cmod w) - (1 - psi (d / 4) (d / 2) (Cmod z0)))
      with (- (psi (d / 4) (d / 2) (Cmod w) - psi (d / 4) (d / 2) (Cmod z0))) by ring.
    rewrite Rabs_Ropp.
    eapply Rle_trans; [ apply psi_lip; lra | ].
    replace (/ (d / 2 - d / 4)) with (4 / d) by (field; lra).
    apply Rmult_le_compat_l; [ lra | apply Cmod_revtri ]. }
  eapply Rle_lt_trans; [ exact Hlip | ].
  apply (Rmult_lt_reg_r (/ (4 / d))); [ apply Rinv_0_lt_compat; lra | ].
  replace (4 / d * Cmod (Cminus w z0) * / (4 / d)) with (Cmod (Cminus w z0))
    by (field; lra).
  replace (eps * / (4 / d)) with (eps / (4 / d)) by (unfold Rdiv; ring).
  exact Hw.
Qed.

(* ----------------------------------------------------------------- *)
(*  1/z is pointwise continuous away from 0.                           *)
(* ----------------------------------------------------------------- *)

Lemma Cinv_ptcont_off0 : forall z0, z0 <> C0 ->
  forall eps, 0 < eps -> exists dd, 0 < dd /\
    forall w, Cmod (Cminus w z0) < dd -> Cmod (Cminus (Cinv w) (Cinv z0)) < eps.
Proof.
  intros z0 Hz0 eps Heps.
  destruct (is_Cderiv_cont Cinv z0 _ (Cderiv_inv z0 Hz0) eps Heps) as [dd [Hdd Hc]].
  exists dd; split; [ exact Hdd | ]; intros w Hw.
  specialize (Hc (Cminus w z0) Hw).
  replace (Cadd z0 (Cminus w z0)) with w in Hc by ring; exact Hc.
Qed.

(* ----------------------------------------------------------------- *)
(*  The cut kernel.                                                    *)
(* ----------------------------------------------------------------- *)

Definition Kcut (Rr d : R) (z : C) : C :=
  Cadd (Cmul (Cinv z) (RtoC (chir d z))) (Cmul z (RtoC (/ (Rr * Rr)))).

Lemma Kcut_ptcont : forall Rr d, 0 < d -> PtcontC (Kcut Rr d).
Proof.
  intros Rr d Hd; unfold Kcut; apply PtcontC_add.
  - apply (cutprod_ptcont Cinv (chir d)).
    + apply chir_bounds.
    + apply chir_ptcont; exact Hd.
    + intro z0; destruct (Ceq_dec z0 C0) as [Hz | Hz].
      * right; exists (d / 4); split; [ lra | ].
        intros w Hw; apply chir_zero; [ exact Hd | ].
        subst z0; replace (Cminus w C0) with w in Hw by ring; lra.
      * left; intros eps Heps; apply Cinv_ptcont_off0; assumption.
  - apply holo_PtcontC; intro z; eexists.
    apply Cderiv_mul; [ apply Cderiv_id | apply Cderiv_const ].
Qed.

Lemma Kcut_CcontC : forall Rr d, 0 < d -> CcontC (Kcut Rr d).
Proof. intros Rr d Hd; apply ptcont_CcontC, Kcut_ptcont; exact Hd. Qed.

Lemma Kcut_eq : forall Rr d z, 0 < d -> d / 2 <= Cmod z ->
  Kcut Rr d z = newman_kernel Rr z.
Proof.
  intros Rr d z Hd Hz; unfold Kcut, newman_kernel.
  rewrite (chir_one d z Hd Hz).
  replace (RtoC 1) with C1 by reflexivity; ring.
Qed.

Lemma newman_kernel_holo : forall Rr z, z <> C0 ->
  exists e, is_Cderiv (newman_kernel Rr) z e.
Proof.
  intros Rr z Hz; unfold newman_kernel; eexists.
  apply Cderiv_add;
    [ apply Cderiv_inv; exact Hz
    | apply Cderiv_mul; [ apply Cderiv_id | apply Cderiv_const ] ].
Qed.

Lemma Kcut_holo : forall Rr d z, 0 < d -> d / 2 < Cmod z ->
  exists e, is_Cderiv (Kcut Rr d) z e.
Proof.
  intros Rr d z Hd Hz.
  assert (Hzne : z <> C0)
    by (intro Hc; rewrite Hc, (proj2 (Cmod0 C0) eq_refl) in Hz; lra).
  destruct (newman_kernel_holo Rr z Hzne) as [e He].
  exists e; apply (is_Cderiv_congr (Kcut Rr d) (newman_kernel Rr) z e
                     (Cmod z - d / 2)); [ lra | | exact He ].
  intros w Hw; apply Kcut_eq; [ exact Hd | ].
  pose proof (Cmod_revtri w z) as HR.
  assert (Hb : Cmod z - Cmod w <= Cmod (Cminus w z)).
  { pose proof (Rle_abs (- (Cmod w - Cmod z))) as Hq; rewrite Rabs_Ropp in Hq; lra. }
  lra.
Qed.

Print Assumptions Kcut_ptcont.
Print Assumptions Kcut_holo.

(* ================================================================= *)
(*  END NewmanKernelCut.v -- a globally continuous stand-in for        *)
(*  K_R = 1/z + z/R^2, exact off the disc |z| < d/2.                   *)
(* ================================================================= *)
