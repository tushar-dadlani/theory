(* ================================================================= *)
(*  LaplacePhi.v  —  Newman A3: the "1/z" term of the Laplace identity.   *)
(*                                                                    *)
(*  The Newman transform identity is  g(z) = Phi(z+1)/(z+1) - 1/z.       *)
(*  Here we compute the elementary half exactly, through the full        *)
(*  transform gfull built in LaplaceFull:                               *)
(*                                                                    *)
(*    laplace_one :  int_0^oo e^{-zt} dt  =  1/z   (Re z > 0),           *)
(*                                                                    *)
(*  i.e. gfull of the constant function 1 is Cinv z.  This validates      *)
(*  the gfull machinery on a known transform and supplies the 1/z          *)
(*  building block.  The truncation g_T(z) = int_0^T e^{-zt} dt is         *)
(*  computed by a component-wise FTC on the C-antiderivative               *)
(*  e^{-zt}/(-z), then z-> the T->oo limit via gfull_cv.  Axiom-clean.    *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia FunctionalExtensionality.
Require Import ComplexField Cmodulus CSeries CIntegral2 CSegInt CExpKernel CexpFull EulerFormula
        ContinuousCoV CImproperIntegral CDirichlet PerronBound PerronEdge LaplaceFull.
Open Scope R_scope.

Lemma Un_cv_ext : forall u v l, (forall n, u n = v n) -> Un_cv u l -> Un_cv v l.
Proof.
  intros u v l Heq Hu eps Heps; destruct (Hu eps Heps) as [N HN];
    exists N; intros n Hn; rewrite <- (Heq n); apply HN; exact Hn.
Qed.

(* extensionality for derivable_pt_lim *)
Lemma dpl_ext : forall (f g : R -> R) t l,
  (forall x, f x = g x) -> derivable_pt_lim f t l -> derivable_pt_lim g t l.
Proof.
  intros f g t l Heq H; assert (f = g) by (apply functional_extensionality; exact Heq);
    subst; exact H.
Qed.

Lemma cexpzt_0 : forall w, cexpzt w 0 = C1.
Proof.
  intro w; unfold cexpzt.
  assert (Hw0 : Cmul w (RtoC 0) = C0) by (unfold Cmul, RtoC, C0; apply Ceq; cbn; ring).
  rewrite Hw0; unfold Cexpf, Cexp, RtoC, C1, C0, Cmul; cbn [Re Im];
    rewrite exp_0, cos_0, sin_0; apply Ceq; cbn; ring.
Qed.

Section One.
Variable z : C.
Hypothesis Hz : 0 < Re z.

Lemma z_ne0 : z <> C0.
Proof. intro H; rewrite H in Hz; cbn in Hz; lra. Qed.

Lemma oppz_ne0 : Copp z <> C0.
Proof. intro H; apply (f_equal Re) in H; cbn in H; lra. Qed.

(*  the real/imag parts of the C-antiderivative  e^{-zt}/(-z)  *)
Lemma GR_deriv : forall t,
  derivable_pt_lim (fun u => Re (Cmul (cexpzt (Copp z) u) (Cinv (Copp z)))) t
                   (Re (cexpzt (Copp z) t)).
Proof.
  intro t.
  assert (Hc : Cmul (Cinv (Copp z)) (Cmul (Copp z) (cexpzt (Copp z) t)) = cexpzt (Copp z) t).
  { replace (Cmul (Cinv (Copp z)) (Cmul (Copp z) (cexpzt (Copp z) t)))
      with (Cmul (Cmul (Cinv (Copp z)) (Copp z)) (cexpzt (Copp z) t)) by ring.
    rewrite (Cinv_l (Copp z) oppz_ne0); ring. }
  assert (Hval : Re (cexpzt (Copp z) t)
    = Re (Cinv (Copp z)) * Re (Cmul (Copp z) (cexpzt (Copp z) t))
      + - Im (Cinv (Copp z)) * Im (Cmul (Copp z) (cexpzt (Copp z) t))).
  { transitivity (Re (Cmul (Cinv (Copp z)) (Cmul (Copp z) (cexpzt (Copp z) t))));
      [ rewrite Hc; reflexivity | unfold Cmul; cbn [Re Im]; ring ]. }
  rewrite Hval.
  apply (dpl_ext (fun u => Re (Cinv (Copp z)) * Re (cexpzt (Copp z) u)
                           + - Im (Cinv (Copp z)) * Im (cexpzt (Copp z) u)));
    [ intro u; unfold Cmul; cbn [Re Im]; ring | ].
  apply derivable_pt_lim_plus;
    [ apply (derivable_pt_lim_scal (fun u => Re (cexpzt (Copp z) u)) (Re (Cinv (Copp z)))
               t (Re (Cmul (Copp z) (cexpzt (Copp z) t))) (Re_cexpzt_deriv (Copp z) t))
    | apply (derivable_pt_lim_scal (fun u => Im (cexpzt (Copp z) u)) (- Im (Cinv (Copp z)))
               t (Im (Cmul (Copp z) (cexpzt (Copp z) t))) (Im_cexpzt_deriv (Copp z) t)) ].
Qed.

Lemma GI_deriv : forall t,
  derivable_pt_lim (fun u => Im (Cmul (cexpzt (Copp z) u) (Cinv (Copp z)))) t
                   (Im (cexpzt (Copp z) t)).
Proof.
  intro t.
  assert (Hc : Cmul (Cinv (Copp z)) (Cmul (Copp z) (cexpzt (Copp z) t)) = cexpzt (Copp z) t).
  { replace (Cmul (Cinv (Copp z)) (Cmul (Copp z) (cexpzt (Copp z) t)))
      with (Cmul (Cmul (Cinv (Copp z)) (Copp z)) (cexpzt (Copp z) t)) by ring.
    rewrite (Cinv_l (Copp z) oppz_ne0); ring. }
  assert (Hval : Im (cexpzt (Copp z) t)
    = Im (Cinv (Copp z)) * Re (Cmul (Copp z) (cexpzt (Copp z) t))
      + Re (Cinv (Copp z)) * Im (Cmul (Copp z) (cexpzt (Copp z) t))).
  { transitivity (Im (Cmul (Cinv (Copp z)) (Cmul (Copp z) (cexpzt (Copp z) t))));
      [ rewrite Hc; reflexivity | unfold Cmul; cbn [Re Im]; ring ]. }
  rewrite Hval.
  apply (dpl_ext (fun u => Im (Cinv (Copp z)) * Re (cexpzt (Copp z) u)
                           + Re (Cinv (Copp z)) * Im (cexpzt (Copp z) u)));
    [ intro u; unfold Cmul; cbn [Re Im]; ring | ].
  apply derivable_pt_lim_plus;
    [ apply (derivable_pt_lim_scal (fun u => Re (cexpzt (Copp z) u)) (Im (Cinv (Copp z)))
               t (Re (Cmul (Copp z) (cexpzt (Copp z) t))) (Re_cexpzt_deriv (Copp z) t))
    | apply (derivable_pt_lim_scal (fun u => Im (cexpzt (Copp z) u)) (Re (Cinv (Copp z)))
               t (Im (Cmul (Copp z) (cexpzt (Copp z) t))) (Im_cexpzt_deriv (Copp z) t)) ].
Qed.

(*  the truncated integral  int_0^T e^{-zt} dt = (e^{-zT}-1)/(-z)  *)
Lemma Cint_cexpzt : forall T (Hcont : Ccont (fun t => cexpzt (Copp z) t)), 0 <= T ->
  Cintf (fun t => cexpzt (Copp z) t) Hcont 0 T
  = Cmul (Cminus (cexpzt (Copp z) T) C1) (Cinv (Copp z)).
Proof.
  intros T Hcont HT; apply Ceq.
  - rewrite Re_Cintf.
    assert (HantiR : antiderivative (fun t => Re (cexpzt (Copp z) t))
              (fun t => Re (Cmul (cexpzt (Copp z) t) (Cinv (Copp z)))) 0 T).
    { split; [ | exact HT ]; intros x _.
      exists (exist _ (Re (cexpzt (Copp z) x)) (GR_deriv x)).
      unfold derive_pt; simpl; reflexivity. }
    rewrite (FTC_antideriv (fun t => Re (cexpzt (Copp z) t))
               (fun t => Re (Cmul (cexpzt (Copp z) t) (Cinv (Copp z)))) 0 T HT
               (fun x _ => proj1 Hcont x) _ HantiR).
    rewrite cexpzt_0; unfold Cminus, Cmul, C1; cbn [Re Im]; ring.
  - rewrite Im_Cintf.
    assert (HantiI : antiderivative (fun t => Im (cexpzt (Copp z) t))
              (fun t => Im (Cmul (cexpzt (Copp z) t) (Cinv (Copp z)))) 0 T).
    { split; [ | exact HT ]; intros x _.
      exists (exist _ (Im (cexpzt (Copp z) x)) (GI_deriv x)).
      unfold derive_pt; simpl; reflexivity. }
    rewrite (FTC_antideriv (fun t => Im (cexpzt (Copp z) t))
               (fun t => Im (Cmul (cexpzt (Copp z) t) (Cinv (Copp z)))) 0 T HT
               (fun x _ => proj2 Hcont x) _ HantiI).
    rewrite cexpzt_0; unfold Cminus, Cmul, C1; cbn [Re Im]; ring.
Qed.

(*  the constant-1 integrand and its transform  *)
Lemma LT_one : forall (Hc1 : Ccont (fun _ : R => C1)) T, 0 <= T ->
  LT (fun _ => C1) Hc1 z T = Cmul (Cminus (cexpzt (Copp z) T) C1) (Cinv (Copp z)).
Proof.
  intros Hc1 T HT; unfold LT.
  rewrite (Cintf_ext (lint (fun _ => C1) z) (fun t => cexpzt (Copp z) t)
             (lint_cont (fun _ => C1) Hc1 z) (Ccont_cexpzt (Copp z)) 0 T)
    by (intro u; unfold lint; ring).
  apply Cint_cexpzt; exact HT.
Qed.

(*  e^{-zt} -> 0 along t = INR n  *)
Lemma cexpzt_cv0 : CUn_cv (fun n => cexpzt (Copp z) (INR n)) C0.
Proof.
  apply CUn_cv_mod0.
  apply (Un_cv_ext (fun n => exp (- (Re z * INR n))));
    [ intro n; rewrite Cmod_cexpzt; f_equal; cbn [Re Copp]; ring | ].
  apply exp_neg_cv0, cv_infty_scal_pos; [ exact Hz | apply cv_infty_INR_loc ].
Qed.

(*  the transform of 1 is 1/z  *)
Theorem laplace_one : forall (Hc1 : Ccont (fun _ : R => C1))
  (Hb1 : forall t : R, Cmod C1 <= 1),
  gfull (fun _ => C1) Hc1 1 Hb1 z Hz = Cinv z.
Proof.
  intros Hc1 Hb1.
  assert (Hne : z <> C0) by apply z_ne0.
  (* Cmod(e^{-z INR n}) -> 0 *)
  assert (Hmod0 : Un_cv (fun n => Cmod (cexpzt (Copp z) (INR n))) 0).
  { intros eps Heps; destruct (cexpzt_cv0 eps Heps) as [N HN]; exists N; intros n Hn.
    unfold R_dist; rewrite Rminus_0_r, Rabs_pos_eq by apply Cmod_nonneg.
    specialize (HN n Hn); replace (Cminus (cexpzt (Copp z) (INR n)) C0)
      with (cexpzt (Copp z) (INR n)) in HN by ring; exact HN. }
  (* the truncations converge to Cinv z *)
  assert (Hcv : CUn_cv (fun n => LT (fun _ => C1) Hc1 z (INR n)) (Cinv z)).
  { assert (Hmod : Un_cv
      (fun n => Cmod (Cminus (LT (fun _ => C1) Hc1 z (INR n)) (Cinv z))) 0).
    { apply (Un_cv_ext (fun n => Cmod (Cinv (Copp z)) * Cmod (cexpzt (Copp z) (INR n)))).
      - intro n; rewrite <- Cmod_mul; rewrite (LT_one Hc1 (INR n) (pos_INR n)); f_equal.
        field; repeat split; solve [ exact Hne | apply oppz_ne0 ].
      - replace 0 with (Cmod (Cinv (Copp z)) * 0) by ring.
        apply Un_cv_cscal_R; exact Hmod0. }
    intros eps Heps; destruct (Hmod eps Heps) as [N HN]; exists N; intros n Hn.
    specialize (HN n Hn); unfold R_dist in HN;
      rewrite Rminus_0_r, Rabs_pos_eq in HN by apply Cmod_nonneg; exact HN. }
  apply (CUn_cv_unique (fun n => LT (fun _ => C1) Hc1 z (INR n)));
    [ apply gfull_cv | exact Hcv ].
Qed.

End One.

Print Assumptions laplace_one.

(* ================================================================= *)
(*  END LaplacePhi.v — the 1/z term:  int_0^oo e^{-zt} dt = 1/z.          *)
(*  Remaining for the full identity g(z) = Phi(z+1)/(z+1) - 1/z:          *)
(*  a real-argument Chebyshev psi (step function), a piecewise-integrable  *)
(*  transform, the u = e^t change of variables, and the Abel-sum <->       *)
(*  integral tie-back to phi_integral_rep.                                *)
(* ================================================================= *)
