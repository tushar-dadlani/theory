(* ================================================================= *)
(*  NewmanIdentity.v  —  Newman A3: the Newman transform identity.        *)
(*                                                                    *)
(*  g(z) = Phi(z+1)/(z+1) - 1/z, where g is the (cell-defined) transform  *)
(*  of Newman's f(t) = psiR(e^t)e^{-t} - 1:                              *)
(*                                                                    *)
(*    newman_identity : for 0 < Re z,                                    *)
(*      StepSum M - OneSum M  ->  Phi(z+1)/(z+1) - 1/z,                   *)
(*                                                                    *)
(*  where StepSum M = sum_k psi(k+1) int_{cell} e^{-(z+1)t} dt  (the        *)
(*  psiR(e^t)e^{-t} part, -> Phi(z+1)/(z+1) by step_transform_cv) and       *)
(*  OneSum M = sum_k int_{cell} e^{-zt} dt  (the -1 part, = int_0^{ln(M+2)} *)
(*  e^{-zt} dt by logpart_additive, -> 1/z).  Axiom-clean.               *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import ComplexField Cmodulus CSeries CIntegral2 CSegInt CExpKernel
        CZetaTerm CFTC CVonMangoldtSeries Chebyshev
        LaplaceFull LaplacePhi CellAdditivity NewmanG.
Open Scope R_scope.

Lemma Un_cv_ext' : forall u v l, (forall n, u n = v n) -> Un_cv u l -> Un_cv v l.
Proof.
  intros u v l Heq Hu eps He; destruct (Hu eps He) as [N HN];
    exists N; intros n Hn; rewrite <- (Heq n); apply HN; exact Hn.
Qed.

Lemma CV_minus_C : forall u v lu lv, CUn_cv u lu -> CUn_cv v lv ->
  CUn_cv (fun n => Cminus (u n) (v n)) (Cminus lu lv).
Proof.
  intros u v lu lv Hu Hv eps He.
  destruct (Hu (eps / 2) ltac:(lra)) as [Nu HNu].
  destruct (Hv (eps / 2) ltac:(lra)) as [Nv HNv].
  exists (max Nu Nv); intros n Hn.
  replace (Cminus (Cminus (u n) (v n)) (Cminus lu lv))
    with (Cadd (Cminus (u n) lu) (Copp (Cminus (v n) lv))) by ring.
  eapply Rle_lt_trans; [ apply Cmod_triangle | ]; rewrite Cmod_opp.
  assert (Cmod (Cminus (u n) lu) < eps / 2) by (apply HNu; lia).
  assert (Cmod (Cminus (v n) lv) < eps / 2) by (apply HNv; lia).
  lra.
Qed.

Lemma cv_infty_ln_INR : cv_infty (fun M => ln (INR (S (S M)))).
Proof.
  intro B; destruct (INR_unbounded (exp B)) as [n0 Hn0]; exists n0; intros M HM.
  rewrite <- (ln_exp B); apply ln_increasing;
    [ apply exp_pos | apply Rlt_le_trans with (INR n0); [ exact Hn0 | apply le_INR; lia ] ].
Qed.

Section Identity.
Variable z : C.
Hypothesis Hz : 0 < Re z.

Let H1 : 1 < Re (Cadd z C1) := ltac:(unfold Cadd, C1; cbn [Re]; lra).

Definition StepSum (M : nat) : C :=
  Cpsum (fun k => Cmul (RtoC (psi (S k)))
           (Cintf (fun t => cexpzt (Copp (Cadd z C1)) t) (Ccont_cexpzt (Copp (Cadd z C1)))
                  (ln (INR (S k))) (ln (INR (S (S k)))))) M.

Definition OneSum (M : nat) : C :=
  Cpsum (fun k => Cintf (fun t => cexpzt (Copp z) t) (Ccont_cexpzt (Copp z))
                    (ln (INR (S k))) (ln (INR (S (S k))))) M.

Lemma OneSum_reduce : forall M,
  OneSum M = Cmul (Cminus (cexpzt (Copp z) (ln (INR (S (S M))))) C1) (Cinv (Copp z)).
Proof.
  intro M; unfold OneSum.
  rewrite <- (logpart_additive (fun t => cexpzt (Copp z) t) (Ccont_cexpzt (Copp z)) M).
  apply (Cint_cexpzt z Hz (ln (INR (S (S M)))) (Ccont_cexpzt (Copp z))).
  rewrite <- ln_1; apply Rlt_le, ln_increasing;
    [ lra | rewrite <- INR_1; apply lt_INR; lia ].
Qed.

Lemma OneSum_cv : CUn_cv OneSum (Cinv z).
Proof.
  assert (Hne : z <> C0) by (intro Ho; apply (f_equal Re) in Ho; cbn in Ho; lra).
  assert (Hopp : Copp z <> C0) by (intro Ho; apply (f_equal Re) in Ho; cbn in Ho; lra).
  assert (Hmod : Un_cv (fun M => Cmod (Cminus (OneSum M) (Cinv z))) 0).
  { apply (Un_cv_ext' (fun M => Cmod (Cinv (Copp z))
                                * exp (- (Re z * ln (INR (S (S M))))))).
    - intro M; rewrite OneSum_reduce.
      transitivity (Cmod (Cmul (cexpzt (Copp z) (ln (INR (S (S M))))) (Cinv (Copp z)))).
      + rewrite Cmod_mul, Cmod_cexpzt; cbn [Re Copp].
        replace (- Re z * ln (INR (S (S M)))) with (- (Re z * ln (INR (S (S M))))) by ring; ring.
      + f_equal; field; repeat split; solve [ exact Hne | exact Hopp ].
    - replace 0 with (Cmod (Cinv (Copp z)) * 0) by ring.
      apply Un_cv_cscal_R, exp_neg_cv0, cv_infty_scal_pos;
        [ exact Hz | apply cv_infty_ln_INR ]. }
  intros eps He; destruct (Hmod eps He) as [N HN]; exists N; intros n Hn.
  specialize (HN n Hn); unfold R_dist in HN;
    rewrite Rminus_0_r, Rabs_pos_eq in HN by apply Cmod_nonneg; exact HN.
Qed.

(*  the Newman transform identity  *)
Theorem newman_identity :
  CUn_cv (fun M => Cminus (StepSum M) (OneSum M))
         (Cminus (Cmul (Cinv (Cadd z C1)) (Phi (Cadd z C1) H1)) (Cinv z)).
Proof.
  apply CV_minus_C; [ apply (step_transform_cv (Cadd z C1) H1) | apply OneSum_cv ].
Qed.

End Identity.

Print Assumptions newman_identity.

(* ================================================================= *)
(*  END NewmanIdentity.v — g(z) = Phi(z+1)/(z+1) - 1/z.                    *)
(*  This is the Newman transform identity: the analytic continuation of    *)
(*  the transform of psiR(e^t)e^{-t}-1 to Re z >= 0 (the Phi pole at 1      *)
(*  cancels the 1/z).  Next: the Newman contour estimate (Cmod_newman_     *)
(*  kernel + gfull_tail) and the Tauberian squeeze to psi(N)/N -> 1.        *)
(* ================================================================= *)
