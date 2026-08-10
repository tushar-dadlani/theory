(* ================================================================= *)
(*  LaplaceFull.v  —  Newman A3 foundation: the full Laplace transform    *)
(*  g(z) = int_0^oo f(t) e^{-zt} dt  (Re z > 0, f continuous & bounded),  *)
(*  as the limit of the truncations g_T, with the right-half-plane tail   *)
(*  bound  |g(z) - g_T(z)| <= B e^{-(Re z) T} / (Re z).                   *)
(*                                                                    *)
(*  Part 1 (this stage): the exponential-tail numeric core --            *)
(*  int_A^B e^{-a t} dt = (e^{-aA} - e^{-aB})/a  and its improper limit    *)
(*  e^{-aA}/a as B -> oo (a>0).  This is the majorant behind every        *)
(*  Laplace tail estimate.  Axiom-clean.                                 *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import ComplexField Cmodulus CSeries CIntegral2 CSegInt CExpKernel ContinuousCoV
        CImproperIntegral PerronBound PerronEdge.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  small convergence helpers                                          *)
(* ----------------------------------------------------------------- *)

Lemma Un_cv_const : forall c : R, Un_cv (fun _ => c) c.
Proof.
  intros c eps Heps; exists 0%nat; intros n _; unfold R_dist;
    replace (c - c) with 0 by ring; rewrite Rabs_R0; exact Heps.
Qed.

Lemma Un_cv_cscal_R : forall u l a, Un_cv u l -> Un_cv (fun k => a * u k) (a * l).
Proof.
  intros u l a Hu eps Heps.
  set (K := Rabs a + 1); assert (HK : 0 < K) by (unfold K; pose proof (Rabs_pos a); lra).
  destruct (Hu (eps / K) ltac:(apply Rdiv_lt_0_compat; [ exact Heps | exact HK ])) as [N HN].
  exists N; intros n Hn; unfold R_dist.
  replace (a * u n - a * l) with (a * (u n - l)) by ring; rewrite Rabs_mult.
  specialize (HN n Hn); unfold R_dist in HN.
  apply Rle_lt_trans with (Rabs a * (eps / K)).
  - apply Rmult_le_compat_l; [ apply Rabs_pos | left; exact HN ].
  - apply Rlt_le_trans with (K * (eps / K));
      [ apply Rmult_lt_compat_r; [ apply Rdiv_lt_0_compat; [ exact Heps | exact HK ] | unfold K; lra ]
      | right; field; lra ].
Qed.

Lemma cv_infty_scal_pos : forall c, 0 < c -> forall u, cv_infty u -> cv_infty (fun k => c * u k).
Proof.
  intros c Hc u Hu M; destruct (Hu (M / c)) as [N HN]; exists N; intros n Hn.
  specialize (HN n Hn).
  apply Rle_lt_trans with (c * (M / c)); [ right; field; apply Rgt_not_eq; exact Hc | ].
  apply Rmult_lt_compat_l; [ exact Hc | exact HN ].
Qed.

Lemma exp_neg_cv0 : forall u, cv_infty u -> Un_cv (fun k => exp (- u k)) 0.
Proof.
  intros u Hu eps Heps; destruct (Hu (- ln eps)) as [N HN].
  exists N; intros n Hn; unfold R_dist; rewrite Rminus_0_r, Rabs_pos_eq by (left; apply exp_pos).
  specialize (HN n Hn); rewrite <- (exp_ln eps Heps); apply exp_increasing; lra.
Qed.

(* ----------------------------------------------------------------- *)
(*  the exponential integral  int_A^B e^{-a t} dt                       *)
(* ----------------------------------------------------------------- *)

Lemma neg_lin_deriv : forall a x, derivable_pt_lim (fun t => - (a * t)) x (- a).
Proof.
  intros a x; replace (- a) with (- (a * 1)) by ring.
  apply derivable_pt_lim_opp, (derivable_pt_lim_scal (fun t => t) a x 1), derivable_pt_lim_id.
Qed.

Lemma exp_neg_scaled_cont : forall a x, continuity_pt (fun t => exp (- (a * t))) x.
Proof.
  intros a x; apply (continuity_pt_comp (fun t => - (a * t)) exp);
    [ apply derivable_continuous_pt; exists (- a); apply neg_lin_deriv
    | apply derivable_continuous_pt; exists (exp (- (a * x))); apply derivable_pt_lim_exp ].
Qed.

Lemma exp_scaled_deriv : forall a x, a <> 0 ->
  derivable_pt_lim (fun t => - / a * exp (- (a * t))) x (exp (- (a * x))).
Proof.
  intros a x Ha.
  assert (Hcomp : derivable_pt_lim (fun t => exp (- (a * t))) x (exp (- (a * x)) * (- a)))
    by (apply (derivable_pt_lim_comp (fun t => - (a * t)) exp x (- a) (exp (- (a * x))));
        [ apply neg_lin_deriv | apply derivable_pt_lim_exp ]).
  replace (exp (- (a * x))) with (- / a * (exp (- (a * x)) * (- a))) by (field; exact Ha).
  apply derivable_pt_lim_scal; exact Hcomp.
Qed.

Lemma exp_int_AB : forall a A B (Ha : 0 < a) (Hab : A <= B)
  (pr : Riemann_integrable (fun t => exp (- (a * t))) A B),
  RiemannInt pr = (exp (- (a * A)) - exp (- (a * B))) / a.
Proof.
  intros a A B Ha Hab pr; assert (Hane : a <> 0) by (apply Rgt_not_eq; exact Ha).
  assert (Hanti : antiderivative (fun t => exp (- (a * t)))
                    (fun x => - / a * exp (- (a * x))) A B).
  { split; [ | exact Hab ]; intros x _.
    exists (exist (fun l => derivable_pt_lim (fun t => - / a * exp (- (a * t))) x l)
              (exp (- (a * x))) (exp_scaled_deriv a x Hane)).
    unfold derive_pt; simpl; reflexivity. }
  rewrite (FTC_antideriv (fun t => exp (- (a * t))) (fun x => - / a * exp (- (a * x))) A B Hab
             (fun x _ => exp_neg_scaled_cont a x) pr Hanti).
  field; exact Hane.
Qed.

(*  the improper tail: int_A^{Tn} e^{-a t} dt -> e^{-aA}/a as Tn -> oo  *)
Lemma exp_improper_tail : forall a A, 0 < a ->
  forall Tn : nat -> R, cv_infty Tn ->
  Un_cv (fun k => (exp (- (a * A)) - exp (- (a * Tn k))) / a) (exp (- (a * A)) / a).
Proof.
  intros a A Ha Tn HTn; assert (Hane : a <> 0) by (apply Rgt_not_eq; exact Ha).
  apply (Un_cv_ext (fun k => / a * (exp (- (a * A)) - exp (- (a * Tn k)))));
    [ intro k; field; exact Hane | ].
  replace (exp (- (a * A)) / a) with (/ a * (exp (- (a * A)) - 0)) by (field; exact Hane).
  apply Un_cv_cscal_R.
  apply (CV_minus (fun _ => exp (- (a * A))) (fun k => exp (- (a * Tn k)))
           (exp (- (a * A))) 0);
    [ apply Un_cv_const
    | apply exp_neg_cv0, cv_infty_scal_pos; [ exact Ha | exact HTn ] ].
Qed.

(*  scaled exponential integral  int_A^{B0} Bc*e^{-a t} dt  *)
Lemma Bexp_cont : forall Bc a x, continuity_pt (fun t => Bc * exp (- (a * t))) x.
Proof.
  intros Bc a x; apply (continuity_pt_mult (fun _ => Bc) (fun t => exp (- (a * t))));
    [ apply continuity_pt_const; intros u v; reflexivity | apply exp_neg_scaled_cont ].
Qed.

Lemma exp_int_AB_scaled : forall Bc a A B0 (Ha : 0 < a) (Hab : A <= B0)
  (pr : Riemann_integrable (fun t => Bc * exp (- (a * t))) A B0),
  RiemannInt pr = Bc * (exp (- (a * A)) - exp (- (a * B0))) / a.
Proof.
  intros Bc a A B0 Ha Hab pr; assert (Hane : a <> 0) by (apply Rgt_not_eq; exact Ha).
  assert (Hanti : antiderivative (fun t => Bc * exp (- (a * t)))
                    (fun x => Bc * (- / a * exp (- (a * x)))) A B0).
  { split; [ | exact Hab ]; intros x _.
    exists (exist (fun l => derivable_pt_lim (fun t => Bc * (- / a * exp (- (a * t)))) x l)
              (Bc * exp (- (a * x)))
              (derivable_pt_lim_scal (fun t => - / a * exp (- (a * t))) Bc x
                 (exp (- (a * x))) (exp_scaled_deriv a x Hane))).
    unfold derive_pt; simpl; reflexivity. }
  rewrite (FTC_antideriv (fun t => Bc * exp (- (a * t)))
             (fun x => Bc * (- / a * exp (- (a * x)))) A B0 Hab
             (fun x _ => Bexp_cont Bc a x) pr Hanti).
  field; exact Hane.
Qed.

(* ----------------------------------------------------------------- *)
(*  Part 2:  the complex truncated Laplace transform + tail bound      *)
(* ----------------------------------------------------------------- *)

Section FullLaplace.
Variable f : R -> C.
Hypothesis Hfc : Ccont f.
Variable B : R.
Hypothesis Hfb : forall t, Cmod (f t) <= B.

Lemma B_nonneg : 0 <= B.
Proof. eapply Rle_trans; [ apply Cmod_nonneg | apply (Hfb 0) ]. Qed.

Definition lint (z : C) (t : R) : C := Cmul (f t) (cexpzt (Copp z) t).

Lemma lint_cont : forall z, Ccont (lint z).
Proof. intro z; apply Ccont_mul; [ exact Hfc | apply Ccont_cexpzt ]. Qed.

(*  the truncated Laplace transform  g_T(z) = int_0^T f(t) e^{-zt} dt  *)
Definition LT (z : C) (T : R) : C := Cintf (lint z) (lint_cont z) 0 T.

(*  the sharp inter-truncation tail bound  *)
Theorem LT_tail_bound : forall z T T', 0 < Re z -> 0 <= T -> T <= T' ->
  Cmod (Cminus (LT z T') (LT z T))
  <= 2 * (B * (exp (- (Re z * T)) - exp (- (Re z * T'))) / Re z).
Proof.
  intros z T T' Hx HT HTT'.
  assert (Hdiff : Cminus (LT z T') (LT z T) = Cintf (lint z) (lint_cont z) T T').
  { unfold LT; rewrite (Cintf_additive (lint z) (lint_cont z) 0 T T'); ring. }
  rewrite Hdiff.
  assert (Hcm : Riemann_integrable (fun u => Cmod (lint z u)) T T')
    by (apply continuity_implies_RiemannInt; [ lra | intros u _; apply Ccont_Cmod, lint_cont ]).
  assert (Hbexp : Riemann_integrable (fun t => B * exp (- (Re z * t))) T T')
    by (apply continuity_implies_RiemannInt; [ lra | intros u _; apply Bexp_cont ]).
  eapply Rle_trans; [ apply (Cintf_mod_le2 (lint z) (lint_cont z) T T' Hcm HTT') | ].
  apply Rmult_le_compat_l; [ lra | ].
  rewrite <- (exp_int_AB_scaled B (Re z) T T' Hx HTT' Hbexp).
  apply (RiemannInt_P19 Hcm Hbexp HTT'); intros u Hu.
  unfold lint; rewrite Cmod_mul, (Cmod_cexpzt (Copp z) u).
  replace (Re (Copp z) * u) with (- (Re z * u)) by (unfold Copp; cbn [Re]; ring).
  apply Rmult_le_compat_r; [ left; apply exp_pos | apply Hfb ].
Qed.

(*  the exponential right-half-plane tail estimate (Newman form)  *)
Corollary LT_tail_bound' : forall z T T', 0 < Re z -> 0 <= T -> T <= T' ->
  Cmod (Cminus (LT z T') (LT z T)) <= 2 * (B * exp (- (Re z * T)) / Re z).
Proof.
  intros z T T' Hx HT HTT'.
  eapply Rle_trans; [ apply LT_tail_bound; assumption | ].
  apply Rmult_le_compat_l; [ lra | ].
  unfold Rdiv; apply Rmult_le_compat_r; [ left; apply Rinv_0_lt_compat; exact Hx | ].
  apply Rmult_le_compat_l; [ apply B_nonneg | ].
  pose proof (exp_pos (- (Re z * T'))); lra.
Qed.

(* ----------------------------------------------------------------- *)
(*  Part 3:  the full transform  g(z) = lim_{T->oo} g_T(z)  (Re z>0)     *)
(* ----------------------------------------------------------------- *)

Lemma exp_le : forall a b, a <= b -> exp a <= exp b.
Proof.
  intros a b Hab; destruct (Rle_lt_or_eq_dec a b Hab) as [H|H];
    [ left; apply exp_increasing; exact H | subst; apply Rle_refl ].
Qed.

Lemma cv_infty_INR_loc : cv_infty (fun n => INR n).
Proof.
  intro M; destruct (INR_unbounded M) as [n0 Hn0]; exists n0; intros n Hn;
    eapply Rlt_le_trans; [ exact Hn0 | apply le_INR; exact Hn ].
Qed.

(*  the geometric-decay majorant of the truncation increments  *)
Definition tailmaj (z : C) (n : nat) : R := 2 * (B * exp (- (Re z * INR n)) / Re z).

Lemma tailmaj_nonneg : forall z n, 0 < Re z -> 0 <= tailmaj z n.
Proof.
  intros z n Hz; unfold tailmaj; apply Rmult_le_pos; [ lra | ].
  unfold Rdiv; apply Rmult_le_pos;
    [ apply Rmult_le_pos; [ apply B_nonneg | left; apply exp_pos ]
    | left; apply Rinv_0_lt_compat; exact Hz ].
Qed.

Lemma tailmaj_cv0 : forall z, 0 < Re z -> Un_cv (tailmaj z) 0.
Proof.
  intros z Hz; unfold tailmaj.
  replace 0 with (2 * B / Re z * 0) by ring.
  apply (Un_cv_ext (fun n => 2 * B / Re z * exp (- (Re z * INR n))));
    [ intro n; field; apply Rgt_not_eq; exact Hz | ].
  apply Un_cv_cscal_R, exp_neg_cv0, cv_infty_scal_pos; [ exact Hz | apply cv_infty_INR_loc ].
Qed.

Lemma tailmaj_dec : forall z m n, 0 < Re z -> (n <= m)%nat -> tailmaj z m <= tailmaj z n.
Proof.
  intros z m n Hz Hnm; unfold tailmaj; apply Rmult_le_compat_l; [ lra | ].
  unfold Rdiv; apply Rmult_le_compat_r; [ left; apply Rinv_0_lt_compat; exact Hz | ].
  apply Rmult_le_compat_l; [ apply B_nonneg | ].
  apply exp_le; apply Ropp_le_contravar, Rmult_le_compat_l;
    [ left; exact Hz | apply le_INR; exact Hnm ].
Qed.

Lemma Lseq_close_sym : forall z m n, 0 < Re z ->
  Cmod (Cminus (LT z (INR m)) (LT z (INR n))) <= tailmaj z (Nat.min m n).
Proof.
  intros z m n Hz; destruct (Nat.le_ge_cases n m) as [Hle | Hge].
  - rewrite (Nat.min_r m n Hle).
    apply (LT_tail_bound' z (INR n) (INR m) Hz (pos_INR n) (le_INR _ _ Hle)).
  - rewrite (Nat.min_l m n Hge).
    replace (Cminus (LT z (INR m)) (LT z (INR n)))
      with (Copp (Cminus (LT z (INR n)) (LT z (INR m)))) by ring.
    rewrite Cmod_opp.
    apply (LT_tail_bound' z (INR m) (INR n) Hz (pos_INR m) (le_INR _ _ Hge)).
Qed.

Lemma Lseq_Re_cauchy : forall z, 0 < Re z -> Cauchy_crit (fun n => Re (LT z (INR n))).
Proof.
  intros z Hz eps Heps; destruct (tailmaj_cv0 z Hz eps Heps) as [N HN].
  exists N; intros m n Hm Hn; unfold R_dist.
  apply Rle_lt_trans with (Cmod (Cminus (LT z (INR m)) (LT z (INR n)))).
  - replace (Re (LT z (INR m)) - Re (LT z (INR n)))
      with (Re (Cminus (LT z (INR m)) (LT z (INR n)))) by (unfold Cminus, Cadd, Copp; cbn; ring).
    apply Cmod_Re.
  - apply Rle_lt_trans with (tailmaj z (Nat.min m n)); [ apply Lseq_close_sym; exact Hz | ].
    apply Rle_lt_trans with (tailmaj z N);
      [ apply (tailmaj_dec z (Nat.min m n) N Hz); apply Nat.min_glb; assumption | ].
    pose proof (HN N (Nat.le_refl N)) as HNN; unfold R_dist in HNN;
      rewrite Rminus_0_r, Rabs_pos_eq in HNN by (apply tailmaj_nonneg; exact Hz); exact HNN.
Qed.

Lemma Lseq_Im_cauchy : forall z, 0 < Re z -> Cauchy_crit (fun n => Im (LT z (INR n))).
Proof.
  intros z Hz eps Heps; destruct (tailmaj_cv0 z Hz eps Heps) as [N HN].
  exists N; intros m n Hm Hn; unfold R_dist.
  apply Rle_lt_trans with (Cmod (Cminus (LT z (INR m)) (LT z (INR n)))).
  - replace (Im (LT z (INR m)) - Im (LT z (INR n)))
      with (Im (Cminus (LT z (INR m)) (LT z (INR n)))) by (unfold Cminus, Cadd, Copp; cbn; ring).
    apply Cmod_Im.
  - apply Rle_lt_trans with (tailmaj z (Nat.min m n)); [ apply Lseq_close_sym; exact Hz | ].
    apply Rle_lt_trans with (tailmaj z N);
      [ apply (tailmaj_dec z (Nat.min m n) N Hz); apply Nat.min_glb; assumption | ].
    pose proof (HN N (Nat.le_refl N)) as HNN; unfold R_dist in HNN;
      rewrite Rminus_0_r, Rabs_pos_eq in HNN by (apply tailmaj_nonneg; exact Hz); exact HNN.
Qed.

(*  the full Laplace transform, for Re z > 0  *)
Definition gfull (z : C) (Hz : 0 < Re z) : C :=
  mkC (proj1_sig (R_complete _ (Lseq_Re_cauchy z Hz)))
      (proj1_sig (R_complete _ (Lseq_Im_cauchy z Hz))).

Lemma gfull_cv : forall z (Hz : 0 < Re z), CUn_cv (fun n => LT z (INR n)) (gfull z Hz).
Proof.
  intros z Hz; apply CUn_cv_comp; split;
    [ exact (proj2_sig (R_complete _ (Lseq_Re_cauchy z Hz)))
    | exact (proj2_sig (R_complete _ (Lseq_Im_cauchy z Hz))) ].
Qed.

(*  the full right-half-plane tail bound  |g(z) - g_T(z)| <= 2 B e^{-(Re z)T}/(Re z)  *)
Theorem gfull_tail : forall z (Hz : 0 < Re z) T, 0 <= T ->
  Cmod (Cminus (gfull z Hz) (LT z T)) <= 2 * (B * exp (- (Re z * T)) / Re z).
Proof.
  intros z Hz T HT; destruct (INR_unbounded T) as [N0 HN0].
  apply Rle_cv_lim with
    (Un := fun k => Cmod (Cminus (LT z (INR (N0 + k))) (LT z T)))
    (Vn := fun _ => 2 * (B * exp (- (Re z * T)) / Re z)).
  - intro k; apply LT_tail_bound'; [ exact Hz | exact HT | ].
    apply Rle_trans with (INR N0); [ left; exact HN0 | apply le_INR; lia ].
  - intros eps Heps; destruct (gfull_cv z Hz eps Heps) as [N1 HN1].
    exists N1; intros k Hk; unfold R_dist.
    eapply Rle_lt_trans; [ apply Cmod_diff_le | ].
    replace (Cminus (Cminus (LT z (INR (N0 + k))) (LT z T)) (Cminus (gfull z Hz) (LT z T)))
      with (Cminus (LT z (INR (N0 + k))) (gfull z Hz)) by ring.
    apply HN1; lia.
  - apply Un_cv_const.
Qed.

End FullLaplace.

Print Assumptions LT_tail_bound'.
Print Assumptions gfull_tail.

(* ================================================================= *)
(*  Parts 1-3 complete: exp-tail core, the sharp truncation tail bound,   *)
(*  and the full transform g(z) = lim g_T(z) (Re z>0) with                *)
(*  |g(z) - g_T(z)| <= 2 B e^{-(Re z) T}/(Re z).  This is the concrete F   *)
(*  fed to the Newman contour argument.  Next: LaplacePhi (identify g      *)
(*  with Phi(z+1)/(z+1) - 1/z and holomorphy at 0).                       *)
(* ================================================================= *)
