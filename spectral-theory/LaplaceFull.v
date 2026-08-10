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
Require Import ComplexField Cmodulus CIntegral2 CSegInt CExpKernel ContinuousCoV
        PerronBound PerronEdge.
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

End FullLaplace.

Print Assumptions LT_tail_bound.
Print Assumptions LT_tail_bound'.

(* ================================================================= *)
(*  Parts 1-2 complete: exp-tail core + the sharp truncation tail bound  *)
(*  |g_{T'}(z) - g_T(z)| <= 2 B e^{-(Re z) T}/(Re z).  Next stage: the    *)
(*  full transform g(z) as the (Cauchy) limit of g_T, and |g - g_T|.      *)
(* ================================================================= *)
