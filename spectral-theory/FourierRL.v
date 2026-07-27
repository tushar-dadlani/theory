(* ================================================================= *)
(*  FourierRL.v  —  the RIEMANN–LEBESGUE lemma (C¹ form).            *)
(*                                                                    *)
(*  Milestone F1 of Fourier-series pointwise convergence (the route   *)
(*  toward Poisson summation → the ζ functional equation):            *)
(*                                                                    *)
(*     RL_cv : Un_cv (fun n => ∫_a^b g(t)·sin((n+½)t) dt) 0           *)
(*                                                                    *)
(*  for a `C1_fun` g.  Proved by integration by parts realized        *)
(*  through the recursive... no — through stdlib's FTC: H(t) =        *)
(*  −g(t)cos(λt)/λ is bundled as a `C1_fun` (`Hc1`) with derivative   *)
(*  `H' = g·sin(λ·) − g'·cos(λ·)/λ` (`H_deriv`, `Hval_cont`), so       *)
(*  `FTC_Riemann` gives the IBP identity (`RL_ibp`), and linearity /   *)
(*  the |∫f|≤∫|f| bound (`RiemannInt_P13/P17/P18/P19`) give           *)
(*     |∫ g·sin(λt)| ≤ (|g(a)|+|g(b)|+∫|g'|)/|λ|   (`RL_bound`),       *)
(*  whence RL_cv since the RHS → 0.                                   *)
(*                                                                    *)
(*  NOTE (stdlib friction): this leaned hard on stdlib `RiemannInt`   *)
(*  (C1_fun/`derive` bookkeeping, implicit-arg plumbing) — the "easy"  *)
(*  half of Fourier convergence.  F2 (the kernel representation,      *)
(*  needing change-of-variables / periodicity that stdlib RiemannInt  *)
(*  lacks cleanly) is the flagged high-risk step.                    *)
(*  Over the classical `Reals` (quarantined).                        *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia. Local Open Scope R_scope.

Lemma lam_mult_deriv : forall lam t, derivable_pt_lim (fun x => lam * x) t lam.
Proof.
  intros lam t.
  pose proof (derivable_pt_lim_scal (fun x => x) lam t 1 (derivable_pt_lim_id t)) as H.
  replace (lam * 1) with lam in H by ring. exact H.
Qed.
Lemma cos_lam_deriv : forall lam t, derivable_pt_lim (fun x => cos (lam * x)) t (- sin (lam * t) * lam).
Proof.
  intros lam t.
  apply (derivable_pt_lim_comp (fun x => lam * x) cos t lam (- sin (lam * t))).
  - apply lam_mult_deriv.
  - apply derivable_pt_lim_cos.
Qed.

Lemma H_deriv : forall (g : C1_fun) (lam : R) t, lam <> 0 ->
  derivable_pt_lim (fun x => - / lam * (c1 g x * cos (lam * x))) t
    (c1 g t * sin (lam * t) - / lam * (derive (c1 g) (diff0 g) t * cos (lam * t))).
Proof.
  intros g lam t Hlam.
  assert (Hg : derivable_pt_lim (c1 g) t (derive (c1 g) (diff0 g) t))
    by (unfold derive, derive_pt; exact (proj2_sig (diff0 g t))).
  set (gd := derive (c1 g) (diff0 g) t) in *.
  replace (c1 g t * sin (lam * t) - / lam * (gd * cos (lam * t)))
    with (- / lam * (gd * cos (lam * t) + c1 g t * (- sin (lam * t) * lam))) by (field; exact Hlam).
  apply derivable_pt_lim_scal.
  apply (derivable_pt_lim_mult (c1 g) (fun x => cos (lam * x)) t gd (- sin (lam * t) * lam)).
  - exact Hg.
  - apply cos_lam_deriv.
Qed.

Lemma lam_mult_cont : forall lam, continuity (fun t => lam * t).
Proof. intros lam x; apply derivable_continuous_pt; exists lam; apply lam_mult_deriv. Qed.
Lemma sin_lam_cont : forall lam, continuity (fun t => sin (lam * t)).
Proof. intros lam x; apply (continuity_pt_comp (fun t => lam * t) sin x); [ apply lam_mult_cont | apply continuity_sin ]. Qed.
Lemma cos_lam_cont : forall lam, continuity (fun t => cos (lam * t)).
Proof. intros lam x; apply (continuity_pt_comp (fun t => lam * t) cos x); [ apply lam_mult_cont | apply continuity_cos ]. Qed.

Lemma Hval_cont : forall (g : C1_fun) (lam : R),
  continuity (fun t => c1 g t * sin (lam * t) - / lam * (derive (c1 g) (diff0 g) t * cos (lam * t))).
Proof.
  intros g lam x. apply continuity_pt_minus.
  - apply continuity_pt_mult; [ apply derivable_continuous_pt, (diff0 g) | apply sin_lam_cont ].
  - apply continuity_pt_scal, continuity_pt_mult; [ apply (cont1 g) | apply cos_lam_cont ].
Qed.

Definition Hc1 (g : C1_fun) (lam : R) (Hlam : lam <> 0) : C1_fun :=
  mkC1 (c1 := fun t => - / lam * (c1 g t * cos (lam * t)))
       (diff0 := fun t => exist _ _ (H_deriv g lam t Hlam))
       (Hval_cont g lam).

(* integration-by-parts identity *)
Lemma RL_ibp : forall (g : C1_fun) (lam a b : R) (Hlam : lam <> 0)
  (pr : Riemann_integrable
          (fun t => c1 g t * sin (lam * t) - / lam * (derive (c1 g) (diff0 g) t * cos (lam * t))) a b),
  RiemannInt pr = - / lam * (c1 g b * cos (lam * b)) - - / lam * (c1 g a * cos (lam * a)).
Proof. intros g lam a b Hlam pr; exact (FTC_Riemann (Hc1 g lam Hlam) pr). Qed.

(* integrability helpers *)
Lemma ri_gdcos : forall (g : C1_fun) (lam a b : R), a <= b ->
  Riemann_integrable (fun t => derive (c1 g) (diff0 g) t * cos (lam * t)) a b.
Proof. intros g lam a b Hab; apply continuity_implies_RiemannInt; [ exact Hab | intros x _; apply continuity_pt_mult; [ apply (cont1 g) | apply cos_lam_cont ] ]. Qed.
Lemma ri_Hplus : forall (g : C1_fun) (lam a b : R), a <= b ->
  Riemann_integrable (fun x => c1 g x * sin (lam * x) + (- / lam) * (derive (c1 g) (diff0 g) x * cos (lam * x))) a b.
Proof. intros g lam a b Hab; apply continuity_implies_RiemannInt; [ exact Hab | intros x _;
  apply continuity_pt_plus; [ apply continuity_pt_mult; [ apply derivable_continuous_pt, (diff0 g) | apply sin_lam_cont ]
                            | apply continuity_pt_scal, continuity_pt_mult; [ apply (cont1 g) | apply cos_lam_cont ] ] ]. Qed.
Lemma ri_Hminus : forall (g : C1_fun) (lam a b : R), a <= b ->
  Riemann_integrable (fun t => c1 g t * sin (lam * t) - / lam * (derive (c1 g) (diff0 g) t * cos (lam * t))) a b.
Proof. intros g lam a b Hab; apply continuity_implies_RiemannInt; [ exact Hab | intros x _; apply (Hval_cont g lam) ]. Qed.
Lemma ri_absgdcos : forall (g : C1_fun) (lam a b : R), a <= b ->
  Riemann_integrable (fun t => Rabs (derive (c1 g) (diff0 g) t * cos (lam * t))) a b.
Proof. intros g lam a b Hab; apply continuity_implies_RiemannInt; [ exact Hab | intros x _;
  apply (continuity_pt_comp (fun t => derive (c1 g) (diff0 g) t * cos (lam * t)) Rabs x);
    [ apply continuity_pt_mult; [ apply (cont1 g) | apply cos_lam_cont ] | apply Rcontinuity_abs ] ]. Qed.

Lemma Hbody_bound : forall (g : C1_fun) (lam x : R), lam <> 0 ->
  Rabs (- / lam * (c1 g x * cos (lam * x))) <= Rabs (c1 g x) / Rabs lam.
Proof.
  intros g lam x Hlam.
  rewrite Rabs_mult, Rabs_Ropp, Rabs_inv by exact Hlam. rewrite Rabs_mult.
  unfold Rdiv; rewrite (Rmult_comm (Rabs (c1 g x)) (/ Rabs lam)).
  apply Rmult_le_compat_l; [ apply Rlt_le, Rinv_0_lt_compat, Rabs_pos_lt; exact Hlam | ].
  rewrite <- (Rmult_1_r (Rabs (c1 g x))) at 2. apply Rmult_le_compat_l; [ apply Rabs_pos | ].
  apply Rabs_le; pose proof (COS_bound (lam * x)); lra.
Qed.

Lemma RL_bound : forall (g : C1_fun) (lam a b : R), lam <> 0 -> a <= b ->
  forall (pr : Riemann_integrable (fun t => c1 g t * sin (lam * t)) a b)
         (prd : Riemann_integrable (fun t => Rabs (derive (c1 g) (diff0 g) t)) a b),
  Rabs (RiemannInt pr) <= (Rabs (c1 g a) + Rabs (c1 g b) + RiemannInt prd) / Rabs lam.
Proof.
  intros g lam a b Hlam Hab pr prd.
  assert (Hla : 0 < Rabs lam) by (apply Rabs_pos_lt; exact Hlam).
  assert (Hla' : Rabs lam <> 0) by (apply Rgt_not_eq; exact Hla).
  pose (prgd := ri_gdcos g lam a b Hab).
  pose (prHm := ri_Hminus g lam a b Hab).
  pose (prHp := ri_Hplus g lam a b Hab).
  pose (prabs := ri_absgdcos g lam a b Hab).
  (* linearity: ∫Hplus = ∫(g sin) + (-/lam) ∫(gd cos) *)
  pose proof (RiemannInt_P13 pr prgd prHp) as HP13.
  (* bridge ∫Hplus = ∫Hminus = Hbody b - Hbody a *)
  assert (Hbr : RiemannInt prHp = RiemannInt prHm)
    by (apply RiemannInt_P18; [ exact Hab | intros x _; field; exact Hlam ]).
  rewrite (RL_ibp g lam a b Hlam prHm) in Hbr.
  (* so ∫(g sin) = (Hbody b - Hbody a) + (/lam) ∫(gd cos) *)
  pose proof (eq_trans (eq_sym Hbr) HP13) as Ht.
  assert (Hval_eq : RiemannInt pr
    = (- / lam * (c1 g b * cos (lam * b)) - - / lam * (c1 g a * cos (lam * a))) + / lam * RiemannInt prgd)
    by (rewrite Ht; ring).
  rewrite Hval_eq.
  eapply Rle_trans; [ apply Rabs_triang | ].
  apply Rle_trans with ((Rabs (c1 g a) + Rabs (c1 g b)) / Rabs lam + / Rabs lam * RiemannInt prd).
  2:{ apply Req_le; field; exact Hla'. }
  apply Rplus_le_compat.
  - (* |Hbody b - Hbody a| <= (|g a| + |g b|)/|lam| *)
    replace (- / lam * (c1 g b * cos (lam * b)) - - / lam * (c1 g a * cos (lam * a)))
      with ((- / lam * (c1 g b * cos (lam * b))) + (- (- / lam * (c1 g a * cos (lam * a))))) by ring.
    eapply Rle_trans; [ apply Rabs_triang | ]. rewrite Rabs_Ropp.
    replace ((Rabs (c1 g a) + Rabs (c1 g b)) / Rabs lam)
      with (Rabs (c1 g b) / Rabs lam + Rabs (c1 g a) / Rabs lam) by (field; exact Hla').
    apply Rplus_le_compat; apply Hbody_bound; exact Hlam.
  - (* |(/lam) ∫(gd cos)| <= (/|lam|) ∫|gd| *)
    rewrite Rabs_mult, Rabs_inv by exact Hlam.
    apply Rmult_le_compat_l; [ apply Rlt_le, Rinv_0_lt_compat; exact Hla | ].
    eapply Rle_trans; [ apply (RiemannInt_P17 prgd prabs Hab) | ].
    apply (RiemannInt_P19 prabs prd Hab).
    intros x _; rewrite Rabs_mult; rewrite <- (Rmult_1_r (Rabs (derive (c1 g) (diff0 g) x))) at 2.
    apply Rmult_le_compat_l; [ apply Rabs_pos | apply Rabs_le; pose proof (COS_bound (lam * x)); lra ].
Qed.

Lemma ri_gsin : forall (g : C1_fun) (lam a b : R), a <= b ->
  Riemann_integrable (fun t => c1 g t * sin (lam * t)) a b.
Proof. intros g lam a b Hab; apply continuity_implies_RiemannInt; [ exact Hab | intros x _; apply continuity_pt_mult; [ apply derivable_continuous_pt, (diff0 g) | apply sin_lam_cont ] ]. Qed.

(* RIEMANN–LEBESGUE (C^1 form): ∫_a^b g(t) sin((n+1/2) t) dt -> 0 *)
Theorem RL_cv : forall (g : C1_fun) (a b : R) (Hab : a <= b)
  (prd : Riemann_integrable (fun t => Rabs (derive (c1 g) (diff0 g) t)) a b),
  Un_cv (fun n => RiemannInt (ri_gsin g (INR n + / 2) a b Hab)) 0.
Proof.
  intros g a b Hab prd eps Heps.
  set (C := Rabs (c1 g a) + Rabs (c1 g b) + RiemannInt prd).
  destruct (INR_unbounded (C / eps)) as [N HN].
  exists N; intros n Hn.
  assert (Hln : 0 < INR n + / 2) by (pose proof (pos_INR n); lra).
  unfold R_dist; rewrite Rminus_0_r.
  eapply Rle_lt_trans; [ apply (RL_bound g (INR n + / 2) a b ltac:(lra) Hab (ri_gsin g (INR n + / 2) a b Hab) prd) | ].
  fold C. rewrite (Rabs_right (INR n + / 2)) by lra.
  assert (Hkey : C / eps < INR n + / 2)
    by (apply Rlt_le_trans with (INR N); [ exact HN | pose proof (le_INR N n Hn); lra ]).
  pose proof (Rmult_lt_compat_r eps (C / eps) (INR n + / 2) Heps Hkey) as Hk2.
  replace (C / eps * eps) with C in Hk2 by (field; lra).
  apply Rmult_lt_reg_r with (INR n + / 2); [ exact Hln | ].
  unfold Rdiv; rewrite Rmult_assoc, Rinv_l, Rmult_1_r by lra. lra.
Qed.

Print Assumptions RL_cv.

(* ================================================================= *)
(*  END FourierRL.v.  Riemann–Lebesgue (C¹): ∫ g·sin((n+½)t) → 0.     *)
(* ================================================================= *)
