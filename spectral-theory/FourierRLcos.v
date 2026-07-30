(* ================================================================= *)
(*  FourierRLcos.v  —  the RIEMANN–LEBESGUE lemma, COSINE half (C¹).  *)
(*                                                                    *)
(*  The companion of FourierRL.RL_cv, and the second prerequisite of  *)
(*  Fourier F3 (pointwise convergence).  For a `C1_fun` g:            *)
(*                                                                    *)
(*     RL_cos_cv : Un_cv (fun n => ∫_a^b g(t)·cos((n+½)t) dt) 0.       *)
(*                                                                    *)
(*  WHY the cosine half is needed.  The localisation of S_N f(x)−f(x)  *)
(*  produces the Dirichlet kernel in the form sin((N+½)(x−y)); as a    *)
(*  function of the integration variable y (with (N+½)x a constant),  *)
(*      sin((N+½)(x−y)) = sin((N+½)x)·cos((N+½)y)                     *)
(*                        − cos((N+½)x)·sin((N+½)y),                   *)
(*  so BOTH ∫ g·cos((N+½)y) and ∫ g·sin((N+½)y) must vanish.  RL_cv    *)
(*  gives only the sine integral; this file gives the cosine one.     *)
(*                                                                    *)
(*  Proof: the same C¹ integration by parts, with the antiderivative  *)
(*  H(t) = g(t)·sin(λt)/λ (so H'(t) = g(t)cos(λt) + g'(t)sin(λt)/λ):   *)
(*      |∫ g·cos(λt)| ≤ (|g(a)|+|g(b)|+∫|g'|)/|λ|   (`RL_bound_c`),    *)
(*  whence RL_cos_cv since the RHS → 0 as λ = n+½ → ∞.                 *)
(*                                                                    *)
(*  Reuses FourierRL's trig-derivative / continuity scaffolding.      *)
(*  Over the classical `Reals` (quarantined).                        *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia. Local Open Scope R_scope.
Require Import FourierRL.

(* d/dt sin(lam·t) = cos(lam·t)·lam  (companion of FourierRL.cos_lam_deriv) *)
Lemma sin_lam_deriv : forall lam t, derivable_pt_lim (fun x => sin (lam * x)) t (cos (lam * t) * lam).
Proof.
  intros lam t.
  apply (derivable_pt_lim_comp (fun x => lam * x) sin t lam (cos (lam * t))).
  - apply lam_mult_deriv.
  - apply derivable_pt_lim_sin.
Qed.

(* H(t) = (1/lam)·g(t)·sin(lam·t) has derivative g(t)cos(lam·t) + (1/lam)g'(t)sin(lam·t) *)
Lemma H_deriv_c : forall (g : C1_fun) (lam : R) t, lam <> 0 ->
  derivable_pt_lim (fun x => / lam * (c1 g x * sin (lam * x))) t
    (c1 g t * cos (lam * t) + / lam * (derive (c1 g) (diff0 g) t * sin (lam * t))).
Proof.
  intros g lam t Hlam.
  assert (Hg : derivable_pt_lim (c1 g) t (derive (c1 g) (diff0 g) t))
    by (unfold derive, derive_pt; exact (proj2_sig (diff0 g t))).
  set (gd := derive (c1 g) (diff0 g) t) in *.
  replace (c1 g t * cos (lam * t) + / lam * (gd * sin (lam * t)))
    with (/ lam * (gd * sin (lam * t) + c1 g t * (cos (lam * t) * lam))) by (field; exact Hlam).
  apply derivable_pt_lim_scal.
  apply (derivable_pt_lim_mult (c1 g) (fun x => sin (lam * x)) t gd (cos (lam * t) * lam)).
  - exact Hg.
  - apply sin_lam_deriv.
Qed.

Lemma Hval_cont_c : forall (g : C1_fun) (lam : R),
  continuity (fun t => c1 g t * cos (lam * t) + / lam * (derive (c1 g) (diff0 g) t * sin (lam * t))).
Proof.
  intros g lam x. apply continuity_pt_plus.
  - apply continuity_pt_mult; [ apply derivable_continuous_pt, (diff0 g) | apply cos_lam_cont ].
  - apply continuity_pt_scal, continuity_pt_mult; [ apply (cont1 g) | apply sin_lam_cont ].
Qed.

Definition Hc1_c (g : C1_fun) (lam : R) (Hlam : lam <> 0) : C1_fun :=
  mkC1 (c1 := fun t => / lam * (c1 g t * sin (lam * t)))
       (diff0 := fun t => exist _ _ (H_deriv_c g lam t Hlam))
       (Hval_cont_c g lam).

(* integration-by-parts identity *)
Lemma RL_ibp_c : forall (g : C1_fun) (lam a b : R) (Hlam : lam <> 0)
  (pr : Riemann_integrable
          (fun t => c1 g t * cos (lam * t) + / lam * (derive (c1 g) (diff0 g) t * sin (lam * t))) a b),
  RiemannInt pr = / lam * (c1 g b * sin (lam * b)) - / lam * (c1 g a * sin (lam * a)).
Proof. intros g lam a b Hlam pr; exact (FTC_Riemann (Hc1_c g lam Hlam) pr). Qed.

(* integrability helpers *)
Lemma ri_gdsin : forall (g : C1_fun) (lam a b : R), a <= b ->
  Riemann_integrable (fun t => derive (c1 g) (diff0 g) t * sin (lam * t)) a b.
Proof. intros g lam a b Hab; apply continuity_implies_RiemannInt; [ exact Hab | intros x _; apply continuity_pt_mult; [ apply (cont1 g) | apply sin_lam_cont ] ]. Qed.
Lemma ri_gcos : forall (g : C1_fun) (lam a b : R), a <= b ->
  Riemann_integrable (fun t => c1 g t * cos (lam * t)) a b.
Proof. intros g lam a b Hab; apply continuity_implies_RiemannInt; [ exact Hab | intros x _; apply continuity_pt_mult; [ apply derivable_continuous_pt, (diff0 g) | apply cos_lam_cont ] ]. Qed.
Lemma ri_Hbody_c : forall (g : C1_fun) (lam a b : R), a <= b ->
  Riemann_integrable (fun t => c1 g t * cos (lam * t) + / lam * (derive (c1 g) (diff0 g) t * sin (lam * t))) a b.
Proof. intros g lam a b Hab; apply continuity_implies_RiemannInt; [ exact Hab | intros x _; apply (Hval_cont_c g lam) ]. Qed.
Lemma ri_absgdsin : forall (g : C1_fun) (lam a b : R), a <= b ->
  Riemann_integrable (fun t => Rabs (derive (c1 g) (diff0 g) t * sin (lam * t))) a b.
Proof. intros g lam a b Hab; apply continuity_implies_RiemannInt; [ exact Hab | intros x _;
  apply (continuity_pt_comp (fun t => derive (c1 g) (diff0 g) t * sin (lam * t)) Rabs x);
    [ apply continuity_pt_mult; [ apply (cont1 g) | apply sin_lam_cont ] | apply Rcontinuity_abs ] ]. Qed.

Lemma Hbody_bound_c : forall (g : C1_fun) (lam x : R), lam <> 0 ->
  Rabs (/ lam * (c1 g x * sin (lam * x))) <= Rabs (c1 g x) / Rabs lam.
Proof.
  intros g lam x Hlam.
  rewrite Rabs_mult, Rabs_inv by exact Hlam. rewrite Rabs_mult.
  unfold Rdiv; rewrite (Rmult_comm (Rabs (c1 g x)) (/ Rabs lam)).
  apply Rmult_le_compat_l; [ apply Rlt_le, Rinv_0_lt_compat, Rabs_pos_lt; exact Hlam | ].
  rewrite <- (Rmult_1_r (Rabs (c1 g x))) at 2. apply Rmult_le_compat_l; [ apply Rabs_pos | ].
  apply Rabs_le; pose proof (SIN_bound (lam * x)); lra.
Qed.

Lemma RL_bound_c : forall (g : C1_fun) (lam a b : R), lam <> 0 -> a <= b ->
  forall (pr : Riemann_integrable (fun t => c1 g t * cos (lam * t)) a b)
         (prd : Riemann_integrable (fun t => Rabs (derive (c1 g) (diff0 g) t)) a b),
  Rabs (RiemannInt pr) <= (Rabs (c1 g a) + Rabs (c1 g b) + RiemannInt prd) / Rabs lam.
Proof.
  intros g lam a b Hlam Hab pr prd.
  assert (Hla : 0 < Rabs lam) by (apply Rabs_pos_lt; exact Hlam).
  assert (Hla' : Rabs lam <> 0) by (apply Rgt_not_eq; exact Hla).
  pose (prgs := ri_gdsin g lam a b Hab).
  pose (prH := ri_Hbody_c g lam a b Hab).
  pose (prabs := ri_absgdsin g lam a b Hab).
  (* linearity: ∫Hbody = ∫(g cos) + (/lam) ∫(g' sin) *)
  pose proof (RiemannInt_P13 pr prgs prH) as HP13.
  (* IBP: ∫Hbody = Hbody b − Hbody a *)
  pose proof (RL_ibp_c g lam a b Hlam prH) as Hibp.
  (* so ∫(g cos) = (Hbody b − Hbody a) − (/lam) ∫(g' sin) *)
  assert (Hval_eq : RiemannInt pr
    = (/ lam * (c1 g b * sin (lam * b)) - / lam * (c1 g a * sin (lam * a))) - / lam * RiemannInt prgs)
    by (rewrite <- Hibp, HP13; ring).
  rewrite Hval_eq.
  eapply Rle_trans; [ apply Rabs_triang | ].
  apply Rle_trans with ((Rabs (c1 g a) + Rabs (c1 g b)) / Rabs lam + / Rabs lam * RiemannInt prd).
  2:{ apply Req_le; field; exact Hla'. }
  apply Rplus_le_compat.
  - (* |Hbody b − Hbody a| <= (|g a| + |g b|)/|lam| *)
    replace (/ lam * (c1 g b * sin (lam * b)) - / lam * (c1 g a * sin (lam * a)))
      with ((/ lam * (c1 g b * sin (lam * b))) + (- (/ lam * (c1 g a * sin (lam * a))))) by ring.
    eapply Rle_trans; [ apply Rabs_triang | ]. rewrite Rabs_Ropp.
    replace ((Rabs (c1 g a) + Rabs (c1 g b)) / Rabs lam)
      with (Rabs (c1 g b) / Rabs lam + Rabs (c1 g a) / Rabs lam) by (field; exact Hla').
    apply Rplus_le_compat; apply Hbody_bound_c; exact Hlam.
  - (* |(/lam) ∫(g' sin)| <= (/|lam|) ∫|g'| *)
    rewrite Rabs_Ropp, Rabs_mult, Rabs_inv by exact Hlam.
    apply Rmult_le_compat_l; [ apply Rlt_le, Rinv_0_lt_compat; exact Hla | ].
    eapply Rle_trans; [ apply (RiemannInt_P17 prgs prabs Hab) | ].
    apply (RiemannInt_P19 prabs prd Hab).
    intros x _; rewrite Rabs_mult; rewrite <- (Rmult_1_r (Rabs (derive (c1 g) (diff0 g) x))) at 2.
    apply Rmult_le_compat_l; [ apply Rabs_pos | apply Rabs_le; pose proof (SIN_bound (lam * x)); lra ].
Qed.

(* RIEMANN–LEBESGUE (C¹, cosine): ∫_a^b g(t) cos((n+1/2) t) dt -> 0 *)
Theorem RL_cos_cv : forall (g : C1_fun) (a b : R) (Hab : a <= b)
  (prd : Riemann_integrable (fun t => Rabs (derive (c1 g) (diff0 g) t)) a b),
  Un_cv (fun n => RiemannInt (ri_gcos g (INR n + / 2) a b Hab)) 0.
Proof.
  intros g a b Hab prd eps Heps.
  set (C := Rabs (c1 g a) + Rabs (c1 g b) + RiemannInt prd).
  destruct (INR_unbounded (C / eps)) as [N HN].
  exists N; intros n Hn.
  assert (Hln : 0 < INR n + / 2) by (pose proof (pos_INR n); lra).
  unfold R_dist; rewrite Rminus_0_r.
  eapply Rle_lt_trans; [ apply (RL_bound_c g (INR n + / 2) a b ltac:(lra) Hab (ri_gcos g (INR n + / 2) a b Hab) prd) | ].
  fold C. rewrite (Rabs_right (INR n + / 2)) by lra.
  assert (Hkey : C / eps < INR n + / 2)
    by (apply Rlt_le_trans with (INR N); [ exact HN | pose proof (le_INR N n Hn); lra ]).
  pose proof (Rmult_lt_compat_r eps (C / eps) (INR n + / 2) Heps Hkey) as Hk2.
  replace (C / eps * eps) with C in Hk2 by (field; lra).
  apply Rmult_lt_reg_r with (INR n + / 2); [ exact Hln | ].
  unfold Rdiv; rewrite Rmult_assoc, Rinv_l, Rmult_1_r by lra. lra.
Qed.

Print Assumptions RL_cos_cv.

(* ================================================================= *)
(*  END FourierRLcos.v.  Riemann–Lebesgue (C¹, cosine):              *)
(*  ∫ g·cos((n+½)t) → 0.  With FourierRL.RL_cv (the sine half) this    *)
(*  closes the oscillatory-decay input to Fourier F3 localisation.    *)
(* ================================================================= *)
