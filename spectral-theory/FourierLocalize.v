(* ================================================================= *)
(*  FourierLocalize.v  —  Fourier F3, step 2: the LOCALISATION        *)
(*  identity (the difference kernel).                                 *)
(*                                                                    *)
(*  For any continuous f, the Fourier partial sum minus the value:    *)
(*                                                                    *)
(*     S_N f(x) − f(x) = (1/2π) ∫_{-π}^{π} (f(y) − f(x)) D_N(x−y) dy.  *)
(*                                                                    *)
(*  This is the object F3 (pointwise convergence) actually studies:    *)
(*  its integrand is (f(y)−f(x))·D_N(x−y), which the removable         *)
(*  singularity step will factor as [(f(y)−f(x))/2 sin((x−y)/2)] ·     *)
(*  sin((N+½)(x−y)) and hand to Riemann–Lebesgue (RL_cv / RL_cos_cv).  *)
(*                                                                    *)
(*  Crux — the kernel NORMALISATION  ∫_{-π}^{π} D_N(x−y) dy = 2π       *)
(*  (kernel_shift_integral).  Rather than change of variables +        *)
(*  periodicity (which stdlib RiemannInt lacks cleanly), we integrate  *)
(*  D_N(x−y) mode by mode, exactly as DirichletIntegral does for       *)
(*  D_N(y): every non-constant mode has zero mean,                    *)
(*     ∫ cos(k(x−y)) dy = cos kx·∫cos ky + sin kx·∫sin ky = 0,         *)
(*  from cos_int_0 (reused) and its new sine companion sin_int_0       *)
(*  (∫_{-π}^{π} sin(ky) dy = 0, FTC with antiderivative −cos(ky)/k).   *)
(*                                                                    *)
(*  The identity itself then follows by linearity from the F2 kernel   *)
(*  representation (FourierKernelRep.kernel_representation).           *)
(*  No new axioms (classical Reals only).                            *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import FourierRL DirichletKernel DirichletIntegral FourierPartialSum FourierKernelRep.
Open Scope R_scope.

(* integrability of continuous integrands on [-π,π] *)
Lemma RIc : forall g, continuity g -> Riemann_integrable g (- PI) PI.
Proof.
  intros g Cg; apply continuity_implies_RiemannInt;
    [ pose proof PI_RGT_0; lra | intros x _; apply Cg ].
Qed.

(* ----------------------------------------------------------------- *)
(*  The sine companion of DirichletIntegral.cos_int_0.               *)
(* ----------------------------------------------------------------- *)

(* the antiderivative −(1/k)·cos(k·t) has derivative sin(k·t) *)
Lemma sinprim_deriv : forall k t, INR k <> 0 ->
  derivable_pt_lim (fun x => - / INR k * cos (INR k * x)) t (sin (INR k * t)).
Proof.
  intros k t Hk.
  pose proof (derivable_pt_lim_scal (fun x => cos (INR k * x)) (- / INR k) t
                (- sin (INR k * t) * INR k) (cos_lam_deriv (INR k) t)) as H.
  replace (- / INR k * (- sin (INR k * t) * INR k)) with (sin (INR k * t)) in H
    by (field; exact Hk).
  exact H.
Qed.

Definition sinprim (k : nat) (Hk : INR k <> 0) : C1_fun :=
  mkC1 (c1 := fun t => - / INR k * cos (INR k * t))
       (diff0 := fun t => exist _ _ (sinprim_deriv k t Hk))
       (sin_lam_cont (INR k)).

Lemma sinprim_val : forall k (Hk : INR k <> 0) t,
  sinprim k Hk t = - / INR k * cos (INR k * t).
Proof. reflexivity. Qed.

(* ∫_{-π}^{π} sin(k t) dt = 0 for k ≥ 1 (the odd modes have zero mean) *)
Lemma sin_int_0 : forall k (Hk : INR k <> 0)
  (pr : Riemann_integrable (fun t => sin (INR k * t)) (- PI) PI),
  RiemannInt pr = 0.
Proof.
  intros k Hk pr.
  pose proof (FTC_Riemann (sinprim k Hk) pr) as FTC.
  assert (Hval : sinprim k Hk PI - sinprim k Hk (- PI) = 0).
  { rewrite !sinprim_val.
    replace (INR k * - PI) with (- (INR k * PI)) by ring.
    rewrite cos_neg; ring. }
  rewrite Hval in FTC; exact FTC.
Qed.

Lemma sin_RI : forall k, Riemann_integrable (fun t => sin (INR k * t)) (- PI) PI.
Proof.
  intro k; apply continuity_implies_RiemannInt;
    [ pose proof PI_RGT_0; lra | intros x _; apply sin_lam_cont ].
Qed.

(* ----------------------------------------------------------------- *)
(*  Continuity / integrability of the shifted kernel.                *)
(* ----------------------------------------------------------------- *)

Lemma cont_sub : forall x, continuity (fun y => x - y).
Proof.
  intros x y; apply continuity_pt_minus.
  - apply continuity_pt_const; intros a b; reflexivity.
  - apply derivable_continuous_pt; exists 1; apply derivable_pt_lim_id.
Qed.

Lemma cont_coskxy : forall k x, continuity (fun y => cos (INR k * (x - y))).
Proof.
  intros k x y.
  apply (continuity_pt_comp (fun y => INR k * (x - y)) cos y).
  - apply (continuity_pt_scal (fun y => x - y) (INR k) y); apply cont_sub.
  - apply continuity_cos.
Qed.

Lemma cont_Dshift : forall N x, continuity (fun y => Dsum N (x - y)).
Proof.
  intros N x y; apply (continuity_pt_comp (fun y => x - y) (Dsum N) y);
    [ apply cont_sub | apply Dsum_cont ].
Qed.

Lemma cont_ccos : forall k x, continuity (fun y => cos (INR k * x) * cos (INR k * y)).
Proof.
  intros k x y; apply (continuity_pt_scal (fun y => cos (INR k * y)) (cos (INR k * x)) y);
    apply cos_lam_cont.
Qed.

Lemma cont_ssin : forall k x, continuity (fun y => sin (INR k * x) * sin (INR k * y)).
Proof.
  intros k x y; apply (continuity_pt_scal (fun y => sin (INR k * y)) (sin (INR k * x)) y);
    apply sin_lam_cont.
Qed.

Definition ri_coskxy (k : nat) (x : R)
  : Riemann_integrable (fun y => cos (INR k * (x - y))) (- PI) PI
  := RIc _ (cont_coskxy k x).
Definition ri_Dshift (N : nat) (x : R)
  : Riemann_integrable (fun y => Dsum N (x - y)) (- PI) PI
  := RIc _ (cont_Dshift N x).

(* ----------------------------------------------------------------- *)
(*  Every shifted non-constant mode has zero mean.                   *)
(* ----------------------------------------------------------------- *)

Lemma kernel_shift_mode : forall k x, INR k <> 0 -> RiemannInt (ri_coskxy k x) = 0.
Proof.
  intros k x Hk; pose proof PI_RGT_0 as HPI.
  assert (pr_u : Riemann_integrable (fun y => cos (INR k * x) * cos (INR k * y)) (- PI) PI)
    by (apply RIc, cont_ccos).
  assert (pr_v : Riemann_integrable (fun y => sin (INR k * x) * sin (INR k * y)) (- PI) PI)
    by (apply RIc, cont_ssin).
  assert (pr_uv : Riemann_integrable
                    (fun y => cos (INR k * x) * cos (INR k * y)
                            + sin (INR k * x) * sin (INR k * y)) (- PI) PI)
    by (apply RIc; intro y; apply continuity_pt_plus; [ apply (cont_ccos k x) | apply (cont_ssin k x) ]).
  assert (E : RiemannInt (ri_coskxy k x) = RiemannInt pr_uv).
  { apply RiemannInt_P18; [ lra | intros y _ ].
    replace (INR k * (x - y)) with (INR k * x - INR k * y) by ring.
    rewrite cos_minus; ring. }
  rewrite E.
  rewrite (RI_add (fun y => cos (INR k * x) * cos (INR k * y))
                  (fun y => sin (INR k * x) * sin (INR k * y))
                  (cont_ccos k x) (cont_ssin k x) pr_u pr_v pr_uv).
  rewrite (RI_scal (fun y => cos (INR k * y)) (cos (INR k * x))
                   (cos_lam_cont (INR k)) (cos_RI k) pr_u).
  rewrite (RI_scal (fun y => sin (INR k * y)) (sin (INR k * x))
                   (sin_lam_cont (INR k)) (sin_RI k) pr_v).
  rewrite (cos_int_0 k Hk (cos_RI k)), (sin_int_0 k Hk (sin_RI k)); ring.
Qed.

(* ----------------------------------------------------------------- *)
(*  THE KERNEL NORMALISATION:  ∫_{-π}^{π} D_N(x−y) dy = 2π.           *)
(* ----------------------------------------------------------------- *)

Theorem kernel_shift_integral : forall N x, RiemannInt (ri_Dshift N x) = 2 * PI.
Proof.
  induction N as [| N IH]; intro x; pose proof PI_RGT_0 as HPI.
  - assert (prc : Riemann_integrable (fct_cte 1) (- PI) PI)
      by (apply RIc; intro y; apply continuity_pt_const; intros a b; reflexivity).
    assert (E : RiemannInt (ri_Dshift 0 x) = RiemannInt prc)
      by (apply RiemannInt_P18; [ lra | intros y _; unfold Dsum, fct_cte; cbn [Rsum]; ring ]).
    rewrite E, RiemannInt_P15; lra.
  - assert (pr3 : Riemann_integrable
                    (fun y => Dsum N (x - y) + 2 * cos (INR (S N) * (x - y))) (- PI) PI)
      by (apply RIc; intro y; apply continuity_pt_plus;
          [ apply (cont_Dshift N x)
          | apply (continuity_pt_scal (fun y => cos (INR (S N) * (x - y))) 2 y);
            apply (cont_coskxy (S N) x) ]).
    assert (E : RiemannInt (ri_Dshift (S N) x) = RiemannInt pr3)
      by (apply RiemannInt_P18; [ lra | intros y _; rewrite Dsum_S; ring ]).
    rewrite E, (RiemannInt_P13 (ri_Dshift N x) (ri_coskxy (S N) x) pr3).
    rewrite IH, (kernel_shift_mode (S N) x (INR_S_neq_0 N)); ring.
Qed.

(* ----------------------------------------------------------------- *)
(*  THE LOCALISATION IDENTITY.                                        *)
(* ----------------------------------------------------------------- *)

Section Localize.

Variable f : R -> R.
Hypothesis Cf : continuity f.

Lemma cont_diffD : forall N x, continuity (fun y => (f y - f x) * Dsum N (x - y)).
Proof.
  intros N x y; apply continuity_pt_mult.
  - apply continuity_pt_minus; [ apply Cf | apply continuity_pt_const; intros a b; reflexivity ].
  - apply (cont_Dshift N x).
Qed.

Definition ri_diffD (N : nat) (x : R)
  : Riemann_integrable (fun y => (f y - f x) * Dsum N (x - y)) (- PI) PI
  := RIc _ (cont_diffD N x).

Theorem localization_identity : forall N x,
  / (2 * PI) * RiemannInt (ri_diffD N x) = SN f Cf N x - f x.
Proof.
  intros N x; pose proof PI_RGT_0 as HPI.
  (* split (f y − f x)·D_N(x−y) = f y·D_N(x−y) + (−f x)·D_N(x−y) *)
  assert (pr_split : Riemann_integrable
                       (fun y => f y * Dsum N (x - y) + (- f x) * Dsum N (x - y)) (- PI) PI).
  { apply RIc; intro y; apply continuity_pt_plus.
    - apply continuity_pt_mult; [ apply Cf | apply (cont_Dshift N x) ].
    - apply (continuity_pt_scal (fun y => Dsum N (x - y)) (- f x) y); apply (cont_Dshift N x). }
  assert (E : RiemannInt (ri_diffD N x) = RiemannInt pr_split)
    by (apply RiemannInt_P18; [ lra | intros y _; ring ]).
  rewrite E, (RiemannInt_P13 (ri_fD f Cf N x) (ri_Dshift N x) pr_split),
          (kernel_shift_integral N x).
  (* (1/2π)·∫ f·D_N(x−·) is exactly S_N f(x), by the F2 kernel representation *)
  assert (HK : / (2 * PI) * RiemannInt (ri_fD f Cf N x) = SN f Cf N x)
    by (rewrite (kernel_representation f Cf N x); unfold KN; reflexivity).
  rewrite <- HK; field; lra.
Qed.

End Localize.

Print Assumptions sin_int_0.
Print Assumptions kernel_shift_integral.
Print Assumptions localization_identity.

(* ================================================================= *)
(*  END FourierLocalize.v                                            *)
(*  S_N f(x) − f(x) = (1/2π)∫ (f(y)−f(x)) D_N(x−y) dy, resting on the  *)
(*  kernel normalisation ∫ D_N(x−y) dy = 2π (mode-by-mode, no         *)
(*  periodicity).  The remaining F3 atom: the removable singularity   *)
(*  making (f(y)−f(x))/(2 sin((x−y)/2)) a C¹ integrand, feeding        *)
(*  Riemann–Lebesgue (RL_cv / RL_cos_cv) to drive this integral → 0.  *)
(* ================================================================= *)
