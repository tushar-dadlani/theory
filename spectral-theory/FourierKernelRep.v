(* ================================================================= *)
(*  FourierKernelRep.v  —  Fourier milestone F2 (kernel representation)*)
(*                                                                    *)
(*  THE convolution identity that pointwise convergence (F3) stands on:*)
(*                                                                    *)
(*     S_N f(x) = (1/2π) ∫_{-π}^{π} f(y) · D_N(x−y) dy,               *)
(*                                                                    *)
(*  for any continuous f, where                                       *)
(*     S_N f(x) = a₀/2 + Σ_{k=1}^{N} (a_k cos kx + b_k sin kx),        *)
(*     a_k = (1/π)∫ f(y)cos(ky) dy,  b_k = (1/π)∫ f(y)sin(ky) dy,      *)
(*     D_N(t) = Dsum N t = 1 + 2 Σ_{k=1}^{N} cos(kt)  (DirichletKernel)*)
(*                                                                    *)
(*  Proof, exactly as flagged in FourierPartialSum.v:                 *)
(*    • single_mode : ∫ f(y)cos(k(x−y)) dy                            *)
(*                    = cos kx·∫f cos ky + sin kx·∫f sin ky,          *)
(*      via cos(k(x−y)) = cos kx cos ky + sin kx sin ky (cos_minus)    *)
(*      and integral linearity (RI_add, RI_scal from FourierPartialSum)*)
(*    • conv_step / J_eq : induction on N via Dsum_S, assembling the   *)
(*      kernel integral out of the single modes.                     *)
(*                                                                    *)
(*  This is the F2 platform.  F3 (pointwise convergence S_N f(x) →     *)
(*  f(x)) still needs the Dini / removable-singularity step feeding    *)
(*  the RIEMANN–LEBESGUE lemma (FourierRL.RL_cv) with the localised    *)
(*  quotient (f(x+u)−f(x))/(2 sin(u/2)); that remains the open next    *)
(*  milestone.                                                        *)
(*                                                                    *)
(*  No new axioms: only the classical Reals already used throughout    *)
(*  (via cos/sin/RiemannInt).  Built on FourierPartialSum,             *)
(*  DirichletKernel and DirichletIntegral.                            *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import FourierRL DirichletKernel DirichletIntegral FourierPartialSum.
Open Scope R_scope.

Section KernelRep.

Variable f : R -> R.
Hypothesis Cf : continuity f.

(* ----------------------------------------------------------------- *)
(*  Continuity / integrability of the integrands.                    *)
(* ----------------------------------------------------------------- *)

Lemma RIc : forall g, continuity g -> Riemann_integrable g (- PI) PI.
Proof.
  intros g Cg; apply continuity_implies_RiemannInt;
    [ pose proof PI_RGT_0; lra | intros x _; apply Cg ].
Qed.

Lemma cont_fcos : forall k, continuity (fun y => f y * cos (INR k * y)).
Proof. intros k y; apply continuity_pt_mult; [ apply Cf | apply cos_lam_cont ]. Qed.

Lemma cont_fsin : forall k, continuity (fun y => f y * sin (INR k * y)).
Proof. intros k y; apply continuity_pt_mult; [ apply Cf | apply sin_lam_cont ]. Qed.

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

Lemma cont_fDcos : forall k x, continuity (fun y => f y * cos (INR k * (x - y))).
Proof. intros k x y; apply continuity_pt_mult; [ apply Cf | apply (cont_coskxy k x) ]. Qed.

Lemma cont_u : forall k x,
  continuity (fun y => cos (INR k * x) * (f y * cos (INR k * y))).
Proof.
  intros k x y; apply (continuity_pt_scal (fun y => f y * cos (INR k * y)) (cos (INR k * x)) y);
    apply (cont_fcos k).
Qed.

Lemma cont_v : forall k x,
  continuity (fun y => sin (INR k * x) * (f y * sin (INR k * y))).
Proof.
  intros k x y; apply (continuity_pt_scal (fun y => f y * sin (INR k * y)) (sin (INR k * x)) y);
    apply (cont_fsin k).
Qed.

Lemma cont_Dshift : forall N x, continuity (fun y => Dsum N (x - y)).
Proof.
  intros N x y; apply (continuity_pt_comp (fun y => x - y) (Dsum N) y);
    [ apply cont_sub | apply Dsum_cont ].
Qed.

Lemma cont_fD : forall N x, continuity (fun y => f y * Dsum N (x - y)).
Proof. intros N x y; apply continuity_pt_mult; [ apply Cf | apply (cont_Dshift N x) ]. Qed.

Lemma cont_scal2 : forall k x,
  continuity (fun y => 2 * (f y * cos (INR k * (x - y)))).
Proof.
  intros k x y; apply (continuity_pt_scal (fun y => f y * cos (INR k * (x - y))) 2 y);
    apply (cont_fDcos k x).
Qed.

(* ----------------------------------------------------------------- *)
(*  Canonical integrability witnesses and the Fourier data.          *)
(* ----------------------------------------------------------------- *)

Definition ri_fcos (k : nat) : Riemann_integrable (fun y => f y * cos (INR k * y)) (- PI) PI
  := RIc _ (cont_fcos k).
Definition ri_fsin (k : nat) : Riemann_integrable (fun y => f y * sin (INR k * y)) (- PI) PI
  := RIc _ (cont_fsin k).
Definition ri_fDcos (k : nat) (x : R)
  : Riemann_integrable (fun y => f y * cos (INR k * (x - y))) (- PI) PI
  := RIc _ (cont_fDcos k x).
Definition ri_fD (N : nat) (x : R)
  : Riemann_integrable (fun y => f y * Dsum N (x - y)) (- PI) PI
  := RIc _ (cont_fD N x).

(* Fourier cosine/sine coefficients *)
Definition acoef (k : nat) : R := / PI * RiemannInt (ri_fcos k).
Definition bcoef (k : nat) : R := / PI * RiemannInt (ri_fsin k).

(* the N-th Fourier partial sum S_N f(x) *)
Definition SN (N : nat) (x : R) : R :=
  acoef 0 / 2
  + Rsum (fun k => acoef k * cos (INR k * x) + bcoef k * sin (INR k * x)) N.

(* the kernel side (1/2π) ∫ f(y) D_N(x−y) dy *)
Definition KN (N : nat) (x : R) : R := / (2 * PI) * RiemannInt (ri_fD N x).

(* the single-mode contribution ∫ f(y) cos(k(x−y)) dy, in coefficient form *)
Definition term (x : R) (k : nat) : R :=
  cos (INR k * x) * RiemannInt (ri_fcos k) + sin (INR k * x) * RiemannInt (ri_fsin k).

(* ----------------------------------------------------------------- *)
(*  little sum-algebra on Rsum.                                       *)
(* ----------------------------------------------------------------- *)

Lemma Rsum_scal : forall c h N, Rsum (fun k => c * h k) N = c * Rsum h N.
Proof. intros c h N; induction N; cbn [Rsum]; [ ring | rewrite IHN; ring ]. Qed.

Lemma Rsum_ext : forall g h N, (forall k, g k = h k) -> Rsum g N = Rsum h N.
Proof. intros g h N H; induction N; cbn [Rsum]; [ reflexivity | rewrite IHN, H; reflexivity ]. Qed.

(* ----------------------------------------------------------------- *)
(*  THE SINGLE-MODE IDENTITY.                                         *)
(* ----------------------------------------------------------------- *)

Lemma single_mode : forall k x, RiemannInt (ri_fDcos k x) = term x k.
Proof.
  intros k x; unfold term. pose proof PI_RGT_0 as HPI.
  assert (pr_u : Riemann_integrable
                   (fun y => cos (INR k * x) * (f y * cos (INR k * y))) (- PI) PI)
    by (apply RIc, cont_u).
  assert (pr_v : Riemann_integrable
                   (fun y => sin (INR k * x) * (f y * sin (INR k * y))) (- PI) PI)
    by (apply RIc, cont_v).
  assert (pr_uv : Riemann_integrable
                    (fun y => cos (INR k * x) * (f y * cos (INR k * y))
                            + sin (INR k * x) * (f y * sin (INR k * y))) (- PI) PI)
    by (apply RIc; intro y; apply continuity_pt_plus;
        [ apply (cont_u k x) | apply (cont_v k x) ]).
  assert (E : RiemannInt (ri_fDcos k x) = RiemannInt pr_uv).
  { apply RiemannInt_P18; [ lra | intros y _ ].
    replace (INR k * (x - y)) with (INR k * x - INR k * y) by ring.
    rewrite cos_minus; ring. }
  rewrite E.
  rewrite (RI_add (fun y => cos (INR k * x) * (f y * cos (INR k * y)))
                  (fun y => sin (INR k * x) * (f y * sin (INR k * y)))
                  (cont_u k x) (cont_v k x) pr_u pr_v pr_uv).
  rewrite (RI_scal (fun y => f y * cos (INR k * y)) (cos (INR k * x))
                   (cont_fcos k) (ri_fcos k) pr_u).
  rewrite (RI_scal (fun y => f y * sin (INR k * y)) (sin (INR k * x))
                   (cont_fsin k) (ri_fsin k) pr_v).
  reflexivity.
Qed.

(* ----------------------------------------------------------------- *)
(*  THE CONVOLUTION ASSEMBLY.                                         *)
(* ----------------------------------------------------------------- *)

(* base: D_0 ≡ 1, so ∫ f·D_0(x−·) = ∫ f = ∫ f·cos(0·) *)
Lemma conv_base : forall x, RiemannInt (ri_fD 0 x) = RiemannInt (ri_fcos 0).
Proof.
  intro x; apply RiemannInt_P18; [ pose proof PI_RGT_0; lra | intros y _ ];
    unfold Dsum; cbn [Rsum].
  replace (INR 0) with 0 by reflexivity; rewrite Rmult_0_l, cos_0; ring.
Qed.

(* step: peel the top Dirichlet mode via Dsum_S *)
Lemma conv_step : forall N x,
  RiemannInt (ri_fD (S N) x)
  = RiemannInt (ri_fD N x) + 2 * RiemannInt (ri_fDcos (S N) x).
Proof.
  intros N x; pose proof PI_RGT_0 as HPI.
  assert (pr2q : Riemann_integrable
                   (fun y => 2 * (f y * cos (INR (S N) * (x - y)))) (- PI) PI)
    by (apply RIc, cont_scal2).
  assert (pr_sum : Riemann_integrable
                     (fun y => f y * Dsum N (x - y)
                             + 2 * (f y * cos (INR (S N) * (x - y)))) (- PI) PI)
    by (apply RIc; intro y; apply continuity_pt_plus;
        [ apply (cont_fD N x) | apply (cont_scal2 (S N) x) ]).
  assert (E : RiemannInt (ri_fD (S N) x) = RiemannInt pr_sum).
  { apply RiemannInt_P18; [ lra | intros y _ ].
    rewrite Dsum_S; ring. }
  rewrite E.
  rewrite (RI_add (fun y => f y * Dsum N (x - y))
                  (fun y => 2 * (f y * cos (INR (S N) * (x - y))))
                  (cont_fD N x) (cont_scal2 (S N) x) (ri_fD N x) pr2q pr_sum).
  rewrite (RI_scal (fun y => f y * cos (INR (S N) * (x - y))) 2
                   (cont_fDcos (S N) x) (ri_fDcos (S N) x) pr2q).
  reflexivity.
Qed.

(* the kernel integral, assembled out of the single modes *)
Lemma J_eq : forall N x,
  RiemannInt (ri_fD N x) = RiemannInt (ri_fcos 0) + 2 * Rsum (term x) N.
Proof.
  induction N as [| N IH]; intro x.
  - cbn [Rsum]; rewrite conv_base; ring.
  - rewrite conv_step, IH, (single_mode (S N) x); cbn [Rsum]; ring.
Qed.

(* ----------------------------------------------------------------- *)
(*  THE KERNEL REPRESENTATION.                                        *)
(* ----------------------------------------------------------------- *)

Lemma KN_eq_SN : forall N x, KN N x = SN N x.
Proof.
  intros N x; pose proof PI_RGT_0 as HPI; assert (HPIn : PI <> 0) by lra.
  unfold KN, SN; rewrite J_eq.
  assert (Hc0 : RiemannInt (ri_fcos 0) = PI * acoef 0)
    by (unfold acoef; field; exact HPIn).
  assert (Hterm : Rsum (term x) N
    = PI * Rsum (fun k => acoef k * cos (INR k * x) + bcoef k * sin (INR k * x)) N).
  { rewrite <- (Rsum_scal PI
        (fun k => acoef k * cos (INR k * x) + bcoef k * sin (INR k * x)) N).
    apply Rsum_ext; intro k; unfold term, acoef, bcoef; field; exact HPIn. }
  rewrite Hc0, Hterm; field; exact HPIn.
Qed.

Theorem kernel_representation : forall N x, SN N x = KN N x.
Proof. intros N x; symmetry; apply KN_eq_SN. Qed.

End KernelRep.

Print Assumptions single_mode.
Print Assumptions kernel_representation.

(* ================================================================= *)
(*  END FourierKernelRep.v                                           *)
(*  The Fourier partial sum is the Dirichlet-kernel convolution:      *)
(*  S_N f(x) = (1/2π)∫_{-π}^{π} f(y) D_N(x−y) dy  for continuous f     *)
(*  (kernel_representation), assembled from the single-mode identity   *)
(*  (single_mode) by induction on N.  This F2 platform feeds F3        *)
(*  (pointwise convergence) via localisation + Riemann–Lebesgue,       *)
(*  which remains the open next milestone.                           *)
(* ================================================================= *)
