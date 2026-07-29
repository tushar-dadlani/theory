(* ================================================================= *)
(*  DirichletIntegral.v  —  Fourier milestone F2 (normalisation): the  *)
(*  Dirichlet kernel integrates to 2π.                               *)
(*                                                                    *)
(*    • sin(nπ) = 0                              (sin_nPI);           *)
(*    • ∫_{-π}^{π} cos(k t) dt = 0  for k ≥ 1     (cos_int_0),         *)
(*      the non-constant Fourier modes have zero mean over a period,   *)
(*      via FTC with the antiderivative sin(kt)/k;                    *)
(*    • ∫_{-π}^{π} D_N = 2π                       (dirichlet_integral),*)
(*      hence (1/2π) ∫ D_N = 1 — the normalisation the pointwise-      *)
(*      convergence proof (F3) rests on.  Proved by induction on N     *)
(*      (Dsum_S) with RiemannInt linearity (P13), extensionality       *)
(*      (P18), the constant integral (P15) and cos_int_0; the kernel   *)
(*      is continuous (Rcossum_cont, Dsum_cont), hence integrable.     *)
(*                                                                    *)
(*  Built on stdlib RiemannInt / FTC_Riemann and FourierRL's C¹       *)
(*  scaffolding (lam_mult_deriv, cos_lam_cont), plus DirichletKernel. *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import FourierRL DirichletKernel.
Open Scope R_scope.

(* sin(n·π) = 0 *)
Lemma sin_nPI : forall n, sin (INR n * PI) = 0.
Proof.
  induction n as [| n IH].
  - simpl; rewrite Rmult_0_l; exact sin_0.
  - rewrite S_INR, Rmult_plus_distr_r, Rmult_1_l, sin_plus, sin_PI, cos_PI, IH; ring.
Qed.

(* d/dt sin(k·t) = cos(k·t)·k *)
Lemma sin_lam_deriv : forall lam t,
  derivable_pt_lim (fun x => sin (lam * x)) t (cos (lam * t) * lam).
Proof.
  intros lam t.
  apply (derivable_pt_lim_comp (fun x => lam * x) sin t lam (cos (lam * t))).
  - apply lam_mult_deriv.
  - apply derivable_pt_lim_sin.
Qed.

(* the antiderivative (1/k)·sin(k·t) has derivative cos(k·t) *)
Lemma cosprim_deriv : forall k t, INR k <> 0 ->
  derivable_pt_lim (fun x => / INR k * sin (INR k * x)) t (cos (INR k * t)).
Proof.
  intros k t Hk.
  pose proof (derivable_pt_lim_scal (fun x => sin (INR k * x)) (/ INR k) t
                (cos (INR k * t) * INR k) (sin_lam_deriv (INR k) t)) as H.
  replace (/ INR k * (cos (INR k * t) * INR k)) with (cos (INR k * t)) in H
    by (field; exact Hk).
  exact H.
Qed.

(* the antiderivative as a C¹ function (so FTC applies) *)
Definition cosprim (k : nat) (Hk : INR k <> 0) : C1_fun :=
  mkC1 (c1 := fun t => / INR k * sin (INR k * t))
       (diff0 := fun t => exist _ _ (cosprim_deriv k t Hk))
       (cos_lam_cont (INR k)).

Lemma cosprim_val : forall k (Hk : INR k <> 0) t,
  cosprim k Hk t = / INR k * sin (INR k * t).
Proof. reflexivity. Qed.

(* THE ATOM: ∫_{-π}^{π} cos(k t) dt = 0 for k ≥ 1 *)
Lemma cos_int_0 : forall k (Hk : INR k <> 0)
  (pr : Riemann_integrable (fun t => cos (INR k * t)) (- PI) PI),
  RiemannInt pr = 0.
Proof.
  intros k Hk pr.
  pose proof (FTC_Riemann (cosprim k Hk) pr) as FTC.
  assert (Hval : cosprim k Hk PI - cosprim k Hk (- PI) = 0).
  { rewrite !cosprim_val, sin_nPI.
    replace (INR k * - PI) with (- (INR k * PI)) by ring.
    rewrite sin_neg, sin_nPI; ring. }
  rewrite Hval in FTC; exact FTC.
Qed.

(* ----------------------------------------------------------------- *)
(*  Continuity / integrability of the Dirichlet kernel.              *)
(* ----------------------------------------------------------------- *)

Lemma INR_S_neq_0 : forall N, INR (S N) <> 0.
Proof. intro N; rewrite S_INR; pose proof (pos_INR N); lra. Qed.

Lemma Rcossum_cont : forall N x,
  continuity_pt (fun t => Rsum (fun k => cos (INR k * t)) N) x.
Proof.
  induction N as [| N IH]; intro x.
  - cbn [Rsum]; apply continuity_pt_const; intros a b; reflexivity.
  - cbn [Rsum].
    apply (continuity_pt_plus (fun t => Rsum (fun k => cos (INR k * t)) N)
                              (fun t => cos (INR (S N) * t)) x).
    + apply IH.
    + apply cos_lam_cont.
Qed.

Lemma Dsum_cont : forall N x, continuity_pt (Dsum N) x.
Proof.
  intros N x; unfold Dsum.
  apply (continuity_pt_plus (fun _ => 1)
           (fun t => 2 * Rsum (fun k => cos (INR k * t)) N) x).
  - apply continuity_pt_const; intros a b; reflexivity.
  - apply (continuity_pt_scal (fun t => Rsum (fun k => cos (INR k * t)) N) 2 x).
    apply Rcossum_cont.
Qed.

Lemma Dsum_RI : forall N, Riemann_integrable (Dsum N) (- PI) PI.
Proof.
  intro N; apply continuity_implies_RiemannInt;
    [ pose proof PI_RGT_0; lra | intros x _; apply Dsum_cont ].
Qed.

Lemma cos_RI : forall k, Riemann_integrable (fun t => cos (INR k * t)) (- PI) PI.
Proof.
  intro k; apply continuity_implies_RiemannInt;
    [ pose proof PI_RGT_0; lra | intros x _; apply cos_lam_cont ].
Qed.

(* THE KERNEL INTEGRAL: ∫_{-π}^{π} D_N = 2π  (so (1/2π) ∫ D_N = 1) *)
Theorem dirichlet_integral : forall N, RiemannInt (Dsum_RI N) = 2 * PI.
Proof.
  induction N as [| N IH].
  - assert (prc : Riemann_integrable (fct_cte 1) (- PI) PI)
      by (apply continuity_implies_RiemannInt;
          [ pose proof PI_RGT_0; lra
          | intros x _; apply continuity_pt_const; intros a b; reflexivity ]).
    assert (E : RiemannInt (Dsum_RI 0) = RiemannInt prc)
      by (apply RiemannInt_P18;
          [ pose proof PI_RGT_0; lra | intros x _; unfold Dsum, fct_cte; cbn [Rsum]; ring ]).
    rewrite E, RiemannInt_P15; pose proof PI_RGT_0; lra.
  - pose proof PI_RGT_0 as HPI.
    assert (pr3 : Riemann_integrable (fun x => Dsum N x + 2 * cos (INR (S N) * x)) (- PI) PI).
    { apply continuity_implies_RiemannInt; [ lra | intros x _; apply continuity_pt_plus;
        [ apply Dsum_cont
        | apply (continuity_pt_scal (fun t => cos (INR (S N) * t)) 2 x); apply cos_lam_cont ] ]. }
    assert (E : RiemannInt (Dsum_RI (S N)) = RiemannInt pr3)
      by (apply RiemannInt_P18; [ lra | intros x _; rewrite Dsum_S; ring ]).
    rewrite E, (RiemannInt_P13 (Dsum_RI N) (cos_RI (S N)) pr3).
    rewrite IH, (cos_int_0 (S N) (INR_S_neq_0 N) (cos_RI (S N))); ring.
Qed.

Print Assumptions sin_nPI.
Print Assumptions cos_int_0.
Print Assumptions dirichlet_integral.
