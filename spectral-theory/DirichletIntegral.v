(* ================================================================= *)
(*  DirichletIntegral.v  —  toward Fourier milestone F2: the mean of   *)
(*  the Dirichlet kernel.                                             *)
(*                                                                    *)
(*  The analytic atom of Fourier-series normalisation:               *)
(*    • sin(nπ) = 0                              (sin_nPI);           *)
(*    • ∫_{-π}^{π} cos(k t) dt = 0  for k ≥ 1     (cos_int_0),         *)
(*      the non-constant Fourier modes have zero mean over a period,   *)
(*      via FTC with the antiderivative sin(kt)/k.                    *)
(*                                                                    *)
(*  cos_int_0 is the analytic atom of the Dirichlet-kernel            *)
(*  normalisation ∫_{-π}^{π} D_N = 2π (so (1/2π)∫ D_N = 1) that the    *)
(*  pointwise-convergence proof (F3) rests on; the remaining assembly  *)
(*  of that kernel integral (Dsum continuity + RiemannInt linearity)   *)
(*  is the next, mechanical step.                                    *)
(*                                                                    *)
(*  Built on stdlib RiemannInt / FTC_Riemann and FourierRL's C¹       *)
(*  scaffolding (lam_mult_deriv, cos_lam_cont).                      *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import FourierRL.
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

Print Assumptions sin_nPI.
Print Assumptions cos_int_0.
