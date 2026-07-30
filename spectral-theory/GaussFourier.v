(* ================================================================= *)
(*  GaussFourier.v  —  Gaussian finale step 2: the self-duality spine. *)
(*                                                                    *)
(*  The Fourier transform of the Gaussian is itself:                  *)
(*      ∫_ℝ e^{−πx²} e^{−2πixξ} dx = e^{−πξ²}.                         *)
(*  Over the classical reals this is the cosine transform             *)
(*      F(ξ) = ∫_ℝ e^{−πx²} cos(2πxξ) dx = e^{−πξ²}                    *)
(*  (the sine part vanishes by oddness).  F is pinned down by an ODE:  *)
(*      F(0) = ∫_ℝ e^{−πx²} = 1                    (gauss_pi),         *)
(*      F'(ξ) = −2πξ · F(ξ)   (differentiate under ∫, then parts:      *)
(*                              d/dx[e^{−πx²}] = −2πx e^{−πx²}).        *)
(*                                                                    *)
(*  This file proves the RIGOROUS SPINE — the ODE-uniqueness:         *)
(*                                                                    *)
(*    gaussian_ode_unique : F' = −2πξ·F  and  F(0) = 1                 *)
(*                          ⇒  F(ξ) = e^{−πξ²}   for all ξ.            *)
(*                                                                    *)
(*  Proof: G(ξ) = F(ξ)·e^{πξ²} has G' ≡ 0 (product/chain rule +        *)
(*  the ODE), hence is constant (null_deriv_const, via MVT), equal to  *)
(*  G(0) = F(0) = 1; so F(ξ) = e^{−πξ²}.                              *)
(*                                                                    *)
(*  HONEST BOUNDARY.  The analytic INPUT F' = −2πξ·F — differentiation *)
(*  under the improper integral sign (dominated convergence / uniform  *)
(*  bounds) plus integration by parts — is the remaining wall; it is   *)
(*  the one genuinely library-scale gap between here and Poisson       *)
(*  summation.  The base case F(0) = 1 IS already machine-checked      *)
(*  (fourier_base + GaussPiValue.gauss_pi).  No new axioms (classical  *)
(*  Reals only).                                                      *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra.
Require Import GaussPiValue.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  Zero derivative on all of ℝ ⇒ constant (via the MVT).           *)
(* ----------------------------------------------------------------- *)

Lemma null_deriv_const : forall (G : R -> R),
  (forall x, derivable_pt_lim G x 0) -> forall x, G x = G 0.
Proof.
  intros G HG' x.
  pose (pr := fun y => exist (fun l => derivable_pt_lim G y l) 0 (HG' y) : derivable_pt G y).
  destruct (Rtotal_order x 0) as [Hlt | [Heq | Hgt]].
  - destruct (MVT_cor1 G x 0 pr Hlt) as [c [Hc _]].
    assert (Hd : derive_pt G c (pr c) = 0) by reflexivity.
    rewrite Hd, Rmult_0_l in Hc; lra.
  - rewrite Heq; reflexivity.
  - destruct (MVT_cor1 G 0 x pr Hgt) as [c [Hc _]].
    assert (Hd : derive_pt G c (pr c) = 0) by reflexivity.
    rewrite Hd, Rmult_0_l in Hc; lra.
Qed.

(* ----------------------------------------------------------------- *)
(*  The ODE-uniqueness spine.                                        *)
(* ----------------------------------------------------------------- *)

Theorem gaussian_ode_unique : forall (F : R -> R),
  (forall x, derivable_pt_lim F x (- (2 * PI * x) * F x)) ->
  F 0 = 1 ->
  forall x, F x = exp (- (PI * x ^ 2)).
Proof.
  intros F HF' HF0 x.
  (* G y = F y · e^{πy²} has G' ≡ 0 *)
  assert (HG' : forall y, derivable_pt_lim (fun z => F z * exp (PI * z ^ 2)) y 0).
  { intro y.
    (* d/dy (π y²) = 2π y *)
    assert (Hin : derivable_pt_lim (fun z => PI * z ^ 2) y (2 * PI * y)).
    { pose proof (derivable_pt_lim_scal (fun z => z ^ 2) PI y
                    (INR 2 * y ^ Init.Nat.pred 2) (derivable_pt_lim_pow y 2)) as Hs.
      replace (2 * PI * y) with (PI * (INR 2 * y ^ Init.Nat.pred 2)) by (simpl; ring).
      exact Hs. }
    (* d/dy e^{πy²} = e^{πy²}·2πy *)
    pose proof (derivable_pt_lim_comp (fun z => PI * z ^ 2) exp y (2 * PI * y)
                  (exp (PI * y ^ 2)) Hin (derivable_pt_lim_exp (PI * y ^ 2))) as Hh.
    (* product rule *)
    pose proof (derivable_pt_lim_mult F (fun z => exp (PI * z ^ 2)) y
                  (- (2 * PI * y) * F y) (exp (PI * y ^ 2) * (2 * PI * y)) (HF' y) Hh) as Hm.
    cbv beta in Hm.
    match type of Hm with
    | derivable_pt_lim _ _ ?V => replace V with 0 in Hm by ring
    end.
    exact Hm. }
  pose proof (null_deriv_const (fun z => F z * exp (PI * z ^ 2)) HG' x) as Hc.
  cbv beta in Hc.
  assert (H0 : F 0 * exp (PI * 0 ^ 2) = 1)
    by (rewrite HF0; replace (PI * 0 ^ 2) with 0 by ring; rewrite exp_0; ring).
  rewrite H0 in Hc.
  (* F x · e^{πx²} = 1  ⇒  F x = e^{−πx²} *)
  assert (Hpos : exp (PI * x ^ 2) <> 0) by (apply Rgt_not_eq; apply exp_pos).
  apply Rmult_eq_reg_r with (exp (PI * x ^ 2)); [ | exact Hpos ].
  rewrite Hc, <- exp_plus.
  replace (- (PI * x ^ 2) + PI * x ^ 2) with 0 by ring.
  rewrite exp_0; reflexivity.
Qed.

(* ----------------------------------------------------------------- *)
(*  Base case: the ξ=0 slice of the transform IS the Gaussian.       *)
(*  (So F(0) = ∫_ℝ e^{−πx²} = 1 is GaussPiValue.gauss_pi.)           *)
(* ----------------------------------------------------------------- *)

Lemma fourier_base : forall x, exp (- (PI * x ^ 2)) * cos (2 * PI * x * 0) = exp_pi x.
Proof.
  intro x; unfold exp_pi.
  replace (2 * PI * x * 0) with 0 by ring.
  rewrite cos_0; ring.
Qed.

Print Assumptions gaussian_ode_unique.

(* ================================================================= *)
(*  END GaussFourier.v                                              *)
(*  The self-duality spine: any F with F' = −2πξ·F and F(0) = 1 is     *)
(*  the Gaussian e^{−πξ²}.  Combined with F(0) = 1 (gauss_pi) this      *)
(*  reduces ∫_ℝ e^{−πx²}e^{−2πixξ} = e^{−πξ²} to the single analytic    *)
(*  input F' = −2πξ·F (differentiation under ∫ + parts) — the library- *)
(*  scale gap remaining before Poisson summation → θ(1/t) = √t·θ(t).   *)
(* ================================================================= *)
