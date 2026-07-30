(* ================================================================= *)
(*  WallisIntegral.v  —  the Wallis integrals  Wₙ = ∫₀^{π/2} sinⁿ.    *)
(*                                                                    *)
(*  Foundation of the "part (A)" stack toward the Gaussian integral    *)
(*  ∫_ℝ e^{−x²} = √π (the Poisson→θ RHS wall).  The Wallis integrals   *)
(*  Wₙ = ∫₀^{π/2} (sin x)ⁿ dx satisfy                                 *)
(*                                                                    *)
(*     W₀ = π/2,   W₁ = 1,   W_{n+2} = ((n+1)/(n+2))·Wₙ,              *)
(*                                                                    *)
(*  the recurrence being FTC applied to                              *)
(*     d/dx[ (sin x)^{n+1} cos x ]                                    *)
(*         = (n+1)(sin x)ⁿ − (n+2)(sin x)^{n+2}                       *)
(*  (product/chain rule + cos² = 1 − sin²), whose integral over        *)
(*  [0,π/2] vanishes at both endpoints — giving                       *)
(*     0 = (n+1)Wₙ − (n+2)W_{n+2}.                                    *)
(*                                                                    *)
(*  All on the BOUNDED interval [0,π/2] with stdlib RiemannInt + FTC   *)
(*  (no improper integral yet).  Next in the stack: the Wallis         *)
(*  product / √n·Wₙ → √(π/2) asymptotics, then the improper-integral   *)
(*  setup and the Gaussian squeeze.  No new axioms (classical Reals).  *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Open Scope R_scope.

Definition sin_pow (n : nat) (x : R) : R := (sin x) ^ n.

Lemma cont_sin_pow : forall n, continuity (sin_pow n).
Proof.
  induction n as [| n IH]; intro x.
  - unfold sin_pow; cbn [pow]; apply continuity_pt_const; intros a b; reflexivity.
  - unfold sin_pow; cbn [pow].
    apply (continuity_pt_mult sin (fun y => (sin y) ^ n) x); [ apply continuity_sin | apply IH ].
Qed.

Lemma sin_pow_RI (n : nat) : Riemann_integrable (sin_pow n) 0 (PI / 2).
Proof.
  apply continuity_implies_RiemannInt;
    [ apply Rlt_le, PI2_RGT_0 | intros x _; apply cont_sin_pow ].
Defined.

Definition Wallis (n : nat) : R := RiemannInt (sin_pow_RI n).

(* ----------------------------------------------------------------- *)
(*  Scalar linearity of RiemannInt on [0,π/2].                       *)
(* ----------------------------------------------------------------- *)

Lemma int_scal : forall (f : R -> R) (c : R), continuity f ->
  forall (prf : Riemann_integrable f 0 (PI / 2))
         (prcf : Riemann_integrable (fun x => c * f x) 0 (PI / 2)),
  RiemannInt prcf = c * RiemannInt prf.
Proof.
  intros f c Cf prf prcf; pose proof PI2_RGT_0 as Hpi.
  assert (pr0 : Riemann_integrable (fun _ : R => 0) 0 (PI / 2))
    by (apply continuity_implies_RiemannInt;
        [ lra | intros x _; apply continuity_pt_const; intros a b; reflexivity ]).
  assert (pr3 : Riemann_integrable (fun x => 0 + c * f x) 0 (PI / 2))
    by (apply continuity_implies_RiemannInt; [ lra | intros x _; apply continuity_pt_plus;
        [ apply continuity_pt_const; intros a b; reflexivity
        | apply (continuity_pt_scal f c x); apply Cf ] ]).
  assert (H0 : RiemannInt pr0 = 0)
    by (transitivity (0 * (PI / 2 - 0)); [ exact (RiemannInt_P15 pr0) | ring ]).
  assert (E : RiemannInt prcf = RiemannInt pr3)
    by (apply RiemannInt_P18; [ lra | intros x _; ring ]).
  rewrite E, (RiemannInt_P13 pr0 prf pr3), H0; ring.
Qed.

(* ----------------------------------------------------------------- *)
(*  Base cases.                                                       *)
(* ----------------------------------------------------------------- *)

Lemma Wallis_0 : Wallis 0 = PI / 2.
Proof.
  unfold Wallis; pose proof PI2_RGT_0 as Hpi.
  assert (prc : Riemann_integrable (fct_cte 1) 0 (PI / 2))
    by (apply continuity_implies_RiemannInt;
        [ lra | intros x _; apply continuity_pt_const; intros a b; reflexivity ]).
  assert (E : RiemannInt (sin_pow_RI 0) = RiemannInt prc)
    by (apply RiemannInt_P18; [ lra | intros x _; unfold sin_pow, fct_cte; reflexivity ]).
  rewrite E, RiemannInt_P15; ring.
Qed.

Lemma mcos_deriv : forall x, derivable_pt_lim (fun y => - cos y) x (sin x).
Proof.
  intro x; pose proof (derivable_pt_lim_opp cos x (- sin x) (derivable_pt_lim_cos x)) as H.
  replace (- - sin x) with (sin x) in H by ring; exact H.
Qed.

Definition mcos : C1_fun :=
  mkC1 (c1 := fun x => - cos x) (diff0 := fun x => exist _ (sin x) (mcos_deriv x)) continuity_sin.

Lemma mcos_val : forall x, mcos x = - cos x.
Proof. reflexivity. Qed.

Lemma Wallis_1 : Wallis 1 = 1.
Proof.
  unfold Wallis; pose proof PI2_RGT_0 as Hpi.
  assert (prsin : Riemann_integrable sin 0 (PI / 2))
    by (apply continuity_implies_RiemannInt; [ lra | intros x _; apply continuity_sin ]).
  assert (E : RiemannInt (sin_pow_RI 1) = RiemannInt prsin)
    by (apply RiemannInt_P18; [ lra | intros x _; unfold sin_pow; cbn [pow]; ring ]).
  pose proof (FTC_Riemann mcos prsin : RiemannInt prsin = mcos (PI / 2) - mcos 0) as F.
  rewrite E, F, !mcos_val, cos_PI2, cos_0; ring.
Qed.

(* ----------------------------------------------------------------- *)
(*  The recurrence via FTC on (sin x)^{n+1} cos x.                    *)
(* ----------------------------------------------------------------- *)

Definition Hval (n : nat) (x : R) : R :=
  INR (S n) * sin_pow n x - INR (S (S n)) * sin_pow (S (S n)) x.

Lemma sin_pow_deriv : forall k x,
  derivable_pt_lim (fun y => (sin y) ^ k) x (INR k * (sin x) ^ (pred k) * cos x).
Proof.
  intros k x.
  apply (derivable_pt_lim_comp sin (fun y => y ^ k) x (cos x) (INR k * (sin x) ^ (pred k)));
    [ apply derivable_pt_lim_sin | apply derivable_pt_lim_pow ].
Qed.

Lemma H_deriv : forall n x, derivable_pt_lim (fun y => (sin y) ^ (S n) * cos y) x (Hval n x).
Proof.
  intros n x.
  pose proof (derivable_pt_lim_mult (fun y => (sin y) ^ (S n)) cos x
                (INR (S n) * (sin x) ^ (pred (S n)) * cos x) (- sin x)
                (sin_pow_deriv (S n) x) (derivable_pt_lim_cos x)) as Hm.
  replace (Hval n x)
    with (INR (S n) * (sin x) ^ (pred (S n)) * cos x * cos x + (sin x) ^ (S n) * (- sin x)).
  - exact Hm.
  - change (pred (S n)) with n; unfold Hval, sin_pow.
    assert (P1 : (sin x) ^ (S n) = sin x * (sin x) ^ n) by (cbn [pow]; ring).
    assert (P2 : (sin x) ^ (S (S n)) = sin x * sin x * (sin x) ^ n) by (cbn [pow]; ring).
    assert (Scc : cos x * cos x = 1 - sin x * sin x)
      by (pose proof (sin2_cos2 x); unfold Rsqr in *; lra).
    rewrite P1, P2, !S_INR.
    replace ((INR n + 1) * (sin x) ^ n * cos x * cos x)
      with ((INR n + 1) * (sin x) ^ n * (1 - sin x * sin x)) by (rewrite <- Scc; ring).
    ring.
Qed.

Lemma Hval_cont : forall n, continuity (Hval n).
Proof.
  intros n x; unfold Hval.
  apply (continuity_pt_minus (fun y => INR (S n) * sin_pow n y)
           (fun y => INR (S (S n)) * sin_pow (S (S n)) y) x).
  - apply (continuity_pt_scal (sin_pow n) (INR (S n)) x); apply cont_sin_pow.
  - apply (continuity_pt_scal (sin_pow (S (S n))) (INR (S (S n))) x); apply cont_sin_pow.
Qed.

Definition H_C1 (n : nat) : C1_fun :=
  mkC1 (c1 := fun x => (sin x) ^ (S n) * cos x)
       (diff0 := fun x => exist _ (Hval n x) (H_deriv n x)) (Hval_cont n).

Lemma H_C1_val : forall n x, H_C1 n x = (sin x) ^ (S n) * cos x.
Proof. reflexivity. Qed.

Theorem Wallis_rec : forall n, Wallis (S (S n)) = (INR (S n) / INR (S (S n))) * Wallis n.
Proof.
  intro n; pose proof PI2_RGT_0 as Hpi.
  assert (HvalRI : Riemann_integrable (Hval n) 0 (PI / 2))
    by (apply continuity_implies_RiemannInt; [ lra | intros x _; apply Hval_cont ]).
  (* FTC: the integral of the derivative vanishes at both endpoints *)
  pose proof (FTC_Riemann (H_C1 n) HvalRI : RiemannInt HvalRI = H_C1 n (PI / 2) - H_C1 n 0) as F.
  rewrite !H_C1_val, sin_PI2, cos_PI2, sin_0, cos_0 in F.
  assert (Hftc : RiemannInt HvalRI = 0) by (rewrite F; cbn [pow]; ring).
  (* linearity: the integral splits into the two Wallis integrals *)
  assert (Hlin : RiemannInt HvalRI = INR (S n) * Wallis n - INR (S (S n)) * Wallis (S (S n))).
  { assert (prF : Riemann_integrable (fun x => INR (S n) * sin_pow n x) 0 (PI / 2))
      by (apply continuity_implies_RiemannInt; [ lra | intros x _;
          apply (continuity_pt_scal (sin_pow n) (INR (S n)) x); apply cont_sin_pow ]).
    assert (prsum : Riemann_integrable
              (fun x => INR (S n) * sin_pow n x + (- INR (S (S n))) * sin_pow (S (S n)) x) 0 (PI / 2))
      by (apply continuity_implies_RiemannInt; [ lra | intros x _; apply continuity_pt_plus;
          [ apply (continuity_pt_scal (sin_pow n) (INR (S n)) x); apply cont_sin_pow
          | apply (continuity_pt_scal (sin_pow (S (S n))) (- INR (S (S n))) x); apply cont_sin_pow ] ]).
    assert (E1 : RiemannInt HvalRI = RiemannInt prsum)
      by (apply RiemannInt_P18; [ lra | intros x _; unfold Hval; ring ]).
    rewrite E1, (RiemannInt_P13 prF (sin_pow_RI (S (S n))) prsum).
    rewrite (int_scal (sin_pow n) (INR (S n)) (cont_sin_pow n) (sin_pow_RI n) prF).
    unfold Wallis; ring. }
  rewrite Hlin in Hftc.
  assert (Hne : INR (S (S n)) <> 0) by (rewrite S_INR; pose proof (pos_INR (S n)); lra).
  assert (Hkey : INR (S (S n)) * Wallis (S (S n)) = INR (S n) * Wallis n) by lra.
  apply (Rmult_eq_reg_l (INR (S (S n)))); [ | exact Hne ].
  replace (INR (S (S n)) * (INR (S n) / INR (S (S n)) * Wallis n)) with (INR (S n) * Wallis n)
    by (field; exact Hne).
  exact Hkey.
Qed.

(* ----------------------------------------------------------------- *)
(*  Nonnegativity.                                                    *)
(* ----------------------------------------------------------------- *)

Lemma Wallis_nonneg : forall n, 0 <= Wallis n.
Proof.
  intro n; unfold Wallis; pose proof PI2_RGT_0 as Hpi.
  assert (pr0 : Riemann_integrable (fun _ : R => 0) 0 (PI / 2))
    by (apply continuity_implies_RiemannInt;
        [ lra | intros x _; apply continuity_pt_const; intros a b; reflexivity ]).
  assert (H0 : RiemannInt pr0 = 0)
    by (transitivity (0 * (PI / 2 - 0)); [ exact (RiemannInt_P15 pr0) | ring ]).
  apply Rle_trans with (RiemannInt pr0); [ rewrite H0; apply Rle_refl | ].
  apply RiemannInt_P19; [ lra | intros x [Hxa Hxb]; unfold sin_pow ].
  apply pow_le; left; apply sin_gt_0; [ exact Hxa | pose proof PI_RGT_0; lra ].
Qed.

Print Assumptions Wallis_rec.
Print Assumptions Wallis_0.
Print Assumptions Wallis_1.

(* ================================================================= *)
(*  END WallisIntegral.v                                             *)
(*  W₀=π/2, W₁=1, W_{n+2}=((n+1)/(n+2))Wₙ, Wₙ≥0.  Next: the Wallis    *)
(*  product and √n·Wₙ → √(π/2), then the improper integral and the    *)
(*  Gaussian squeeze toward ∫_ℝ e^{−x²} = √π.                         *)
(* ================================================================= *)
