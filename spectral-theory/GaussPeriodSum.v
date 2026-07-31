(* ================================================================= *)
(*  GaussPeriodSum.v  —  Poisson→θ, Phase P2 (step 2): the two         *)
(*  reusable atoms of the finite-sum assembly.                        *)
(*                                                                    *)
(*    unit_shift_neg : ∫_{−n}^{−n+1} e^{−πtu²}cos(2πum)                 *)
(*                   = ∫_0^1 e^{−πt(x−n)²}cos(2πxm)   (left cells);    *)
(*    cont_sum       : continuity of a finite sum of continuous fns;   *)
(*    RInt_sum       : ∫ (Σ_{n≤M} h_n) = Σ_{n≤M} ∫ h_n                  *)
(*                     (finite-sum linearity of the Riemann integral). *)
(*                                                                    *)
(*  Together with unit_shift (right cells) these reduce ∫_{−N}^{N} of   *)
(*  the scaled Gaussian, cell by cell, to ∫_0^1 (partial Θ_t)·cos.     *)
(*  No new axioms (classical Reals only).                             *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import GaussSubst LocalCoV GaussPeriodCoeff.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  The left-cell substitution u = x − n.                            *)
(* ----------------------------------------------------------------- *)

Lemma unit_shift_neg : forall t m n
  (pr1 : Riemann_integrable (sg t (INR m)) (- INR n) (- INR n + 1))
  (pr2 : Riemann_integrable (fun x => exp (- (PI * t * (x - INR n) ^ 2)) * cos (2 * PI * x * INR m)) 0 1),
  RiemannInt pr1 = RiemannInt pr2.
Proof.
  intros t m n pr1 pr2.
  set (g := fun x => x - INR n).
  set (g' := fun _ : R => 1).
  assert (Hab : (0 : R) <= 1) by lra.
  assert (Hderiv : forall x, 0 <= x <= 1 -> derivable_pt_lim g x (g' x)).
  { intros x _; unfold g, g'; replace 1 with (1 - 0) by ring;
      apply derivable_pt_lim_minus; [ apply derivable_pt_lim_id | apply derivable_pt_lim_const ]. }
  assert (Hcont' : forall x, 0 <= x <= 1 -> continuity_pt g' x)
    by (intros x _; apply continuity_pt_const; intros a b; reflexivity).
  assert (Hmap : forall x, 0 <= x <= 1 -> g 0 <= g x <= g 1) by (intros x [Hx1 Hx2]; unfold g; lra).
  assert (Hfc : forall u, g 0 <= u <= g 1 -> continuity_pt (sg t (INR m)) u)
    by (intros u _; apply cont_sg).
  assert (prL : Riemann_integrable (fun x => sg t (INR m) (g x) * g' x) 0 1).
  { apply continuity_implies_RiemannInt; [ exact Hab | intros x Hx ].
    apply continuity_pt_mult; [ | apply continuity_pt_const; intros a b; reflexivity ].
    apply (continuity_pt_comp g (sg t (INR m)) x);
      [ apply derivable_continuous_pt; exists (g' x); apply Hderiv; exact Hx | apply cont_sg ]. }
  assert (prR : Riemann_integrable (sg t (INR m)) (g 0) (g 1))
    by (apply continuity_implies_RiemannInt; [ unfold g; lra | intros u _; apply cont_sg ]).
  pose proof (cov_local g g' (sg t (INR m)) 0 1 Hab Hderiv Hcont' Hmap Hfc prL prR) as Hcv.
  assert (HL : RiemannInt prL = RiemannInt pr2).
  { apply RiemannInt_P18; [ exact Hab | intros x _; unfold sg, g, g' ].
    rewrite Rmult_1_r; f_equal.
    symmetry; replace (2 * PI * x * INR m) with (2 * PI * (x - INR n) * INR m + 2 * INR (n * m) * PI)
      by (rewrite mult_INR; ring).
    apply cos_period. }
  assert (HR : RiemannInt prR = RiemannInt pr1).
  { assert (Hg0 : g 0 = - INR n) by (unfold g; ring).
    assert (Hg1 : g 1 = - INR n + 1) by (unfold g; ring).
    revert prR Hcv; rewrite Hg0, Hg1; intros prR Hcv; apply RiemannInt_P5. }
  rewrite <- HL, Hcv; symmetry; exact HR.
Qed.

(* ----------------------------------------------------------------- *)
(*  Continuity and integral linearity of finite sums.                *)
(* ----------------------------------------------------------------- *)

Lemma cont_sum : forall (h : nat -> R -> R) M,
  (forall n, continuity (h n)) -> continuity (fun x => sum_f_R0 (fun n => h n x) M).
Proof.
  intros h M Hc; induction M as [| M IH]; intro x; simpl.
  - apply Hc.
  - apply continuity_pt_plus; [ apply IH | apply Hc ].
Qed.

Lemma RInt_sum : forall (h : nat -> R -> R) (a b : R),
  (forall n, continuity (h n)) -> a <= b ->
  forall (M : nat)
         (prS : Riemann_integrable (fun x => sum_f_R0 (fun n => h n x) M) a b)
         (prs : forall n, Riemann_integrable (h n) a b),
  RiemannInt prS = sum_f_R0 (fun n => RiemannInt (prs n)) M.
Proof.
  intros h a b Hcont Hab M; induction M as [| M IH]; intros prS prs.
  - change (RiemannInt prS = RiemannInt (prs 0%nat)).
    apply RiemannInt_P18; [ exact Hab | intros x _; reflexivity ].
  - change (RiemannInt prS = sum_f_R0 (fun n => RiemannInt (prs n)) M + RiemannInt (prs (S M))).
    assert (prSM : Riemann_integrable (fun x => sum_f_R0 (fun n => h n x) M) a b)
      by (apply continuity_implies_RiemannInt; [ exact Hab | intros x _; apply cont_sum; exact Hcont ]).
    assert (prS' : Riemann_integrable (fun x => sum_f_R0 (fun n => h n x) M + 1 * h (S M) x) a b)
      by (apply continuity_implies_RiemannInt; [ exact Hab | intros x _; apply continuity_pt_plus;
          [ apply cont_sum; exact Hcont | apply (continuity_pt_scal (h (S M)) 1 x); apply Hcont ] ]).
    pose proof (RiemannInt_P13 prSM (prs (S M)) prS') as HP.
    assert (HS : RiemannInt prS = RiemannInt prS')
      by (apply RiemannInt_P18; [ exact Hab | intros x _; simpl; ring ]).
    rewrite HS, HP, (IH prSM prs); ring.
Qed.

Print Assumptions unit_shift_neg.
Print Assumptions RInt_sum.

(* ================================================================= *)
(*  END GaussPeriodSum.v (P2 step 2)                                *)
(*  The left-cell substitution and finite-sum integral linearity.      *)
(*  Next: Chasles ∫_{−N}^{N} = Σ cells, then unit_shift/unit_shift_neg  *)
(*  + RInt_sum give ∫_{−N}^{N} sg = ∫_0^1 (gTheta_partial)·cos, and P1   *)
(*  closes c_k = (1/√t)e^{−πk²/t}.                                     *)
(* ================================================================= *)
