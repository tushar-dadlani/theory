(* ================================================================= *)
(*  GaussPeriodCoeff.v  —  Poisson→θ, Phase P2 (step 1): the unit-     *)
(*  interval substitution.                                            *)
(*                                                                    *)
(*  The k-th Fourier coefficient of the periodization Θ_t unfolds, cell *)
(*  by cell, to the scaled Gaussian transform (P1).  The atom is:      *)
(*                                                                    *)
(*    unit_shift : ∫_n^{n+1} e^{−πtu²}cos(2πum) du                     *)
(*               = ∫_0^1 e^{−πt(x+n)²}cos(2πxm) dx                     *)
(*                                                                    *)
(*  (m, n natural numbers).  Proof: shift u = x+n (cov_local, g = x+n) *)
(*  turns the left integrand into e^{−πt(x+n)²}cos(2π(x+n)m), and       *)
(*  cos(2π(x+n)m) = cos(2πxm) by 2π-periodicity (cos_period, since      *)
(*  2πnm = 2π·(nm)).  No new axioms (classical Reals only).            *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import GaussSubst LocalCoV.
Open Scope R_scope.

(* the scaled Gaussian cosine integrand *)
Definition sg (t xi u : R) : R := exp (- (PI * t * u ^ 2)) * cos (2 * PI * u * xi).

Lemma cont_sg : forall t xi, continuity (sg t xi).
Proof.
  intros t xi x; unfold sg; apply continuity_pt_mult.
  - apply (continuity_pt_comp (fun u => - (PI * t * u ^ 2)) exp x).
    + apply (continuity_pt_opp (fun u => PI * t * u ^ 2) x).
      apply (continuity_pt_scal (fun u => u ^ 2) (PI * t) x); apply (cont_pow (fun u => u) 2); apply cont_id.
    + apply derivable_continuous_pt; exists (exp (- (PI * t * x ^ 2))); apply derivable_pt_lim_exp.
  - apply (continuity_pt_comp (fun u => 2 * PI * u * xi) cos x); [ | apply continuity_cos ].
    apply continuity_pt_mult; [ | apply continuity_pt_const; intros a b; reflexivity ].
    apply (continuity_pt_scal (fun u => u) (2 * PI) x); apply cont_id.
Qed.

Lemma sg_int : forall t xi a b, Riemann_integrable (sg t xi) a b.
Proof.
  intros t xi a b; destruct (Rle_lt_dec a b) as [H | H].
  - apply continuity_implies_RiemannInt; [ exact H | intros x _; apply cont_sg ].
  - apply RiemannInt_P1; apply continuity_implies_RiemannInt; [ lra | intros x _; apply cont_sg ].
Qed.

(* ----------------------------------------------------------------- *)
(*  The unit-interval substitution.                                  *)
(* ----------------------------------------------------------------- *)

Lemma unit_shift : forall t m n
  (pr1 : Riemann_integrable (sg t (INR m)) (INR n) (INR n + 1))
  (pr2 : Riemann_integrable (fun x => exp (- (PI * t * (x + INR n) ^ 2)) * cos (2 * PI * x * INR m)) 0 1),
  RiemannInt pr1 = RiemannInt pr2.
Proof.
  intros t m n pr1 pr2.
  set (g := fun x => x + INR n).
  set (g' := fun _ : R => 1).
  assert (Hab : (0 : R) <= 1) by lra.
  assert (Hderiv : forall x, 0 <= x <= 1 -> derivable_pt_lim g x (g' x)).
  { intros x _; unfold g, g'; replace 1 with (1 + 0) by ring;
      apply derivable_pt_lim_plus; [ apply derivable_pt_lim_id | apply derivable_pt_lim_const ]. }
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
  (* RiemannInt prL = RiemannInt pr2 (integrand match + cos periodicity) *)
  assert (HL : RiemannInt prL = RiemannInt pr2).
  { apply RiemannInt_P18; [ exact Hab | intros x _; unfold sg, g, g' ].
    rewrite Rmult_1_r; f_equal.
    replace (2 * PI * (x + INR n) * INR m) with (2 * PI * x * INR m + 2 * INR (n * m) * PI)
      by (rewrite mult_INR; ring).
    apply cos_period. }
  (* RiemannInt prR = RiemannInt pr1 (bounds g 0 = INR n, g 1 = INR n + 1) *)
  assert (HR : RiemannInt prR = RiemannInt pr1).
  { assert (Hg0 : g 0 = INR n) by (unfold g; ring).
    assert (Hg1 : g 1 = INR n + 1) by (unfold g; ring).
    revert prR Hcv; rewrite Hg0, Hg1; intros prR Hcv; apply RiemannInt_P5. }
  rewrite <- HL, Hcv; symmetry; exact HR.
Qed.

Print Assumptions unit_shift.

(* ================================================================= *)
(*  END GaussPeriodCoeff.v (P2 step 1)                              *)
(*  ∫_n^{n+1} e^{−πtu²}cos(2πum) = ∫_0^1 e^{−πt(x+n)²}cos(2πxm).  Summing *)
(*  over the cells (Chasles) and matching the GaussPeriodization       *)
(*  partial sum reduces ∫_{−N}^{N} to ∫_0^1 (partial Θ_t)·cos — the     *)
(*  next P2 step, then P1 gives the value c_k = (1/√t)e^{−πk²/t}.       *)
(* ================================================================= *)
