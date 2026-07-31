(* ================================================================= *)
(*  GaussPeriodInt.v  —  Poisson→θ, Phase P2 (step 4): the combine.    *)
(*                                                                    *)
(*    period_integral : ∫_{−(S M)}^{S M} e^{−πtu²}cos(2πum) du          *)
(*                     = ∫_0^1 (gTheta_partial t x M)·cos(2πxm) dx      *)
(*                                                                    *)
(*  Chasles (GaussChasles) splits ∫_{−N}^{N} into the 2N unit cells;    *)
(*  unit_shift / unit_shift_neg pull each cell back to ∫_0^1 of a       *)
(*  shifted Gaussian; RInt_sum collects the sums into one ∫_0^1; and     *)
(*  the shifted sums recombine to gRp/gLp (sum_eq + scal_sum, matching   *)
(*  (x+n)²t = t(x+n)²).  No new axioms (classical Reals only).          *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import GaussSubst GaussPeriodization GaussPeriodCoeff GaussPeriodSum GaussChasles.
Open Scope R_scope.

(* the right/left cell integrands (unit_shift / unit_shift_neg outputs) *)
Definition Rc (t : R) (m n : nat) : R -> R :=
  fun x => exp (- (PI * t * (x + INR n) ^ 2)) * cos (2 * PI * x * INR m).
Definition Lc (t : R) (m n : nat) : R -> R :=
  fun x => exp (- (PI * t * (x - INR (S n)) ^ 2)) * cos (2 * PI * x * INR m).

Lemma cont_Rc : forall t m n, continuity (Rc t m n).
Proof.
  intros t m n x; unfold Rc; apply continuity_pt_mult.
  - apply (continuity_pt_comp (fun y => - (PI * t * (y + INR n) ^ 2)) exp x).
    + apply (continuity_pt_opp (fun y => PI * t * (y + INR n) ^ 2) x).
      apply (continuity_pt_scal (fun y => (y + INR n) ^ 2) (PI * t) x).
      apply (cont_pow (fun y => y + INR n) 2); intro y; apply continuity_pt_plus;
        [ apply cont_id | apply continuity_pt_const; intros a b; reflexivity ].
    + apply derivable_continuous_pt; exists (exp (- (PI * t * (x + INR n) ^ 2))); apply derivable_pt_lim_exp.
  - apply (continuity_pt_comp (fun y => 2 * PI * y * INR m) cos x); [ | apply continuity_cos ].
    apply continuity_pt_mult; [ | apply continuity_pt_const; intros a b; reflexivity ].
    apply (continuity_pt_scal (fun y => y) (2 * PI) x); apply cont_id.
Qed.

Lemma cont_Lc : forall t m n, continuity (Lc t m n).
Proof.
  intros t m n x; unfold Lc; apply continuity_pt_mult.
  - apply (continuity_pt_comp (fun y => - (PI * t * (y - INR (S n)) ^ 2)) exp x).
    + apply (continuity_pt_opp (fun y => PI * t * (y - INR (S n)) ^ 2) x).
      apply (continuity_pt_scal (fun y => (y - INR (S n)) ^ 2) (PI * t) x).
      apply (cont_pow (fun y => y - INR (S n)) 2); intro y; apply continuity_pt_minus;
        [ apply cont_id | apply continuity_pt_const; intros a b; reflexivity ].
    + apply derivable_continuous_pt; exists (exp (- (PI * t * (x - INR (S n)) ^ 2))); apply derivable_pt_lim_exp.
  - apply (continuity_pt_comp (fun y => 2 * PI * y * INR m) cos x); [ | apply continuity_cos ].
    apply continuity_pt_mult; [ | apply continuity_pt_const; intros a b; reflexivity ].
    apply (continuity_pt_scal (fun y => y) (2 * PI) x); apply cont_id.
Qed.

Lemma Rc_int : forall t m n a b, Riemann_integrable (Rc t m n) a b.
Proof.
  intros; destruct (Rle_lt_dec a b);
    [ apply continuity_implies_RiemannInt; [ assumption | intros x _; apply cont_Rc ]
    | apply RiemannInt_P1; apply continuity_implies_RiemannInt; [ lra | intros x _; apply cont_Rc ] ].
Qed.

Lemma Lc_int : forall t m n a b, Riemann_integrable (Lc t m n) a b.
Proof.
  intros; destruct (Rle_lt_dec a b);
    [ apply continuity_implies_RiemannInt; [ assumption | intros x _; apply cont_Lc ]
    | apply RiemannInt_P1; apply continuity_implies_RiemannInt; [ lra | intros x _; apply cont_Lc ] ].
Qed.

(* ----------------------------------------------------------------- *)
(*  Reductions of the two halves to ∫_0^1 of a partial sum.          *)
(* ----------------------------------------------------------------- *)

Lemma right_reduction : forall t m M
  (pr : Riemann_integrable (sg t (INR m)) 0 (INR (S M)))
  (prS : Riemann_integrable (fun x => sum_f_R0 (fun n => Rc t m n x) M) 0 1),
  RiemannInt pr = RiemannInt prS.
Proof.
  intros t m M pr prS.
  transitivity (sum_f_R0 (fun n => RiemannInt (sg_int t (INR m) (INR n) (INR n + 1))) M);
    [ apply (chasles_R t m M pr) | ].
  transitivity (sum_f_R0 (fun n => RiemannInt (Rc_int t m n 0 1)) M).
  - apply sum_eq; intros i _;
      exact (unit_shift t m i (sg_int t (INR m) (INR i) (INR i + 1)) (Rc_int t m i 0 1)).
  - symmetry; exact (RInt_sum (fun n => Rc t m n) 0 1 (fun n => cont_Rc t m n) ltac:(lra) M prS (fun n => Rc_int t m n 0 1)).
Qed.

Lemma left_reduction : forall t m M
  (pr : Riemann_integrable (sg t (INR m)) (- INR (S M)) 0)
  (prS : Riemann_integrable (fun x => sum_f_R0 (fun n => Lc t m n x) M) 0 1),
  RiemannInt pr = RiemannInt prS.
Proof.
  intros t m M pr prS.
  transitivity (sum_f_R0 (fun n => RiemannInt (sg_int t (INR m) (- INR (S n)) (- INR n))) M);
    [ apply (chasles_L t m M pr) | ].
  transitivity (sum_f_R0 (fun n => RiemannInt (Lc_int t m n 0 1)) M).
  - apply sum_eq; intros i _.
    assert (E : - INR i = - INR (S i) + 1) by (rewrite S_INR; ring).
    transitivity (RiemannInt (sg_int t (INR m) (- INR (S i)) (- INR (S i) + 1))).
    + generalize (sg_int t (INR m) (- INR (S i)) (- INR (S i) + 1)); rewrite <- E; intro p; apply RiemannInt_P5.
    + exact (unit_shift_neg t m (S i) (sg_int t (INR m) (- INR (S i)) (- INR (S i) + 1)) (Lc_int t m i 0 1)).
  - symmetry; exact (RInt_sum (fun n => Lc t m n) 0 1 (fun n => cont_Lc t m n) ltac:(lra) M prS (fun n => Lc_int t m n 0 1)).
Qed.

(* ----------------------------------------------------------------- *)
(*  The shifted sums recombine to gRp / gLp.                         *)
(* ----------------------------------------------------------------- *)

Lemma sum_Rc_eq : forall t m M x,
  sum_f_R0 (fun n => Rc t m n x) M = cos (2 * PI * x * INR m) * gRp t x M.
Proof.
  intros t m M x; unfold gRp; rewrite scal_sum; apply sum_eq; intros i _; unfold Rc, gR.
  replace (PI * t * (x + INR i) ^ 2) with (PI * (x + INR i) ^ 2 * t) by ring; reflexivity.
Qed.

Lemma sum_Lc_eq : forall t m M x,
  sum_f_R0 (fun n => Lc t m n x) M = cos (2 * PI * x * INR m) * gLp t x M.
Proof.
  intros t m M x; unfold gLp; rewrite scal_sum; apply sum_eq; intros i _; unfold Lc, gL.
  replace (PI * t * (x - INR (S i)) ^ 2) with (PI * (x - INR (S i)) ^ 2 * t) by ring; reflexivity.
Qed.

(* ----------------------------------------------------------------- *)
(*  The combine.                                                     *)
(* ----------------------------------------------------------------- *)

Lemma period_integral : forall t m M
  (pr : Riemann_integrable (sg t (INR m)) (- INR (S M)) (INR (S M)))
  (prT : Riemann_integrable (fun x => gTheta_partial t x M * cos (2 * PI * x * INR m)) 0 1),
  RiemannInt pr = RiemannInt prT.
Proof.
  intros t m M pr prT.
  assert (Hab : - INR (S M) <= INR (S M)) by (pose proof (pos_INR (S M)); lra).
  pose proof (RiemannInt_P26 (sg_int t (INR m) (- INR (S M)) 0) (sg_int t (INR m) 0 (INR (S M))) pr) as HP.
  assert (prSR : Riemann_integrable (fun x => sum_f_R0 (fun n => Rc t m n x) M) 0 1)
    by (apply continuity_implies_RiemannInt; [ lra | intros x _; apply cont_sum; intro n; apply cont_Rc ]).
  assert (prSL : Riemann_integrable (fun x => sum_f_R0 (fun n => Lc t m n x) M) 0 1)
    by (apply continuity_implies_RiemannInt; [ lra | intros x _; apply cont_sum; intro n; apply cont_Lc ]).
  rewrite <- HP.
  rewrite (right_reduction t m M (sg_int t (INR m) 0 (INR (S M))) prSR).
  rewrite (left_reduction t m M (sg_int t (INR m) (- INR (S M)) 0) prSL).
  assert (prSum : Riemann_integrable
                    (fun x => sum_f_R0 (fun n => Lc t m n x) M + 1 * sum_f_R0 (fun n => Rc t m n x) M) 0 1)
    by (apply continuity_implies_RiemannInt; [ lra | intros x _; apply continuity_pt_plus;
        [ apply cont_sum; intro n; apply cont_Lc
        | apply (continuity_pt_scal (fun y => sum_f_R0 (fun n => Rc t m n y) M) 1 x);
          apply cont_sum; intro n; apply cont_Rc ] ]).
  pose proof (RiemannInt_P13 prSL prSR prSum) as HP13.
  assert (HTeq : RiemannInt prT = RiemannInt prSum)
    by (apply RiemannInt_P18; [ lra | intros x _; rewrite sum_Rc_eq, sum_Lc_eq;
        unfold gTheta_partial; ring ]).
  rewrite HTeq, HP13; ring.
Qed.

Print Assumptions period_integral.

(* ================================================================= *)
(*  END GaussPeriodInt.v (P2 step 4)                                *)
(*  ∫_{−(S M)}^{S M} e^{−πtu²}cos(2πum) = ∫_0^1 (gTheta_partial t x M)  *)
(*  ·cos(2πxm).  Next: uniform convergence gTheta_partial → gauss_theta *)
(*  gives ∫_0^1 (partial)·cos → c_k, and P1 gives c_k = (1/√t)e^{−πk²/t}.*)
(* ================================================================= *)
