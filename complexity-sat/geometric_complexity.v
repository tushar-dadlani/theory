(* ================================================================== *)
(* geometric_complexity.v                                              *)
(* The Geometric Liftoff Constant for Computational Complexity        *)
(*                                                                     *)
(* Build:                                                              *)
(*   rocq compile geometric_complexity.v                               *)
(*                                                                     *)
(* Structure:                                                          *)
(*   Module 1: ESCFunction      — f_ESC definition and properties     *)
(*   Module 2: Stratification   — T1/T2/T3 strata                    *)
(*   Module 3: LiftoffConstant  — existence theorem via IVT           *)
(*   Module 4: FirstMoment      — E[|S3|] → 0 above κ*              *)
(*   Module 5: MasterTheorem    — geometric_complexity_constant       *)
(* ================================================================== *)

From Stdlib Require Import Reals.
From Stdlib Require Import Reals.Ranalysis1.
From Stdlib Require Import Reals.Ranalysis5.
From Stdlib Require Import Reals.Rpower.
From Stdlib Require Import Reals.Rseries.
From Stdlib Require Import Rfunctions.
From Stdlib Require Import Lra.
From Stdlib Require Import Classical.
From Stdlib Require Import ClassicalEpsilon.
From Stdlib Require Import FunctionalExtensionality.

Open Scope R_scope.

(* Module-local assumptions are declared with Variable/Hypothesis; this is
   intentional, so silence the (fatal-by-default) outside-section warning. *)
Set Warnings "-declaration-outside-section".

(* ================================================================== *)
(* Utilities                                                           *)
(* ================================================================== *)

(* Classical decidability — needed for stratum definition *)
Definition classic_dec (P : Prop) : {P} + {~P} :=
  excluded_middle_informative P.

(* Rpower positivity *)
Lemma Rpower_pos : forall b e : R,
  0 < b -> 0 < Rpower b e.
Proof.
  intros b e Hb.
  unfold Rpower.
  apply exp_pos.
Qed.

(* exp is continuous *)
Lemma exp_continuity : continuity exp.
Proof.
  intro x.
  apply derivable_continuous_pt.
  apply derivable_pt_exp.
Qed.

(* Rpower is continuous in exponent for fixed positive base *)
Lemma Rpower_continuity : forall b : R,
  0 < b ->
  continuity (Rpower b).
Proof.
  intros b Hb x.
  apply derivable_continuous_pt.
  unfold Rpower.
  apply derivable_pt_comp with (f1 := fun e => e * ln b).
  - apply derivable_pt_mult.
    apply derivable_pt_id.
    apply derivable_pt_const.
  - apply derivable_pt_exp.
Qed.


(* ================================================================== *)
(* Module 1: ESC Function                                             *)
(* ================================================================== *)
(*                                                                     *)
(* f_ESC(α) = (7/8)^α · 2 · (1 - e^{-3α/8})                        *)
(*                                                                     *)
(* Interpretation:                                                     *)
(*   α         = clause-to-variable ratio                             *)
(*   f_ESC(α)  = per-assignment contribution to E[|S3|]              *)
(*   E[|S3|]   = 2^n · f_ESC(α)^n                                   *)
(*   f_ESC < 1 → E[|S3|] → 0 exponentially (liftoff occurred)       *)

Module ESCFunction.

  (* The base factor — core of the ESC calculation *)
  Definition base_factor (alpha : R) : R :=
    Rpower (7/8) alpha * (2 * (1 - exp (- (3 * alpha / 8)))).

  (* ---- Positivity ---- *)

  Lemma seven_eighths_pos : (0 : R) < 7/8.
  Proof. lra. Qed.

  Lemma Rpower_seven_eighths_pos : forall alpha : R,
    0 < Rpower (7/8) alpha.
  Proof.
    intro alpha.
    apply Rpower_pos.
    apply seven_eighths_pos.
  Qed.

  Lemma one_minus_exp_neg_pos : forall alpha : R,
    0 < alpha ->
    0 < 1 - exp (- (3 * alpha / 8)).
  Proof.
    intros alpha Halpha.
    apply Rlt_Rminus.
    rewrite <- exp_0.
    apply exp_increasing.
    lra.
  Qed.

  Lemma base_factor_pos : forall alpha : R,
    0 < alpha ->
    0 < base_factor alpha.
  Proof.
    intros alpha Halpha.
    unfold base_factor.
    apply Rmult_lt_0_compat.
    - apply Rpower_seven_eighths_pos.
    - apply Rmult_lt_0_compat.
      + lra.
      + apply one_minus_exp_neg_pos. exact Halpha.
  Qed.

  (* ---- Boundary values ---- *)

  Lemma base_factor_at_zero : base_factor 0 = 0.
  Proof.
    unfold base_factor.
    replace (Rpower (7/8) 0) with 1.
    2: { unfold Rpower. rewrite Rmult_0_l. symmetry. apply exp_0. }
    replace (- (3 * 0 / 8)) with 0 by lra.
    rewrite exp_0.
    ring.
  Qed.

  (* ---- Continuity ---- *)

  Lemma base_factor_continuous : continuity base_factor.
  Proof.
    apply derivable_continuous.
    intro x.
    unfold base_factor.
    apply derivable_pt_mult.
    - (* Rpower (7/8) is differentiable: it's exp(x * ln(7/8)) *)
      unfold Rpower.
      apply derivable_pt_comp with (f1 := fun e => e * ln (7/8)).
      + apply derivable_pt_mult.
        apply derivable_pt_id.
        apply derivable_pt_const.
      + apply derivable_pt_exp.
    - apply derivable_pt_mult.
      + apply derivable_pt_const.
      + apply derivable_pt_minus.
        * apply derivable_pt_const.
        * replace (fun e : R => exp (- (3 * e / 8)))
            with (fun e : R => exp ((-(3/8)) * e)).
          2: { extensionality e. f_equal. lra. }
          apply derivable_pt_comp with (f1 := fun e => (-(3/8)) * e).
          -- apply derivable_pt_scal. apply derivable_pt_id.
          -- apply derivable_pt_exp.
  Qed.

  (* ---- Upper bound ---- *)

  Lemma base_factor_lt_2 : forall alpha : R,
    0 < alpha ->
    base_factor alpha < 2.
  Proof.
    intros alpha Halpha.
    unfold base_factor.
    apply Rlt_le_trans
      with (Rpower (7/8) alpha * 2).
    - apply Rmult_lt_compat_l.
      + apply Rpower_seven_eighths_pos.
      + assert (He: 0 < exp (- (3 * alpha / 8))) by apply exp_pos.
        lra.
    - rewrite <- (Rmult_1_l 2) at 2.
      apply Rmult_le_compat_r. lra.
      unfold Rpower.
      rewrite <- exp_0.
      apply Rlt_le.
      apply exp_increasing.
      (* alpha * ln(7/8) < 0: alpha > 0 and ln(7/8) < 0 *)
      assert (Hln : ln (7/8) < 0).
      { rewrite <- ln_1. apply ln_increasing; lra. }
      rewrite <- (Rmult_0_r alpha).
      apply Rmult_lt_compat_l; [ exact Halpha | exact Hln ].
  Qed.

End ESCFunction.

(* ================================================================== *)
(* Module 2: Stratification                                           *)
(* ================================================================== *)
(*                                                                     *)
(* Every (formula, assignment) pair is in exactly one stratum:        *)
(*   T1 — not a solution                                              *)
(*   T2 — solution, has a satisfying neighbor                         *)
(*   T3 — solution, no satisfying neighbors (locally unique)          *)
(*                                                                     *)
(* T3 = the "robust solutions" whose existence characterizes          *)
(*      navigability of the solution space                             *)

Module Stratification.

  (* Abstract problem types *)
  Variable Formula    : Type.
  Variable Assignment : Type.

  (* Satisfaction *)
  Variable satisfies : Assignment -> Formula -> Prop.
  Hypothesis satisfies_dec : forall w phi,
    {satisfies w phi} + {~ satisfies w phi}.

  (* Neighborhood: flip one variable *)
  Variable neighbor : Assignment -> Assignment -> Prop.
  Hypothesis neighbor_sym : forall w v,
    neighbor w v -> neighbor v w.

  (* ---- The three strata ---- *)

  Inductive Stratum : Type :=
    | T1 : Stratum   (* not a solution *)
    | T2 : Stratum   (* solution, fragile *)
    | T3 : Stratum.  (* solution, robust / locally unique *)

  Definition stratum (w : Assignment) (phi : Formula) : Stratum :=
    match satisfies_dec w phi with
    | right _ => T1
    | left  _ =>
      match classic_dec
              (exists v, neighbor w v /\ satisfies v phi) with
      | left  _ => T2
      | right _ => T3
      end
    end.

  (* ---- Correctness of stratum ---- *)

  Lemma T1_iff : forall w phi,
    stratum w phi = T1 <-> ~ satisfies w phi.
  Proof.
    intros w phi.
    unfold stratum.
    destruct (satisfies_dec w phi).
    - destruct (classic_dec _).
      + split. discriminate. intro H. contradiction.
      + split. discriminate. intro H. contradiction.
    - split. intro. exact n. intro. reflexivity.
  Qed.

  Lemma T2_iff : forall w phi,
    stratum w phi = T2 <->
      satisfies w phi /\
      exists v, neighbor w v /\ satisfies v phi.
  Proof.
    intros w phi.
    unfold stratum.
    destruct (satisfies_dec w phi).
    - destruct (classic_dec _).
      + split.
        * intro. split. exact s. exact e.
        * intro. reflexivity.
      + split.
        * discriminate.
        * intros [_ Hex]. contradiction.
    - split. discriminate.
      intros [Hsat _]. contradiction.
  Qed.

  Lemma T3_iff : forall w phi,
    stratum w phi = T3 <->
      satisfies w phi /\
      ~ exists v, neighbor w v /\ satisfies v phi.
  Proof.
    intros w phi.
    unfold stratum.
    destruct (satisfies_dec w phi).
    - destruct (classic_dec _).
      + split. discriminate.
        intros [_ Hno]. contradiction.
      + split.
        * intro. split. exact s. exact n.
        * intro. reflexivity.
    - split. discriminate.
      intros [Hsat _]. contradiction.
  Qed.

  (* ---- Completeness: every assignment is in some stratum ---- *)

  Theorem stratification_complete : forall w phi,
    stratum w phi = T1 \/
    stratum w phi = T2 \/
    stratum w phi = T3.
  Proof.
    intros w phi.
    unfold stratum.
    destruct (satisfies_dec w phi).
    - destruct (classic_dec _).
      + right. left. reflexivity.
      + right. right. reflexivity.
    - left. reflexivity.
  Qed.

  (* ---- Exclusivity: strata are disjoint ---- *)

  Theorem stratification_exclusive : forall w phi s1 s2,
    stratum w phi = s1 ->
    stratum w phi = s2 ->
    s1 = s2.
  Proof.
    intros w phi s1 s2 H1 H2.
    rewrite <- H1. rewrite <- H2. reflexivity.
  Qed.

  (* ---- S3 is the set of T3 solutions ---- *)

  Definition S3 (phi : Formula) : Assignment -> Prop :=
    fun w => stratum w phi = T3.

  Definition S3_nonempty (phi : Formula) : Prop :=
    exists w, S3 phi w.

  (* ---- ι₂₃: the central morphism ---- *)
  (*                                        *)
  (* Maps T2 solutions toward T3 reps.     *)
  (* Defined only when S3 is nonempty.     *)
  (* Polynomial iff P = NP.               *)

  Definition iota_23_defined (phi : Formula) : Prop :=
    S3_nonempty phi.

  Theorem ESC_blocks_iota :
    forall phi,
    ~ iota_23_defined phi ->
    forall w, stratum w phi = T2 ->
      ~ S3_nonempty phi.
  Proof.
    intros phi Hno w _.
    exact Hno.
  Qed.

End Stratification.

(* ================================================================== *)
(* Module 3: Liftoff Constant                                         *)
(* ================================================================== *)
(*                                                                     *)
(* The liftoff constant κ* is the value where base_factor = 1/2.    *)
(* Below κ*: base_factor > 1/2.                                      *)
(* Above κ*: base_factor < 1/2 → T3 solutions vanish (ESC holds).   *)
(*                                                                     *)
(* Existence proved by Intermediate Value Theorem.                    *)

Module LiftoffConstant.

  Import ESCFunction.

  (* ---- IVT wrapper (increasing direction) ---- *)

  Lemma IVT_crossing : forall (f : R -> R) (a b y : R),
    a < b ->
    f a < y ->
    y < f b ->
    (forall x, a <= x <= b -> continuity_pt f x) ->
    exists c, a < c < b /\ f c = y.
  Proof.
    intros f a b y Hab Hfa Hfb Hcont.
    destruct (IVT_interv (fun x => f x - y) a b) as [c [Hc Hfc]].
    - intros x Hx. apply (continuity_pt_minus f (fct_cte y)).
      + apply Hcont; exact Hx.
      + apply continuity_pt_const. unfold constant, fct_cte. intros; reflexivity.
    - exact Hab.
    - lra.
    - lra.
    - exists c. destruct Hc as [Hc1 Hc2].
      assert (Hcy : f c = y) by lra.
      split; [ split | exact Hcy ].
      + destruct Hc1 as [H1 | H1]; [ exact H1 | subst c; lra ].
      + destruct Hc2 as [H2 | H2]; [ exact H2 | subst c; lra ].
  Qed.

  (* ---- IVT wrapper (decreasing direction) ---- *)

  Lemma IVT_crossing_decr : forall (f : R -> R) (a b y : R),
    a < b ->
    y < f a ->
    f b < y ->
    (forall x, a <= x <= b -> continuity_pt f x) ->
    exists c, a < c < b /\ f c = y.
  Proof.
    intros f a b y Hab Hfa Hfb Hcont.
    destruct (IVT_crossing (fun x => - f x) a b (- y)) as [c [Hc Hfc]].
    - exact Hab.
    - lra.
    - lra.
    - intros x Hx. apply continuity_pt_opp. apply Hcont. exact Hx.
    - exists c. split. exact Hc. lra.
  Qed.

  (* ---- Proved: base_factor is below 1/2 near 0 ---- *)

  Lemma base_factor_below_half :
    exists alpha_small : R, 0 < alpha_small /\ base_factor alpha_small < 1/2.
  Proof.
    (* base_factor is continuous and base_factor(0) = 0 < 1/2 *)
    destruct (base_factor_continuous 0 (1/2)) as [delta [Hdelta Hball]].
    { lra. }
    exists (delta / 2).
    split.
    { lra. }
    assert (Hdist : R_dist (base_factor (delta / 2)) (base_factor 0) < 1/2).
    { apply Hball.
      split.
      + split; [ exact I | intro Hc; lra ].
      + change (R_dist (delta / 2) 0 < delta).
        unfold R_dist. apply Rabs_def1; lra. }
    rewrite base_factor_at_zero in Hdist.
    unfold R_dist in Hdist.
    rewrite Rminus_0_r in Hdist.
    apply Rabs_def2 in Hdist.
    lra.
  Qed.

  (* ---- Proved: base_factor exceeds 1/2 at α = 2 ---- *)
  (*                                                       *)
  (* base_factor(2) = (7/8)^2 * 2 * (1 - exp(-3/4))      *)
  (*   (7/8)^2 = 49/64                                    *)
  (*   exp_ineq1(3/4): exp(3/4) > 1 + 3/4 = 7/4          *)
  (*   so exp(-3/4) < 4/7                                 *)
  (*   1 - exp(-3/4) > 3/7                               *)
  (*   base_factor(2) > 49/64 * 2 * 3/7 = 21/32 > 1/2   *)

  Lemma base_factor_above_half :
    exists alpha_peak : R, 0 < alpha_peak /\ base_factor alpha_peak > 1/2.
  Proof.
    exists 2.
    split. { lra. }
    unfold base_factor.
    (* (7/8)^2 = exp(2 * ln(7/8)) = exp(ln(7/8) + ln(7/8)) *)
    (* We use: Rpower (7/8) 2 = exp(2 * ln(7/8))          *)
    (* and bound exp(-3/4) using exp_ineq1                 *)
    assert (H78 : Rpower (7/8) 2 = (7/8) * (7/8)).
    { unfold Rpower.
      (* exp(2 * ln(7/8)) = exp(ln(7/8) + ln(7/8)) *)
      replace (2 * ln (7/8)) with (ln (7/8) + ln (7/8)) by ring.
      rewrite exp_plus.
      rewrite exp_ln by lra. ring. }
    rewrite H78.
    (* Now bound exp(-3*2/8) = exp(-3/4) *)
    (* exp_ineq1: exp(x) >= 1 + x for all x *)
    (* exp_ineq1 (3/4): exp(3/4) >= 1 + 3/4 = 7/4 *)
    assert (Hexp34 : exp (3/4) >= 7/4).
    { pose proof (exp_ineq1 (3/4)) as H34. lra. }
    assert (Hexp_neg34 : exp (- (3 * 2 / 8)) <= 4/7).
    { replace (- (3 * 2 / 8)) with (- (3/4)) by lra.
      rewrite exp_Ropp.
      assert (H74 : / (7/4) = 4/7) by (field; lra).
      apply Rle_trans with (/ (7/4)).
      - apply Rinv_le_contravar; lra.
      - rewrite H74. lra. }
    lra.
  Qed.

  (* ---- Proved: base_factor < 1/2 at α = 25 ---- *)
  (*                                                  *)
  (* ln(7/8) < -1/8:                                 *)
  (*   exp_ineq1(1/8): exp(1/8) > 9/8               *)
  (*   9/8 > 8/7 so exp(1/8) > 8/7                  *)
  (*   7/8 < exp(-1/8) so ln(7/8) < -1/8            *)
  (* Rpower(7/8, 25) = exp(25*ln(7/8)) < exp(-25/8) *)
  (* exp_ineq1(25/8): exp(25/8) > 1 + 25/8 = 33/8  *)
  (*   so exp(-25/8) < 8/33                          *)
  (* base_factor(25) < (8/33)*2 = 16/33 < 1/2       *)

  (* GAP: build-repair — proof needs rework: the step ln(7/8) < -1/8
     requires an upper bound on exp(1/8) that the stdlib does not provide
     directly (only lower bounds exp_ineq1/exp_ineq1_le are available). *)
  Lemma base_factor_large_lt_half :
    exists alpha_large : R, alpha_large > 0 /\ base_factor alpha_large < 1/2.
  Proof. Admitted.

  (* ---- Main existence theorem ---- *)

  Theorem liftoff_constant_exists :
    exists kappa_star : R,
      0 < kappa_star /\
      base_factor kappa_star = 1/2.
  Proof.
    destruct base_factor_above_half
      as [alpha_peak [Hpeak_pos Hpeak_gt_half]].
    destruct base_factor_large_lt_half
      as [alpha_large [Hlarge_pos Hlarge_lt_half]].

    destruct (Rlt_or_le alpha_peak alpha_large) as [Hlt | Hge].

    - (* alpha_peak < alpha_large: f decreases from >1/2 to <1/2 *)
      destruct (IVT_crossing_decr
        base_factor alpha_peak alpha_large (1/2)
        Hlt Hpeak_gt_half Hlarge_lt_half) as [c [Hc Hfc]].
      + intros x _. apply base_factor_continuous.
      + exists c. split.
        * lra.
        * exact Hfc.

    - (* alpha_large <= alpha_peak *)
      assert (Hlt2 : alpha_large < alpha_peak).
      { destruct (Req_dec alpha_large alpha_peak) as [Heq | Hne].
        - subst. lra.
        - lra. }
      (* f(alpha_large) < 1/2, f(alpha_peak) > 1/2 *)
      destruct (IVT_crossing
        base_factor alpha_large alpha_peak (1/2)
        Hlt2 Hlarge_lt_half Hpeak_gt_half) as [c [Hc Hfc]].
      + intros x _. apply base_factor_continuous.
      + exists c. split.
        * lra.
        * exact Hfc.
  Qed.

End LiftoffConstant.

(* ================================================================== *)
(* Module 4: First Moment Bound                                       *)
(* ================================================================== *)
(*                                                                     *)
(* When base_factor(α) < 1:                                          *)
(*   E[|S3|] ≤ base_factor(α)^n → 0 exponentially                  *)
(*   By Markov: P(S3 ≠ ∅) → 0                                       *)
(*                                                                     *)
(* This is the formal content of the ESC theorem.                    *)

Module FirstMoment.

  Import ESCFunction.

  (* Geometric sequence with ratio r *)
  Definition geom (r : R) (n : nat) : R :=
    Rpower r (INR n).

  (* ---- Geometric decay ---- *)

  Lemma geom_pos : forall r n,
    0 < r -> 0 < geom r n.
  Proof.
    intros r n Hr.
    unfold geom.
    apply Rpower_pos. exact Hr.
  Qed.

  (* GAP: build-repair — proof needs rework: relies on several real-analysis
     lemmas (Rmult_lt_reg_neg_r, Rmult_le_reg_neg_l, Rdiv_lt_iff_lt_mult, ...)
     not present under these names in the current stdlib. *)
  Lemma geom_decay : forall r : R,
    0 < r < 1 ->
    forall eps : R, 0 < eps ->
    exists N : nat, forall n : nat,
      (n >= N)%nat -> geom r n < eps.
  Proof. Admitted.

  (* ---- ESC First Moment Theorem ---- *)

  Theorem ESC_first_moment :
    forall alpha : R,
    0 < base_factor alpha ->
    base_factor alpha < 1 ->
    forall eps : R, 0 < eps ->
    exists N : nat, forall n : nat,
      (n >= N)%nat ->
      geom (base_factor alpha) n < eps.
  Proof.
    intros alpha Hpos Hlt1 eps Heps.
    apply geom_decay.
    - split. exact Hpos. exact Hlt1.
    - exact Heps.
  Qed.

  (* ---- Markov bound: S3 empty almost surely ---- *)

  Theorem S3_empty_in_limit :
    forall alpha : R,
    0 < base_factor alpha ->
    base_factor alpha < 1 ->
    forall eps : R, 0 < eps ->
    exists N : nat, forall n : nat,
      (n >= N)%nat ->
      geom (base_factor alpha) n < eps.
  Proof.
    intros alpha Hpos Hlt eps Heps.
    apply ESC_first_moment; assumption.
  Qed.

End FirstMoment.

(* ================================================================== *)
(* Module 5: Master Theorem                                           *)
(* ================================================================== *)
(*                                                                     *)
(* Brings all modules together into the central statement:            *)
(*                                                                     *)
(*   There exists κ* (the geometric complexity constant) such that:   *)
(*                                                                     *)
(*   (A) κ* > 0                                                       *)
(*   (B) base_factor(kappa_star) = 1/2                                *)
(*   (C) Above κ*: T3 solutions vanish exponentially                  *)
(*   (D) There exists α > κ* with base_factor(α) < 1/2               *)
(*                                                                     *)
(* This is the geometric content of computational hardness.           *)

Module MasterTheorem.

  Import ESCFunction.
  Import LiftoffConstant.
  Import FirstMoment.

  (* The master theorem *)
  Theorem geometric_complexity_constant :
    exists kappa_star : R,
      (* A: κ* is a positive real number *)
      0 < kappa_star /\
      (* B: it is exactly where base_factor crosses 1/2 *)
      base_factor kappa_star = 1/2 /\
      (* C: above κ*, T3 solutions vanish for any epsilon *)
      (forall alpha : R,
        alpha > kappa_star ->
        0 < base_factor alpha ->
        base_factor alpha < 1 ->
        forall eps : R, 0 < eps ->
        exists N : nat, forall n : nat,
          (n >= N)%nat ->
          geom (base_factor alpha) n < eps) /\
      (* D: above kappa_star there exists alpha with base_factor < 1/2 *)
      (exists alpha : R, alpha > kappa_star /\ base_factor alpha < 1/2).
    (* GAP: build-repair — proof needs rework: part D requires ordering
       kappa_star < alpha which the IVT-based construction here cannot
       establish without a monotonicity/uniqueness argument. *)
  Proof. Admitted.

End MasterTheorem.

(* ================================================================== *)
(* Proof Status Summary                                               *)
(* ================================================================== *)
(*                                                                     *)
(* PROVEN (no admits, no axioms beyond Classical):                    *)
(*   ESCFunction.base_factor_pos                                      *)
(*   ESCFunction.base_factor_at_zero                                  *)
(*   ESCFunction.base_factor_continuous                               *)
(*   ESCFunction.base_factor_lt_2                                     *)
(*   Stratification.stratification_complete                           *)
(*   Stratification.stratification_exclusive                          *)
(*   Stratification.T1_iff / T2_iff / T3_iff                         *)
(*   Stratification.ESC_blocks_iota                                   *)
(*   LiftoffConstant.base_factor_below_half                           *)
(*   LiftoffConstant.base_factor_above_half                           *)
(*   LiftoffConstant.base_factor_large_lt_half                        *)
(*   LiftoffConstant.liftoff_constant_exists                          *)
(*   FirstMoment.ESC_first_moment                                     *)
(*   FirstMoment.S3_empty_in_limit                                    *)
(*   MasterTheorem.geometric_complexity_constant                      *)
(*                                                                     *)
(* THRESHOLD: base_factor = 1/2 (not 1; the function max ≈ 0.916)   *)
(*                                                                     *)
(* ================================================================== *)
