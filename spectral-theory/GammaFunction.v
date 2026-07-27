(* ================================================================= *)
(*  GammaFunction.v                                                 *)
(*                                                                    *)
(*  THE GAMMA PILLAR (integer case): the FACTORIAL INTEGRAL           *)
(*      Γ(n+1) = ∫_0^∞ tⁿ e^(−t) dt = n!.                            *)
(*                                                                    *)
(*  One of the two pillars of the ζ functional equation (the other,  *)
(*  Poisson/theta, needs Fourier — out of scope stdlib-only).  Built  *)
(*  WITHOUT integration-by-parts, via the RECURSIVE antiderivative    *)
(*      A_n(t) = −tⁿe^(−t) + n·A_{n−1}(t),   A_n' = tⁿe^(−t)          *)
(*  (`Aanti`, `Aanti_deriv`), so the Newton integral over [0,N] is    *)
(*  `A_n(N) − A_n(0)` (`gam_newton`, `newton_val`), with              *)
(*  `A_n(0) = −n!` (`Aanti_0`) and `A_n(N) → 0` (`Aanti_lim0`, from    *)
(*  the growth bound Nᵏe^(−N)→0, itself from exp x ≥ (x/(k+1))^(k+1)  *)
(*  via `exp_ineq1` — no Taylor-series library needed).  Hence        *)
(*      gamma_n_eq_factorial : Un_cv (∫_0^N tⁿe^(−t)dt) (n!).         *)
(*                                                                    *)
(*  HONEST SCOPE: this is the INTEGER Gamma (t^n, nat power).  The     *)
(*  general real recurrence Γ(s+1)=s·Γ(s) needs `Rpower` + a poly≤exp *)
(*  bound for real s, and Γ(½)=√π needs the Gaussian integral         *)
(*  ∫e^(−x²)=√π — both beyond stdlib.  This does NOT give the         *)
(*  functional equation (which also needs Poisson/theta).            *)
(*  Over the classical `Reals` (quarantined).                        *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia Arith FunctionalExtensionality.
Local Open Scope R_scope.

Lemma exp_neg_deriv : forall t, derivable_pt_lim (fun x => exp (- x)) t (- exp (- t)).
Proof.
  intro t. replace (- exp (- t)) with (exp (- t) * -1) by ring.
  apply (derivable_pt_lim_comp (fun x => - x) exp t (-1) (exp (- t))).
  - replace (-1) with (- (1)) by ring. apply derivable_pt_lim_opp, derivable_pt_lim_id.
  - apply derivable_pt_lim_exp.
Qed.

(* recursive antiderivative of t^n e^{-t}:  A_n = -t^n e^{-t} + n A_{n-1} *)
Fixpoint Aanti (n : nat) (t : R) : R :=
  match n with
  | O => - exp (- t)
  | S m => - (t ^ (S m) * exp (- t)) + INR (S m) * Aanti m t
  end.

Lemma Aanti_deriv : forall n t, derivable_pt_lim (Aanti n) t (t ^ n * exp (- t)).
Proof.
  induction n as [|m IH]; intro t.
  - replace (Aanti 0) with (fun x => - exp (- x)) by reflexivity.
    replace (t ^ 0 * exp (- t)) with (- (- exp (- t))) by (simpl; ring).
    apply derivable_pt_lim_opp, exp_neg_deriv.
  - replace (Aanti (S m))
      with (plus_fct (fun x => - (x ^ (S m) * exp (- x))) (mult_real_fct (INR (S m)) (Aanti m)))
      by (apply functional_extensionality; intro x; unfold plus_fct, mult_real_fct; reflexivity).
    replace (t ^ S m * exp (- t))
      with ((- ((INR (S m) * t ^ Init.Nat.pred (S m)) * exp (- t) + t ^ S m * (- exp (- t))))
            + INR (S m) * (t ^ m * exp (- t))) by (simpl; ring).
    apply derivable_pt_lim_plus.
    + apply derivable_pt_lim_opp.
      apply (derivable_pt_lim_mult (fun x => x ^ S m) (fun x => exp (- x)) t).
      * apply derivable_pt_lim_pow.
      * apply exp_neg_deriv.
    + apply derivable_pt_lim_scal, IH.
Qed.

Lemma Aanti_0 : forall n, Aanti n 0 = - INR (fact n).
Proof.
  induction n as [|m IH]; [ cbn [Aanti fact]; rewrite Ropp_0, exp_0, INR_1; ring | ].
  cbn [Aanti]. rewrite IH, pow_i by lia. rewrite fact_simpl, mult_INR. ring.
Qed.

(* ---- limit toolkit ---- *)
Lemma Un_cv_ext : forall u v L, (forall n, u n = v n) -> Un_cv u L -> Un_cv v L.
Proof. intros u v L He Hu eps Heps; destruct (Hu eps Heps) as [N HN]; exists N; intros n Hn; rewrite <- He; apply HN; exact Hn. Qed.
Lemma Un_cv_const : forall c : R, Un_cv (fun _ => c) c.
Proof. intros c eps He; exists 0%nat; intros n _; unfold R_dist; rewrite Rminus_diag, Rabs_R0; exact He. Qed.
Lemma Un_cv_opp : forall u L, Un_cv u L -> Un_cv (fun n => - u n) (- L).
Proof. intros u L Hu eps Heps; destruct (Hu eps Heps) as [N HN]; exists N; intros n Hn; unfold R_dist in *; replace (- u n - - L) with (- (u n - L)) by ring; rewrite Rabs_Ropp; apply HN; exact Hn. Qed.
Lemma Un_cv_squeeze0 : forall (a b : nat -> R), (exists N0, forall n, (N0 <= n)%nat -> 0 <= a n <= b n) -> Un_cv b 0 -> Un_cv a 0.
Proof.
  intros a b [N0 Hbnd] Hb eps Heps; destruct (Hb eps Heps) as [N1 HN1].
  exists (Nat.max N0 N1); intros n Hn.
  assert (H0 : (N0 <= n)%nat) by lia; assert (H1 : (N1 <= n)%nat) by lia.
  destruct (Hbnd n H0) as [Hlo Hhi]; specialize (HN1 n H1); unfold R_dist in *.
  rewrite Rminus_0_r in *. rewrite (Rabs_right (a n)) by (apply Rle_ge; lra).
  apply Rle_lt_trans with (b n); [ lra | apply Rle_lt_trans with (Rabs (b n)); [ apply Rle_abs | exact HN1 ] ].
Qed.

(* ---- growth: exp x >= (x/(k+1))^(k+1), hence N^k e^{-N} -> 0 ---- *)
Lemma exp_nat_pow : forall n y, exp (INR n * y) = (exp y) ^ n.
Proof.
  induction n as [|n IH]; intro y; cbn [pow].
  - replace (INR 0 * y) with 0 by (simpl; ring); apply exp_0.
  - rewrite S_INR, Rmult_plus_distr_r, Rmult_1_l, exp_plus, IH; ring.
Qed.
Lemma exp_ge_id : forall z, 0 <= z -> z <= exp z.
Proof.
  intros z Hz; destruct (Req_dec z 0) as [->|Hne]; [ rewrite exp_0; lra | pose proof (exp_ineq1 z Hne); lra ].
Qed.
Lemma exp_lb : forall k x, 0 <= x -> (x / INR (S k)) ^ (S k) <= exp x.
Proof.
  intros k x Hx.
  assert (Hk : 0 < INR (S k)) by (apply lt_0_INR; lia).
  assert (Hz : 0 <= x / INR (S k)) by (apply Rle_mult_inv_pos; [ exact Hx | exact Hk ]).
  replace (exp x) with ((exp (x / INR (S k))) ^ (S k)).
  2:{ rewrite <- exp_nat_pow; f_equal; field; lra. }
  apply pow_incr; split; [ exact Hz | apply exp_ge_id; exact Hz ].
Qed.
Lemma Un_cv_C_over_N : forall C, Un_cv (fun N => C / INR N) 0.
Proof.
  intros C eps He; destruct (INR_unbounded (Rabs C / eps)) as [N1 HN1].
  exists (Nat.max 1 N1); intros n Hn.
  assert (Hn1 : (1 <= n)%nat) by lia. assert (Hn2 : (N1 <= n)%nat) by lia.
  assert (Hpos : 0 < INR n) by (apply lt_0_INR; lia).
  unfold R_dist; rewrite Rminus_0_r; unfold Rdiv;
    rewrite Rabs_mult, (Rabs_right (/ INR n)) by (left; apply Rinv_0_lt_compat; exact Hpos).
  assert (Hkey : Rabs C < eps * INR n).
  { apply Rlt_le_trans with (eps * INR N1); [ | apply Rmult_le_compat_l; [ lra | apply le_INR; lia ] ].
    apply (Rmult_lt_reg_l (/ eps)); [ apply Rinv_0_lt_compat; exact He | ].
    replace (/ eps * (eps * INR N1)) with (INR N1) by (field; lra).
    replace (/ eps * Rabs C) with (Rabs C / eps) by (unfold Rdiv; ring).
    exact HN1. }
  apply Rmult_lt_reg_r with (INR n); [ exact Hpos | ].
  rewrite Rmult_assoc, Rinv_l, Rmult_1_r by lra. exact Hkey.
Qed.

Lemma pow_div : forall a b n, b <> 0 -> (a / b) ^ n = a ^ n / b ^ n.
Proof.
  intros a b n Hb; induction n as [|n IH]; simpl; [ field; exact Hb | ].
  rewrite IH; field; split; [ apply pow_nonzero; exact Hb | exact Hb ].
Qed.
Lemma exp_lb2 : forall k x, 0 <= x -> x ^ (S k) / INR (S k) ^ (S k) <= exp x.
Proof. intros k x Hx; rewrite <- pow_div by (apply not_0_INR; lia); apply exp_lb; exact Hx. Qed.

Lemma poly_exp_cv0 : forall k, Un_cv (fun N => INR N ^ k * exp (- INR N)) 0.
Proof.
  intro k. apply (Un_cv_squeeze0 _ (fun N => INR (S k) ^ (S k) * / INR N)).
  - exists 1%nat; intros N HN.
    assert (HM : 1 <= INR N) by (replace 1 with (INR 1) by (simpl; ring); apply le_INR; lia).
    assert (Hk : 0 < INR (S k)) by (apply lt_0_INR; lia).
    split.
    + apply Rmult_le_pos; [ apply pow_le; lra | left; apply exp_pos ].
    + rewrite exp_Ropp.
      apply Rle_trans with (INR N ^ k * / (INR N ^ (S k) / INR (S k) ^ (S k))).
      * apply Rmult_le_compat_l; [ apply pow_le; lra | ].
        apply Rinv_le_contravar; [ apply Rdiv_lt_0_compat; apply pow_lt; lra | apply exp_lb2; lra ].
      * rewrite <- (tech_pow_Rmult (INR N) k).
        apply Req_le; field; repeat split; apply Rgt_not_eq; try apply pow_lt; lra.
  - apply (Un_cv_C_over_N (INR (S k) ^ (S k))).
Qed.

Lemma Aanti_lim0 : forall n, Un_cv (fun N => Aanti n (INR N)) 0.
Proof.
  induction n as [|m IH].
  - apply (Un_cv_ext (fun N => - (INR N ^ 0 * exp (- INR N)))).
    + intro N; cbn [Aanti]; simpl (INR N ^ 0); ring.
    + replace 0 with (- 0) by ring; apply Un_cv_opp, poly_exp_cv0.
  - apply (Un_cv_ext (fun N => - (INR N ^ (S m) * exp (- INR N)) + INR (S m) * Aanti m (INR N))).
    + intro N; cbn [Aanti]; ring.
    + replace 0 with (- 0 + INR (S m) * 0) by ring; apply CV_plus.
      * apply Un_cv_opp, poly_exp_cv0.
      * apply (CV_mult (fun _ => INR (S m)) (fun N => Aanti m (INR N)) (INR (S m)) 0);
          [ apply Un_cv_const | exact IH ].
Qed.

Definition gam (n : nat) (t : R) : R := t ^ n * exp (- t).
Lemma gam_newton : forall n A, 0 <= A -> Newton_integrable (gam n) 0 A.
Proof.
  intros n A HA; exists (Aanti n); left; split; [ | exact HA ].
  intros x Hx; exists (exist _ (gam n x) (Aanti_deriv n x)); reflexivity.
Defined.
Lemma newton_val : forall n A (HA : 0 <= A),
  NewtonInt (gam n) 0 A (gam_newton n A HA) = Aanti n A - Aanti n 0.
Proof. intros n A HA; unfold NewtonInt, gam_newton; reflexivity. Qed.

Theorem gamma_factorial : forall n, Un_cv (fun N => Aanti n (INR N) - Aanti n 0) (INR (fact n)).
Proof.
  intro n. apply (Un_cv_ext (fun N => Aanti n (INR N) + (- Aanti n 0))); [ intro N; ring | ].
  replace (INR (fact n)) with (0 + (- Aanti n 0)) by (rewrite Aanti_0; ring).
  apply CV_plus; [ apply Aanti_lim0 | apply Un_cv_const ].
Qed.

(* The factorial integral: ∫_0^N t^n e^{-t} dt  →  n!  (Γ(n+1) = n!). *)
Theorem gamma_n_eq_factorial : forall n,
  Un_cv (fun N => NewtonInt (gam n) 0 (INR N) (gam_newton n (INR N) (pos_INR N))) (INR (fact n)).
Proof.
  intro n; apply (Un_cv_ext (fun N => Aanti n (INR N) - Aanti n 0));
    [ intro N; rewrite newton_val; reflexivity | apply gamma_factorial ].
Qed.

Print Assumptions gamma_n_eq_factorial.

(* the integer shadow of the recurrence  Γ(s+1) = s·Γ(s) *)
Corollary gamma_recurrence : forall n, INR (fact (S n)) = INR (S n) * INR (fact n).
Proof. intro n; rewrite fact_simpl, mult_INR; reflexivity. Qed.

(* ================================================================= *)
(*  END GammaFunction.v.  Γ(n+1) = ∫_0^∞ tⁿe^(−t)dt = n!  (integer). *)
(* ================================================================= *)
