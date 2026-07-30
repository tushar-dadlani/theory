(* ================================================================= *)
(*  GaussSqueeze.v  —  Gaussian part-A stack, step 4a: the POINTWISE   *)
(*  squeeze bounds for the Gaussian.                                  *)
(*                                                                    *)
(*  The elementary bounds that flank e^{−x²} between two n-th powers,  *)
(*  which (after change of variables) become Wallis integrals:        *)
(*                                                                    *)
(*    gauss_lower_pt : (1 − x²/n)ⁿ ≤ e^{−x²}      (for x² ≤ n);        *)
(*    gauss_upper_pt : e^{−x²} ≤ (1 + x²/n)⁻ⁿ     (all x).            *)
(*                                                                    *)
(*  Both from 1 + s ≤ eˢ (exp_ineq1_le) applied at s = ∓x²/n, raised   *)
(*  to the n-th power (pow_incr), using (e^{−t})ⁿ = e^{−nt} = e^{−x²}. *)
(*                                                                    *)
(*  HONEST BOUNDARY.  These are the pointwise inputs.  Turning them    *)
(*  into ∫₀^√n(1−x²/n)ⁿ = √n·W_{2n+1} and ∫₀^∞(1+x²/n)⁻ⁿ = √n·W_{2n−2} *)
(*  needs change of variables (x = √n·sinθ / √n·tanθ — absent from     *)
(*  stdlib RiemannInt) and, for the ∞ side, the improper integral —    *)
(*  the same wall the whole Gaussian route sits against.  No new       *)
(*  axioms (classical Reals only).                                    *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Open Scope R_scope.

(* (eᵃ)ⁿ = e^{n·a} *)
Lemma exp_pow_nat : forall a n, (exp a) ^ n = exp (INR n * a).
Proof.
  intros a n; induction n as [| n IH].
  - simpl; rewrite Rmult_0_l, exp_0; reflexivity.
  - cbn [pow]; rewrite IH, <- exp_plus, S_INR; f_equal; ring.
Qed.

(* ----------------------------------------------------------------- *)
(*  Lower bound:  (1 − x²/n)ⁿ ≤ e^{−x²}   for x² ≤ n.                 *)
(* ----------------------------------------------------------------- *)

Lemma gauss_lower_pt : forall n x, 0 < INR n -> x ^ 2 <= INR n ->
  (1 - x ^ 2 / INR n) ^ n <= exp (- x ^ 2).
Proof.
  intros n x Hn Hx.
  assert (Hx2 : 0 <= x ^ 2) by nra.
  set (t := x ^ 2 / INR n) in *.
  assert (Ht0 : 0 <= t)
    by (unfold t, Rdiv; apply Rmult_le_pos; [ exact Hx2 | left; apply Rinv_0_lt_compat; exact Hn ]).
  assert (Ht1 : t <= 1).
  { apply Rmult_le_reg_r with (INR n); [ exact Hn | ].
    unfold t; rewrite Rmult_1_l; replace (x ^ 2 / INR n * INR n) with (x ^ 2) by (field; lra); exact Hx. }
  assert (Hb : 1 - t <= exp (- t)) by (pose proof (exp_ineq1_le (- t)); lra).
  assert (Hexp : (exp (- t)) ^ n = exp (- x ^ 2))
    by (rewrite exp_pow_nat; f_equal; unfold t; field; lra).
  rewrite <- Hexp; apply pow_incr; split; [ lra | exact Hb ].
Qed.

(* ----------------------------------------------------------------- *)
(*  Upper bound:  e^{−x²} ≤ (1 + x²/n)⁻ⁿ   for all x.                 *)
(* ----------------------------------------------------------------- *)

Lemma gauss_upper_pt : forall n x, 0 < INR n ->
  exp (- x ^ 2) <= / (1 + x ^ 2 / INR n) ^ n.
Proof.
  intros n x Hn.
  assert (Hx2 : 0 <= x ^ 2) by nra.
  set (t := x ^ 2 / INR n) in *.
  assert (Ht0 : 0 <= t)
    by (unfold t, Rdiv; apply Rmult_le_pos; [ exact Hx2 | left; apply Rinv_0_lt_compat; exact Hn ]).
  assert (H1t : 0 < 1 + t) by lra.
  assert (Hb : exp (- t) <= / (1 + t)).
  { pose proof (exp_ineq1_le t) as He; rewrite exp_Ropp; apply Rinv_le_contravar; [ exact H1t | exact He ]. }
  assert (Hexp : (exp (- t)) ^ n = exp (- x ^ 2))
    by (rewrite exp_pow_nat; f_equal; unfold t; field; lra).
  rewrite <- Hexp.
  apply Rle_trans with ((/ (1 + t)) ^ n).
  - apply pow_incr; split; [ left; apply exp_pos | exact Hb ].
  - apply Req_le; rewrite Rinv_pow by lra; reflexivity.
Qed.

Print Assumptions gauss_lower_pt.
Print Assumptions gauss_upper_pt.

(* ================================================================= *)
(*  END GaussSqueeze.v                                               *)
(*  (1−x²/n)ⁿ ≤ e^{−x²} ≤ (1+x²/n)⁻ⁿ.  The pointwise flanks; the       *)
(*  change of variables to √n·W_{2n±} and the improper ∞-integral      *)
(*  are the remaining wall.                                          *)
(* ================================================================= *)
