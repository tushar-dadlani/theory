(* ================================================================= *)
(*  WallisProduct.v  —  Gaussian part-A stack, step 2: the Wallis     *)
(*  product relation, positivity, and monotonicity.                  *)
(*                                                                    *)
(*  Building on WallisIntegral (Wₙ = ∫₀^{π/2} sinⁿ, W₀=π/2, W₁=1,      *)
(*  W_{n+2} = ((n+1)/(n+2))Wₙ):                                       *)
(*                                                                    *)
(*    Wallis_pos      : 0 < Wₙ            (two-step induction);       *)
(*    Wallis_monotone : W_{n+1} ≤ Wₙ      (sinⁿ⁺¹ ≤ sinⁿ on [0,π/2]); *)
(*    Wallis_product  : (n+1)·Wₙ·W_{n+1} = π/2   (EXACT — telescopes  *)
(*                      through the recurrence from W₀·W₁ = π/2);     *)
(*    Wallis_ratio_bounds : (n+1)/(n+2) ≤ W_{n+1}/Wₙ ≤ 1.             *)
(*                                                                    *)
(*  These squeeze the ratio to 1 and give W_n² ~ π/(2n) — the input    *)
(*  the Gaussian squeeze (part A) converges against.  All on the       *)
(*  bounded interval [0,π/2].  No new axioms (classical Reals only).   *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import WallisIntegral.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  Positivity, by two-step induction through the recurrence.        *)
(* ----------------------------------------------------------------- *)

Lemma Wallis_pos : forall n, 0 < Wallis n.
Proof.
  assert (H : forall n, 0 < Wallis n /\ 0 < Wallis (S n)).
  { induction n as [| n [IH1 IH2]].
    - split; [ rewrite Wallis_0; pose proof PI_RGT_0; lra | rewrite Wallis_1; lra ].
    - split; [ exact IH2 | ].
      rewrite Wallis_rec; apply Rmult_lt_0_compat; [ | exact IH1 ].
      apply Rdiv_lt_0_compat; rewrite S_INR; pose proof (pos_INR n); [ lra | rewrite S_INR; lra ]. }
  intro n; apply (H n).
Qed.

(* ----------------------------------------------------------------- *)
(*  Monotonicity: sinⁿ⁺¹ ≤ sinⁿ on [0,π/2].                          *)
(* ----------------------------------------------------------------- *)

Lemma Wallis_monotone : forall n, Wallis (S n) <= Wallis n.
Proof.
  intro n; unfold Wallis; apply RiemannInt_P19; [ pose proof PI2_RGT_0; lra | intros x [Hxa Hxb] ].
  unfold sin_pow; cbn [pow].
  assert (Hs0 : 0 <= sin x) by (left; apply sin_gt_0; [ exact Hxa | pose proof PI_RGT_0; lra ]).
  assert (Hs1 : sin x <= 1) by (pose proof (SIN_bound x); lra).
  assert (Hp : 0 <= (sin x) ^ n) by (apply pow_le; exact Hs0).
  nra.
Qed.

(* ----------------------------------------------------------------- *)
(*  THE WALLIS PRODUCT:  (n+1)·Wₙ·W_{n+1} = π/2.                      *)
(* ----------------------------------------------------------------- *)

Theorem Wallis_product : forall n, (INR n + 1) * Wallis n * Wallis (S n) = PI / 2.
Proof.
  induction n as [| n IH].
  - rewrite Wallis_0, Wallis_1; replace (INR 0) with 0 by reflexivity; lra.
  - rewrite (Wallis_rec n), !S_INR.
    assert (Hne : INR n + 1 + 1 <> 0) by (pose proof (pos_INR n); lra).
    replace ((INR n + 1 + 1) * Wallis (S n) * ((INR n + 1) / (INR n + 1 + 1) * Wallis n))
      with ((INR n + 1) * Wallis n * Wallis (S n)) by (field; exact Hne).
    exact IH.
Qed.

(* ----------------------------------------------------------------- *)
(*  Ratio bounds:  (n+1)/(n+2) ≤ W_{n+1}/Wₙ ≤ 1.                      *)
(* ----------------------------------------------------------------- *)

Lemma Wallis_ratio_bounds : forall n,
  (INR n + 1) / (INR n + 2) <= Wallis (S n) / Wallis n <= 1.
Proof.
  intro n; pose proof (Wallis_pos n) as Hpn; pose proof (pos_INR n) as Hn0.
  split.
  - apply Rmult_le_reg_r with (Wallis n); [ exact Hpn | ].
    replace (Wallis (S n) / Wallis n * Wallis n) with (Wallis (S n)) by (field; lra).
    replace ((INR n + 1) / (INR n + 2) * Wallis n) with (Wallis (S (S n)))
      by (rewrite (Wallis_rec n), !S_INR; field; lra).
    apply Wallis_monotone.
  - apply Rmult_le_reg_r with (Wallis n); [ exact Hpn | ].
    replace (Wallis (S n) / Wallis n * Wallis n) with (Wallis (S n)) by (field; lra).
    rewrite Rmult_1_l; apply Wallis_monotone.
Qed.

Print Assumptions Wallis_product.
Print Assumptions Wallis_ratio_bounds.

(* ================================================================= *)
(*  END WallisProduct.v                                              *)
(*  (n+1)·Wₙ·W_{n+1} = π/2 exactly, Wₙ>0, W_{n+1}≤Wₙ, and the ratio    *)
(*  bounds (n+1)/(n+2) ≤ W_{n+1}/Wₙ ≤ 1.  Next: the ratio → 1 and       *)
(*  n·Wₙ² → π/2, then the Gaussian squeeze.                           *)
(* ================================================================= *)
