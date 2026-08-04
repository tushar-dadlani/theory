(* ================================================================= *)
(*  EulerFactorLog.v  —  the per-prime 3-4-1 inequality.               *)
(*                                                                    *)
(*  From 3 + 4 cos x + cos 2x = 2(1+cos x)^2 >= 0 and the log-series    *)
(*  (LogGeomSeries), for 0 <= r < 1 and any phi:                       *)
(*                                                                    *)
(*    3 L(0,r) + 4 L(phi,r) + L(2 phi,r) >= 0,   L(θ,r) = -1/2 ln D(θ,r)*)
(*                                                                    *)
(*  where D(θ,r) = 1 - 2 r cos θ + r^2 = |1 - r e^{iθ}|^2.  This is the *)
(*  logarithmic form of the Mertens per-prime Euler-factor inequality  *)
(*  |1-p^{-σ}|^{-3}|1-p^{-(σ+it)}|^{-4}|1-p^{-(σ+2it)}|^{-1} >= 1.       *)
(*  Axiom-clean.                                                       *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import LogGeomSeries.
Open Scope R_scope.

(* the trigonometric kernel *)
Lemma three_four_one : forall x, 3 + 4 * cos x + cos (2 * x) = 2 * (1 + cos x) ^ 2.
Proof.
  intro x; rewrite cos_2a; pose proof (sin2_cos2 x) as Hcs; unfold Rsqr in Hcs.
  replace (sin x * sin x) with (1 - cos x * cos x) by nra; ring.
Qed.

(* the log-series limit *)
Definition L (θ r : R) : R := - (/2) * ln (1 - 2 * r * cos θ + r ^ 2).

Lemma L_cv : forall θ r, 0 <= r < 1 -> Un_cv (fun N => lsum θ N r) (L θ r).
Proof. intros θ r H; apply log_geom_series; exact H. Qed.

(* the combined per-term of 3-4-1 *)
Definition ct (φ r : R) (k : nat) : R :=
  r ^ (S k) / INR (S k) * (3 + 4 * cos (INR (S k) * φ) + cos (INR (S k) * (2 * φ))).

Lemma term_eq : forall φ r k,
  3 * lterm 0 k r + 4 * lterm φ k r + lterm (2 * φ) k r = ct φ r k.
Proof.
  intros φ r k; unfold lterm, ct.
  replace (INR (S k) * 0) with 0 by ring; rewrite cos_0.
  field; apply not_0_INR; lia.
Qed.

Lemma combo_eq : forall φ r N,
  3 * lsum 0 N r + 4 * lsum φ N r + lsum (2 * φ) N r = sum_f_R0 (ct φ r) N.
Proof.
  intros φ r N; unfold lsum; induction N as [|N IH].
  - cbn [sum_f_R0]; apply term_eq.
  - rewrite !tech5, <- IH; pose proof (term_eq φ r (S N)); lra.
Qed.

Lemma ct_nonneg : forall φ r k, 0 <= r -> 0 <= ct φ r k.
Proof.
  intros φ r k Hr; unfold ct.
  apply Rmult_le_pos.
  - apply Rmult_le_pos;
      [ apply pow_le; exact Hr | apply Rlt_le, Rinv_0_lt_compat, lt_0_INR; lia ].
  - replace (INR (S k) * (2 * φ)) with (2 * (INR (S k) * φ)) by ring.
    rewrite three_four_one; apply Rmult_le_pos; [ lra | apply pow2_ge_0 ].
Qed.

Lemma combo_partial_nonneg : forall φ r N, 0 <= r ->
  0 <= 3 * lsum 0 N r + 4 * lsum φ N r + lsum (2 * φ) N r.
Proof.
  intros φ r N Hr; rewrite combo_eq.
  apply cond_pos_sum; intro k; apply ct_nonneg; exact Hr.
Qed.

(* THE PER-PRIME 3-4-1 INEQUALITY (logarithmic form) *)
Theorem per_prime_log : forall φ r, 0 <= r < 1 ->
  0 <= 3 * L 0 r + 4 * L φ r + L (2 * φ) r.
Proof.
  intros φ r Hr.
  apply Rle_cv_lim with (Un := fun _ : nat => 0)
           (Vn := fun N => 3 * lsum 0 N r + 4 * lsum φ N r + lsum (2 * φ) N r).
  - intro N; apply combo_partial_nonneg; apply Hr.
  - apply Un_cv_const.
  - apply CV_plus; [ apply CV_plus | apply L_cv; exact Hr ].
    + apply (CV_mult (fun _ => 3) (fun N => lsum 0 N r) 3 (L 0 r));
        [ apply Un_cv_const | apply L_cv; exact Hr ].
    + apply (CV_mult (fun _ => 4) (fun N => lsum φ N r) 4 (L φ r));
        [ apply Un_cv_const | apply L_cv; exact Hr ].
Qed.

Print Assumptions per_prime_log.

(* ================================================================= *)
(*  END EulerFactorLog.v                                              *)
(* ================================================================= *)
