(* ================================================================= *)
(*  GaussSqrtStep.v  —  Gaussian part-A stack, step 5a: the √-step.    *)
(*                                                                    *)
(*  Turning the SQUARED Wallis asymptotic (n+1)Wₙ² → π/2 into the       *)
(*  linear √n·W_{2n+1} → √π/2, and hence the lower Gaussian integral    *)
(*  ∫₀^√n (1−x²/n)ⁿ → √π/2.                                            *)
(*                                                                    *)
(*    wallis_sqrt_cv    : √(m+1)·Wₘ → √(π/2)   (√ of Wallis_sq_asymp,   *)
(*                        via sequential continuity of √);             *)
(*    ratio_half_cv     : n/(2n+2) → 1/2;                              *)
(*    sqrt_wallis_2np1_cv : √n·W_{2n+1} → √π/2                          *)
(*                        (= √(n/(2n+2))·(√(2n+2)·W_{2n+1}), CV_mult);  *)
(*    gauss_lower_integral_cv : ∫₀^√n (1−x²/n)ⁿ dx → √π/2.              *)
(*                                                                    *)
(*  The √-step is pure Un_cv + sqrt continuity (continuity_seq,        *)
(*  CV_mult, sqrt_mult) — no integrals.  The final corollary feeds the *)
(*  bounded lower flank (gauss_lower_wallis) through it.  What remains  *)
(*  for ∫_ℝ e^{−x²} = √π is the improper ∫₀^∞ (upper flank + the actual *)
(*  Gaussian, absent from stdlib RiemannInt).  No new axioms.          *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import WallisIntegral WallisAsymptotics GaussWallis.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  Un_cv plumbing.                                                  *)
(* ----------------------------------------------------------------- *)

Lemma Un_cv_ext : forall (f g : nat -> R) l,
  (forall n, f n = g n) -> Un_cv f l -> Un_cv g l.
Proof.
  intros f g l Hfg Hf eps He; destruct (Hf eps He) as [N HN].
  exists N; intros n Hn; rewrite <- Hfg; apply HN; exact Hn.
Qed.

Lemma Un_cv_2np1 : forall (u : nat -> R) L,
  Un_cv u L -> Un_cv (fun n => u (2 * n + 1)%nat) L.
Proof.
  intros u L H eps He; destruct (H eps He) as [N HN].
  exists N; intros n Hn; apply HN; lia.
Qed.

Lemma Un_cv_eventually_eq : forall (f g : nat -> R) l N0,
  (forall n, (N0 <= n)%nat -> f n = g n) -> Un_cv f l -> Un_cv g l.
Proof.
  intros f g l N0 Heq Hf eps He; destruct (Hf eps He) as [N HN].
  exists (max N N0); intros n Hn; rewrite <- Heq by lia; apply HN; lia.
Qed.

(* ----------------------------------------------------------------- *)
(*  n/(2n+2) → 1/2.                                                  *)
(* ----------------------------------------------------------------- *)

Lemma ratio_half_cv : Un_cv (fun n => INR n / (2 * INR n + 2)) (1 / 2).
Proof.
  intros eps He.
  destruct (INR_unbounded (/ eps)) as [N HN].
  exists N; intros n Hn.
  assert (Hd : 0 < 2 * INR n + 2) by (pose proof (pos_INR n); lra).
  assert (Hle : INR N <= INR n) by (apply le_INR; exact Hn).
  assert (Hbig : / eps < 2 * INR n + 2) by (pose proof (pos_INR n); lra).
  unfold R_dist.
  replace (INR n / (2 * INR n + 2) - 1 / 2) with (- / (2 * INR n + 2)) by (field; lra).
  rewrite Rabs_Ropp, Rabs_right by (apply Rgt_ge; apply Rinv_0_lt_compat; exact Hd).
  apply Rlt_le_trans with (/ / eps).
  - apply Rinv_lt_contravar;
      [ apply Rmult_lt_0_compat; [ apply Rinv_0_lt_compat; exact He | exact Hd ] | exact Hbig ].
  - rewrite Rinv_inv; apply Rle_refl.
Qed.

(* ----------------------------------------------------------------- *)
(*  √(m+1)·Wₘ → √(π/2).                                              *)
(* ----------------------------------------------------------------- *)

Lemma wallis_sqrt_cv : Un_cv (fun m => sqrt (INR m + 1) * Wallis m) (sqrt (PI / 2)).
Proof.
  apply (Un_cv_ext (fun m => sqrt ((INR m + 1) * (Wallis m) ^ 2))
                   (fun m => sqrt (INR m + 1) * Wallis m) (sqrt (PI / 2))).
  - intro m.
    rewrite sqrt_mult by (pose proof (pos_INR m); pose proof (Wallis_nonneg m); nra).
    f_equal.
    replace ((Wallis m) ^ 2) with (Wallis m * Wallis m) by ring.
    apply sqrt_square; apply Wallis_nonneg.
  - apply (continuity_seq sqrt (fun m => (INR m + 1) * (Wallis m) ^ 2) (PI / 2)).
    + apply continuity_pt_sqrt; pose proof PI_RGT_0; lra.
    + exact Wallis_sq_asymp.
Qed.

(* ----------------------------------------------------------------- *)
(*  √n·W_{2n+1} → √π/2.                                              *)
(* ----------------------------------------------------------------- *)

Theorem sqrt_wallis_2np1_cv :
  Un_cv (fun n => sqrt (INR n) * Wallis (2 * n + 1)) (sqrt PI / 2).
Proof.
  pose proof (Un_cv_2np1 _ _ wallis_sqrt_cv) as Ha.
  assert (Hr : Un_cv (fun n => sqrt (INR n / (INR (2 * n + 1) + 1))) (sqrt (1 / 2))).
  { apply (continuity_seq sqrt (fun n => INR n / (INR (2 * n + 1) + 1)) (1 / 2)).
    - apply continuity_pt_sqrt; lra.
    - apply (Un_cv_ext (fun n => INR n / (2 * INR n + 2))
                       (fun n => INR n / (INR (2 * n + 1) + 1)) (1 / 2)).
      + intro n.
        assert (HD : INR (2 * n + 1) + 1 = 2 * INR n + 2)
          by (rewrite plus_INR, mult_INR; simpl; ring).
        rewrite HD; reflexivity.
      + exact ratio_half_cv. }
  pose proof (CV_mult _ _ _ _ Hr Ha) as Hm.
  assert (Hval : sqrt (1 / 2) * sqrt (PI / 2) = sqrt PI / 2).
  { pose proof PI_RGT_0; rewrite <- sqrt_mult by lra.
    replace (1 / 2 * (PI / 2)) with (PI * (/ 2 * / 2)) by lra.
    rewrite sqrt_mult by lra; rewrite sqrt_square by lra; lra. }
  rewrite Hval in Hm.
  apply (Un_cv_ext
           (fun n => sqrt (INR n / (INR (2 * n + 1) + 1)) *
                     (sqrt (INR (2 * n + 1) + 1) * Wallis (2 * n + 1)))
           (fun n => sqrt (INR n) * Wallis (2 * n + 1)) (sqrt PI / 2)).
  - intro n; set (D := INR (2 * n + 1) + 1).
    assert (HD : 0 < D) by (unfold D; pose proof (pos_INR (2 * n + 1)); lra).
    assert (Hnn : 0 <= INR n / D)
      by (unfold Rdiv; apply Rmult_le_pos; [ apply pos_INR | left; apply Rinv_0_lt_compat; exact HD ]).
    rewrite <- Rmult_assoc, <- (sqrt_mult (INR n / D) D Hnn (Rlt_le _ _ HD)).
    replace (INR n / D * D) with (INR n) by (field; lra).
    reflexivity.
  - exact Hm.
Qed.

(* ----------------------------------------------------------------- *)
(*  The lower Gaussian integral converges to √π/2.                   *)
(* ----------------------------------------------------------------- *)

Corollary gauss_lower_integral_cv :
  forall (pr : forall n, Riemann_integrable (fun x => (1 - x ^ 2 / INR n) ^ n) 0 (sqrt (INR n))),
  Un_cv (fun n => RiemannInt (pr n)) (sqrt PI / 2).
Proof.
  intro pr.
  apply (Un_cv_eventually_eq (fun n => sqrt (INR n) * Wallis (2 * n + 1))
                             (fun n => RiemannInt (pr n)) (sqrt PI / 2) 1).
  - intros n Hn; symmetry; apply gauss_lower_wallis.
    pose proof (le_INR 1 n Hn) as HL; simpl in HL; lra.
  - exact sqrt_wallis_2np1_cv.
Qed.

Print Assumptions sqrt_wallis_2np1_cv.
Print Assumptions gauss_lower_integral_cv.

(* ================================================================= *)
(*  END GaussSqrtStep.v                                              *)
(*  √n·W_{2n+1} → √π/2, hence ∫₀^√n (1−x²/n)ⁿ → √π/2.  The bounded      *)
(*  lower flank of the Gaussian integral now has its limit, axiom-free.*)
(*  Only the improper ∫₀^∞ (upper flank / the actual Gaussian) remains. *)
(* ================================================================= *)
