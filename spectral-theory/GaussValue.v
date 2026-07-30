(* ================================================================= *)
(*  GaussValue.v  —  Gaussian part-A stack, step 5 (finale):           *)
(*  the squeeze ∫₀^√n e^{−x²} → √π/2, and ∫₀^∞ e^{−x²} = √π/2.          *)
(*                                                                    *)
(*  Both Wallis flanks converge to √π/2:                              *)
(*    √n·W_{2n+1} ≤ ∫₀^√n e^{−x²} ≤ √n·W_{2n−2},                       *)
(*  with √n·W_{2n+1} → √π/2 (sqrt_wallis_2np1_cv) and                  *)
(*       √n·W_{2n−2} → √π/2 (sqrt_wallis_2nm2_cv, built here).         *)
(*  The sandwich gives ∫₀^√n e^{−x²} → √π/2 (gauss_partial_cv), and     *)
(*  feeding that through the monotone improper scaffold                *)
(*  (GaussImproper.improper_welldef, with Aₖ = √k → ∞) yields          *)
(*                                                                    *)
(*      ∫₀^∞ e^{−x²} = √π/2   (gauss_improper).                       *)
(*                                                                    *)
(*  This closes the classical Gaussian value on the half-line — the    *)
(*  archimedean normalisation the Poisson→θ line rests on (∫_ℝ e^{−x²}  *)
(*  = √π, ∫_ℝ e^{−πx²} = 1).  No new axioms (classical Reals only).    *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import WallisIntegral WallisAsymptotics GaussSubst GaussWallis
  GaussSqueeze GaussSqrtStep GaussUpperSubst GaussImproper.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  More Un_cv plumbing.                                             *)
(* ----------------------------------------------------------------- *)

Lemma Un_cv_2n : forall (u : nat -> R) L, Un_cv u L -> Un_cv (fun n => u (2 * n)%nat) L.
Proof. intros u L H eps He; destruct (H eps He) as [N HN]; exists N; intros n Hn; apply HN; lia. Qed.

Lemma Un_cv_unshift : forall (f : nat -> R) L, Un_cv (fun n => f (S n)) L -> Un_cv f L.
Proof.
  intros f L H eps He; destruct (H eps He) as [N HN].
  exists (S N); intros n Hn; destruct n as [| m]; [ lia | apply (HN m); lia ].
Qed.

Lemma Un_cv_sandwich : forall (a b c : nat -> R) L (N0 : nat),
  Un_cv a L -> Un_cv c L -> (forall n, (N0 <= n)%nat -> a n <= b n <= c n) -> Un_cv b L.
Proof.
  intros a b c L N0 Ha Hc Hmid eps He.
  destruct (Ha eps He) as [Na HNa]; destruct (Hc eps He) as [Nc HNc].
  exists (max (max Na Nc) N0); intros n Hn.
  pose proof (HNa n (Nat.le_trans _ _ _ (Nat.le_trans _ _ _ (Nat.le_max_l Na Nc) (Nat.le_max_l _ N0)) Hn)) as Da.
  pose proof (HNc n (Nat.le_trans _ _ _ (Nat.le_trans _ _ _ (Nat.le_max_r Na Nc) (Nat.le_max_l _ N0)) Hn)) as Dc.
  pose proof (Hmid n (Nat.le_trans _ _ _ (Nat.le_max_r _ N0) Hn)) as [Hm1 Hm2].
  unfold R_dist in *.
  pose proof (Rabs_def2 _ _ Da) as [_ Da2].
  pose proof (Rabs_def2 _ _ Dc) as [Dc1 _].
  apply Rabs_def1; lra.
Qed.

Lemma ratio_half_cv2 : Un_cv (fun m => (INR m + 1) / (2 * INR m + 1)) (1 / 2).
Proof.
  intros eps He.
  destruct (INR_unbounded (/ eps)) as [N HN].
  exists N; intros m Hm.
  assert (Hd : 0 < 2 * INR m + 1) by (pose proof (pos_INR m); lra).
  assert (Hle : INR N <= INR m) by (apply le_INR; exact Hm).
  assert (Hbig : / eps < 2 * (2 * INR m + 1)) by (pose proof (pos_INR m); lra).
  unfold R_dist.
  replace ((INR m + 1) / (2 * INR m + 1) - 1 / 2) with (/ (2 * (2 * INR m + 1)))
    by (field; apply Rgt_not_eq; exact Hd).
  rewrite Rabs_right by (apply Rgt_ge; apply Rinv_0_lt_compat; lra).
  apply Rlt_le_trans with (/ / eps);
    [ apply Rinv_lt_contravar;
      [ apply Rmult_lt_0_compat; [ apply Rinv_0_lt_compat; exact He | lra ] | exact Hbig ]
    | rewrite Rinv_inv; apply Rle_refl ].
Qed.

(* ----------------------------------------------------------------- *)
(*  √n·W_{2n−2} → √π/2   (the upper flank's Wallis limit).           *)
(* ----------------------------------------------------------------- *)

Theorem sqrt_wallis_2nm2_cv :
  Un_cv (fun n => sqrt (INR n) * Wallis (2 * (n - 1))) (sqrt PI / 2).
Proof.
  apply Un_cv_unshift.
  apply (Un_cv_ext (fun m => sqrt (INR (S m)) * Wallis (2 * m))
                   (fun m => sqrt (INR (S m)) * Wallis (2 * (S m - 1))) (sqrt PI / 2)).
  { intro m; replace (2 * (S m - 1))%nat with (2 * m)%nat by lia; reflexivity. }
  (* now: Un_cv (fun m => √(m+1)·W_{2m}) (√π/2) *)
  pose proof (Un_cv_2n _ _ wallis_sqrt_cv) as Ha.
  assert (Hr : Un_cv (fun m => sqrt (INR (S m) / (INR (2 * m) + 1))) (sqrt (1 / 2))).
  { apply (continuity_seq sqrt (fun m => INR (S m) / (INR (2 * m) + 1)) (1 / 2)).
    - apply continuity_pt_sqrt; lra.
    - apply (Un_cv_ext (fun m => (INR m + 1) / (2 * INR m + 1))
                       (fun m => INR (S m) / (INR (2 * m) + 1)) (1 / 2)).
      + intro m; rewrite S_INR;
          replace (INR (2 * m) + 1) with (2 * INR m + 1) by (rewrite mult_INR; simpl; ring);
          reflexivity.
      + exact ratio_half_cv2. }
  pose proof (CV_mult _ _ _ _ Hr Ha) as Hm.
  assert (Hval : sqrt (1 / 2) * sqrt (PI / 2) = sqrt PI / 2).
  { pose proof PI_RGT_0; rewrite <- sqrt_mult by lra.
    replace (1 / 2 * (PI / 2)) with (PI * (/ 2 * / 2)) by lra.
    rewrite sqrt_mult by lra; rewrite sqrt_square by lra; lra. }
  rewrite Hval in Hm.
  apply (Un_cv_ext
           (fun m => sqrt (INR (S m) / (INR (2 * m) + 1)) *
                     (sqrt (INR (2 * m) + 1) * Wallis (2 * m)))
           (fun m => sqrt (INR (S m)) * Wallis (2 * m)) (sqrt PI / 2)).
  - intro m; set (D := INR (2 * m) + 1).
    assert (HD : 0 < D) by (unfold D; pose proof (pos_INR (2 * m)); lra).
    assert (Hnn : 0 <= INR (S m) / D)
      by (unfold Rdiv; apply Rmult_le_pos; [ apply pos_INR | left; apply Rinv_0_lt_compat; exact HD ]).
    rewrite <- Rmult_assoc, <- (sqrt_mult (INR (S m) / D) D Hnn (Rlt_le _ _ HD)).
    replace (INR (S m) / D * D) with (INR (S m)) by (field; lra).
    reflexivity.
  - exact Hm.
Qed.

(* ----------------------------------------------------------------- *)
(*  The squeeze:  ∫₀^√n e^{−x²} → √π/2.                              *)
(* ----------------------------------------------------------------- *)

Theorem gauss_partial_cv :
  forall (pr : forall n, Riemann_integrable (fun x => exp (- x ^ 2)) 0 (sqrt (INR n))),
  Un_cv (fun n => RiemannInt (pr n)) (sqrt PI / 2).
Proof.
  intro pr.
  apply (Un_cv_sandwich (fun n => sqrt (INR n) * Wallis (2 * n + 1))
                        (fun n => RiemannInt (pr n))
                        (fun n => sqrt (INR n) * Wallis (2 * (n - 1))) (sqrt PI / 2) 1).
  - exact sqrt_wallis_2np1_cv.
  - exact sqrt_wallis_2nm2_cv.
  - intros n Hn1.
    assert (Hn : 0 < INR n) by (apply lt_0_INR; lia).
    assert (Hsn0 : 0 <= sqrt (INR n)) by apply sqrt_pos.
    split.
    + (* √n·W_{2n+1} ≤ ∫₀^√n e^{−x²} *)
      assert (prLow : Riemann_integrable (fun x => (1 - x ^ 2 / INR n) ^ n) 0 (sqrt (INR n)))
        by (apply continuity_implies_RiemannInt; [ exact Hsn0 | intros x _; apply (cont_gaussp n) ]).
      rewrite <- (gauss_lower_wallis n Hn prLow).
      apply RiemannInt_P19; [ exact Hsn0 | intros x [Hx1 Hx2] ].
      apply gauss_lower_pt; [ exact Hn | ].
      apply Rlt_le; replace (INR n) with (sqrt (INR n) * sqrt (INR n))
        by (rewrite sqrt_sqrt; [ reflexivity | lra ]).
      replace (x ^ 2) with (x * x) by ring.
      apply Rmult_le_0_lt_compat; lra.
    + (* ∫₀^√n e^{−x²} ≤ √n·W_{2n−2} *)
      apply gauss_upper_bound; lia.
Qed.

(* ----------------------------------------------------------------- *)
(*  Feeding the squeeze through the improper scaffold.               *)
(* ----------------------------------------------------------------- *)

Definition exp_sq (x : R) : R := exp (- x ^ 2).

Lemma cont_exp_sq : forall x, continuity_pt exp_sq x.
Proof.
  intro x; unfold exp_sq.
  apply (continuity_pt_comp (fun y => - y ^ 2) exp x).
  - apply (continuity_pt_opp (fun y => y ^ 2) x).
    apply (cont_pow (fun y => y) 2); apply cont_id.
  - apply derivable_continuous_pt; exists (exp (- x ^ 2)); apply derivable_pt_lim_exp.
Qed.

Lemma exp_sq_int : forall a b, Riemann_integrable exp_sq a b.
Proof.
  intros a b; destruct (Rle_lt_dec a b) as [H | H].
  - apply continuity_implies_RiemannInt; [ exact H | intros x _; apply cont_exp_sq ].
  - apply RiemannInt_P1; apply continuity_implies_RiemannInt;
      [ lra | intros x _; apply cont_exp_sq ].
Qed.

Lemma cv_infty_sqrt : cv_infty (fun k => sqrt (INR k)).
Proof.
  intro M; destruct (Rle_or_lt M 0) as [HM | HM].
  - exists 1%nat; intros k Hk.
    apply Rle_lt_trans with 0; [ exact HM | apply sqrt_lt_R0 ].
    apply Rlt_le_trans with (INR 1); [ simpl; lra | apply le_INR; exact Hk ].
  - destruct (INR_unbounded (M * M)) as [N HN].
    exists N; intros k Hk.
    destruct (Rlt_le_dec M (sqrt (INR k))) as [Hlt | Hle]; [ exact Hlt | exfalso ].
    assert (Hik : INR k <= M * M).
    { rewrite <- (sqrt_sqrt (INR k)) by apply pos_INR.
      apply Rmult_le_compat; [ apply sqrt_pos | apply sqrt_pos | exact Hle | exact Hle ]. }
    pose proof (le_INR N k Hk); lra.
Qed.

Theorem gauss_improper : ImproperCv exp_sq exp_sq_int (sqrt PI / 2).
Proof.
  apply (improper_welldef exp_sq exp_sq_int
           (fun x _ => Rlt_le _ _ (exp_pos (- x ^ 2)))
           (fun k => sqrt (INR k)) (sqrt PI / 2)).
  - intro k; apply sqrt_pos.
  - exact cv_infty_sqrt.
  - exact (gauss_partial_cv (fun k => exp_sq_int 0 (sqrt (INR k)))).
Qed.

Print Assumptions gauss_partial_cv.
Print Assumptions gauss_improper.

(* ================================================================= *)
(*  END GaussValue.v                                                 *)
(*  ∫₀^√n e^{−x²} → √π/2 (the Wallis squeeze) and ∫₀^∞ e^{−x²} = √π/2   *)
(*  (monotone improper limit).  The classical Gaussian value on the    *)
(*  half-line, axiom-free — the archimedean normalisation for the       *)
(*  Poisson→θ functional equation (∫_ℝ e^{−x²} = √π, ∫_ℝ e^{−πx²} = 1). *)
(* ================================================================= *)
