(* ================================================================= *)
(*  SelbergMainTerm.v  —  Sum_{n<=N} Lam2(n) = 2N ln N + O(N) (Step 2d, v4a).*)
(*                                                                    *)
(*  From selberg_sum_eq  Sum Lam2 = Sum_{d<=N} mu(d) Slog2(floor(N/d)),  *)
(*  the bracket Slog2(y) = Alsq(y)+O(ln^2 y) (Slog2_bracket) with        *)
(*  Alsq(INR y) = INR y*Qfun(INR y) + 2 INR y, mu_hyperbola             *)
(*  (2 Sum mu floor = 2), and floor(N/d) = N/d - frac collapse the sum   *)
(*  to  INR N * P'(N) + O(N):                                           *)
(*      | Sum Lam2 - INR N * P'(N) - 2 | <= 16 N     (A_estimate),      *)
(*  each per-term error being <= 2 + 2(ln N-ln d)^2 + 2(ln N-ln d)      *)
(*  (|mu|<=1), summed via sumlogsq_ratio_bound + sumlog_ratio_le +      *)
(*  Tlog_sharp.  With P'(N)=2 ln N+O(1) (PartB):                        *)
(*      | Sum Lam2 - 2N ln N | <= (88+2 Kup) N   (lam2_sum_bound).      *)
(*  Axiom-clean.                                                        *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia Arith List.
Require Import DirichletConv RealMobius SelbergSymmetry Chebyshev ChebyshevBound
        MertensVonMangoldt StirlingSharp SumLogSq SumLogSqRatio SelbergSum
        EulerMaclaurin MobiusBound MobiusOverD PartB.
Import ListNotations.
Open Scope R_scope.

(* Sum_{d<=N} (ln N - ln d) <= N  (the linear log-ratio, via Tlog_sharp) *)
Lemma sumlog_ratio_le : forall N, (1 <= N)%nat ->
  Rls (seq 1 N) (fun d => ln (INR N) - ln (INR d)) <= INR N.
Proof.
  intros N HN.
  rewrite (Rls_ext _ (fun d => ln (INR N) - ln (INR d))
             (fun d => ln (INR N) + (-1) * ln (INR d)) (seq 1 N)) by (intros; ring).
  rewrite Rls_add, <- (Rls_scal _ (-1) (fun d => ln (INR d)) (seq 1 N)),
          (Rls_seq_const (ln (INR N)) 1 N).
  change (Rls (seq 1 N) (fun d => ln (INR d))) with (Tlog N).
  pose proof (Tlog_sharp N HN) as [Tlo Thi]; nra.
Qed.

Lemma Alsq_eq : forall y, Alsq (INR y) = INR y * Qfun (INR y) + 2 * INR y.
Proof. intro y; unfold Alsq, Qfun; ring. Qed.

(* the per-term error bound *)
Lemma X_bound : forall N d, (1 <= d)%nat -> (d <= N)%nat ->
  Rabs (Slog2 (N / d)%nat - INR N / INR d * Qfun (INR (N / d)%nat) - 2 * INR (N / d)%nat)
  <= 2 + 2 * ((ln (INR N) - ln (INR d)) * (ln (INR N) - ln (INR d)))
       + 2 * (ln (INR N) - ln (INR d)).
Proof.
  intros N d Hd HdN.
  assert (HdR : 0 < INR d) by (apply lt_0_INR; lia).
  assert (HNR : 0 < INR N) by (apply lt_0_INR; lia).
  assert (Hy : (1 <= N / d)%nat).
  { assert (Hdd : (d / d = 1)%nat) by (apply Nat.div_same; lia).
    rewrite <- Hdd; apply Nat.Div0.div_le_mono; lia. }
  set (y := (N / d)%nat) in *.
  set (L := ln (INR N) - ln (INR d)) in *.
  assert (HyR : 1 <= INR y) by (apply (le_INR 1); lia).
  assert (HL0 : 0 <= L) by (unfold L; assert (ln (INR d) <= ln (INR N)) by (apply ln_le; [ lra | apply le_INR; lia ]); lra).
  assert (Hlny : ln (INR y) <= L).
  { assert (Hle : INR y <= INR N / INR d) by (pose proof (frac_bounds N d Hd) as [Hf0 _]; unfold y; lra).
    apply Rle_trans with (ln (INR N / INR d)).
    - apply ln_le; [ lra | exact Hle ].
    - unfold L.
      assert (H1 : ln (INR N / INR d) = ln (INR N) - ln (INR d)).
      { unfold Rdiv; rewrite ln_mult by (try exact HNR; apply Rinv_0_lt_compat; exact HdR).
        rewrite ln_Rinv by exact HdR; lra. }
      lra. }
  assert (Hln0 : 0 <= ln (INR y)) by (rewrite <- ln_1; apply ln_le; lra).
  assert (Hlnsq : ln (INR y) * ln (INR y) <= L * L)
    by (apply Rmult_le_compat; [ exact Hln0 | exact Hln0 | exact Hlny | exact Hlny ]).
  assert (HLL : 0 <= L * L) by (apply Rmult_le_pos; exact HL0).
  assert (Hll2 : 0 <= ln (INR y) * ln (INR y)) by (apply Rmult_le_pos; exact Hln0).
  pose proof (Slog2_bracket y Hy) as [Slo Shi].
  pose proof (frac_bounds N d Hd) as [Hf0 Hf1].
  assert (HX : Slog2 y - INR N / INR d * Qfun (INR y) - 2 * INR y
             = (Slog2 y - Alsq (INR y)) - (INR N / INR d - INR y) * Qfun (INR y))
    by (rewrite Alsq_eq; ring).
  rewrite HX.
  assert (HQabs : Rabs (Qfun (INR y)) <= L * L + 2 * L)
    by (unfold Qfun; apply Rabs_le; split; lra).
  assert (HSAbs : Rabs (Slog2 y - Alsq (INR y)) <= 2 + L * L)
    by (apply Rabs_le; split; lra).
  eapply Rle_trans; [ apply Rabs_triang | ]; rewrite Rabs_Ropp.
  eapply Rle_trans; [ apply Rplus_le_compat; [ apply HSAbs | ] | ].
  - rewrite Rabs_mult.
    assert (Hfr : Rabs (INR N / INR d - INR y) <= 1)
      by (rewrite Rabs_pos_eq by (unfold y in *; lra); unfold y in *; lra).
    apply Rle_trans with (1 * Rabs (Qfun (INR y)));
      [ apply Rmult_le_compat_r; [ apply Rabs_pos | exact Hfr ] | ].
    rewrite Rmult_1_l; exact HQabs.
  - lra.
Qed.

(* Sum Lam2 = INR N * P'(N) + 2 + O(N) *)
Theorem A_estimate : forall N, (1 <= N)%nat ->
  Rabs (Rls (seq 1 N) Lam2 - INR N * Pprime N - 2) <= 16 * INR N.
Proof.
  intros N HN.
  assert (Hcomb : Rls (seq 1 N) Lam2 - INR N * Pprime N - 2
    = Rls (seq 1 N) (fun d => IZR (mu d) * Slog2 (N / d)%nat
        - IZR (mu d) * (INR N / INR d) * Qfun (INR (N / d)%nat)
        - 2 * (IZR (mu d) * INR (N / d)%nat))).
  { assert (HA : Rls (seq 1 N) Lam2
        = Rls (seq 1 N) (fun d => IZR (mu d) * Slog2 (N / d)%nat)) by (apply selberg_sum_eq).
    assert (HB : INR N * Pprime N
        = Rls (seq 1 N) (fun d => IZR (mu d) * (INR N / INR d) * Qfun (INR (N / d)%nat))).
    { unfold Pprime; rewrite Rls_scal; apply Rls_ext; intros d _; unfold Rdiv; ring. }
    assert (HC : (2:R)
        = Rls (seq 1 N) (fun d => 2 * (IZR (mu d) * INR (N / d)%nat))).
    { rewrite <- (Rls_scal _ 2 (fun d => IZR (mu d) * INR (N / d)%nat) (seq 1 N)),
              (mu_hyperbola N HN); ring. }
    rewrite HA, HB. rewrite HC at 1.
    rewrite <- Rls_sub, <- Rls_sub; reflexivity. }
  rewrite Hcomb.
  eapply Rle_trans; [ apply Rls_abs | ].
  eapply Rle_trans with
    (Rls (seq 1 N) (fun d => 2 + 2 * ((ln (INR N) - ln (INR d)) * (ln (INR N) - ln (INR d)))
                            + 2 * (ln (INR N) - ln (INR d)))).
  - apply Rls_le; intros d Hd; apply in_seq in Hd.
    replace (IZR (mu d) * Slog2 (N / d)%nat
             - IZR (mu d) * (INR N / INR d) * Qfun (INR (N / d)%nat)
             - 2 * (IZR (mu d) * INR (N / d)%nat))
      with (IZR (mu d) * (Slog2 (N / d)%nat - INR N / INR d * Qfun (INR (N / d)%nat)
                          - 2 * INR (N / d)%nat)) by (unfold Rdiv; ring).
    rewrite Rabs_mult.
    assert (Hmu : Rabs (IZR (mu d)) <= 1).
    { rewrite <- abs_IZR; replace 1 with (IZR 1) by (simpl; ring);
        apply IZR_le; destruct (mu_abs_le_1 d ltac:(lia)); lia. }
    apply Rle_trans with (1 * Rabs (Slog2 (N / d)%nat - INR N / INR d * Qfun (INR (N / d)%nat)
                                    - 2 * INR (N / d)%nat)).
    + apply Rmult_le_compat_r; [ apply Rabs_pos | exact Hmu ].
    + rewrite Rmult_1_l; apply X_bound; lia.
  - (* sum the per-term bound *)
    rewrite (Rls_ext _ _
      (fun d => 2 + (2 * ((ln (INR N) - ln (INR d)) * (ln (INR N) - ln (INR d)))
                     + 2 * (ln (INR N) - ln (INR d)))) (seq 1 N)) by (intros; ring).
    rewrite Rls_add, (Rls_seq_const 2 1 N), Rls_add.
    rewrite <- (Rls_scal _ 2 (fun d => (ln (INR N) - ln (INR d)) * (ln (INR N) - ln (INR d))) (seq 1 N)).
    rewrite <- (Rls_scal _ 2 (fun d => ln (INR N) - ln (INR d)) (seq 1 N)).
    rewrite (Rls_ext _ (fun d => (ln (INR N) - ln (INR d)) * (ln (INR N) - ln (INR d)))
             (fun d => (ln (INR N) - ln (INR d)) ^ 2) (seq 1 N)) by (intros; ring).
    pose proof (sumlogsq_ratio_bound N HN) as Hsq.
    pose proof (sumlog_ratio_le N HN) as Hlin.
    assert (0 <= INR N) by apply pos_INR.
    lra.
Qed.

(* the summed Selberg formula *)
Theorem lam2_sum_bound : forall N, (1 <= N)%nat ->
  Rabs (Rls (seq 1 N) Lam2 - 2 * INR N * ln (INR N)) <= (88 + 2 * Kup) * INR N.
Proof.
  intros N HN.
  pose proof (A_estimate N HN) as HA; apply abs_bnd in HA.
  pose proof (Pprime_bound N HN) as HP; apply abs_bnd in HP.
  assert (HN1 : 1 <= INR N) by (apply (le_INR 1); lia).
  pose proof (pos_INR N).
  assert (HE : Rls (seq 1 N) Lam2 - 2 * INR N * ln (INR N)
    = (Rls (seq 1 N) Lam2 - INR N * Pprime N - 2)
      + INR N * (Pprime N - 2 * ln (INR N)) + 2) by ring.
  rewrite HE; apply Rabs_le; split; nra.
Qed.

Print Assumptions lam2_sum_bound.

(* ================================================================= *)
(*  END SelbergMainTerm.v  —  Sum_{n<=N} Lam2(n) = 2N ln N + O(N).      *)
(* ================================================================= *)
