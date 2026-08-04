(* ================================================================= *)
(*  ChebyshevPrime.v  —  Chebyshev's theorem: pi(x) has order x/log x. *)
(*                                                                    *)
(*  From the two-sided Chebyshev bound on psi (ChebyshevBound) and the *)
(*  regrouping psi N <= pi(N) ln N (PrimePowerReindex), we get          *)
(*     a * N/ln N  <=  pi_count N  <=  b * N/ln N                       *)
(*  for large N.  The lower bound is pi >= psi/ln N; the upper bound    *)
(*  splits primes at sqrt N (small primes <= sqrt N; each large prime   *)
(*  contributes >= ln(sqrt N) to theta <= psi).  Axiom-clean.          *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia Arith List.
Require Import ChebyshevBound Chebyshev VonMangoldtGlobal Ell2Primes
        PrimePowerReindex.
Open Scope R_scope.

(* ================================================================= *)
(*  0.  real-analysis scaffolding                                     *)
(* ================================================================= *)

Lemma ln2_pos : 0 < ln 2.
Proof. rewrite <- ln_1; apply ln_increasing; lra. Qed.

Lemma ln_le_2sqrt : forall x, 0 < x -> ln x <= 2 * sqrt x.
Proof.
  intros x Hx; assert (Hs : 0 < sqrt x) by (apply sqrt_lt_R0; exact Hx).
  assert (Hxx : x = sqrt x * sqrt x) by (rewrite sqrt_sqrt; lra).
  assert (Hln : ln x = 2 * ln (sqrt x))
    by (rewrite Hxx at 1; rewrite ln_mult by lra; lra).
  pose proof (ln_self1 (sqrt x) Hs); lra.
Qed.

Lemma ln_sqrt_half : forall x, 0 < x -> ln (sqrt x) = / 2 * ln x.
Proof.
  intros x Hx; assert (Hs : 0 < sqrt x) by (apply sqrt_lt_R0; exact Hx).
  assert (Hxx : sqrt x * sqrt x = x) by (apply sqrt_sqrt; lra).
  assert (ln x = ln (sqrt x) + ln (sqrt x))
    by (rewrite <- ln_mult by lra; rewrite Hxx; reflexivity).
  lra.
Qed.

Lemma ln_INR_pos : forall N, (2 <= N)%nat -> 0 < ln (INR N).
Proof.
  intros N HN; rewrite <- ln_1; apply ln_increasing; [ lra | ].
  apply Rlt_le_trans with (INR 2); [ simpl; lra | apply le_INR; exact HN ].
Qed.

(* eventually a positive-slope line dominates sqrt *)
Lemma sqrt_le_lin_eps : forall eps, 0 < eps ->
  exists N0, forall N, (N0 <= N)%nat -> sqrt (INR N) <= eps * INR N.
Proof.
  intros eps Heps.
  destruct (INR_unbounded (/ (eps * eps))) as [N0 HN0]; exists (S N0); intros N HN.
  assert (HNpos : 0 < INR N) by (apply lt_0_INR; lia).
  assert (HNbig : / (eps * eps) < INR N)
    by (apply Rlt_le_trans with (INR N0); [ exact HN0 | apply le_INR; lia ]).
  assert (Heps2 : 0 < eps * eps) by nra.
  assert (Hkey : 1 <= eps * sqrt (INR N)).
  { assert (H1 : 1 < eps * eps * INR N).
    { pose proof (Rmult_lt_compat_l (eps * eps) _ _ Heps2 HNbig) as Hh.
      rewrite Rinv_r in Hh by (apply Rgt_not_eq; exact Heps2); exact Hh. }
    assert (H2 : 1 < (eps * sqrt (INR N)) * (eps * sqrt (INR N))).
    { replace ((eps * sqrt (INR N)) * (eps * sqrt (INR N)))
        with (eps * eps * (sqrt (INR N) * sqrt (INR N))) by ring.
      rewrite sqrt_sqrt by lra; exact H1. }
    assert (Ht0 : 0 <= eps * sqrt (INR N))
      by (apply Rmult_le_pos; [ lra | apply sqrt_pos ]); nra. }
  assert (HsqNN : sqrt (INR N) * sqrt (INR N) = INR N) by (apply sqrt_sqrt; lra).
  assert (Hx : eps * INR N = (eps * sqrt (INR N)) * sqrt (INR N))
    by (rewrite <- HsqNN at 1; ring).
  pose proof (sqrt_pos (INR N)); rewrite Hx; nra.
Qed.

(* Nat.sqrt versus real sqrt *)
Lemma INR_sqrt_le : forall N, INR (Nat.sqrt N) <= sqrt (INR N).
Proof.
  intro N; pose proof (Nat.sqrt_spec N ltac:(lia)) as [Hlo _].
  assert (H : INR (Nat.sqrt N) * INR (Nat.sqrt N) <= INR N)
    by (rewrite <- mult_INR; apply le_INR; exact Hlo).
  rewrite <- (sqrt_Rsqr (INR (Nat.sqrt N))) by apply pos_INR.
  apply sqrt_le_1_alt; unfold Rsqr; exact H.
Qed.

Lemma sqrtN_le_2sqrt : forall N, (1 <= N)%nat -> sqrt (INR N) <= 2 * INR (Nat.sqrt N).
Proof.
  intros N HN; pose proof (Nat.sqrt_spec N ltac:(lia)) as [_ Hhi].
  assert (Hy1 : (1 <= Nat.sqrt N)%nat).
  { pose proof (Nat.sqrt_le_mono 1 N ltac:(lia)) as Hm; rewrite Nat.sqrt_1 in Hm; exact Hm. }
  assert (H : INR N < (INR (Nat.sqrt N) + 1) * (INR (Nat.sqrt N) + 1)).
  { apply Rlt_le_trans with (INR (S (Nat.sqrt N) * S (Nat.sqrt N))).
    - apply lt_INR; exact Hhi.
    - rewrite mult_INR, !S_INR; apply Rle_refl. }
  assert (Hsq : sqrt (INR N) <= INR (Nat.sqrt N) + 1).
  { rewrite <- (sqrt_Rsqr (INR (Nat.sqrt N) + 1)) by (pose proof (pos_INR (Nat.sqrt N)); lra).
    apply sqrt_le_1_alt; unfold Rsqr; lra. }
  assert (1 <= INR (Nat.sqrt N)) by (apply (le_INR 1); exact Hy1); lra.
Qed.

Lemma ln_sqrtN_lower : forall N, (16 <= N)%nat ->
  / 4 * ln (INR N) <= ln (INR (Nat.sqrt N)).
Proof.
  intros N HN.
  assert (HNpos : 0 < INR N) by (apply lt_0_INR; lia).
  assert (Hsqrtpos : 0 < sqrt (INR N)) by (apply sqrt_lt_R0; exact HNpos).
  assert (Hy : sqrt (INR N) / 2 <= INR (Nat.sqrt N))
    by (pose proof (sqrtN_le_2sqrt N ltac:(lia)); lra).
  assert (Hypos : 0 < INR (Nat.sqrt N)) by lra.
  assert (Hdivpos : 0 < sqrt (INR N) / 2) by lra.
  apply Rle_trans with (ln (sqrt (INR N) / 2)); [ | apply ln_le; [ exact Hdivpos | exact Hy ] ].
  (* ln(sqrt N / 2) = (1/2) ln N - ln 2 *)
  assert (Heq : ln (sqrt (INR N) / 2) = / 2 * ln (INR N) - ln 2).
  { unfold Rdiv; rewrite ln_mult by (try lra; apply Rinv_0_lt_compat; lra).
    rewrite ln_Rinv by lra; rewrite ln_sqrt_half by exact HNpos; ring. }
  rewrite Heq.
  (* need (1/4) ln N <= (1/2) ln N - ln 2, i.e. ln 2 <= (1/4) ln N, i.e. ln N >= 4 ln 2 *)
  assert (Hln16 : 4 * ln 2 <= ln (INR N)).
  { apply Rle_trans with (ln (INR 16)).
    - replace (INR 16) with (2 ^ 4) by (simpl; lra).
      rewrite ln_pow by lra; simpl; lra.
    - apply ln_le; [ simpl; lra | apply le_INR; exact HN ]. }
  lra.
Qed.

(* ================================================================= *)
(*  1.  theta and the elementary inequalities                        *)
(* ================================================================= *)

Definition tterm (n : nat) : R := if primeb n then ln (INR n) else 0%R.
Definition iterm (n : nat) : R := if primeb n then 1%R else 0%R.

Definition theta (N : nat) : R := Rsum tterm 1 N.

Lemma pi_count_iterm : forall N, pi_count N = Rsum iterm 1 N.
Proof. intro N; reflexivity. Qed.

Lemma theta_le_psi : forall N, theta N <= psi N.
Proof.
  intro N; unfold theta, tterm; rewrite psi_Rsum; apply Rsum_le.
  intros n Hn; destruct (primeb n) eqn:E.
  - apply primeb_nprime in E; rewrite (Lam_prime n E); apply Rle_refl.
  - apply Lam_nonneg.
Qed.

Lemma tterm_nonneg : forall n, 0 <= tterm n.
Proof.
  intro n; unfold tterm; destruct (primeb n) eqn:E; [ | apply Rle_refl ].
  apply primeb_nprime in E; destruct E as [H2 _]; apply ln_INR_nonneg; lia.
Qed.

(* ================================================================= *)
(*  2.  the lower bound:  pi_count N >= (ln2/2) N / ln N              *)
(* ================================================================= *)

Lemma picount_lower : exists (a : R) (N0 : nat), 0 < a /\
  forall N, (N0 <= N)%nat -> a * (INR N / ln (INR N)) <= pi_count N.
Proof.
  pose proof ln2_pos as Hln2.
  destruct (sqrt_le_lin_eps (ln 2 / 16) ltac:(lra)) as [N1 HN1].
  exists (ln 2 / 2), (Nat.max N1 16); split; [ lra | ].
  intros N HN.
  assert (HNpos : 0 < INR N) by (apply lt_0_INR; lia).
  assert (Hlnpos : 0 < ln (INR N)) by (apply ln_INR_pos; lia).
  assert (HN16 : 16 <= INR N)
    by (apply Rle_trans with (INR 16); [ simpl; lra | apply le_INR; lia ]).
  (* (ln2/2) N <= psi N *)
  assert (Hpsilow : ln 2 / 2 * INR N <= psi N).
  { apply Rle_trans with ((INR N - 1) * ln 2 - ln (INR (N + 1))); [ | apply psi_lower ].
    assert (Hsq : sqrt (INR N) <= ln 2 / 16 * INR N) by (apply HN1; lia).
    assert (Hsqrt2 : sqrt 2 * sqrt 2 = 2) by (apply sqrt_sqrt; lra).
    assert (Hsqrt2pos : 0 <= sqrt 2) by apply sqrt_pos.
    assert (Hsqrt2le : sqrt 2 <= 2) by nra.
    assert (HsqNnneg : 0 <= sqrt (INR N)) by apply sqrt_pos.
    assert (HlnN1 : ln (INR (N + 1)) <= 2 * sqrt (INR (N + 1)))
      by (apply ln_le_2sqrt; apply lt_0_INR; lia).
    assert (HsqN1 : sqrt (INR (N + 1)) <= sqrt 2 * sqrt (INR N)).
    { rewrite <- sqrt_mult by lra; apply sqrt_le_1_alt.
      rewrite plus_INR; simpl; nra. }
    nra. }
  (* divide by ln N *)
  apply Rle_trans with (psi N / ln (INR N)).
  - unfold Rdiv; rewrite <- Rmult_assoc.
    apply Rmult_le_compat_r; [ apply Rlt_le, Rinv_0_lt_compat; exact Hlnpos | exact Hpsilow ].
  - unfold Rdiv; apply (Rmult_le_reg_r (ln (INR N))); [ exact Hlnpos | ].
    rewrite Rmult_assoc, Rinv_l by lra; rewrite Rmult_1_r.
    apply psi_le_picount_lnN; lia.
Qed.

(* ================================================================= *)
(*  3.  the upper bound:  pi_count N <= (2 + 4 Kup) N / ln N          *)
(* ================================================================= *)

Lemma picount_upper : exists (b : R) (N0 : nat),
  forall N, (N0 <= N)%nat -> pi_count N <= b * (INR N / ln (INR N)).
Proof.
  exists (2 + 4 * Kup), 16%nat; intros N HN.
  set (y := Nat.sqrt N).
  assert (HyN : (y <= N)%nat) by (unfold y; apply Nat.sqrt_le_lin).
  assert (Hs16 : Nat.sqrt 16 = 4%nat) by reflexivity.
  assert (Hy2 : (2 <= y)%nat).
  { unfold y; apply Nat.le_trans with (Nat.sqrt 16);
      [ rewrite Hs16; lia | apply Nat.sqrt_le_mono; lia ]. }
  assert (HNpos : 0 < INR N) by (apply lt_0_INR; lia).
  assert (Hlnpos : 0 < ln (INR N)) by (apply ln_INR_pos; lia).
  assert (Hylnpos : 0 < ln (INR y)) by (apply ln_INR_pos; exact Hy2).
  (* split pi_count at y *)
  assert (Hsplit : pi_count N = Rsum iterm 1 y + Rsum iterm (1 + y) (N - y)).
  { rewrite pi_count_iterm.
    replace (Rsum iterm 1 N) with (Rsum iterm 1 (y + (N - y))) by (f_equal; lia).
    apply Rsum_split. }
  (* head <= INR y *)
  assert (Hhead : Rsum iterm 1 y <= INR y).
  { rewrite <- (Rsum_one 1 y); apply Rsum_le; intros n _.
    unfold iterm; destruct (primeb n); lra. }
  (* tail <= theta N / ln (INR y) *)
  assert (Htail : Rsum iterm (1 + y) (N - y) <= theta N / ln (INR y)).
  { apply Rle_trans with (Rsum (fun n => / ln (INR y) * tterm n) (1 + y) (N - y)).
    - apply Rsum_le; intros n Hn; apply in_seq in Hn.
      unfold iterm, tterm; destruct (primeb n) eqn:E;
        [ | rewrite Rmult_0_r; apply Rle_refl ].
      apply primeb_nprime in E; destruct E as [Hn2 _].
      apply (Rmult_le_reg_r (ln (INR y))); [ exact Hylnpos | ].
      replace (/ ln (INR y) * ln (INR n) * ln (INR y)) with (ln (INR n)) by (field; lra).
      rewrite Rmult_1_l; apply ln_le; [ apply lt_0_INR; lia | apply le_INR; lia ].
    - rewrite <- Rsum_scale.
      unfold Rdiv; rewrite (Rmult_comm (theta N)).
      apply Rmult_le_compat_l; [ apply Rlt_le, Rinv_0_lt_compat; exact Hylnpos | ].
      (* tail of theta <= theta N *)
      unfold theta.
      replace (Rsum tterm 1 N) with (Rsum tterm 1 (y + (N - y))) by (f_equal; lia).
      rewrite Rsum_split.
      assert (0 <= Rsum tterm 1 y) by (apply Rsum_nonneg; intros; apply tterm_nonneg); lra. }
  (* theta N <= psi N <= Kup * INR N *)
  assert (HthetaN : theta N <= Kup * INR N)
    by (apply Rle_trans with (psi N); [ apply theta_le_psi | rewrite Rmult_comm; apply psi_upper ]).
  (* assemble *)
  assert (HKup : 0 < Kup) by (unfold Kup; pose proof ln2_pos; lra).
  assert (Hlny4 : / 4 * ln (INR N) <= ln (INR y)) by (apply ln_sqrtN_lower; lia).
  (* pi_count N <= INR y + Kup*INR N/ln(INR y) <= 2N/lnN + 4 Kup N/lnN *)
  rewrite Hsplit.
  apply Rle_trans with (INR y + theta N / ln (INR y)).
  { apply Rplus_le_compat; assumption. }
  apply Rle_trans with (INR y + (Kup * INR N) / ln (INR y)).
  { apply Rplus_le_compat_l; unfold Rdiv; apply Rmult_le_compat_r;
      [ apply Rlt_le, Rinv_0_lt_compat; exact Hylnpos | exact HthetaN ]. }
  (* bound both summands by multiples of N/lnN *)
  assert (Hb1 : INR y <= 2 * (INR N / ln (INR N))).
  { apply Rle_trans with (sqrt (INR N)); [ apply INR_sqrt_le | ].
    apply (Rmult_le_reg_r (ln (INR N))); [ exact Hlnpos | ].
    unfold Rdiv; rewrite Rmult_assoc, Rmult_assoc, Rinv_l by lra; rewrite Rmult_1_r.
    pose proof (ln_le_2sqrt (INR N) HNpos) as Hls; pose proof (sqrt_pos (INR N)) as Hsp.
    assert (HNsq : sqrt (INR N) * sqrt (INR N) = INR N) by (apply sqrt_sqrt; lra); nra. }
  assert (Hb2core : INR N * / ln (INR y) <= 4 * (INR N * / ln (INR N))).
  { apply Rle_trans with (INR N * / (/ 4 * ln (INR N))).
    - apply Rmult_le_compat_l; [ lra | apply Rinv_le_contravar;
        [ apply Rmult_lt_0_compat; [ lra | exact Hlnpos ] | exact Hlny4 ] ].
    - rewrite Rinv_mult, Rinv_inv; apply Req_le; ring. }
  assert (Hb2 : (Kup * INR N) / ln (INR y) <= 4 * Kup * (INR N / ln (INR N))).
  { unfold Rdiv; rewrite Rmult_assoc.
    apply Rle_trans with (Kup * (4 * (INR N * / ln (INR N))));
      [ apply Rmult_le_compat_l; [ apply Rlt_le; exact HKup | exact Hb2core ] | apply Req_le; ring ]. }
  nra.
Qed.

(* ================================================================= *)
(*  4.  Chebyshev's theorem                                           *)
(* ================================================================= *)

Theorem chebyshev_theorem : exists (a b : R) (N0 : nat), 0 < a /\
  forall N, (N0 <= N)%nat ->
    a * (INR N / ln (INR N)) <= pi_count N /\ pi_count N <= b * (INR N / ln (INR N)).
Proof.
  destruct picount_lower as [a [Na [Ha Hlow]]].
  destruct picount_upper as [b [Nb Hupp]].
  exists a, b, (Nat.max Na Nb); split; [ exact Ha | ].
  intros N HN; split; [ apply Hlow; lia | apply Hupp; lia ].
Qed.

Print Assumptions chebyshev_theorem.

(* ================================================================= *)
(*  END ChebyshevPrime.v                                             *)
(*  pi(x) is pinned between a*x/ln x and b*x/ln x — Chebyshev's theorem.*)
(* ================================================================= *)
