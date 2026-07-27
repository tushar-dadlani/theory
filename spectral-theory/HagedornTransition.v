(* ================================================================= *)
(*  HagedornTransition.v                                            *)
(*                                                                    *)
(*  THE PRIMON-GAS PHASE TRANSITION at the critical temperature.     *)
(*                                                                    *)
(*  In the primon / Riemann gas (which `PrimonGas` models via unique  *)
(*  factorization), a prime `p` is a particle of energy `log p`, so a *)
(*  number `n` has energy `log n`, and the partition function at      *)
(*  inverse temperature `b` is the partial sum                        *)
(*      Zpart b N = Σ_{k=0}^N (k+1)^(−b)   ( → ζ(b) as N→∞ ).         *)
(*                                                                    *)
(*  The Hagedorn transition at the critical `b_c = 1`:                *)
(*    • SUBCRITICAL (b > 1): the partition function is FINITE         *)
(*        `Zpart_cv` — Zpart b converges (monotone + bounded, the     *)
(*        bound by Cauchy condensation ∑ 2^{j(1−b)} < ∞).             *)
(*    • CRITICAL   (b = 1): the partition function DIVERGES           *)
(*        `Zpart1_diverges` — the harmonic series is unbounded        *)
(*        (H_{2^m} ≥ 1 + m/2).                                        *)
(*  bundled in `hagedorn_transition`.                                 *)
(*                                                                    *)
(*  Over the classical `Reals` (quarantined: `Rpower` needs exp/ln,   *)
(*  `growing_cv` needs completeness — the partition function lives on  *)
(*  the analytic side, like `EulerProductR`).                        *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia Arith.
Local Open Scope R_scope.

Definition Zpart (b : R) (N : nat) : R := sum_f_R0 (fun k => Rpower (INR (S k)) (- b)) N.

Lemma Zpart1_eq_harmonic : forall N, Zpart 1 N = sum_f_R0 (fun k => / INR (S k)) N.
Proof.
  intro N; unfold Zpart; apply sum_eq; intros k Hk.
  rewrite Rpower_Ropp, Rpower_1 by (apply lt_0_INR; lia); reflexivity.
Qed.

Lemma sum_split : forall f a b,
  sum_f_R0 f (a + S b) = sum_f_R0 f a + sum_f_R0 (fun k => f (S a + k)%nat) b.
Proof.
  intros f a b; induction b as [|b IH].
  - replace (a + 1)%nat with (S a) by lia. cbn [sum_f_R0]. rewrite Nat.add_0_r. reflexivity.
  - replace (a + S (S b))%nat with (S (a + S b)) by lia.
    rewrite tech5, IH, tech5.
    replace (S a + S b)%nat with (S (a + S b)) by lia. ring.
Qed.

Lemma harmonic_double : forall n,
  sum_f_R0 (fun k => / INR (S k)) n + / 2 <= sum_f_R0 (fun k => / INR (S k)) (2 * n + 1).
Proof.
  intro n. replace (2 * n + 1)%nat with (n + S n)%nat by lia.
  rewrite (sum_split (fun k => / INR (S k)) n n).
  apply Rplus_le_compat_l.
  apply Rle_trans with (sum_f_R0 (fun _ => / INR (2 * S n)) n).
  - right. rewrite sum_cte, mult_INR. replace (INR 2) with 2 by (simpl; ring).
    field. apply Rgt_not_eq, lt_0_INR; lia.
  - apply sum_Rle; intros k Hk. apply Rinv_le_contravar.
    + apply lt_0_INR; lia.
    + apply le_INR; lia.
Qed.

Lemma harmonic_ge : forall m, 1 + INR m / 2 <= sum_f_R0 (fun k => / INR (S k)) (2 ^ m - 1).
Proof.
  induction m as [|m IH].
  - replace (2 ^ 0 - 1)%nat with 0%nat by reflexivity.
    cbn [sum_f_R0]. rewrite INR_1, Rinv_1. simpl (INR 0). lra.
  - assert (H1 : (1 <= 2 ^ m)%nat) by (assert (2 ^ m <> 0)%nat by (apply Nat.pow_nonzero; discriminate); lia).
    replace (2 ^ S m - 1)%nat with (2 * (2 ^ m - 1) + 1)%nat
      by (rewrite Nat.pow_succ_r'; lia).
    eapply Rle_trans; [ | apply harmonic_double ].
    assert (E : 1 + INR (S m) / 2 = (1 + INR m / 2) + / 2) by (rewrite S_INR; field).
    rewrite E. apply Rplus_le_compat_r. exact IH.
Qed.

Lemma harmonic_diverges : forall M, exists N, sum_f_R0 (fun k => / INR (S k)) N > M.
Proof.
  intro M. destruct (INR_unbounded (2 * M)) as [m Hm].
  exists (2 ^ m - 1)%nat.
  apply Rlt_le_trans with (1 + INR m / 2); [ lra | apply harmonic_ge ].
Qed.

Theorem Zpart1_diverges : forall M, exists N, Zpart 1 N > M.
Proof. intro M; destruct (harmonic_diverges M) as [N HN]; exists N; rewrite Zpart1_eq_harmonic; exact HN. Qed.

(* ---- Part B: convergence for b > 1 (Cauchy condensation) ---- *)
Lemma Rpower_pos : forall x y, 0 < Rpower x y.
Proof. intros; unfold Rpower; apply exp_pos. Qed.

Lemma Rpower_negexp_antimono : forall x y e, 0 < x -> x <= y -> 0 <= e -> Rpower y (- e) <= Rpower x (- e).
Proof.
  intros x y e Hx Hxy He. unfold Rpower.
  assert (Hln : ln x <= ln y)
    by (destruct (Rle_lt_or_eq _ _ Hxy) as [Hlt|Heq]; [ left; apply ln_increasing; lra | rewrite Heq; apply Rle_refl ]).
  assert (Harg : - e * ln y <= - e * ln x) by nra.
  destruct (Rle_lt_or_eq _ _ Harg) as [Hlt|Heq]; [ left; apply exp_increasing; exact Hlt | rewrite Heq; apply Rle_refl ].
Qed.

Lemma Zpart_growing : forall b, Un_growing (Zpart b).
Proof.
  intros b n; unfold Zpart; rewrite tech5; cbn beta.
  pose proof (Rpower_pos (INR (S (S n))) (- b)); lra.
Qed.

Lemma Zpart_mono : forall b M N, (M <= N)%nat -> Zpart b M <= Zpart b N.
Proof.
  intros b M N; induction N as [|N IH]; intro H.
  - assert (M = 0)%nat by lia; subst; apply Rle_refl.
  - destruct (Nat.eq_dec M (S N)) as [->|Hne]; [ apply Rle_refl | ].
    apply Rle_trans with (Zpart b N); [ apply IH; lia | apply Zpart_growing ].
Qed.

Lemma pow2_pos : forall m, (0 < 2 ^ m)%nat.
Proof. intro m; apply Nat.neq_0_lt_0, Nat.pow_nonzero; discriminate. Qed.

Lemma block_val : forall b m, Rpower (INR (2 ^ m)) (- b) * INR (2 ^ m) = Rpower 2 (1 - b) ^ m.
Proof.
  intros b m. assert (Hpos : 0 < INR (2 ^ m)) by (apply lt_0_INR, pow2_pos).
  rewrite <- (Rpower_1 (INR (2 ^ m))) at 2 by exact Hpos.
  rewrite <- Rpower_plus. replace (- b + 1) with (1 - b) by ring.
  rewrite pow_INR. replace (INR 2) with 2 by (simpl; ring).
  rewrite <- (Rpower_pow m 2) by lra. rewrite Rpower_mult.
  rewrite <- (Rpower_pow m (Rpower 2 (1 - b))) by (apply Rpower_pos). rewrite Rpower_mult.
  f_equal; ring.
Qed.

Lemma Zpart_block : forall b m, 1 < b ->
  Zpart b (2 ^ S m - 1) <= Zpart b (2 ^ m - 1) + Rpower 2 (1 - b) ^ m.
Proof.
  intros b m Hb. pose proof (pow2_pos m) as H2m.
  replace (2 ^ S m - 1)%nat with ((2 ^ m - 1) + S (2 ^ m - 1))%nat
    by (rewrite Nat.pow_succ_r'; lia).
  unfold Zpart. rewrite (sum_split (fun k => Rpower (INR (S k)) (- b)) (2 ^ m - 1) (2 ^ m - 1)).
  apply Rplus_le_compat_l.
  apply Rle_trans with (Rpower (INR (2 ^ m)) (- b) * INR (2 ^ m)).
  - apply Rle_trans with (sum_f_R0 (fun _ => Rpower (INR (2 ^ m)) (- b)) (2 ^ m - 1)).
    + apply sum_Rle; intros k Hk. cbn beta.
      apply Rpower_negexp_antimono; [ apply lt_0_INR, pow2_pos | apply le_INR; lia | lra ].
    + rewrite sum_cte. replace (INR (S (2 ^ m - 1))) with (INR (2 ^ m)) by (f_equal; lia).
      apply Rle_refl.
  - apply Req_le, block_val.
Qed.

Lemma Hdya : forall b, 1 < b -> forall m,
  Zpart b (2 ^ m - 1) <= 1 + (1 - Rpower 2 (1 - b) ^ m) / (1 - Rpower 2 (1 - b)).
Proof.
  intros b Hb. set (r := Rpower 2 (1 - b)).
  assert (Hr0 : 0 < r) by (apply Rpower_pos).
  assert (Hr1 : r < 1)
    by (unfold r; apply Rlt_le_trans with (Rpower 2 0); [ apply Rpower_lt; lra | rewrite Rpower_O; lra ]).
  induction m as [|m IH].
  - replace (2 ^ 0 - 1)%nat with 0%nat by reflexivity.
    unfold Zpart; cbn [sum_f_R0]; rewrite INR_1; unfold Rpower; rewrite ln_1, Rmult_0_r, exp_0.
    right; simpl (r ^ 0); field; lra.
  - eapply Rle_trans; [ apply Zpart_block; exact Hb | ].
    fold r. eapply Rle_trans; [ apply Rplus_le_compat_r; exact IH | ].
    assert (Hrs : r ^ S m = r * r ^ m) by (simpl; ring).
    right; rewrite Hrs; field; lra.
Qed.

Lemma le_pow2 : forall n, (n <= 2 ^ n - 1)%nat.
Proof.
  intro n; assert (S n <= 2 ^ n)%nat; [ | lia ].
  induction n as [|n IH]; [ simpl; lia | rewrite Nat.pow_succ_r'; lia ].
Qed.

Lemma Zpart_ub : forall b, 1 < b -> has_ub (Zpart b).
Proof.
  intros b Hb. set (r := Rpower 2 (1 - b)).
  assert (Hr0 : 0 < r) by (apply Rpower_pos).
  assert (Hr1 : r < 1)
    by (unfold r; apply Rlt_le_trans with (Rpower 2 0); [ apply Rpower_lt; lra | rewrite Rpower_O; lra ]).
  unfold has_ub, bound, is_upper_bound, EUn.
  exists (1 + 1 / (1 - r)). intros x [n Hn]. rewrite Hn.
  apply Rle_trans with (Zpart b (2 ^ n - 1)); [ apply Zpart_mono, le_pow2 | ].
  apply Rle_trans with (1 + (1 - r ^ n) / (1 - r)); [ apply Hdya; exact Hb | ].
  apply Rplus_le_compat_l. unfold Rdiv. apply Rmult_le_compat_r.
  - left; apply Rinv_0_lt_compat; lra.
  - assert (0 < r ^ n) by (apply pow_lt; exact Hr0); lra.
Qed.

Theorem Zpart_cv : forall b, 1 < b -> { l : R | Un_cv (Zpart b) l }.
Proof. intros b Hb; apply growing_cv; [ apply Zpart_growing | apply Zpart_ub; exact Hb ]. Qed.

Theorem hagedorn_transition :
  (forall b, 1 < b -> exists l : R, Un_cv (Zpart b) l) /\
  (forall M : R, exists N, Zpart 1 N > M).
Proof.
  split; [ | exact Zpart1_diverges ].
  intros b Hb; destruct (Zpart_cv b Hb) as [l Hl]; exists l; exact Hl.
Qed.

Print Assumptions hagedorn_transition.

(* ================================================================= *)
(*  END HagedornTransition.v.  Partition function finite for b>1,     *)
(*  divergent at b=1 — the primon-gas phase transition.              *)
(* ================================================================= *)
