(* ================================================================= *)
(*  ChebyshevBound.v  —  the Chebyshev prime bound  ψ(x) ≍ x.          *)
(*                                                                    *)
(*  Contour-free, from the pieces already proven:                    *)
(*   • order_swap_identity : Σ_{n≤N} log n = Σ_{d≤N} Λ(d)⌊N/d⌋  (Chebyshev)*)
(*   • Tlog_eq_ln_fact    : Σ_{n≤N} log n = log(N!)            (Chebyshev)*)
(*   • central_upper/lower: (2M)! ≍ 4^M·(M!)²            (CentralBinomialBound)*)
(*                                                                    *)
(*  STEP 1 (this section) — the squeeze.  With D(N) := chsum N −       *)
(*  2·chsum(⌊N/2⌋) = Σ_{d≤N} Λ(d)·(⌊N/d⌋ mod 2), and Λ ≥ 0 with each   *)
(*  coefficient in {0,1}:                                            *)
(*        ψ(N) − ψ(⌊N/2⌋)  ≤  D(N)  ≤  ψ(N).                          *)
(*  (Steps 2–3 — the D(N) ≍ N estimate and the dyadic telescoping —   *)
(*  follow; see below.)  Uses classical Reals (quarantined, via ln).  *)
(* ================================================================= *)

Require Import VonMangoldtGlobal Chebyshev CentralBinomialBound.
From Stdlib Require Import Arith Lia PeanoNat List Reals Lra Factorial Wf_nat.
Import ListNotations.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  A tiny sum toolkit:  Rsum f a n = Σ_{i=a}^{a+n−1} f i.            *)
(* ----------------------------------------------------------------- *)
Definition Rsum (f : nat -> R) (a n : nat) : R := fold_right Rplus 0%R (map f (seq a n)).

Lemma Rsum_split : forall f a m k, Rsum f a (m + k) = (Rsum f a m + Rsum f (a + m) k)%R.
Proof. intros; unfold Rsum; rewrite seq_app, map_app, Rsum_app; reflexivity. Qed.

Lemma Rsum_le : forall f g a n,
  (forall i, In i (seq a n) -> f i <= g i) -> Rsum f a n <= Rsum g a n.
Proof.
  intros f g a n; unfold Rsum; generalize (seq a n) as l; intro l.
  induction l as [| x l IH]; intro H; simpl; [ lra | ].
  apply Rplus_le_compat; [ apply H; left; reflexivity | apply IH; intros i Hi; apply H; right; exact Hi ].
Qed.

Lemma Rsum_ext : forall f g a n,
  (forall i, In i (seq a n) -> f i = g i) -> Rsum f a n = Rsum g a n.
Proof.
  intros f g a n; unfold Rsum; generalize (seq a n) as l; intro l.
  induction l as [| x l IH]; intro H; simpl; [ reflexivity | ].
  f_equal; [ apply H; left; reflexivity | apply IH; intros i Hi; apply H; right; exact Hi ].
Qed.

Lemma Rsum_nonneg : forall f a n,
  (forall i, In i (seq a n) -> 0 <= f i) -> 0 <= Rsum f a n.
Proof.
  intros f a n; unfold Rsum; generalize (seq a n) as l; intro l.
  induction l as [| x l IH]; intro H; simpl; [ lra | ].
  apply Rplus_le_le_0_compat; [ apply H; left; reflexivity | apply IH; intros i Hi; apply H; right; exact Hi ].
Qed.

Lemma Rsum_scale : forall c f a n, (c * Rsum f a n)%R = Rsum (fun i => c * f i) a n.
Proof.
  intros c f a n; unfold Rsum; generalize (seq a n) as l; intro l.
  induction l as [| x l IH]; simpl; [ ring | rewrite <- IH; ring ].
Qed.

Lemma Rsum_minus : forall f g a n, (Rsum f a n - Rsum g a n)%R = Rsum (fun i => f i - g i) a n.
Proof.
  intros f g a n; unfold Rsum; generalize (seq a n) as l; intro l.
  induction l as [| x l IH]; simpl; [ ring | rewrite <- IH; ring ].
Qed.

Lemma Rsum_const0 : forall a n, Rsum (fun _ => 0%R) a n = 0%R.
Proof.
  intros a n; unfold Rsum; generalize (seq a n) as l; intro l.
  induction l as [| x l IH]; simpl; [ reflexivity | rewrite IH; ring ].
Qed.

Lemma div2_le : forall N, (N / 2 <= N)%nat.
Proof. intro N; apply Nat.div_le_upper_bound; lia. Qed.

(* ----------------------------------------------------------------- *)
(*  The {0,1} coefficient  a_d = ⌊N/d⌋ − 2⌊N/2d⌋ = ⌊N/d⌋ mod 2.       *)
(* ----------------------------------------------------------------- *)
Definition coef (N d : nat) : nat := (N / d - 2 * (N / (2 * d)))%nat.

Lemma coef_eq_mod : forall N d, (1 <= d)%nat -> coef N d = ((N / d) mod 2)%nat.
Proof. intros N d Hd; unfold coef; apply floor_half_step; exact Hd. Qed.

Lemma coef_le1 : forall N d, (1 <= d)%nat -> (coef N d <= 1)%nat.
Proof. intros N d Hd; rewrite coef_eq_mod by exact Hd; pose proof (Nat.mod_upper_bound (N / d) 2); lia. Qed.

(* on the top half  N/2 < d ≤ N,  ⌊N/d⌋ = 1  so the coefficient is 1 *)
Lemma coef_tail : forall N d, (N / 2 < d)%nat -> (d <= N)%nat -> coef N d = 1%nat.
Proof.
  intros N d Hlo Hhi.
  assert (Hd : (1 <= d)%nat) by lia.
  assert (H2d : (N < 2 * d)%nat).
  { pose proof (Nat.div_mod N 2 ltac:(lia)); pose proof (Nat.mod_upper_bound N 2 ltac:(lia)); lia. }
  assert (Hq : (N / d = 1)%nat).
  { pose proof (Nat.div_mod N d ltac:(lia)); pose proof (Nat.mod_upper_bound N d ltac:(lia)); nia. }
  assert (Hq2 : (N / (2 * d) = 0)%nat) by (apply Nat.div_small; lia).
  unfold coef; rewrite Hq, Hq2; lia.
Qed.

(* ----------------------------------------------------------------- *)
(*  chsum(⌊N/2⌋) re-indexed over [1..N] with ⌊N/2d⌋ (zeros past N/2). *)
(* ----------------------------------------------------------------- *)
Lemma chsum_half : forall N,
  chsum (N / 2) = Rsum (fun d => Lam d * INR (N / (2 * d)))%R 1 N.
Proof.
  intro N.
  assert (Hc : chsum (N / 2) = Rsum (fun d => Lam d * INR (N / (2 * d)))%R 1 (N / 2)).
  { unfold chsum, Rsum. f_equal. apply map_ext_in.
    intros d Hd; apply in_seq in Hd. rewrite Nat.Div0.div_div. reflexivity. }
  rewrite Hc.
  replace N with (N / 2 + (N - N / 2))%nat at 2 by (pose proof (div2_le N); lia).
  rewrite Rsum_split.
  assert (Htail : Rsum (fun d => Lam d * INR (N / (2 * d)))%R (1 + N / 2) (N - N / 2) = 0%R).
  { rewrite (Rsum_ext _ (fun _ => 0%R)); [ apply Rsum_const0 | ].
    intros d Hd; apply in_seq in Hd.
    assert (N / (2 * d) = 0)%nat by
      (apply Nat.div_small; pose proof (Nat.div_mod N 2 ltac:(lia));
       pose proof (Nat.mod_upper_bound N 2 ltac:(lia)); lia).
    rewrite H; simpl; ring. }
  rewrite Htail; ring.
Qed.

Lemma psi_Rsum : forall N, psi N = Rsum Lam 1 N.
Proof. reflexivity. Qed.

Lemma INR2 : INR 2 = 2%R.
Proof. simpl; lra. Qed.

Lemma Rsum_split_half : forall f N,
  Rsum f 1 N = (Rsum f 1 (N / 2) + Rsum f (1 + N / 2) (N - N / 2))%R.
Proof. intros f N; replace N with (N / 2 + (N - N / 2))%nat at 1 by (pose proof (div2_le N); lia); apply Rsum_split. Qed.

(* D(N) = chsum N − 2·chsum(⌊N/2⌋) as the {0,1}-coefficient sum *)
Definition Dch (N : nat) : R := (chsum N - 2 * chsum (N / 2))%R.

Lemma D_as_sum : forall N, Dch N = Rsum (fun d => Lam d * INR (coef N d))%R 1 N.
Proof.
  intro N; unfold Dch.
  assert (HchN : chsum N = Rsum (fun d => Lam d * INR (N / d))%R 1 N) by reflexivity.
  rewrite HchN, chsum_half, Rsum_scale, Rsum_minus.
  apply Rsum_ext; intros d Hd; apply in_seq in Hd.
  assert (Hge : (2 * (N / (2 * d)) <= N / d)%nat).
  { replace (2 * d)%nat with (d * 2)%nat by lia. rewrite <- Nat.Div0.div_div.
    pose proof (Nat.div_mod (N / d) 2 ltac:(lia)); lia. }
  unfold coef; rewrite minus_INR by exact Hge; rewrite mult_INR, INR2; ring.
Qed.

(* ================================================================= *)
(*  STEP 1 — THE SQUEEZE.                                            *)
(* ================================================================= *)
Theorem squeeze_upper : forall N, Dch N <= psi N.
Proof.
  intro N; rewrite D_as_sum, psi_Rsum.
  apply Rsum_le; intros d Hd; apply in_seq in Hd.
  assert (Hc : INR (coef N d) <= 1).
  { pose proof (coef_le1 N d ltac:(lia)) as Hle; apply le_INR in Hle; rewrite INR_1 in Hle; exact Hle. }
  pose proof (Lam_nonneg d); nra.
Qed.

Theorem squeeze_lower : forall N, (psi N - psi (N / 2) <= Dch N)%R.
Proof.
  intro N; rewrite D_as_sum.
  assert (Htail : (psi N - psi (N / 2))%R = Rsum Lam (1 + N / 2) (N - N / 2)).
  { rewrite (psi_Rsum N), (psi_Rsum (N / 2)), (Rsum_split_half Lam N); ring. }
  rewrite Htail, (Rsum_split_half (fun d => Lam d * INR (coef N d))%R N).
  assert (Hhead : 0 <= Rsum (fun d => Lam d * INR (coef N d))%R 1 (N / 2)).
  { apply Rsum_nonneg; intros d Hd; apply in_seq in Hd.
    apply Rmult_le_pos; [ apply Lam_nonneg | apply pos_INR ]. }
  assert (Heq : Rsum (fun d => Lam d * INR (coef N d))%R (1 + N / 2) (N - N / 2)
                = Rsum Lam (1 + N / 2) (N - N / 2)).
  { apply Rsum_ext; intros d Hd; apply in_seq in Hd.
    assert (coef N d = 1)%nat by (apply coef_tail; lia).
    rewrite H, INR_1; ring. }
  rewrite Heq; lra.
Qed.

Print Assumptions squeeze_upper.

(* ================================================================= *)
(*  STEP 2 — THE NUMERICAL INPUT  D(N) ≍ N  (central binomial).      *)
(*                                                                    *)
(*  D(N) = chsum N − 2·chsum(⌊N/2⌋) = log(N!) − 2·log(⌊N/2⌋!).        *)
(*  With  4^M/(2M+1) ≤ C(2M,M) ≤ 4^M  (CentralBinomialBound):        *)
(*     D(2M) ≤ (2M)·log2,   (2M)·log2 − log(2M+1) ≤ D(2M),           *)
(*  and, uniformly in parity,  D(N) ≤ N·log2 + log(N+1).             *)
(* ================================================================= *)

(* real logs of factorials are positive, and small ln toolkit *)
Lemma lnfact_pos : forall n, (0 < INR (fact n))%R.
Proof. intro n; apply lt_0_INR, lt_O_fact. Qed.

Lemma lpos : forall n, (1 <= n)%nat -> (0 <= ln (INR n))%R.
Proof. intros n Hn; apply ln_ge0; rewrite <- INR_1; apply le_INR; lia. Qed.

Lemma ln_le : forall x y, (0 < x)%R -> (x <= y)%R -> (ln x <= ln y)%R.
Proof.
  intros x y Hx Hxy; destruct (Rle_lt_or_eq_dec x y Hxy) as [Hlt|Heq].
  - left; apply ln_increasing; assumption.
  - rewrite Heq; apply Rle_refl.
Qed.

Lemma ln4 : ln (INR 4) = (2 * ln 2)%R.
Proof. replace (INR 4) with (2 * 2)%R by (simpl; lra); rewrite ln_mult by lra; lra. Qed.

Lemma half_2M : forall M, ((2 * M) / 2 = M)%nat.
Proof. intro M; rewrite Nat.mul_comm; apply Nat.div_mul; lia. Qed.

(* the ln-factorial form of D(N) via the order-swap identity *)
Lemma Dch_eq_ln : forall N,
  Dch N = (ln (INR (fact N)) - 2 * ln (INR (fact (N / 2))))%R.
Proof.
  intro N; unfold Dch.
  rewrite <- (order_swap_identity N), <- (order_swap_identity (N / 2)).
  rewrite !Tlog_eq_ln_fact; ring.
Qed.

(* upper Chebyshev numeric bound on the even argument *)
Lemma D_upper_even : forall M, (Dch (2 * M) <= INR (2 * M) * ln 2)%R.
Proof.
  intro M.
  rewrite Dch_eq_ln.
  rewrite (half_2M M).
  pose proof (central_upper M) as HC.
  apply le_INR in HC.
  rewrite !mult_INR, pow_INR in HC.
  set (b := INR (fact M)) in *.
  set (a := INR (fact (2 * M))) in *.
  assert (Hb : (0 < b)%R) by apply lnfact_pos.
  assert (Ha : (0 < a)%R) by apply lnfact_pos.
  assert (H4 : (0 < INR 4)%R) by (simpl; lra).
  assert (Hpow : (0 < INR 4 ^ M)%R) by (apply pow_lt; exact H4).
  assert (Hbb : (0 < b * b)%R) by (apply Rmult_lt_0_compat; exact Hb).
  assert (Hln : (ln a <= ln (INR 4 ^ M * (b * b)))%R)
    by (apply ln_le; [ exact Ha | exact HC ]).
  rewrite (ln_mult _ _ Hpow Hbb), (ln_pow (INR 4) H4 M),
          (ln_mult _ _ Hb Hb), ln4 in Hln.
  rewrite mult_INR, INR2.
  nra.
Qed.

(* lower Chebyshev numeric bound on the even argument *)
Lemma D_lower_even : forall M,
  (INR (2 * M) * ln 2 - ln (INR (2 * M + 1)) <= Dch (2 * M))%R.
Proof.
  intro M.
  rewrite Dch_eq_ln.
  rewrite (half_2M M).
  pose proof (central_lower M) as HC.
  apply le_INR in HC.
  rewrite !mult_INR, pow_INR in HC.
  set (b := INR (fact M)) in *.
  set (a := INR (fact (2 * M))) in *.
  assert (Hb : (0 < b)%R) by apply lnfact_pos.
  assert (Ha : (0 < a)%R) by apply lnfact_pos.
  assert (H4 : (0 < INR 4)%R) by (simpl; lra).
  assert (Hpow : (0 < INR 4 ^ M)%R) by (apply pow_lt; exact H4).
  assert (Hbb : (0 < b * b)%R) by (apply Rmult_lt_0_compat; exact Hb).
  assert (Hs : (0 < INR (2 * M + 1))%R) by (apply lt_0_INR; lia).
  assert (Hlhs : (0 < INR 4 ^ M * (b * b))%R) by (apply Rmult_lt_0_compat; [exact Hpow|exact Hbb]).
  assert (Hln : (ln (INR 4 ^ M * (b * b)) <= ln (INR (2 * M + 1) * a))%R)
    by (apply ln_le; [ exact Hlhs | exact HC ]).
  rewrite (ln_mult _ _ Hpow Hbb), (ln_pow (INR 4) H4 M),
          (ln_mult _ _ Hb Hb), ln4, (ln_mult _ _ Hs Ha) in Hln.
  rewrite mult_INR, INR2.
  nra.
Qed.

(* the uniform (all-N) upper bound  D(N) ≤ N·log2 + log(N+1) *)
Lemma D_upper : forall N,
  (Dch N <= INR N * ln 2 + ln (INR (N + 1)))%R.
Proof.
  intro N.
  assert (Hln2 : (0 <= ln 2)%R) by (apply ln_ge0; lra).
  pose proof (Nat.div_mod N 2 ltac:(lia)) as Hdm.
  pose proof (Nat.mod_upper_bound N 2 ltac:(lia)) as Hmb.
  destruct (N mod 2) as [|[|r]] eqn:Er; [ | | lia ].
  - (* even: N = 2*(N/2) *)
    assert (HNeq : N = (2 * (N / 2))%nat) by lia.
    assert (Hpos : (0 <= ln (INR (N + 1)))%R) by (apply lpos; lia).
    rewrite HNeq at 1.
    pose proof (D_upper_even (N / 2)) as HE.
    replace (INR (2 * (N / 2))) with (INR N) in HE by (rewrite <- HNeq; reflexivity).
    lra.
  - (* odd: N = 2*(N/2) + 1 *)
    set (M := (N / 2)%nat).
    assert (HNeq : N = (2 * M + 1)%nat) by (unfold M; lia).
    assert (Hdch : Dch N = (ln (INR (fact N)) - 2 * ln (INR (fact M)))%R)
      by (rewrite Dch_eq_ln; reflexivity).
    assert (Hb : (0 < INR (fact M))%R) by apply lnfact_pos.
    assert (H4 : (0 < INR 4)%R) by (simpl; lra).
    assert (Hpow : (0 < INR 4 ^ M)%R) by (apply pow_lt; exact H4).
    assert (Hbb : (0 < INR (fact M) * INR (fact M))%R) by (apply Rmult_lt_0_compat; exact Hb).
    assert (Hrhs : (0 < INR 4 ^ M * (INR (fact M) * INR (fact M)))%R)
      by (apply Rmult_lt_0_compat; [exact Hpow|exact Hbb]).
    assert (Hs : (0 < INR (2 * M + 1))%R) by (apply lt_0_INR; lia).
    assert (HfN : INR (fact N) = (INR (2 * M + 1) * INR (fact (2 * M)))%R).
    { replace (fact N) with ((2 * M + 1) * fact (2 * M))%nat.
      - rewrite mult_INR; reflexivity.
      - replace N with (S (2 * M)) by lia; rewrite fact_S; f_equal; lia. }
    pose proof (central_upper M) as HC.
    apply le_INR in HC.
    rewrite !mult_INR, pow_INR in HC.
    assert (Hfbound : (INR (fact N) <=
                       INR (2 * M + 1) * (INR 4 ^ M * (INR (fact M) * INR (fact M))))%R).
    { rewrite HfN; apply Rmult_le_compat_l; [ apply Rlt_le; exact Hs | exact HC ]. }
    assert (Hlnbound : (ln (INR (fact N)) <=
                        ln (INR (2 * M + 1)) + INR M * (2 * ln 2)
                        + (ln (INR (fact M)) + ln (INR (fact M))))%R).
    { eapply Rle_trans.
      - apply ln_le; [ apply lnfact_pos | exact Hfbound ].
      - rewrite (ln_mult _ _ Hs Hrhs), (ln_mult _ _ Hpow Hbb),
                (ln_pow (INR 4) H4 M), ln4, (ln_mult _ _ Hb Hb); lra. }
    assert (Hmono : (ln (INR (2 * M + 1)) <= ln (INR (N + 1)))%R)
      by (apply ln_le; [ apply lt_0_INR; lia | apply le_INR; lia ]).
    assert (HNln2 : (INR N * ln 2 = 2 * INR M * ln 2 + ln 2)%R).
    { rewrite HNeq, plus_INR, mult_INR, INR2, INR_1; ring. }
    rewrite Hdch; nra.
Qed.

(* ================================================================= *)
(*  STEP 3 — THE CHEBYSHEV BOUND  ψ(x) ≍ x.                          *)
(*                                                                    *)
(*  Lower:  ψ(2M) ≥ (2M)·log2 − log(2M+1)   (immediate from          *)
(*          squeeze_upper : D(N) ≤ ψ(N), and STEP 2 lower).          *)
(*  Upper:  ψ(N) ≤ (2·log2 + 2)·N, by strong induction on N: with    *)
(*          squeeze_lower  ψ(N) − ψ(⌊N/2⌋) ≤ D(N)  and D_upper,       *)
(*          ψ(N) ≤ D(N) + ψ(⌊N/2⌋) ≤ (N·log2 + log(N+1)) + K·⌊N/2⌋,   *)
(*          and log(N+1) ≤ N closes the recursion at K = 2·log2 + 2. *)
(* ================================================================= *)

(* ln x ≤ x − 1, hence log(N+1) ≤ N *)
Lemma ln_self1 : forall x, (0 < x)%R -> (ln x <= x - 1)%R.
Proof.
  intros x Hx; destruct (Req_dec x 1) as [->|Hne].
  - rewrite ln_1; lra.
  - assert (Hx1 : (x - 1)%R <> 0%R) by (intro Hc; apply Hne; lra).
    pose proof (exp_ineq1 (x - 1) Hx1) as He.
    assert (Hlt : (x < exp (x - 1))%R) by lra.
    apply (ln_increasing x (exp (x - 1)) Hx) in Hlt.
    rewrite ln_exp in Hlt; lra.
Qed.

Lemma ln_Sn_le : forall n, (ln (INR (n + 1)) <= INR n)%R.
Proof.
  intro n.
  assert (H : (0 < INR (n + 1))%R) by (apply lt_0_INR; lia).
  pose proof (ln_self1 (INR (n + 1)) H) as HH.
  replace (INR (n + 1)) with (INR n + 1)%R in HH |- *
    by (rewrite plus_INR, INR_1; reflexivity).
  lra.
Qed.

Lemma psi_0 : psi 0 = 0%R.
Proof. reflexivity. Qed.

(* the explicit Chebyshev constant for the upper bound *)
Definition Kup : R := (2 * ln 2 + 2)%R.

(* UPPER: ψ(N) ≤ (2·log2 + 2)·N, for every N *)
Theorem psi_upper : forall N, (psi N <= INR N * Kup)%R.
Proof.
  intro N.
  apply (lt_wf_ind N (fun n => (psi n <= INR n * Kup)%R)).
  clear N; intros N IH.
  destruct (Nat.eq_dec N 0) as [->|Hpos].
  - rewrite psi_0; simpl; lra.
  - pose (m := (N / 2)%nat).
    assert (HMlt : (m < N)%nat) by (unfold m; apply Nat.div_lt; lia).
    specialize (IH m HMlt).
    pose proof (squeeze_lower N) as HS; fold m in HS.
    pose proof (D_upper N) as HD.
    pose proof (ln_Sn_le N) as HL.
    assert (H2M : (2 * INR m <= INR N)%R).
    { replace (2 * INR m)%R with (INR (2 * m)) by (rewrite mult_INR, INR2; ring).
      apply le_INR; unfold m.
      pose proof (Nat.div_mod N 2 ltac:(lia));
      pose proof (Nat.mod_upper_bound N 2 ltac:(lia)); lia. }
    assert (Hln2 : (0 <= ln 2)%R) by (apply ln_ge0; lra).
    assert (Hprod : (2 * (INR m * ln 2) <= INR N * ln 2)%R).
    { replace (2 * (INR m * ln 2))%R with (2 * INR m * ln 2)%R by ring.
      apply Rmult_le_compat_r; [ exact Hln2 | exact H2M ]. }
    unfold Kup in *.
    replace (INR N * (2 * ln 2 + 2))%R
      with (2 * (INR N * ln 2) + 2 * INR N)%R by ring.
    replace (INR m * (2 * ln 2 + 2))%R
      with (2 * (INR m * ln 2) + 2 * INR m)%R in IH by ring.
    lra.
Qed.

(* LOWER: ψ(2M) ≥ (2M)·log2 − log(2M+1) *)
Theorem psi_lower_even : forall M,
  (INR (2 * M) * ln 2 - ln (INR (2 * M + 1)) <= psi (2 * M))%R.
Proof.
  intro M.
  pose proof (squeeze_upper (2 * M)) as HU.
  pose proof (D_lower_even M) as HD.
  lra.
Qed.

(* ================================================================= *)
(*  THE CHEBYSHEV BOUND  ψ(x) ≍ x  (two-sided, explicit constants).  *)
(*    0 < log2,                                                       *)
(*    ψ(N)   ≤ (2·log2 + 2)·N            (all N),                     *)
(*    ψ(2M)  ≥ (2M)·log2 − log(2M+1)     (even lower witness).        *)
(* ================================================================= *)
Theorem chebyshev_psi_bound :
  (0 < ln 2)%R
  /\ (forall N, (psi N <= INR N * (2 * ln 2 + 2))%R)
  /\ (forall M, (INR (2 * M) * ln 2 - ln (INR (2 * M + 1)) <= psi (2 * M))%R).
Proof.
  repeat split.
  - rewrite <- ln_1; apply ln_increasing; lra.
  - exact psi_upper.
  - exact psi_lower_even.
Qed.

Print Assumptions chebyshev_psi_bound.
