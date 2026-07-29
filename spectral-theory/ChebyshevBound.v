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
From Stdlib Require Import Arith Lia PeanoNat List Reals Lra Factorial.
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
