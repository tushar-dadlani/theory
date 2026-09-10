(* ================================================================= *)
(*  CLPhi0Lower.v  --  Phi(sigma,chi_0) is unbounded as sigma -> 1+.  *)
(*                                                                    *)
(*  CLPrincipalLogDeriv.pchi0_val says Phi(s,chi_0) is the ordinary    *)
(*  von Mangoldt series with the terms divisible by p deleted.  This   *)
(*  file bounds what was deleted and concludes that the remainder      *)
(*  still diverges.                                                    *)
(*                                                                    *)
(*  THE DELETED PART SPLITS IN TWO, and neither half needs a new       *)
(*  reindexing over prime powers:                                     *)
(*    - the single term n = p, worth ln p * p^{-sigma} <= ln p;        *)
(*    - every other n divisible by p, which is then NOT prime (a       *)
(*      prime divisible by p equals p), so Lambda(n) = bpp(n) there    *)
(*      and CPPowTail.ppow_tail_bound caps the whole lot by Kpp.       *)
(*  So the deletion costs at most ln p + Kpp, a constant, while        *)
(*  CPhiZetaLower.PhiR_unbounded makes the full series exceed any M.   *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia Arith List ZArith Znumtheory.
Require Import VonMangoldtGlobal Ell2Primes Chebyshev ChebyshevPrime
        PrimePowerReindex CPPowTail CPhiZetaLower CZetaTerm2 CLWeightAnti.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  Part A -- generic sum lemmas.                                      *)
(* ----------------------------------------------------------------- *)

Lemma sum_f_R0_plus : forall f g N,
  sum_f_R0 (fun k => f k + g k) N = sum_f_R0 f N + sum_f_R0 g N.
Proof.
  intros f g N. induction N as [| N IH]; [ reflexivity | ].
  rewrite !tech5, IH. ring.
Qed.

Lemma sum_zero_below : forall f N,
  (forall k, (k <= N)%nat -> f k = 0) -> sum_f_R0 f N = 0.
Proof.
  intros f N. induction N as [| N IH]; intro H.
  - cbn [sum_f_R0]. apply H. lia.
  - rewrite tech5, (H (S N)) by lia.
    rewrite IH by (intros k Hk; apply H; lia). ring.
Qed.

Lemma sum_single_le : forall (f : nat -> R) (j : nat) (B : R) N,
  (forall k, k <> j -> f k = 0) -> (forall k, f k <= B) -> 0 <= B ->
  sum_f_R0 f N <= B.
Proof.
  intros f j B N Hz Hb HB. induction N as [| N IH].
  - cbn [sum_f_R0]. apply Hb.
  - rewrite tech5. destruct (Nat.eq_dec (S N) j) as [E | E].
    + rewrite (sum_zero_below f N) by (intros k Hk; apply Hz; lia).
      pose proof (Hb (S N)). lra.
    + rewrite (Hz (S N) E). lra.
Qed.

(* ----------------------------------------------------------------- *)
(*  Part B -- the split.                                               *)
(* ----------------------------------------------------------------- *)

Section P0L.

Variable p : nat.
Hypothesis Hp : prime (Z.of_nat p).

Lemma Hp2 : (2 <= p)%nat.
Proof. pose proof (prime_ge_2 _ Hp); lia. Qed.

Definition ppart (sig : R) (k : nat) : R :=
  if (S k mod p =? 0)%nat then Lam (S k) * Rpower (INR (S k)) (- sig) else 0.
Definition chi0part (sig : R) (k : nat) : R :=
  if (S k mod p =? 0)%nat then 0 else Lam (S k) * Rpower (INR (S k)) (- sig).
Definition single (sig : R) (k : nat) : R :=
  if (S k =? p)%nat then Lam (S k) * Rpower (INR (S k)) (- sig) else 0.

Lemma split_sum : forall sig N,
  sum_f_R0 (ppart sig) N + sum_f_R0 (chi0part sig) N = PhiR sig N.
Proof.
  intros sig N. rewrite <- sum_f_R0_plus. unfold PhiR.
  apply sum_eq. intros k _. unfold ppart, chi0part.
  destruct (S k mod p =? 0)%nat; ring.
Qed.

(* a multiple of p other than p itself is not prime *)
Lemma mult_not_prime : forall n, (S n mod p = 0)%nat -> S n <> p ->
  primeb (S n) = false.
Proof.
  intros n Hmod Hne.
  destruct (primeb (S n)) eqn:E; [ | reflexivity ].
  exfalso.
  assert (Hpr : prime (Z.of_nat (S n)))
    by (apply nprime_iff_Zprime, primeb_nprime, E).
  assert (Hd : Nat.divide p (S n))
    by (apply (proj1 (Nat.Lcm0.mod_divide (S n) p)); exact Hmod).
  pose proof Hp2 as H2.
  assert (Hle : (p <= S n)%nat) by (apply Nat.divide_pos_le; [ lia | exact Hd ]).
  assert (Hdp : Z.divide (Z.of_nat p) (Z.of_nat (S n))).
  { destruct Hd as [q Hq]. exists (Z.of_nat q).
    rewrite Hq, Nat2Z.inj_mul. ring. }
  destruct Hpr as [Hn1 Hrel].
  assert (Hrange : (1 <= Z.of_nat p < Z.of_nat (S n))%Z) by lia.
  destruct (Hrel (Z.of_nat p) Hrange) as [_ _ Hgcd].
  assert (Hd1 : Z.divide (Z.of_nat p) 1%Z)
    by (apply Hgcd; [ apply Z.divide_refl | exact Hdp ]).
  apply Z.divide_1_r in Hd1. lia.
Qed.

Lemma ppart_le : forall sig k, 1 <= sig ->
  ppart sig k <= single sig k + bpp (S k) * Rpower (INR (S k)) (- sig).
Proof.
  intros sig k Hs.
  assert (HR : 0 < Rpower (INR (S k)) (- sig)) by (unfold Rpower; apply exp_pos).
  assert (HB : 0 <= bpp (S k)) by apply bpp_nonneg.
  assert (HL : 0 <= Lam (S k)) by apply Lam_nonneg.
  unfold ppart, single.
  destruct (S k mod p =? 0)%nat eqn:E.
  - destruct (S k =? p)%nat eqn:E2.
    + nra.
    + apply Nat.eqb_neq in E2.
      assert (Hnp : primeb (S k) = false)
        by (apply mult_not_prime; [ apply Nat.eqb_eq; exact E | exact E2 ]).
      assert (Hb : bpp (S k) = Lam (S k))
        by (unfold bpp, tterm; rewrite Hnp; ring).
      rewrite Hb. nra.
  - destruct (S k =? p)%nat; nra.
Qed.

Lemma single_bound : forall sig N, 1 <= sig ->
  sum_f_R0 (single sig) N <= ln (INR p).
Proof.
  intros sig N Hs.
  apply (sum_single_le (single sig) (p - 1)%nat).
  - intros k Hk. unfold single.
    replace (S k =? p)%nat with false; [ reflexivity | ].
    symmetry. apply Nat.eqb_neq. pose proof Hp2. lia.
  - intro k. unfold single. destruct (S k =? p)%nat eqn:E; [ | ].
    + apply Nat.eqb_eq in E. rewrite E.
      assert (Hp1 : 1 <= INR p)
        by (rewrite <- INR_1; apply le_INR; pose proof Hp2; lia).
      assert (Hstep : Rpower (INR p) (- sig) <= Rpower (INR p) (-1))
        by (apply Rpower_exp_anti; lra).
      rewrite (Rpower_neg1 (INR p)) in Hstep by lra.
      assert (HLp : Lam p = ln (INR p))
        by (apply Lam_prime, nprime_iff_Zprime, Hp).
      rewrite HLp.
      assert (Hln : 0 <= ln (INR p)) by (rewrite <- ln_1; apply ln_le'; lra).
      assert (Hinv : / INR p <= 1)
        by (rewrite <- Rinv_1; apply Rinv_le_contravar; lra).
      assert (HR : 0 < Rpower (INR p) (- sig)) by (unfold Rpower; apply exp_pos).
      nra.
    + rewrite <- ln_1. apply ln_le'; [ lra | ].
      rewrite <- INR_1. apply le_INR. pose proof Hp2. lia.
  - rewrite <- ln_1. apply ln_le'; [ lra | ].
    rewrite <- INR_1. apply le_INR. pose proof Hp2. lia.
Qed.

Theorem ppart_bound : forall sig N, 1 <= sig ->
  sum_f_R0 (ppart sig) N <= ln (INR p) + Kpp.
Proof.
  intros sig N Hs.
  eapply Rle_trans.
  - apply sum_Rle. intros k _. apply (ppart_le sig k Hs).
  - rewrite sum_f_R0_plus.
    pose proof (single_bound sig N Hs).
    pose proof (ppow_tail_bound sig N Hs). lra.
Qed.

(* ---- THE lower bound ---- *)

Theorem Phi0R_lower : forall sig N, 1 <= sig ->
  PhiR sig N - (ln (INR p) + Kpp) <= sum_f_R0 (chi0part sig) N.
Proof.
  intros sig N Hs.
  pose proof (split_sum sig N) as Hsplit.
  pose proof (ppart_bound sig N Hs). lra.
Qed.

Corollary chi0part_unbounded : forall M, exists N del, 0 < del /\
  forall sig, 1 <= sig -> sig <= 1 + del -> M <= sum_f_R0 (chi0part sig) N.
Proof.
  intro M.
  destruct (PhiR_unbounded (M + (ln (INR p) + Kpp))) as [N [del [Hdel HP]]].
  exists N, del. split; [ exact Hdel | ].
  intros sig Hs1 Hs2.
  pose proof (HP sig Hs1 Hs2) as H1.
  pose proof (Phi0R_lower sig N Hs1) as H2. lra.
Qed.

End P0L.

Print Assumptions Phi0R_lower.
Print Assumptions chi0part_unbounded.

(* ================================================================= *)
(*  END CLPhi0Lower.v                                                 *)
(* ================================================================= *)
