(* ================================================================= *)
(*  CharTailBound.v  --  the twisted tails, at s = 1 and s = 1/2.     *)
(*                                                                    *)
(*  Feeds RAbelSum.abel_tail with B = p from CCharSumBound.PS_bound.  *)
(*  Because chi is REAL, everything can be done over R: CRealChar.chz *)
(*  is the {-1,0,1} avatar and chz_spec bridges it to dchar, so the    *)
(*  bounded character sums transfer to bounded REAL partial sums.      *)
(*                                                                    *)
(*    | L(1,chi) - sum_{n<=M+1} chi(n)/n |     <= 2p / (M+2)          *)
(*    | Lh       - sum_{n<=M+1} chi(n)/sqrt n | <= 2p / sqrt (M+2)    *)
(*                                                                    *)
(*  The first pins L(1,chi) with the O(1/y) error the hyperbola's main *)
(*  term needs; the second kills its far region.  Both are the SAME    *)
(*  abel_tail, which is why that lemma was stated for a general weight.*)
(*                                                                    *)
(*  Part A is generic: a uniform tail bound is a Cauchy criterion, so  *)
(*  it yields the limit AND passes to it with the same rate.           *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia Arith List ZArith Znumtheory.
Require Import ComplexField Cmodulus RootsOfUnity ZmodOrder DirichletModP
        GaussSum CCharSumBound CRealChar BaselZeta SqrtSumAsym RAbelSum.
Import ListNotations.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  Part A -- a uniform tail bound gives the limit, with the rate.     *)
(* ----------------------------------------------------------------- *)

Section TailToLimit.

Variable c w : nat -> R.
Variable K : R.
Hypothesis HK : 0 < K.
Hypothesis Hw : forall n, 0 <= w (S n) /\ w (S n) <= w n.
Hypothesis Hw0 : Un_cv w 0.
Hypothesis Htail : forall M j,
  Rabs (sum_f_R0 c (M + S j)%nat - sum_f_R0 c M) <= K * w (S M).

Lemma w_nonneg : forall n, 0 <= w n.
Proof.
  intro n. destruct n as [| n]; [ destruct (Hw 0%nat); lra | apply (Hw n) ].
Qed.

Lemma w_anti : forall a b, (a <= b)%nat -> w b <= w a.
Proof.
  intros a b Hab. induction b as [| b IH].
  - replace a with 0%nat by lia. apply Rle_refl.
  - destruct (Nat.eq_dec a (S b)) as [E | E]; [ rewrite E; apply Rle_refl | ].
    eapply Rle_trans; [ apply (Hw b) | apply IH; lia ].
Qed.

Lemma tail_cauchy : Cauchy_crit (sum_f_R0 c).
Proof.
  assert (HK0 : K <> 0) by (apply Rgt_not_eq; lra).
  intros eps He.
  destruct (Hw0 (eps / K)) as [N HN]; [ apply Rdiv_lt_0_compat; lra | ].
  assert (HwN : w (S N) < eps / K).
  { specialize (HN (S N) ltac:(lia)). unfold R_dist in HN.
    rewrite Rminus_0_r, (Rabs_right (w (S N))) in HN
      by (apply Rle_ge, w_nonneg). exact HN. }
  assert (Hkey : forall a b, (N <= a)%nat -> (a < b)%nat ->
            R_dist (sum_f_R0 c b) (sum_f_R0 c a) < eps).
  { intros a b Ha Hab. unfold R_dist.
    replace b with (a + S (b - a - 1))%nat by lia.
    eapply Rle_lt_trans; [ apply Htail | ].
    assert (Hwa : w (S a) <= w (S N)) by (apply w_anti; lia).
    apply Rlt_le_trans with (K * (eps / K)).
    - apply Rmult_lt_compat_l; lra.
    - right. field. exact HK0. }
  exists N. intros n m Hn Hm.
  destruct (lt_eq_lt_dec n m) as [[Hlt | Heq] | Hgt].
  - rewrite R_dist_sym. apply Hkey; lia.
  - subst m. rewrite R_dist_eq. exact He.
  - apply Hkey; lia.
Qed.

Definition tail_lim : { L | Un_cv (sum_f_R0 c) L } := R_complete _ tail_cauchy.
Definition Lc : R := proj1_sig tail_lim.

Lemma Lc_cv : Un_cv (sum_f_R0 c) Lc.
Proof. exact (proj2_sig tail_lim). Qed.

Theorem Lc_tail : forall M, Rabs (Lc - sum_f_R0 c M) <= K * w (S M).
Proof.
  intro M.
  apply Rle_cv_lim with
    (Un := fun j => Rabs (sum_f_R0 c (M + S j)%nat - sum_f_R0 c M))
    (Vn := fun _ : nat => K * w (S M)).
  - intro j. apply Htail.
  - apply cv_Rabs.
    apply (CV_minus (fun j => sum_f_R0 c (M + S j)%nat)
                    (fun _ : nat => sum_f_R0 c M)).
    + intros eps He. destruct (Lc_cv eps He) as [N0 HN0].
      exists N0. intros j Hj. apply HN0. lia.
    + apply cv_const.
  - apply cv_const.
Qed.

End TailToLimit.

(* ----------------------------------------------------------------- *)
(*  Part B -- the two weights.                                        *)
(* ----------------------------------------------------------------- *)

Definition w1 (k : nat) : R := / INR (S k).
Definition wh (k : nat) : R := / sqrt (INR (S k)).

Lemma SkR_pos : forall k, 0 < INR (S k).
Proof. intro k. apply Rlt_le_trans with 1; [ lra | apply (le_INR 1); lia ]. Qed.

Lemma w1_dec : forall n, 0 <= w1 (S n) /\ w1 (S n) <= w1 n.
Proof.
  intro n. unfold w1. split.
  - apply Rlt_le, Rinv_0_lt_compat, SkR_pos.
  - apply Rinv_le_contravar; [ apply SkR_pos | apply le_INR; lia ].
Qed.

Lemma wh_dec : forall n, 0 <= wh (S n) /\ wh (S n) <= wh n.
Proof.
  intro n. unfold wh.
  assert (H1 : 0 < sqrt (INR (S n))) by (apply sqrt_lt_R0, SkR_pos).
  assert (H2 : 0 < sqrt (INR (S (S n)))) by (apply sqrt_lt_R0, SkR_pos).
  split.
  - apply Rlt_le, Rinv_0_lt_compat, H2.
  - apply Rinv_le_contravar; [ exact H1 | apply sqrt_le_1_alt, le_INR; lia ].
Qed.

Lemma w1_cv0 : Un_cv w1 0.
Proof. exact Un_cv_inv_Sn. Qed.

Lemma wh_cv0 : Un_cv wh 0.
Proof.
  intros eps He.
  destruct (Un_cv_inv_Sn (eps * eps)) as [N HN];
    [ apply Rmult_lt_0_compat; lra | ].
  exists N. intros n Hn. specialize (HN n Hn). unfold R_dist in *.
  rewrite Rminus_0_r in *.
  assert (Hpi : 0 < / INR (S n)) by (apply Rinv_0_lt_compat, SkR_pos).
  rewrite (Rabs_right (/ INR (S n))) in HN by (apply Rle_ge; lra).
  unfold wh. rewrite <- sqrt_inv, (Rabs_right (sqrt (/ INR (S n))))
    by (apply Rle_ge, sqrt_pos).
  replace eps with (sqrt (Rsqr eps)) by (apply sqrt_Rsqr; lra).
  apply sqrt_lt_1_alt. unfold Rsqr. lra.
Qed.

(* ----------------------------------------------------------------- *)
(*  Part C -- the character.                                          *)
(* ----------------------------------------------------------------- *)

Lemma Cadd_C0_r : forall z : C, Cadd z C0 = z.
Proof. intro z. apply Ceq; unfold Cadd, C0; cbn [Re Im]; ring. Qed.

Lemma Sf_single : forall (f : nat -> C) x, Sf f [x] = f x.
Proof. intros f x. unfold Sf. cbn [map fold_right]. apply Cadd_C0_r. Qed.

Section CharTail.

Variable p g A : nat.
Hypothesis Hp : prime (Z.of_nat p).
Hypothesis Hg : (1 <= g <= p - 1)%nat.
Hypothesis Hord : ord p g = (p - 1)%nat.
Hypothesis HA : (0 < A < p - 1)%nat.
Hypothesis Hreal : forall n, Cconj (dchar p g A n) = dchar p g A n.

Definition cr (n : nat) : R := IZR (chz p g A n).
Definition ca (k : nat) : R := cr (S k).

Lemma PS_rec : forall M, PS p g A (S M) = Cadd (PS p g A M) (dchar p g A (S M)).
Proof.
  intro M. unfold PS. rewrite seq_S, Sf_app.
  replace (1 + M)%nat with (S M) by lia.
  rewrite Sf_single. reflexivity.
Qed.

Lemma PS_real : forall N, PS p g A (S N) = RtoC (sum_f_R0 ca N).
Proof.
  induction N as [| N IH].
  - unfold PS. cbn [seq]. rewrite Sf_single. cbn [sum_f_R0].
    unfold ca, cr. rewrite (chz_spec p g A Hreal 1%nat). reflexivity.
  - rewrite PS_rec, IH, tech5, <- (chz_spec p g A Hreal (S (S N))).
    apply Ceq; unfold ca, cr, Cadd, RtoC; cbn [Re Im]; ring.
Qed.

Lemma ca_bound : forall N, Rabs (sum_f_R0 ca N) <= INR p.
Proof.
  intro N. rewrite <- Cmod_RtoC, <- PS_real.
  apply (PS_bound p g A Hp Hg Hord HA).
Qed.

Lemma twoP_pos : 0 < 2 * INR p.
Proof.
  assert (Hp2 : (2 <= p)%nat) by (pose proof (prime_ge_2 _ Hp); lia).
  assert (INR 2 <= INR p) by (apply le_INR; exact Hp2).
  simpl in *. lra.
Qed.

Theorem char_tail_1 : forall M j,
  Rabs (sum_f_R0 (fun k => ca k * w1 k) (M + S j)%nat
        - sum_f_R0 (fun k => ca k * w1 k) M) <= 2 * INR p * w1 (S M).
Proof. intros M j. apply abel_tail; [ apply ca_bound | apply w1_dec ]. Qed.

Theorem char_tail_h : forall M j,
  Rabs (sum_f_R0 (fun k => ca k * wh k) (M + S j)%nat
        - sum_f_R0 (fun k => ca k * wh k) M) <= 2 * INR p * wh (S M).
Proof. intros M j. apply abel_tail; [ apply ca_bound | apply wh_dec ]. Qed.

(* L(1,chi) as a real number, and sum chi(n)/sqrt n *)
Definition Lchi1 : R :=
  Lc (fun k => ca k * w1 k) w1 (2 * INR p) twoP_pos w1_dec w1_cv0 char_tail_1.

Definition Lchih : R :=
  Lc (fun k => ca k * wh k) wh (2 * INR p) twoP_pos wh_dec wh_cv0 char_tail_h.

Theorem Lchi1_cv : Un_cv (sum_f_R0 (fun k => ca k * w1 k)) Lchi1.
Proof. apply Lc_cv. Qed.

Theorem Lchih_cv : Un_cv (sum_f_R0 (fun k => ca k * wh k)) Lchih.
Proof. apply Lc_cv. Qed.

Theorem Lchi1_tail : forall M,
  Rabs (Lchi1 - sum_f_R0 (fun k => ca k * w1 k) M) <= 2 * INR p * w1 (S M).
Proof. apply Lc_tail. Qed.

Theorem Lchih_tail : forall M,
  Rabs (Lchih - sum_f_R0 (fun k => ca k * wh k) M) <= 2 * INR p * wh (S M).
Proof. apply Lc_tail. Qed.

End CharTail.

Print Assumptions Lchi1_tail.
Print Assumptions Lchih_tail.

(* ================================================================= *)
(*  END CharTailBound.v                                               *)
(* ================================================================= *)
