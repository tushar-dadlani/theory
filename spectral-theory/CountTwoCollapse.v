(* ================================================================= *)
(*  CountTwoCollapse.v  —  Count = 2 → mean → two infinities → collapse.  *)
(*                                                                    *)
(*  The count-2 / first-prime picture, in rigorous real-sequence-limit    *)
(*  form (Stdlib `Reals`; the repo has no `Rbar`).  Foundation and lead-in *)
(*  to the prime-2 ↔ ζ capstone (FirstPrimeZeta.v):                       *)
(*                                                                    *)
(*   Stage 0 (ZFC cardinality) : a 2-element set has cardinality 2         *)
(*        (`card_two`, via Coq's `Ensembles`/`Finite_sets` — AXIOM-FREE).  *)
(*   Stage 1 (mean)            : mean x y = (x+y)/2, symmetric, between.    *)
(*   Stage 2 (positive limit)  : 2^n → +∞  (`pow2_cv_infty`).             *)
(*   Stage 3 (oscillating)     : (-2)^n oscillates by parity —             *)
(*        even n → +∞ (`neg2_even_cv_infty`), odd n → −∞                   *)
(*        (`neg2_odd_cv_neg_infty`, the −∞ encoded as negated → +∞, the    *)
(*        repo's convention), with |(-2)^n| = 2^n (`neg2_pow_abs`).        *)
(*   Stage 4 (collapse)        : (x+y)/2^n → 0 and (x−y)/2^n → 0.          *)
(*                                                                    *)
(*  `card_two` is axiom-free; the rest uses only the 4 standard            *)
(*  classical-Reals axioms (no `Extensionality_Ensembles`).               *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia Ensembles Finite_sets Powerset_facts.
Require Import LogGeomSeries BaselZeta.
Open Scope R_scope.

(* ===== Stage 0: ZFC cardinality of 2 elements ("Count = 2") ===== *)
Definition pairR (x y : R) : Ensemble R := Add R (Add R (Empty_set R) x) y.

Lemma card_two : forall x y : R, x <> y -> cardinal R (pairR x y) 2.
Proof.
  intros x y Hxy. unfold pairR.
  apply card_add.
  - apply card_add; [ apply card_empty | intro H; inversion H ].
  - intro H. apply Add_inv in H. destruct H as [H | H]; [ inversion H | congruence ].
Qed.

(* ===== Stage 1: the mean of the count-2 pair ===== *)
Definition mean (x y : R) : R := (x + y) / 2.
Lemma mean_sym : forall x y, mean x y = mean y x.
Proof. intros; unfold mean; lra. Qed.
Lemma mean_between : forall x y, x <= y -> x <= mean x y <= y.
Proof. intros; unfold mean; lra. Qed.

(* ===== Stage 2: 2^n -> +infinity (the positive limit) ===== *)
Lemma pow2_ge_Sn : forall n, INR n + 1 <= 2 ^ n.
Proof.
  induction n as [| n IH]; [ simpl; lra | ].
  rewrite S_INR. simpl. pose proof (pos_INR n). lra.
Qed.

Lemma cv_infty_ext : forall f g, (forall n, f n = g n) -> cv_infty g -> cv_infty f.
Proof.
  intros f g Heq Hg M. destruct (Hg M) as [N HN]. exists N. intros n Hn.
  rewrite Heq. apply HN; exact Hn.
Qed.

Lemma pow2_cv_infty : cv_infty (fun n => 2 ^ n).
Proof.
  intro M. destruct (INR_unbounded (M - 1)) as [N HN].
  exists N. intros n Hn. pose proof (pow2_ge_Sn n).
  assert (INR N <= INR n) by (apply le_INR; exact Hn). lra.
Qed.

(* general: 2^(f k) -> +inf when f k >= k *)
Lemma cv_infty_pow2_comp : forall (f : nat -> nat),
  (forall k, (k <= f k)%nat) -> cv_infty (fun k => 2 ^ (f k)).
Proof.
  intros f Hf M. destruct (INR_unbounded (M - 1)) as [N HN].
  exists N. intros k Hk. pose proof (pow2_ge_Sn (f k)).
  assert (INR N <= INR k) by (apply le_INR; exact Hk).
  assert (INR k <= INR (f k)) by (apply le_INR; apply Hf). lra.
Qed.

(* ===== Stage 3: (-2)^n oscillates by parity (the oscillating limit) ===== *)
Lemma neg2_pow_eq : forall n, (-2) ^ n = (-1) ^ n * 2 ^ n.
Proof. induction n as [| n IH]; simpl; [ lra | rewrite IH; ring ]. Qed.

Lemma m1_pow_abs : forall n, Rabs ((-1) ^ n) = 1.
Proof.
  induction n as [| n IH]; simpl; [ apply Rabs_R1 | ].
  rewrite Rabs_mult, IH, Rmult_1_r.
  replace (Rabs (-1)) with 1 by (rewrite Rabs_left; lra). reflexivity.
Qed.

Lemma neg2_pow_abs : forall n, Rabs ((-2) ^ n) = 2 ^ n.
Proof.
  intro n. rewrite neg2_pow_eq, Rabs_mult, m1_pow_abs, Rmult_1_l.
  apply Rabs_right, Rle_ge, pow_le; lra.
Qed.

Lemma m1_pow_even : forall k, (-1) ^ (2 * k) = 1.
Proof.
  induction k as [| k IH]; [ reflexivity | ].
  replace (2 * S k)%nat with (2 * k + 2)%nat by lia.
  rewrite pow_add, IH. simpl. ring.
Qed.
Lemma m1_pow_odd : forall k, (-1) ^ (S (2 * k)) = -1.
Proof.
  intro k. replace (S (2 * k)) with (2 * k + 1)%nat by lia.
  rewrite pow_add, m1_pow_even. simpl. ring.
Qed.

Lemma neg2_even : forall k, (-2) ^ (2 * k) = 2 ^ (2 * k).
Proof. intro k. rewrite neg2_pow_eq, m1_pow_even. lra. Qed.
Lemma neg2_odd : forall k, (-2) ^ (S (2 * k)) = - (2 ^ (S (2 * k))).
Proof. intro k. rewrite neg2_pow_eq, m1_pow_odd. lra. Qed.

Lemma neg2_even_cv_infty : cv_infty (fun k => (-2) ^ (2 * k)).
Proof.
  apply (cv_infty_ext _ (fun k => 2 ^ (2 * k))); [ apply neg2_even | ].
  apply cv_infty_pow2_comp. intro k. lia.
Qed.
Lemma neg2_odd_cv_neg_infty : cv_infty (fun k => - (-2) ^ (S (2 * k))).
Proof.
  apply (cv_infty_ext _ (fun k => 2 ^ (S (2 * k)))).
  - intro k. rewrite neg2_odd. lra.
  - apply cv_infty_pow2_comp. intro k. lia.
Qed.

(* ===== Stage 4: the collapse (x +/- y)/2^n -> 0 ===== *)
Lemma inv2_pow_cv0 : Un_cv (fun n => (/ 2) ^ n) 0.
Proof. apply pow_cv0. rewrite Rabs_right; lra. Qed.

Lemma over_pow2_cv0 : forall c, Un_cv (fun n => c / 2 ^ n) 0.
Proof.
  intro c. apply (Un_cv_ext (fun n => c * (/ 2) ^ n)).
  - intro n. unfold Rdiv. rewrite Rinv_pow by lra. reflexivity.
  - apply Un_cv_scal_0. apply inv2_pow_cv0.
Qed.

Lemma sum_over_pow2_cv0 : forall x y, Un_cv (fun n => (x + y) / 2 ^ n) 0.
Proof. intros. apply over_pow2_cv0. Qed.
Lemma diff_over_pow2_cv0 : forall x y, Un_cv (fun n => (x - y) / 2 ^ n) 0.
Proof. intros. apply over_pow2_cv0. Qed.

(* ===== The count-2 picture, bundled ===== *)
Theorem count_two_picture : forall x y : R, x <> y ->
  cardinal R (pairR x y) 2
  /\ cv_infty (fun n => 2 ^ n)
  /\ cv_infty (fun k => (-2) ^ (2 * k))
  /\ cv_infty (fun k => - (-2) ^ (S (2 * k)))
  /\ Un_cv (fun n => (x + y) / 2 ^ n) 0
  /\ Un_cv (fun n => (x - y) / 2 ^ n) 0.
Proof.
  intros x y Hxy. repeat split.
  - apply card_two; exact Hxy.
  - apply pow2_cv_infty.
  - apply neg2_even_cv_infty.
  - apply neg2_odd_cv_neg_infty.
  - apply sum_over_pow2_cv0.
  - apply diff_over_pow2_cv0.
Qed.

Print Assumptions card_two.
Print Assumptions count_two_picture.
