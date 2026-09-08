(* ================================================================= *)
(*  SqrtSumAsym.v  --  sum_{n<=y} 1/sqrt n  =  2 sqrt y + C + O(1/sqrt y) *)
(*                                                                    *)
(*  The first analytic brick of the elementary hyperbola proof of      *)
(*  L(1,chi) <> 0 for a real chi.  The RATE matters: in the hyperbola  *)
(*  the error is weighted by sum_{d<=sqrt x} 1/sqrt d, which is of     *)
(*  size x^{1/4}, so anything weaker than O(1/sqrt y) would not close. *)
(*                                                                    *)
(*  Everything is telescoping -- no integrals, no Euler-Maclaurin.     *)
(*  Writing a = sqrt n and b = sqrt (n-1), so a*a - b*b = 1,           *)
(*                                                                    *)
(*    1/sqrt n - 2(sqrt n - sqrt(n-1))  =  - 1/(a (a+b)^2),           *)
(*                                                                    *)
(*  which is O(n^{-3/2}) because (a+b)^2 >= a^2 = n.  Summing that     *)
(*  telescoped correction converges, and its own tail is bounded by a  *)
(*  SECOND telescoping, 1/(n sqrt n) <= 2(1/sqrt(n-1) - 1/sqrt n).     *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia Arith.
Require Import CSeries.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  Part A -- generic facts about sum_f_R0.                            *)
(* ----------------------------------------------------------------- *)

Lemma sum_tel_up : forall (u : nat -> R) N,
  sum_f_R0 (fun k => u (S k) - u k) N = u (S N) - u 0%nat.
Proof.
  intros u N. induction N as [| N IH]; [ simpl; ring | ].
  rewrite tech5, IH. ring.
Qed.

Lemma sum_tel_down : forall (u : nat -> R) N,
  sum_f_R0 (fun k => u k - u (S k)) N = u 0%nat - u (S N).
Proof.
  intros u N. induction N as [| N IH]; [ simpl; ring | ].
  rewrite tech5, IH. ring.
Qed.

(* the majorant is only required beyond N -- essential, because the
   second telescoping majorant is NEGATIVE at k = 0 *)
Lemma sum_diff_maj : forall (a b : nat -> R) N j,
  (forall k, (N < k)%nat -> Rabs (a k) <= b k) ->
  Rabs (sum_f_R0 a (N + j) - sum_f_R0 a N) <= sum_f_R0 b (N + j) - sum_f_R0 b N.
Proof.
  intros a b N j H. induction j as [| j IH].
  - rewrite Nat.add_0_r.
    replace (sum_f_R0 a N - sum_f_R0 a N) with 0 by ring.
    rewrite Rabs_R0. lra.
  - replace (N + S j)%nat with (S (N + j))%nat by lia.
    rewrite !tech5.
    replace (sum_f_R0 a (N + j) + a (S (N + j)) - sum_f_R0 a N)
      with ((sum_f_R0 a (N + j) - sum_f_R0 a N) + a (S (N + j))) by ring.
    eapply Rle_trans; [ apply Rabs_triang | ].
    replace (sum_f_R0 b (N + j) + b (S (N + j)) - sum_f_R0 b N)
      with ((sum_f_R0 b (N + j) - sum_f_R0 b N) + b (S (N + j))) by ring.
    apply Rplus_le_compat; [ exact IH | apply H; lia ].
Qed.

Lemma cv_shift : forall (u : nat -> R) C N,
  Un_cv u C -> Un_cv (fun j => u (N + j)%nat) C.
Proof.
  intros u C N H eps He. destruct (H eps He) as [M HM].
  exists M. intros j Hj. apply HM. lia.
Qed.

Lemma cv_const : forall c : R, Un_cv (fun _ => c) c.
Proof.
  intros c eps He. exists 0%nat. intros n _.
  unfold R_dist. replace (c - c) with 0 by ring. rewrite Rabs_R0. exact He.
Qed.

Lemma cv_Rabs : forall (u : nat -> R) l,
  Un_cv u l -> Un_cv (fun n => Rabs (u n)) (Rabs l).
Proof.
  intros u l H eps He. destruct (H eps He) as [N HN].
  exists N. intros n Hn. unfold R_dist in *.
  eapply Rle_lt_trans; [ apply Rabs_triang_inv2 | apply (HN n Hn) ].
Qed.

(* ----------------------------------------------------------------- *)
(*  Part B -- the two algebraic identities behind the telescopings.    *)
(* ----------------------------------------------------------------- *)

Lemma dt_key : forall a b : R, 0 < a -> 0 <= b -> a * a - b * b = 1 ->
  / a - 2 * (a - b) = - / (a * ((a + b) * (a + b))).
Proof.
  intros a b Ha Hb Hd.
  assert (Hc : 0 < a + b) by lra.
  assert (Ha0 : a <> 0) by (apply Rgt_not_eq; lra).
  assert (Hc0 : a + b <> 0) by (apply Rgt_not_eq; lra).
  assert (HX : a * ((a + b) * (a + b)) <> 0) by (apply Rgt_not_eq; nra).
  assert (Hsub : a - b = / (a + b)).
  { apply (Rmult_eq_reg_r (a + b)); [ | exact Hc0 ].
    rewrite Rinv_l by exact Hc0.
    replace ((a - b) * (a + b)) with (a * a - b * b) by ring. exact Hd. }
  rewrite Hsub.
  apply (Rmult_eq_reg_r (a * ((a + b) * (a + b)))); [ | exact HX ].
  rewrite <- Ropp_mult_distr_l, Rinv_l by exact HX.
  replace ((/ a - 2 * / (a + b)) * (a * ((a + b) * (a + b))))
    with ((/ a * a) * ((a + b) * (a + b))
          - 2 * (/ (a + b) * (a + b)) * (a * (a + b))) by ring.
  rewrite (Rinv_l a Ha0), (Rinv_l (a + b) Hc0).
  replace (1 * ((a + b) * (a + b)) - 2 * 1 * (a * (a + b)))
    with (- (a * a - b * b)) by ring.
  rewrite Hd. ring.
Qed.

Lemma inv_diff_key : forall a b : R, 0 < b -> 0 < a -> a * a - b * b = 1 ->
  / b - / a = / ((a + b) * (a * b)).
Proof.
  intros a b Hb Ha Hd.
  assert (Ha0 : a <> 0) by (apply Rgt_not_eq; lra).
  assert (Hb0 : b <> 0) by (apply Rgt_not_eq; lra).
  assert (HX : (a + b) * (a * b) <> 0) by (apply Rgt_not_eq; nra).
  apply (Rmult_eq_reg_r ((a + b) * (a * b))); [ | exact HX ].
  rewrite Rinv_l by exact HX.
  replace ((/ b - / a) * ((a + b) * (a * b)))
    with ((/ b * b) * ((a + b) * a) - (/ a * a) * ((a + b) * b)) by ring.
  rewrite (Rinv_l a Ha0), (Rinv_l b Hb0).
  replace (1 * ((a + b) * a) - 1 * ((a + b) * b)) with (a * a - b * b) by ring.
  exact Hd.
Qed.

(* ----------------------------------------------------------------- *)
(*  Part C -- the three sequences.                                     *)
(* ----------------------------------------------------------------- *)

Definition st (k : nat) : R := / sqrt (INR (S k)).
Definition Sq (N : nat) : R := sum_f_R0 st N.          (* sum_{n=1}^{N+1} 1/sqrt n *)
Definition dt (k : nat) : R := st k - 2 * (sqrt (INR (S k)) - sqrt (INR k)).
Definition bt (k : nat) : R := / (INR (S k) * sqrt (INR (S k))).
Definition Btel (k : nat) : R := 2 * (/ sqrt (INR k) - / sqrt (INR (S k))).

Lemma sqrtS_pos : forall k, 0 < sqrt (INR (S k)).
Proof.
  intro k. apply sqrt_lt_R0.
  apply Rlt_le_trans with 1; [ lra | apply (le_INR 1); lia ].
Qed.

Lemma Sq_tel : forall N, sum_f_R0 dt N = Sq N - 2 * sqrt (INR (S N)).
Proof.
  induction N as [| N IH].
  - unfold Sq, dt. cbn [sum_f_R0]. rewrite INR_0, sqrt_0. ring.
  - rewrite tech5, IH. unfold Sq, dt. rewrite tech5. ring.
Qed.

Lemma dt_bound : forall k, Rabs (dt k) <= bt k.
Proof.
  intro k. unfold dt, bt, st.
  set (a := sqrt (INR (S k))). set (b := sqrt (INR k)).
  assert (H1 : 1 <= INR (S k)) by (apply (le_INR 1); lia).
  assert (Ha : 0 < a) by (unfold a; apply sqrtS_pos).
  assert (Hb : 0 <= b) by (unfold b; apply sqrt_pos).
  assert (Haa : a * a = INR (S k)) by (unfold a; apply sqrt_sqrt; lra).
  assert (Hbb : b * b = INR k) by (unfold b; apply sqrt_sqrt; apply pos_INR).
  assert (Hd : a * a - b * b = 1) by (rewrite Haa, Hbb, S_INR; ring).
  rewrite (dt_key a b Ha Hb Hd), Rabs_Ropp, Rabs_right
    by (apply Rle_ge, Rlt_le, Rinv_0_lt_compat; nra).
  rewrite <- Haa.
  apply Rinv_le_contravar; nra.
Qed.

Lemma bt_nonneg : forall k, 0 <= bt k.
Proof.
  intro k. unfold bt. apply Rlt_le, Rinv_0_lt_compat.
  pose proof (sqrtS_pos k). pose proof (pos_INR (S k)).
  assert (0 < INR (S k)) by (apply Rlt_le_trans with 1; [ lra | apply (le_INR 1); lia ]).
  nra.
Qed.

Lemma bt_le_Btel : forall k, (1 <= k)%nat -> bt k <= Btel k.
Proof.
  intros k Hk. unfold bt, Btel.
  set (a := sqrt (INR (S k))). set (b := sqrt (INR k)).
  assert (H1 : 1 <= INR (S k)) by (apply (le_INR 1); lia).
  assert (Hk1 : 1 <= INR k) by (apply (le_INR 1); lia).
  assert (Ha : 0 < a) by (unfold a; apply sqrtS_pos).
  assert (Hb : 0 < b) by (unfold b; apply sqrt_lt_R0; lra).
  assert (Haa : a * a = INR (S k)) by (unfold a; apply sqrt_sqrt; lra).
  assert (Hbb : b * b = INR k) by (unfold b; apply sqrt_sqrt; lra).
  assert (Hd : a * a - b * b = 1) by (rewrite Haa, Hbb, S_INR; ring).
  assert (Hba : b <= a) by nra.
  rewrite (inv_diff_key a b Hb Ha Hd).
  assert (HW : 0 < (a + b) * (a * b)) by nra.
  replace (2 * / ((a + b) * (a * b))) with (/ (((a + b) * (a * b)) / 2))
    by (field; lra).
  rewrite <- Haa.
  apply Rinv_le_contravar; nra.
Qed.

Lemma sum_Btel : forall N, sum_f_R0 Btel N = 2 * (0 - / sqrt (INR (S N))).
Proof.
  intro N.
  replace (sum_f_R0 Btel N)
    with (2 * sum_f_R0 (fun k => / sqrt (INR k) - / sqrt (INR (S k))) N).
  - rewrite sum_tel_down. rewrite INR_0, sqrt_0, Rinv_0. reflexivity.
  - induction N as [| N IH]; [ cbn [sum_f_R0]; unfold Btel; ring | ].
    rewrite !tech5, <- IH. unfold Btel at 1. ring.
Qed.

(* ----------------------------------------------------------------- *)
(*  Part D -- convergence of the correction series.                    *)
(* ----------------------------------------------------------------- *)

Lemma sum_bt_ub : forall N, sum_f_R0 bt N <= 3.
Proof.
  intro N. destruct N as [| N].
  - simpl. unfold bt. simpl. rewrite sqrt_1. lra.
  - replace (S N) with (0 + S N)%nat by lia.
    pose proof (sum_diff_maj bt Btel 0%nat (S N)
      (fun k Hk => eq_ind_r (fun r => r <= Btel k) (bt_le_Btel k ltac:(lia))
                     (Rabs_right (bt k) (Rle_ge _ _ (bt_nonneg k))))) as Hmaj.
    assert (Habs : sum_f_R0 bt (0 + S N) - sum_f_R0 bt 0%nat
                   <= sum_f_R0 Btel (0 + S N) - sum_f_R0 Btel 0%nat).
    { eapply Rle_trans; [ apply Rle_abs | exact Hmaj ]. }
    rewrite !sum_Btel in Habs.
    simpl (sum_f_R0 bt 0%nat) in *. unfold bt at 2 in Habs.
    simpl (INR (S 0)) in Habs. rewrite sqrt_1 in Habs.
    pose proof (sqrtS_pos (0 + S N)) as Hp.
    assert (0 < / sqrt (INR (S (0 + S N)))) by (apply Rinv_0_lt_compat; exact Hp).
    lra.
Qed.

Lemma bt_cv : { T | Un_cv (sum_f_R0 bt) T }.
Proof.
  apply growing_cv.
  - intro n. rewrite tech5. pose proof (bt_nonneg (S n)). lra.
  - exists 3. intros x [n Hn]. rewrite Hn. apply sum_bt_ub.
Qed.

Definition dtcv : { C | Un_cv (sum_f_R0 dt) C } :=
  Rseries_abs_cv dt bt dt_bound bt_cv.

Definition Csq : R := proj1_sig dtcv.

Lemma Csq_cv : Un_cv (sum_f_R0 dt) Csq.
Proof. exact (proj2_sig dtcv). Qed.

(* ----------------------------------------------------------------- *)
(*  Part E -- the tail bound, and the headline asymptotic.             *)
(* ----------------------------------------------------------------- *)

Lemma dt_tail_j : forall N j,
  Rabs (sum_f_R0 dt (N + j) - sum_f_R0 dt N) <= 2 / sqrt (INR (S N)).
Proof.
  intros N j.
  eapply Rle_trans; [ apply (sum_diff_maj dt bt N j (fun k _ => dt_bound k)) | ].
  assert (Hstep : sum_f_R0 bt (N + j) - sum_f_R0 bt N
                  <= sum_f_R0 Btel (N + j) - sum_f_R0 Btel N).
  { eapply Rle_trans; [ apply Rle_abs | ].
    apply (sum_diff_maj bt Btel N j).
    intros k Hk. rewrite (Rabs_right (bt k) (Rle_ge _ _ (bt_nonneg k))).
    apply bt_le_Btel. lia. }
  eapply Rle_trans; [ exact Hstep | ].
  rewrite !sum_Btel.
  pose proof (sqrtS_pos (N + j)) as Hp.
  assert (0 < / sqrt (INR (S (N + j)))) by (apply Rinv_0_lt_compat; exact Hp).
  unfold Rdiv. lra.
Qed.

Theorem sqrt_sum_tail : forall N,
  Rabs (Csq - sum_f_R0 dt N) <= 2 / sqrt (INR (S N)).
Proof.
  intro N.
  apply Rle_cv_lim with
    (Un := fun j => Rabs (sum_f_R0 dt (N + j) - sum_f_R0 dt N))
    (Vn := fun _ : nat => 2 / sqrt (INR (S N))).
  - intro j. apply dt_tail_j.
  - apply cv_Rabs.
    apply (CV_minus (fun j => sum_f_R0 dt (N + j)%nat)
                    (fun _ : nat => sum_f_R0 dt N)).
    + apply cv_shift. exact Csq_cv.
    + apply cv_const.
  - apply cv_const.
Qed.

(* the headline: sum_{n=1}^{N+1} 1/sqrt n = 2 sqrt (N+1) + Csq + O(1/sqrt (N+1)) *)
Theorem sqrt_sum_asym : forall N,
  Rabs (Sq N - 2 * sqrt (INR (S N)) - Csq) <= 2 / sqrt (INR (S N)).
Proof.
  intro N.
  replace (Sq N - 2 * sqrt (INR (S N)) - Csq)
    with (- (Csq - sum_f_R0 dt N)) by (rewrite Sq_tel; ring).
  rewrite Rabs_Ropp. apply sqrt_sum_tail.
Qed.

Print Assumptions sqrt_sum_asym.

(* ================================================================= *)
(*  END SqrtSumAsym.v                                                 *)
(* ================================================================= *)
