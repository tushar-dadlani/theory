(* ================================================================= *)
(*  RAbelSum.v  --  summation by parts over R, and the tail bound     *)
(*  it gives for  sum a_k w_k  when the partial sums of a are BOUNDED *)
(*  and w decreases to 0.                                             *)
(*                                                                    *)
(*      | sum_{k=M+1}^{N} a_k w_k |  <=  2 B w_{M+1}                  *)
(*                                                                    *)
(*  This is the one estimate that makes a Dirichlet L-series behave    *)
(*  past its absolute-convergence abscissa: the character sums are     *)
(*  bounded (CCharSumBound.PS_bound), so every twisted tail is small   *)
(*  even though sum 1/n diverges.  Stated for a general weight, so     *)
(*  the SAME lemma serves w = 1/n (needed for L(1,chi)) and            *)
(*  w = 1/sqrt n (needed for the hyperbola's inner sums).              *)
(*                                                                    *)
(*  Note the bound is UNIFORM in the upper limit N -- that is what     *)
(*  makes it a Cauchy criterion and not just a single estimate.        *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia Arith.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  Part A -- the algebraic identity (Abel / summation by parts).      *)
(* ----------------------------------------------------------------- *)

Lemma abel_parts : forall (u v : nat -> R) j,
  sum_f_R0 (fun i => (u (S i) - u i) * v i) j
  = u (S j) * v (S j) - u 0%nat * v 0%nat
    - sum_f_R0 (fun i => u (S i) * (v (S i) - v i)) j.
Proof.
  intros u v j. induction j as [| j IH]; [ cbn [sum_f_R0]; ring | ].
  rewrite !tech5, IH. ring.
Qed.

Lemma sum_tel_down_R : forall (v : nat -> R) N,
  sum_f_R0 (fun i => v i - v (S i)) N = v 0%nat - v (S N).
Proof.
  intros v N. induction N as [| N IH]; [ cbn [sum_f_R0]; ring | ].
  rewrite tech5, IH. ring.
Qed.

Lemma sum_shift_diff : forall (c : nat -> R) M j,
  sum_f_R0 (fun i => c (M + S i)%nat) j
  = sum_f_R0 c (M + S j)%nat - sum_f_R0 c M.
Proof.
  intros c M j. induction j as [| j IH].
  - cbn [sum_f_R0]. replace (M + 1)%nat with (S M) by lia.
    rewrite tech5. ring.
  - rewrite tech5, IH.
    replace (M + S (S j))%nat with (S (M + S j))%nat by lia.
    rewrite tech5. ring.
Qed.

(* ----------------------------------------------------------------- *)
(*  Part B -- the bound.                                              *)
(* ----------------------------------------------------------------- *)

Lemma abel_bound : forall (u v : nat -> R) (B : R) j,
  (forall i, Rabs (u i) <= B) ->
  (forall i, 0 <= v (S i) /\ v (S i) <= v i) ->
  Rabs (sum_f_R0 (fun i => (u (S i) - u i) * v i) j) <= 2 * B * v 0%nat.
Proof.
  intros u v B j HB Hv.
  assert (HB0 : 0 <= B)
    by (eapply Rle_trans; [ apply Rabs_pos | apply (HB 0%nat) ]).
  assert (Hv0 : forall i, 0 <= v i).
  { intro i. destruct i as [| i]; [ | apply (Hv i) ].
    destruct (Hv 0%nat) as [Hp Hle]. lra. }
  rewrite abel_parts.
  set (T1 := u (S j) * v (S j)).
  set (T2 := u 0%nat * v 0%nat).
  set (T3 := sum_f_R0 (fun i => u (S i) * (v (S i) - v i)) j).
  assert (H1 : Rabs T1 <= B * v (S j)).
  { unfold T1. rewrite Rabs_mult, (Rabs_right (v (S j))) by (apply Rle_ge, Hv0).
    apply Rmult_le_compat_r; [ apply Hv0 | apply HB ]. }
  assert (H2 : Rabs T2 <= B * v 0%nat).
  { unfold T2. rewrite Rabs_mult, (Rabs_right (v 0%nat)) by (apply Rle_ge, Hv0).
    apply Rmult_le_compat_r; [ apply Hv0 | apply HB ]. }
  assert (H3 : Rabs T3 <= B * (v 0%nat - v (S j))).
  { unfold T3. eapply Rle_trans; [ apply Rsum_abs | ].
    eapply Rle_trans.
    - apply (sum_Rle _ (fun i => B * (v i - v (S i)))).
      intros i _. rewrite Rabs_mult.
      rewrite (Rabs_left1 (v (S i) - v i)) by (destruct (Hv i); lra).
      replace (- (v (S i) - v i)) with (v i - v (S i)) by ring.
      apply Rmult_le_compat_r; [ destruct (Hv i); lra | apply HB ].
    - rewrite (sum_eq (fun i => B * (v i - v (S i)))
                      (fun i => (v i - v (S i)) * B) j
                      (fun i _ => Rmult_comm B (v i - v (S i)))).
      rewrite <- (scal_sum (fun i => v i - v (S i)) j B).
      rewrite sum_tel_down_R. apply Rle_refl. }
  assert (Htri : Rabs (T1 - T2 - T3) <= Rabs T1 + Rabs T2 + Rabs T3).
  { replace (T1 - T2 - T3) with ((T1 + - T2) + - T3) by ring.
    eapply Rle_trans; [ apply Rabs_triang | ]. rewrite Rabs_Ropp.
    apply Rplus_le_compat_r.
    eapply Rle_trans; [ apply Rabs_triang | ]. rewrite Rabs_Ropp. apply Rle_refl. }
  lra.
Qed.

(* ----------------------------------------------------------------- *)
(*  Part C -- the headline: a uniform tail bound.                      *)
(* ----------------------------------------------------------------- *)

Theorem abel_tail : forall (a w : nat -> R) (B : R) M j,
  (forall n, Rabs (sum_f_R0 a n) <= B) ->
  (forall n, 0 <= w (S n) /\ w (S n) <= w n) ->
  Rabs (sum_f_R0 (fun k => a k * w k) (M + S j)%nat
        - sum_f_R0 (fun k => a k * w k) M) <= 2 * B * w (S M).
Proof.
  intros a w B M j HB Hw.
  rewrite <- (sum_shift_diff (fun k => a k * w k) M j).
  set (u := fun i => sum_f_R0 a (M + i)%nat).
  set (v := fun i => w (M + S i)%nat).
  rewrite (sum_eq (fun i => a (M + S i)%nat * w (M + S i)%nat)
                  (fun i => (u (S i) - u i) * v i) j).
  - replace (2 * B * w (S M)) with (2 * B * v 0%nat)
      by (unfold v; replace (M + 1)%nat with (S M) by lia; reflexivity).
    apply abel_bound.
    + intro i. unfold u. apply HB.
    + intro i. unfold v.
      replace (M + S (S i))%nat with (S (M + S i))%nat by lia. apply Hw.
  - intros i _. unfold u, v.
    replace (M + S i)%nat with (S (M + i))%nat by lia.
    rewrite tech5. ring.
Qed.

Print Assumptions abel_tail.

(* ================================================================= *)
(*  END RAbelSum.v                                                    *)
(* ================================================================= *)
