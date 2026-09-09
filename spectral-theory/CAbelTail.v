(* ================================================================= *)
(*  CAbelTail.v  --  summation by parts with COMPLEX coefficients and *)
(*  a REAL decreasing weight.                                         *)
(*                                                                    *)
(*    | sum_{k=M+1}^{N} a_k w_k |  <=  2 B w_{M+1}                     *)
(*                                                                    *)
(*  RAbelSum.abel_tail is the all-real version; CAbelSummation.        *)
(*  Cabel_summation is the raw C-valued identity with no bound.  The   *)
(*  case actually needed for L-functions is mixed: a_k = chi(k) is     *)
(*  complex with bounded partial sums (CCharSumBound.PS_bound), while  *)
(*  the weight ln k k^{-sigma} is real and eventually decreasing.      *)
(*                                                                    *)
(*  TWO CHANGES FROM RAbelSum.abel_tail, both forced by the intended   *)
(*  use on D(s) = sum chi(n) ln n n^{-s}:                              *)
(*                                                                    *)
(*  (1) the monotonicity hypothesis is LOCAL, required only from M on. *)
(*      ln n n^{-sigma} INCREASES from n = 1 to n = 2 and only then    *)
(*      decreases, so a global hypothesis would be false and the       *)
(*      lemma unusable.  The proof never needed it globally.           *)
(*                                                                    *)
(*  (2) the weight enters as RtoC (w k), so Cmod (a k * RtoC (w k))    *)
(*      = Cmod (a k) * Rabs (w k); the telescoping stays entirely in R.*)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import ComplexField Cmodulus CSeries RAbelSum.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  Part A -- the identity.                                            *)
(* ----------------------------------------------------------------- *)

Lemma Cabel_parts : forall (u : nat -> C) (v : nat -> R) j,
  Cpsum (fun i => Cmul (Cminus (u (S i)) (u i)) (RtoC (v i))) j
  = Cminus (Cminus (Cmul (u (S j)) (RtoC (v (S j))))
                   (Cmul (u 0%nat) (RtoC (v 0%nat))))
           (Cpsum (fun i => Cmul (u (S i))
                     (Cminus (RtoC (v (S i))) (RtoC (v i)))) j).
Proof.
  intros u v j. induction j as [| j IH]; [ cbn [Cpsum]; ring | ].
  replace (Cpsum (fun i => Cmul (Cminus (u (S i)) (u i)) (RtoC (v i))) (S j))
    with (Cadd (Cpsum (fun i => Cmul (Cminus (u (S i)) (u i)) (RtoC (v i))) j)
               (Cmul (Cminus (u (S (S j))) (u (S j))) (RtoC (v (S j)))))
    by reflexivity.
  replace (Cpsum (fun i => Cmul (u (S i))
                    (Cminus (RtoC (v (S i))) (RtoC (v i)))) (S j))
    with (Cadd (Cpsum (fun i => Cmul (u (S i))
                    (Cminus (RtoC (v (S i))) (RtoC (v i)))) j)
               (Cmul (u (S (S j)))
                    (Cminus (RtoC (v (S (S j)))) (RtoC (v (S j))))))
    by reflexivity.
  rewrite IH. ring.
Qed.

Lemma Cpsum_ext : forall F G N, (forall k, F k = G k) -> Cpsum F N = Cpsum G N.
Proof.
  intros F G N H. induction N as [| N IH]; [ apply H | ].
  replace (Cpsum F (S N)) with (Cadd (Cpsum F N) (F (S N))) by reflexivity.
  replace (Cpsum G (S N)) with (Cadd (Cpsum G N) (G (S N))) by reflexivity.
  rewrite IH, (H (S N)). reflexivity.
Qed.

Lemma Cpsum_shift_diff : forall (c : nat -> C) M j,
  Cpsum (fun i => c (M + S i)%nat) j
  = Cminus (Cpsum c (M + S j)%nat) (Cpsum c M).
Proof.
  intros c M j. induction j as [| j IH].
  - cbn [Cpsum]. replace (M + 1)%nat with (S M) by lia.
    replace (Cpsum c (S M)) with (Cadd (Cpsum c M) (c (S M))) by reflexivity.
    ring.
  - replace (Cpsum (fun i => c (M + S i)%nat) (S j))
      with (Cadd (Cpsum (fun i => c (M + S i)%nat) j) (c (M + S (S j))%nat))
      by reflexivity.
    rewrite IH.
    replace (M + S (S j))%nat with (S (M + S j))%nat by lia.
    replace (Cpsum c (S (M + S j)))
      with (Cadd (Cpsum c (M + S j)) (c (S (M + S j)))) by reflexivity.
    ring.
Qed.

(* ----------------------------------------------------------------- *)
(*  Part B -- the bound.                                               *)
(* ----------------------------------------------------------------- *)

Lemma Cmod_mul_RtoC : forall (z : C) (r : R),
  Cmod (Cmul z (RtoC r)) = Cmod z * Rabs r.
Proof. intros z r. rewrite Cmod_mul, Cmod_RtoC. reflexivity. Qed.

Lemma Cabel_bound : forall (u : nat -> C) (v : nat -> R) (B : R) j,
  (forall i, Cmod (u i) <= B) ->
  (forall i, 0 <= v (S i) /\ v (S i) <= v i) ->
  Cmod (Cpsum (fun i => Cmul (Cminus (u (S i)) (u i)) (RtoC (v i))) j)
  <= 2 * B * v 0%nat.
Proof.
  intros u v B j HB Hv.
  assert (HB0 : 0 <= B)
    by (eapply Rle_trans; [ apply Cmod_nonneg | apply (HB 0%nat) ]).
  assert (Hv0 : forall i, 0 <= v i).
  { intro i. destruct i as [| i]; [ | apply (Hv i) ].
    destruct (Hv 0%nat) as [Hp Hle]. lra. }
  rewrite Cabel_parts.
  set (T1 := Cmul (u (S j)) (RtoC (v (S j)))).
  set (T2 := Cmul (u 0%nat) (RtoC (v 0%nat))).
  set (T3 := Cpsum (fun i => Cmul (u (S i))
                      (Cminus (RtoC (v (S i))) (RtoC (v i)))) j).
  assert (H1 : Cmod T1 <= B * v (S j)).
  { unfold T1. rewrite Cmod_mul_RtoC, (Rabs_pos_eq _ (Hv0 (S j))).
    apply Rmult_le_compat_r; [ apply Hv0 | apply HB ]. }
  assert (H2 : Cmod T2 <= B * v 0%nat).
  { unfold T2. rewrite Cmod_mul_RtoC, (Rabs_pos_eq _ (Hv0 0%nat)).
    apply Rmult_le_compat_r; [ apply Hv0 | apply HB ]. }
  assert (H3 : Cmod T3 <= B * (v 0%nat - v (S j))).
  { unfold T3. eapply Rle_trans; [ apply Cmod_Cpsum_le | ].
    eapply Rle_trans.
    - apply (sum_Rle _ (fun i => B * (v i - v (S i)))).
      intros i _.
      replace (Cminus (RtoC (v (S i))) (RtoC (v i)))
        with (RtoC (v (S i) - v i))
        by (apply Ceq; unfold Cminus, Cadd, Copp, RtoC; cbn [Re Im]; ring).
      rewrite Cmod_mul_RtoC, (Rabs_left1 (v (S i) - v i))
        by (destruct (Hv i); lra).
      replace (- (v (S i) - v i)) with (v i - v (S i)) by ring.
      apply Rmult_le_compat_r; [ destruct (Hv i); lra | apply HB ].
    - rewrite (sum_eq (fun i => B * (v i - v (S i)))
                      (fun i => (v i - v (S i)) * B) j
                      (fun i _ => Rmult_comm B (v i - v (S i)))).
      rewrite <- (scal_sum (fun i => v i - v (S i)) j B).
      rewrite sum_tel_down_R. apply Rle_refl. }
  assert (Htri : Cmod (Cminus (Cminus T1 T2) T3)
                 <= Cmod T1 + Cmod T2 + Cmod T3).
  { replace (Cminus (Cminus T1 T2) T3) with (Cadd (Cadd T1 (Copp T2)) (Copp T3))
      by ring.
    eapply Rle_trans; [ apply Cmod_triangle | ]. rewrite Cmod_opp.
    apply Rplus_le_compat_r.
    eapply Rle_trans; [ apply Cmod_triangle | ]. rewrite Cmod_opp.
    apply Rle_refl. }
  lra.
Qed.

(* ----------------------------------------------------------------- *)
(*  Part C -- the tail bound, monotonicity required only from M on.    *)
(* ----------------------------------------------------------------- *)

Theorem Cabel_tail : forall (a : nat -> C) (w : nat -> R) (B : R) M j,
  (forall n, Cmod (Cpsum a n) <= B) ->
  (forall n, (M <= n)%nat -> 0 <= w (S n) /\ w (S n) <= w n) ->
  Cmod (Cminus (Cpsum (fun k => Cmul (a k) (RtoC (w k))) (M + S j)%nat)
               (Cpsum (fun k => Cmul (a k) (RtoC (w k))) M))
  <= 2 * B * w (S M).
Proof.
  intros a w B M j HB Hw.
  rewrite <- (Cpsum_shift_diff (fun k => Cmul (a k) (RtoC (w k))) M j).
  set (u := fun i => Cpsum a (M + i)%nat).
  set (v := fun i => w (M + S i)%nat).
  rewrite (Cpsum_ext (fun i => Cmul (a (M + S i)%nat) (RtoC (w (M + S i)%nat)))
                     (fun i => Cmul (Cminus (u (S i)) (u i)) (RtoC (v i))) j).
  - replace (2 * B * w (S M)) with (2 * B * v 0%nat)
      by (unfold v; replace (M + 1)%nat with (S M) by lia; reflexivity).
    apply Cabel_bound.
    + intro i. unfold u. apply HB.
    + intro i. unfold v.
      replace (M + S (S i))%nat with (S (M + S i))%nat by lia.
      apply Hw. lia.
  - intro i. unfold u, v.
    replace (M + S i)%nat with (S (M + i))%nat by lia.
    replace (Cpsum a (S (M + i))) with (Cadd (Cpsum a (M + i)) (a (S (M + i))))
      by reflexivity.
    ring.
Qed.

Print Assumptions Cabel_tail.

(* ================================================================= *)
(*  END CAbelTail.v                                                   *)
(* ================================================================= *)
