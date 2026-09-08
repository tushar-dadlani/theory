(* ================================================================= *)
(*  HyperbolaBridges.v  --  reindexing RS <-> sum_f_R0, and the three *)
(*  estimates restated in RS form.                                    *)
(*                                                                    *)
(*  SqrtSumAsym and CharTailBound are written with sum_f_R0, which is  *)
(*  0-indexed; HyperbolaSplit is written with RS, which is 1-indexed.  *)
(*  RS F (S M) = sum_f_R0 (fun k => F (S k)) M is the whole content,   *)
(*  but it has to be discharged once per sequence.                     *)
(*                                                                    *)
(*    ach_tail : |RS ach Y - Lchih| <= 2p / sqrt (Y+1)                *)
(*    w1s_tail : |RS w1s Y - Lchi1| <= 2p / (Y+1)                     *)
(*    bh_asym  : |RS bh Y - 2 sqrt Y - Csq| <= 2 / sqrt Y             *)
(*                                                                    *)
(*  plus the crude consequences (RS ach bounded, RS bh <= 2 sqrt Y + C)*)
(*  that the assembly actually consumes.                               *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia Arith ZArith Znumtheory List.
Require Import CRealChar CRealCharPos SqrtSumAsym RAbelSum CharTailBound
        HyperbolaSplit HyperbolaLower HyperbolaDouble.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  Part A -- generic.                                                *)
(* ----------------------------------------------------------------- *)

Lemma RS_abs_le : forall F G X,
  (forall n, (1 <= n <= X)%nat -> Rabs (F n) <= G n) -> Rabs (RS F X) <= RS G X.
Proof.
  intros F G X. induction X as [| X IH]; intro H.
  - cbn [RS]. rewrite Rabs_R0. apply Rle_refl.
  - cbn [RS]. eapply Rle_trans; [ apply Rabs_triang | ].
    apply Rplus_le_compat.
    + apply IH. intros n Hn. apply H. lia.
    + apply H. lia.
Qed.

Lemma INR_ge1 : forall n, (1 <= n)%nat -> 1 <= INR n.
Proof. intros n Hn. apply (le_INR 1); lia. Qed.

Lemma sqrt_INR_ge1 : forall n, (1 <= n)%nat -> 1 <= sqrt (INR n).
Proof.
  intros n Hn. rewrite <- sqrt_1. apply sqrt_le_1_alt. apply INR_ge1; lia.
Qed.

Lemma RS_bh_bridge : forall M, RS bh (S M) = Sq M.
Proof.
  induction M as [| M IH].
  - cbn [RS sum_f_R0]. unfold bh, Sq, st. cbn [sum_f_R0]. ring.
  - replace (RS bh (S (S M))) with (RS bh (S M) + bh (S (S M))) by reflexivity.
    rewrite IH. unfold Sq. rewrite tech5. unfold bh, st. ring.
Qed.

Theorem bh_asym : forall Y, (1 <= Y)%nat ->
  Rabs (RS bh Y - 2 * sqrt (INR Y) - Csq) <= 2 / sqrt (INR Y).
Proof.
  intros Y HY. destruct Y as [| M]; [ lia | ].
  rewrite RS_bh_bridge. unfold Rdiv. apply sqrt_sum_asym.
Qed.

Lemma bh_bounded : forall Y, (1 <= Y)%nat ->
  RS bh Y <= 2 * sqrt (INR Y) + Rabs Csq + 2.
Proof.
  intros Y HY.
  assert (Hs : 1 <= sqrt (INR Y)) by (apply sqrt_INR_ge1; lia).
  assert (Hd : 2 / sqrt (INR Y) <= 2).
  { assert (Hinv : / sqrt (INR Y) <= 1).
    { rewrite <- Rinv_1. apply Rinv_le_contravar; lra. }
    unfold Rdiv. lra. }
  pose proof (bh_asym Y HY) as H.
  pose proof (Rle_abs (RS bh Y - 2 * sqrt (INR Y) - Csq)) as H2.
  pose proof (Rle_abs Csq). lra.
Qed.

(* ----------------------------------------------------------------- *)
(*  Part B -- the character sequences.                                *)
(* ----------------------------------------------------------------- *)

Section Bridges.

Variable p g A : nat.
Hypothesis Hp : prime (Z.of_nat p).
Hypothesis Hg : (1 <= g <= p - 1)%nat.
Hypothesis Hord : ZmodOrder.ord p g = (p - 1)%nat.
Hypothesis HA : (0 < A < p - 1)%nat.
Hypothesis Hreal : forall n,
  ComplexField.Cconj (DirichletModP.dchar p g A n) = DirichletModP.dchar p g A n.

Definition w1s (d : nat) : R := IZR (chz p g A d) / INR d.

Notation LH := (Lchih p g A Hp Hg Hord HA Hreal).
Notation L1 := (Lchi1 p g A Hp Hg Hord HA Hreal).

Lemma RS_ach_bridge : forall M,
  RS (ach p g A) (S M) = sum_f_R0 (fun k => ca p g A k * wh k) M.
Proof.
  induction M as [| M IH].
  - cbn [RS sum_f_R0]. unfold ach, ca, cr, wh, Rdiv. ring.
  - replace (RS (ach p g A) (S (S M)))
      with (RS (ach p g A) (S M) + ach p g A (S (S M))) by reflexivity.
    rewrite tech5, IH. unfold ach, ca, cr, wh, Rdiv. ring.
Qed.

Lemma RS_w1s_bridge : forall M,
  RS w1s (S M) = sum_f_R0 (fun k => ca p g A k * w1 k) M.
Proof.
  induction M as [| M IH].
  - cbn [RS sum_f_R0]. unfold w1s, ca, cr, w1, Rdiv. ring.
  - replace (RS w1s (S (S M))) with (RS w1s (S M) + w1s (S (S M))) by reflexivity.
    rewrite tech5, IH. unfold w1s, ca, cr, w1, Rdiv. ring.
Qed.

Theorem ach_tail : forall Y, (1 <= Y)%nat ->
  Rabs (RS (ach p g A) Y - LH) <= 2 * INR p / sqrt (INR (S Y)).
Proof.
  intros Y HY. destruct Y as [| M]; [ lia | ].
  rewrite RS_ach_bridge, Rabs_minus_sym.
  pose proof (Lchih_tail p g A Hp Hg Hord HA Hreal M) as H.
  unfold wh in H. unfold Rdiv. exact H.
Qed.

Theorem w1s_tail : forall Y, (1 <= Y)%nat ->
  Rabs (RS w1s Y - L1) <= 2 * INR p / INR (S Y).
Proof.
  intros Y HY. destruct Y as [| M]; [ lia | ].
  rewrite RS_w1s_bridge, Rabs_minus_sym.
  pose proof (Lchi1_tail p g A Hp Hg Hord HA Hreal M) as H.
  unfold w1 in H. unfold Rdiv. exact H.
Qed.

(* ----- the crude consequences the assembly consumes ----- *)

Lemma ach_bounded : forall Y, (1 <= Y)%nat -> Rabs (RS (ach p g A) Y) <= Rabs LH + 2 * INR p.
Proof.
  intros Y HY.
  assert (Hs : 1 <= sqrt (INR (S Y))) by (apply sqrt_INR_ge1; lia).
  assert (Hp0 : 0 <= INR p) by apply pos_INR.
  pose proof (ach_tail Y HY) as H.
  assert (Hd : 2 * INR p / sqrt (INR (S Y)) <= 2 * INR p).
  { assert (Hinv : / sqrt (INR (S Y)) <= 1).
    { rewrite <- Rinv_1. apply Rinv_le_contravar; lra. }
    unfold Rdiv. nra. }
  assert (Ht : Rabs (RS (ach p g A) Y) - Rabs LH <= Rabs (RS (ach p g A) Y - LH))
    by apply Rabs_triang_inv.
  lra.
Qed.

End Bridges.

Print Assumptions ach_tail.
Print Assumptions bh_asym.

(* ================================================================= *)
(*  END HyperbolaBridges.v                                            *)
(* ================================================================= *)
