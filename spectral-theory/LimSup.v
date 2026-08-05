(* ================================================================= *)
(*  LimSup.v  —  RUNG 1 of the Erdos-Selberg limsup layer.             *)
(*                                                                    *)
(*  A reusable, RELATIONAL limsup for bounded real sequences:          *)
(*                                                                    *)
(*    is_limsup u L :=                                                 *)
(*      (forall eps>0, eventually  u n < L + eps)                      *)
(*      /\ (forall eps>0, infinitely often  L - eps < u n).            *)
(*                                                                    *)
(*  The API is relational so nothing downstream depends on proof       *)
(*  terms.  We prove:                                                  *)
(*    limsup_exists    : bounded u  ->  { L | is_limsup u L }          *)
(*    is_limsup_unique : is_limsup u L1 -> is_limsup u L2 -> L1 = L2   *)
(*    is_limsup_le_ub  : (forall n, u n <= C) -> L <= C                *)
(*    is_limsup_nonneg : (forall n, 0 <= u n) -> 0 <= L                *)
(*                                                                    *)
(*  Existence is built from stdlib completeness (tail suprema) and     *)
(*  decreasing_cv (the tail suprema decrease to their inf = L).        *)
(*  Uses only the classical-Reals axioms (classic via NNPP).           *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia Arith Classical_Prop.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  The relational interface.                                         *)
(* ----------------------------------------------------------------- *)

Definition is_limsup (u : nat -> R) (L : R) : Prop :=
  (forall eps, 0 < eps -> exists N0, forall n, (N0 <= n)%nat -> u n < L + eps)
  /\ (forall eps, 0 < eps -> forall N, exists k, (N <= k)%nat /\ L - eps < u k).

(* ----------------------------------------------------------------- *)
(*  Uniqueness and the two comparison lemmas (no boundedness needed). *)
(* ----------------------------------------------------------------- *)

Lemma is_limsup_unique : forall u L1 L2,
  is_limsup u L1 -> is_limsup u L2 -> L1 = L2.
Proof.
  intros u L1 L2 [Ha1 Hb1] [Ha2 Hb2].
  destruct (Rtotal_order L1 L2) as [H | [H | H]]; [ exfalso | exact H | exfalso ].
  - destruct (Ha1 ((L2 - L1) / 2) ltac:(lra)) as [N0 HN0].
    destruct (Hb2 ((L2 - L1) / 2) ltac:(lra) N0) as [k [Hk Hgt]].
    specialize (HN0 k Hk); lra.
  - destruct (Ha2 ((L1 - L2) / 2) ltac:(lra)) as [N0 HN0].
    destruct (Hb1 ((L1 - L2) / 2) ltac:(lra) N0) as [k [Hk Hgt]].
    specialize (HN0 k Hk); lra.
Qed.

Lemma is_limsup_le_ub : forall u L C,
  is_limsup u L -> (forall n, u n <= C) -> L <= C.
Proof.
  intros u L C [_ Hb] Hub.
  destruct (Rle_or_lt L C) as [H | H]; [ exact H | exfalso ].
  destruct (Hb ((L - C) / 2) ltac:(lra) 0%nat) as [k [_ Hgt]].
  pose proof (Hub k); lra.
Qed.

Lemma is_limsup_nonneg : forall u L,
  is_limsup u L -> (forall n, 0 <= u n) -> 0 <= L.
Proof.
  intros u L [Ha _] Hnn.
  destruct (Rle_or_lt 0 L) as [H | H]; [ exact H | exfalso ].
  destruct (Ha (- L / 2) ltac:(lra)) as [N0 HN0].
  specialize (HN0 N0 (le_n N0)); pose proof (Hnn N0); lra.
Qed.

(* ----------------------------------------------------------------- *)
(*  A lub is approximated from below (classical).                     *)
(* ----------------------------------------------------------------- *)

Lemma lub_approx : forall (E : R -> Prop) s,
  is_lub E s -> forall eps, 0 < eps -> exists x, E x /\ s - eps < x.
Proof.
  intros E s [Hub Hlub] eps Heps.
  apply NNPP; intro Hcon.
  assert (Hb : is_upper_bound E (s - eps)).
  { intros x Hx. destruct (Rle_or_lt x (s - eps)) as [H | H]; [ exact H | ].
    exfalso; apply Hcon; exists x; split; [ exact Hx | exact H ]. }
  specialize (Hlub (s - eps) Hb); lra.
Qed.

(* ----------------------------------------------------------------- *)
(*  Existence, for a bounded sequence.                                *)
(* ----------------------------------------------------------------- *)

Section Existence.

Variable u : nat -> R.
Hypothesis Hlb : exists m, forall n, m <= u n.
Hypothesis Hub : exists M, forall n, u n <= M.

Definition tail_set (N : nat) (x : R) : Prop := exists k, (N <= k)%nat /\ x = u k.

Lemma tail_lub_sig : forall N, { s | is_lub (tail_set N) s }.
Proof.
  intro N. apply completeness.
  - destruct Hub as [M HM]. exists M. intros x [k [_ ->]]. apply HM.
  - exists (u N). exists N. split; [ apply le_n | reflexivity ].
Defined.

Definition tsup (N : nat) : R := proj1_sig (tail_lub_sig N).

Lemma tsup_is_lub : forall N, is_lub (tail_set N) (tsup N).
Proof. intro N; unfold tsup; apply (proj2_sig (tail_lub_sig N)). Qed.

Lemma tsup_ub : forall N k, (N <= k)%nat -> u k <= tsup N.
Proof.
  intros N k Hk. destruct (tsup_is_lub N) as [Hu _]; apply Hu.
  exists k; split; [ exact Hk | reflexivity ].
Qed.

Lemma tsup_decreasing : Un_decreasing tsup.
Proof.
  intro N. destruct (tsup_is_lub (S N)) as [_ Hlub2].
  apply Hlub2. intros x [k [Hk ->]]. apply tsup_ub; lia.
Qed.

Lemma tsup_antitone : forall a b, (a <= b)%nat -> tsup b <= tsup a.
Proof.
  intros a b Hab; induction Hab as [ | b Hab IH ]; [ apply Rle_refl | ].
  eapply Rle_trans; [ apply tsup_decreasing | exact IH ].
Qed.

Lemma tsup_has_lb : has_lb tsup.
Proof.
  destruct Hlb as [m Hm]. exists (- m). intros x [i ->].
  unfold opp_seq; apply Ropp_le_contravar.
  apply Rle_trans with (u i); [ apply Hm | apply tsup_ub; apply le_n ].
Qed.

Definition Lsup : R := proj1_sig (decreasing_cv tsup tsup_decreasing tsup_has_lb).

Lemma tsup_cv : Un_cv tsup Lsup.
Proof. unfold Lsup; apply (proj2_sig (decreasing_cv tsup tsup_decreasing tsup_has_lb)). Qed.

Lemma tsup_ge_Lsup : forall N, Lsup <= tsup N.
Proof.
  intro N. destruct (Rle_or_lt Lsup (tsup N)) as [H | H]; [ exact H | exfalso ].
  destruct (tsup_cv (Lsup - tsup N) ltac:(lra)) as [M HM].
  specialize (HM (Nat.max M N) (Nat.le_max_l _ _)).
  assert (Hdec : tsup (Nat.max M N) <= tsup N)
    by (apply tsup_antitone; apply Nat.le_max_r).
  unfold R_dist in HM; apply Rabs_def2 in HM; lra.
Qed.

Lemma Lsup_is_limsup : is_limsup u Lsup.
Proof.
  split.
  - intros eps Heps.
    destruct (tsup_cv eps Heps) as [N0 HN0].
    exists N0; intros n Hn.
    apply Rle_lt_trans with (tsup N0); [ apply tsup_ub; exact Hn | ].
    specialize (HN0 N0 (le_n N0)); unfold R_dist in HN0; apply Rabs_def2 in HN0; lra.
  - intros eps Heps N.
    destruct (lub_approx (tail_set N) (tsup N) (tsup_is_lub N) eps Heps)
      as [x [[k [Hk Hx]] Hgt]].
    exists k; split; [ exact Hk | ].
    pose proof (tsup_ge_Lsup N); subst x; lra.
Qed.

Theorem limsup_exists : { L | is_limsup u L }.
Proof. exists Lsup; apply Lsup_is_limsup. Defined.

End Existence.

Print Assumptions limsup_exists.

(* ================================================================= *)
(*  END LimSup.v  —  RUNG 1: the limsup interface (bounded seqs).      *)
(* ================================================================= *)
