(* ================================================================= *)
(*  QProd.v                                                          *)
(*                                                                    *)
(*  PRODUCTS OF (embedded) CYCLOTOMIC FACTORS over ℚ (brick 6b).     *)
(*                                                                    *)
(*  qprod l := ∏_{d∈l} emb(Φ_d).  It is permutation-invariant, splits *)
(*  over append, and every listed factor divides it.  With           *)
(*  "remove" it factors out one element, giving product-over-sublist  *)
(*  divisibility — the combinatorial tool behind the coprimality of   *)
(*  the cyclotomic factors of X^n−1.  AXIOM-FREE.                    *)
(* ================================================================= *)

From Stdlib Require Import QArith Qcanon List Lia Arith Permutation.
Import ListNotations.
Require Import QPoly QPolyGcd QPolyEmbed Cyclotomic.
Open Scope Qc_scope.

Definition qprod (l : list nat) : qpoly :=
  fold_right (fun d acc => qmul (emb (Phi d)) acc) [1] l.

Lemma qeval_qprod_cons : forall d l x,
  qeval (qprod (d :: l)) x = qeval (emb (Phi d)) x * qeval (qprod l) x.
Proof. intros d l x; unfold qprod; simpl; rewrite qeval_mul; reflexivity. Qed.

Lemma qeval_qprod_nil : forall x, qeval (qprod []) x = 1.
Proof. intro x; unfold qprod; simpl; ring. Qed.

Lemma qprod_perm : forall l1 l2, Permutation l1 l2 ->
  forall x, qeval (qprod l1) x = qeval (qprod l2) x.
Proof.
  intros l1 l2 Hp; induction Hp; intro t.
  - reflexivity.
  - rewrite !qeval_qprod_cons, IHHp; reflexivity.
  - rewrite !qeval_qprod_cons; ring.
  - rewrite IHHp1, IHHp2; reflexivity.
Qed.

Lemma qeval_qprod_app : forall l1 l2 x,
  qeval (qprod (l1 ++ l2)) x = qeval (qprod l1) x * qeval (qprod l2) x.
Proof.
  induction l1 as [|a l1 IH]; intros l2 x.
  - rewrite app_nil_l, qeval_qprod_nil; ring.
  - rewrite <- app_comm_cons, !qeval_qprod_cons, IH; ring.
Qed.

Lemma qdivides_qprod_in : forall d l, In d l -> qdivides (emb (Phi d)) (qprod l).
Proof.
  induction l as [|a l IH]; intro Hin; [ destruct Hin | ].
  destruct Hin as [-> | Hin].
  - exists (qprod l); intro x; rewrite qeval_qprod_cons; reflexivity.
  - destruct (IH Hin) as [r Hr]; exists (qmul (emb (Phi a)) r); intro x.
    rewrite qeval_qprod_cons, qeval_mul, Hr; ring.
Qed.

(* remove factors out one element *)
Lemma remove_app_mid : forall d l1 l2, ~ In d l1 -> ~ In d l2 ->
  remove Nat.eq_dec d (l1 ++ d :: l2) = l1 ++ l2.
Proof.
  intros d l1 l2 H1 H2; rewrite remove_app; simpl.
  destruct (Nat.eq_dec d d) as [_ | Hne]; [ | exfalso; apply Hne; reflexivity ].
  rewrite !notin_remove by assumption; reflexivity.
Qed.

Lemma qprod_remove : forall d l, In d l -> NoDup l -> forall x,
  qeval (qprod l) x = qeval (emb (Phi d)) x * qeval (qprod (remove Nat.eq_dec d l)) x.
Proof.
  intros d l Hin Hnd x.
  destruct (in_split d l Hin) as [l1 [l2 Heq]]; subst l.
  apply NoDup_remove in Hnd; destruct Hnd as [Hnd Hni].
  assert (Hn1 : ~ In d l1) by (intro; apply Hni, in_or_app; left; assumption).
  assert (Hn2 : ~ In d l2) by (intro; apply Hni, in_or_app; right; assumption).
  rewrite (qprod_perm _ _ (Permutation_sym (Permutation_middle l1 l2 d)) x), qeval_qprod_cons.
  rewrite (remove_app_mid d l1 l2 Hn1 Hn2); reflexivity.
Qed.

Lemma nodup_remove_fn : forall (a : nat) l, NoDup l -> NoDup (remove Nat.eq_dec a l).
Proof.
  intros a l H; induction H as [|x l0 Hx Hnd IH]; simpl; [ constructor | ].
  destruct (Nat.eq_dec a x) as [_ | Hne]; [ exact IH | ].
  constructor; [ intro Hin; apply in_remove in Hin; destruct Hin as [Hin _]; contradiction | exact IH ].
Qed.

(* product over a sublist divides product over the (NoDup) superlist *)
Theorem qdivides_qprod_incl : forall l1 l2,
  incl l1 l2 -> NoDup l1 -> NoDup l2 -> qdivides (qprod l1) (qprod l2).
Proof.
  induction l1 as [|a l1 IH]; intros l2 Hincl Hnd1 Hnd2.
  - exists (qprod l2); intro x; rewrite qeval_qprod_nil; ring.
  - inversion Hnd1 as [| ? ? Hna Hnd1']; subst.
    assert (Hain : In a l2) by (apply Hincl; left; reflexivity).
    assert (Hincl' : incl l1 (remove Nat.eq_dec a l2)).
    { intros y Hy; apply in_in_remove; [ intro; subst; contradiction | apply Hincl; right; exact Hy ]. }
    destruct (IH (remove Nat.eq_dec a l2) Hincl' Hnd1' (nodup_remove_fn a l2 Hnd2)) as [r Hr].
    exists r; intro x.
    rewrite qeval_qprod_cons, (qprod_remove a l2 Hain Hnd2 x), Hr; ring.
Qed.

Print Assumptions qdivides_qprod_incl.

(* ================================================================= *)
(*  END QProd.v                                                      *)
(*  ∏_{d∈l} Φ_d over ℚ: permutation-invariant, splits over append,   *)
(*  factor-divisibility, and product-over-sublist divisibility.      *)
(*  Closed under the global context (axiom-free).                    *)
(* ================================================================= *)
