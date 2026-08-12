(* ================================================================= *)
(*  BerryKeatingFree.v                                                *)
(*                                                                    *)
(*  A genuinely INFINITE-DIMENSIONAL non-commutative dagger algebra:  *)
(*  the free *-algebra on two self-adjoint generators q (position /   *)
(*  multiplication) and p (momentum / shift).  Elements are           *)
(*  coefficient functions  word -> C  (words in {q,p}); the product   *)
(*  is convolution over concatenations and the adjoint is             *)
(*  word-reversal + conjugation -- a TOTAL, exact *-structure with no  *)
(*  unbounded-operator domain issues.  Any ell^2 shift/multiplication  *)
(*  representation is a quotient of this universal algebra.           *)
(*                                                                    *)
(*  Instantiating BerryKeating.DagAlg, q and p are self-adjoint with  *)
(*  [q,p] <> 0 (q p <> p q), so:                                       *)
(*     - q p is NOT self-adjoint       (qp_not_selfadj),              *)
(*     - q p + p q IS self-adjoint     (symmetrised_selfadj_free).    *)
(*  Now xp_selfadj_iff_commute bites on genuinely infinite-dimensional *)
(*  non-commuting self-adjoint operators.                            *)
(*                                                                    *)
(*  Axioms: the standard classical-Reals ones plus                    *)
(*  functional_extensionality (equality of coefficient functions).    *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra List Arith Lia FunctionalExtensionality.
Require Import ComplexField BerryKeating.
Import ListNotations.
Open Scope R_scope.

Inductive gen := gq | gp.
Definition gen_eq_dec : forall x y : gen, {x = y} + {x <> y}.
Proof. decide equality. Defined.
Definition word := list gen.
Definition Elt := word -> C.

Definition Csum (l : list C) : C := fold_right Cadd C0 l.
Definition splits (w : word) : list (word * word) :=
  map (fun k => (firstn k w, skipn k w)) (seq 0 (S (length w))).

Definition Fadd (a b : Elt) : Elt := fun w => Cadd (a w) (b w).
Definition Fdag (a : Elt) : Elt := fun w => Cconj (a (rev w)).
Definition Fmul (a b : Elt) : Elt :=
  fun w => Csum (map (fun pr => Cmul (a (fst pr)) (b (snd pr))) (splits w)).

Lemma Csum_conj : forall l, Cconj (Csum l) = Csum (map Cconj l).
Proof.
  induction l as [|x l IH]; simpl; [ apply Ceq; simpl; ring | rewrite Cconj_add, IH; reflexivity ].
Qed.

Lemma Csum_app : forall l1 l2, Csum (l1 ++ l2) = Cadd (Csum l1) (Csum l2).
Proof.
  induction l1 as [|x l1 IH]; intro l2; simpl;
    [ apply Ceq; simpl; ring | rewrite IH; apply Ceq; simpl; ring ].
Qed.

Lemma Csum_rev : forall l, Csum (rev l) = Csum l.
Proof.
  induction l as [|x l IH]; simpl; [ reflexivity | ].
  rewrite Csum_app; simpl; rewrite IH; apply Ceq; simpl; ring.
Qed.

Lemma rev_seq_0Sn : forall n, rev (seq 0 (S n)) = map (fun k => (n - k)%nat) (seq 0 (S n)).
Proof.
  intro n. apply nth_ext with (d := 0%nat) (d' := 0%nat).
  - rewrite length_rev, length_map; reflexivity.
  - intros i Hi. rewrite length_rev, length_seq in Hi.
    rewrite rev_nth by (rewrite length_seq; exact Hi). rewrite length_seq.
    rewrite (nth_indep (map (fun k => (n - k)%nat) (seq 0 (S n))) 0%nat ((fun k => (n - k)%nat) 0%nat))
      by (rewrite length_map, length_seq; exact Hi).
    rewrite map_nth, !seq_nth by lia. lia.
Qed.

Lemma splits_rev : forall w,
  splits (rev w) = map (fun pr => (rev (snd pr), rev (fst pr))) (rev (splits w)).
Proof.
  intro w. unfold splits. rewrite length_rev.
  rewrite (map_ext_in
             (fun k => (firstn k (rev w), skipn k (rev w)))
             (fun k => (rev (skipn (length w - k)%nat w), rev (firstn (length w - k)%nat w)))
             (seq 0 (S (length w))))
    by (intros k _; rewrite firstn_rev, skipn_rev; reflexivity).
  rewrite <- map_rev, map_map, rev_seq_0Sn, map_map. apply map_ext; intro k; reflexivity.
Qed.

Lemma Fadd_comm : forall a b, Fadd a b = Fadd b a.
Proof. intros a b; apply functional_extensionality; intro w; unfold Fadd; apply Cadd_comm'. Qed.

Lemma Fdag_add : forall a b, Fdag (Fadd a b) = Fadd (Fdag a) (Fdag b).
Proof. intros a b; apply functional_extensionality; intro w; unfold Fdag, Fadd; apply Cconj_add. Qed.

Lemma Fdag_invol : forall a, Fdag (Fdag a) = a.
Proof.
  intro a; apply functional_extensionality; intro w; unfold Fdag.
  rewrite rev_involutive, Cconj_involutive; reflexivity.
Qed.

Lemma Fdag_comp : forall a b, Fdag (Fmul a b) = Fmul (Fdag b) (Fdag a).
Proof.
  intros a b; apply functional_extensionality; intro w.
  unfold Fdag at 1; unfold Fmul.
  rewrite Csum_conj, map_map, splits_rev, map_map, map_rev, Csum_rev.
  unfold Fdag. f_equal. apply map_ext; intro pr.
  cbn [fst snd]. rewrite Cconj_mul. apply Cmul_comm'.
Qed.

Definition Free_DagAlg : DagAlg :=
  {| Op := Elt; Oadd := Fadd; Ocomp := Fmul; Odag := Fdag;
     Oadd_comm := Fadd_comm; Odag_add := Fdag_add;
     Odag_comp := Fdag_comp; Odag_invol := Fdag_invol |}.

(* the two self-adjoint generators *)
Definition q : Elt := fun w => if list_eq_dec gen_eq_dec w [gq] then C1 else C0.
Definition p : Elt := fun w => if list_eq_dec gen_eq_dec w [gp] then C1 else C0.

Lemma q_selfadj : SelfAdj Free_DagAlg q.
Proof.
  unfold SelfAdj, Free_DagAlg; simpl. apply functional_extensionality; intro w.
  unfold Fdag, q.
  destruct (list_eq_dec gen_eq_dec w [gq]) as [->|E].
  - simpl; destruct (list_eq_dec gen_eq_dec [gq] [gq]) as [_|N];
      [ apply Ceq; simpl; ring | exfalso; apply N; reflexivity ].
  - destruct (list_eq_dec gen_eq_dec (rev w) [gq]) as [E2|_];
      [ exfalso; apply E; rewrite <- (rev_involutive w), E2; reflexivity
      | apply Ceq; simpl; ring ].
Qed.

Lemma p_selfadj : SelfAdj Free_DagAlg p.
Proof.
  unfold SelfAdj, Free_DagAlg; simpl. apply functional_extensionality; intro w.
  unfold Fdag, p.
  destruct (list_eq_dec gen_eq_dec w [gp]) as [->|E].
  - simpl; destruct (list_eq_dec gen_eq_dec [gp] [gp]) as [_|N];
      [ apply Ceq; simpl; ring | exfalso; apply N; reflexivity ].
  - destruct (list_eq_dec gen_eq_dec (rev w) [gp]) as [E2|_];
      [ exfalso; apply E; rewrite <- (rev_involutive w), E2; reflexivity
      | apply Ceq; simpl; ring ].
Qed.

(* [q,p] <> 0 : the products differ at the word [gq;gp] (coeff 1 vs 0) *)
Lemma qp_ne_pq : Fmul q p <> Fmul p q.
Proof.
  intro H. apply (f_equal (fun f => f [gq; gp])) in H.
  unfold Fmul, splits, q, p in H; simpl in H.
  apply (f_equal Re) in H; revert H;
    unfold Cadd, Cmul, C0, C1, Cconj; simpl; lra.
Qed.

Theorem qp_not_selfadj : ~ SelfAdj Free_DagAlg (Ocomp Free_DagAlg q p).
Proof.
  intro H. apply qp_ne_pq.
  exact (proj1 (xp_selfadj_iff_commute Free_DagAlg q p q_selfadj p_selfadj) H).
Qed.

Theorem symmetrised_selfadj_free :
  SelfAdj Free_DagAlg (Oadd Free_DagAlg (Ocomp Free_DagAlg q p) (Ocomp Free_DagAlg p q)).
Proof. apply anticomm_selfadj; [ exact q_selfadj | exact p_selfadj ]. Qed.

Print Assumptions qp_not_selfadj.
Print Assumptions symmetrised_selfadj_free.
