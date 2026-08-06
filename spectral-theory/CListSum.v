(* ================================================================= *)
(*  CListSum.v  —  Milestone A / B3a: a C-valued list sum Cls and its   *)
(*  bridge to the R-valued Rls (Re_Cls / Im_Cls).  This lets the        *)
(*  R-valued Dirichlet-hyperbola combinatorics (hyperbola_swap) be      *)
(*  reused componentwise, and provides the finite Cauchy-product        *)
(*  separation (Cls_prodsep) needed for the Dirichlet-series product.   *)
(*  All lemmas are trivial mirrors of Rls / sumf.                       *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia List.
Require Import ComplexField Cmodulus CSeries RealMobius.
Import ListNotations.
Open Scope R_scope.

Definition Cls {A : Type} (l : list A) (f : A -> C) : C :=
  fold_right Cadd C0 (map f l).

Lemma Cls_nil : forall A (f : A -> C), Cls (@nil A) f = C0.
Proof. reflexivity. Qed.

Lemma Cls_cons : forall A (f : A -> C) x l, Cls (x :: l) f = Cadd (f x) (Cls l f).
Proof. reflexivity. Qed.

Lemma Cls_ext : forall A (f g : A -> C) l,
  (forall x, In x l -> f x = g x) -> Cls l f = Cls l g.
Proof.
  intros A f g l; induction l as [|a l IH]; intro H; [ reflexivity | ].
  rewrite !Cls_cons, (H a (in_eq a l)), IH;
    [ reflexivity | intros x Hx; apply H; right; exact Hx ].
Qed.

Lemma Cls_app : forall A (f : A -> C) l1 l2,
  Cls (l1 ++ l2) f = Cadd (Cls l1 f) (Cls l2 f).
Proof.
  intros A f l1 l2; induction l1 as [|a l1 IH]; [ cbn [app]; rewrite Cls_nil; ring | ].
  cbn [app]; rewrite !Cls_cons, IH; ring.
Qed.

Lemma Cls_scal : forall A (c : C) (f : A -> C) l,
  Cmul c (Cls l f) = Cls l (fun x => Cmul c (f x)).
Proof.
  intros A c f l; induction l as [|a l IH]; [ rewrite !Cls_nil; ring | ].
  rewrite !Cls_cons, <- IH; ring.
Qed.

Lemma Cls_map : forall A B (g : A -> B) (f : B -> C) l,
  Cls (map g l) f = Cls l (fun x => f (g x)).
Proof.
  intros A B g f l; induction l as [|a l IH]; [ reflexivity | ].
  cbn [map]; rewrite !Cls_cons, IH; reflexivity.
Qed.

Lemma Re_Cls : forall A (f : A -> C) l, Re (Cls l f) = Rls l (fun x => Re (f x)).
Proof.
  intros A f l; induction l as [|a l IH]; [ reflexivity | ].
  rewrite Cls_cons, Rls_cons; unfold Cadd; cbn [Re]; rewrite IH; reflexivity.
Qed.

Lemma Im_Cls : forall A (f : A -> C) l, Im (Cls l f) = Rls l (fun x => Im (f x)).
Proof.
  intros A f l; induction l as [|a l IH]; [ reflexivity | ].
  rewrite Cls_cons, Rls_cons; unfold Cadd; cbn [Im]; rewrite IH; reflexivity.
Qed.

Lemma Cmod_Cls_le : forall A (f : A -> C) l,
  Cmod (Cls l f) <= Rls l (fun x => Cmod (f x)).
Proof.
  intros A f l; induction l as [|a l IH];
    [ rewrite Cls_nil; replace (Cmod C0) with 0 by (symmetry; apply Cmod0; reflexivity);
      simpl; apply Rle_refl | ].
  rewrite Cls_cons, Rls_cons.
  eapply Rle_trans; [ apply Cmod_triangle | apply Rplus_le_compat_l; exact IH ].
Qed.

Lemma Cls_list_prod : forall A B (l1 : list A) (l2 : list B) (F : A * B -> C),
  Cls (list_prod l1 l2) F = Cls l1 (fun a => Cls l2 (fun b => F (a, b))).
Proof.
  intros A B l1 l2 F; induction l1 as [|a l1 IH]; [ reflexivity | ].
  cbn [list_prod]; rewrite Cls_app, Cls_map, Cls_cons, IH; reflexivity.
Qed.

Lemma Cls_prodsep : forall (l1 l2 : list nat) (X Y : nat -> C),
  Cls (list_prod l1 l2) (fun de => Cmul (X (fst de)) (Y (snd de)))
  = Cmul (Cls l1 X) (Cls l2 Y).
Proof.
  intros l1 l2 X Y; rewrite Cls_list_prod.
  transitivity (Cls l1 (fun a => Cmul (Cls l2 Y) (X a))).
  - apply Cls_ext; intros a _; cbn [fst snd].
    transitivity (Cls l2 (fun b => Cmul (X a) (Y b))).
    + apply Cls_ext; intros b _; reflexivity.
    + rewrite <- Cls_scal; ring.
  - rewrite <- Cls_scal; ring.
Qed.

Lemma Cpsum_shift_eq_Cls : forall (g : nat -> C) N,
  Cpsum (fun n => g (S n)) N = Cls (seq 1 (S N)) g.
Proof.
  intros g N; induction N as [|N IH];
    [ cbn [Cpsum seq]; rewrite Cls_cons, Cls_nil; ring | ].
  cbn [Cpsum]; rewrite IH, (List.seq_S (S N) 1), Cls_app, Cls_cons, Cls_nil.
  replace (1 + S N)%nat with (S (S N)) by lia; ring.
Qed.

Print Assumptions Cls_prodsep.
Print Assumptions Cpsum_shift_eq_Cls.

(* ================================================================= *)
(*  END CListSum.v  —  the C-valued list sum toolkit (B3a).            *)
(* ================================================================= *)
