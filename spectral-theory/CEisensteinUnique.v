(* ================================================================= *)
(*  CEisensteinUnique.v  —  UNIQUENESS of factorization in Z[omega].   *)
(*                                                                    *)
(*    eassoc  : x and y differ by a unit                               *)
(*    aperm   : permutation up to associates                           *)
(*    unique_factorization : two irreducible factorizations of the     *)
(*              same element are aperm                                 *)
(*                                                                    *)
(*  Uniqueness is only ever true UP TO UNITS AND ORDER, so the         *)
(*  statement has to carry both.  aperm is Permutation with the        *)
(*  cons rule relaxed from equality to eassoc -- four constructors,    *)
(*  and Permutation embeds into it by reflexivity of eassoc.           *)
(*                                                                    *)
(*  THE INDUCTION HAS TO BE STRENGTHENED BY A UNIT.  Peeling pi off    *)
(*  the left and its associate x = pi.v off the right and cancelling   *)
(*  pi leaves  u . prodl t1 = v . prodl l2'', not an equality of bare  *)
(*  products: a unit is left over and there is nowhere to put it.      *)
(*  Carrying a unit u in the statement absorbs it -- the recursive     *)
(*  call runs with v^{-1}u -- and this is the only reason unique_aux   *)
(*  is not just the theorem itself.  Trying to push the unit into an   *)
(*  element of the list instead forces a proof that associates of      *)
(*  irreducibles are irreducible, and then the lists no longer match   *)
(*  by permutation.                                                    *)
(*                                                                    *)
(*  Cancelling pi is legitimate because Z[omega] is a domain           *)
(*  (CEisensteinUFD.emul_cancel) and irreducibles are nonzero.         *)
(*  classic is inherited from the existence file only; the uniqueness  *)
(*  argument itself is constructive.                                   *)
(* ================================================================= *)

From Stdlib Require Import ZArith Znumtheory Lia Ring List Permutation.
Require Import CEisenstein CEisensteinUnits CEisensteinDiv CEisensteinGcd
        CEisensteinUFD.
Import ListNotations.
Open Scope Z_scope.

(* ----------------------------------------------------------------- *)
(*  A.  units and associates                                           *)
(* ----------------------------------------------------------------- *)
Lemma eunit_one : eunit eone.
Proof. exists eone. ring. Qed.

Lemma eunit_inv_unit : forall u v, emul u v = eone -> eunit v.
Proof. intros u v H. exists u. rewrite <- H. ring. Qed.

Lemma eunit_mul : forall a b, eunit a -> eunit b -> eunit (emul a b).
Proof.
  intros a b [x Hx] [y Hy]. exists (emul x y).
  transitivity (emul (emul a x) (emul b y)); [ ring | rewrite Hx, Hy; ring ].
Qed.

Lemma edvd_unit_unit : forall y u, eunit u -> edvd y u -> eunit y.
Proof.
  intros y u [ui Hui] [w Hw]. exists (emul w ui).
  rewrite <- Hui, Hw. ring.
Qed.

Definition eassoc (x y : Eis) : Prop := exists u, eunit u /\ y = emul x u.

Lemma eassoc_refl : forall x, eassoc x x.
Proof. intro x. exists eone. split; [ apply eunit_one | ring ]. Qed.

(* ----------------------------------------------------------------- *)
(*  B.  permutation up to associates                                   *)
(* ----------------------------------------------------------------- *)
Inductive aperm : list Eis -> list Eis -> Prop :=
| aperm_nil   : aperm [] []
| aperm_cons  : forall x y l1 l2, eassoc x y -> aperm l1 l2 -> aperm (x :: l1) (y :: l2)
| aperm_swap  : forall x y l, aperm (x :: y :: l) (y :: x :: l)
| aperm_trans : forall l1 l2 l3, aperm l1 l2 -> aperm l2 l3 -> aperm l1 l3.

Lemma aperm_refl : forall l, aperm l l.
Proof.
  induction l as [| x t IH]; [ apply aperm_nil | ].
  apply aperm_cons; [ apply eassoc_refl | exact IH ].
Qed.

Lemma perm_aperm : forall l1 l2, Permutation l1 l2 -> aperm l1 l2.
Proof.
  intros l1 l2 H. induction H.
  - apply aperm_nil.
  - apply aperm_cons; [ apply eassoc_refl | exact IHPermutation ].
  - apply aperm_swap.
  - apply (aperm_trans _ _ _ IHPermutation1 IHPermutation2).
Qed.

(* ----------------------------------------------------------------- *)
(*  C.  products respect permutation                                   *)
(* ----------------------------------------------------------------- *)
Lemma prodl_perm : forall l1 l2, Permutation l1 l2 -> prodl l1 = prodl l2.
Proof.
  intros l1 l2 H. induction H; simpl.
  - reflexivity.
  - rewrite IHPermutation. reflexivity.
  - ring.
  - rewrite IHPermutation1, IHPermutation2. reflexivity.
Qed.

(* a product of irreducibles that is a unit must be empty *)
Lemma prodl_unit_nil : forall l, Forall eirred l -> eunit (prodl l) -> l = [].
Proof.
  intros l Hl Hu. destruct l as [| y r]; [ reflexivity | exfalso ].
  inversion Hl as [| y' r' Hy Hr]; subst.
  apply (proj1 Hy).
  apply (edvd_unit_unit y (prodl (y :: r)) Hu).
  exists (prodl r). simpl. reflexivity.
Qed.

(* ----------------------------------------------------------------- *)
(*  D.  UNIQUENESS                                                     *)
(* ----------------------------------------------------------------- *)
Lemma unique_aux : forall l1 l2 u, eunit u ->
  Forall eirred l1 -> Forall eirred l2 ->
  emul u (prodl l1) = prodl l2 -> aperm l1 l2.
Proof.
  induction l1 as [| pi t1 IH]; intros l2 u Hu Hl1 Hl2 Hprod.
  - (* the left side is a unit, so the right list is empty *)
    simpl in Hprod.
    assert (Hpu : eunit (prodl l2)).
    { rewrite <- Hprod. destruct Hu as [ui Hui]. exists ui.
      transitivity (emul u ui); [ ring | exact Hui ]. }
    rewrite (prodl_unit_nil l2 Hl2 Hpu). apply aperm_nil.
  - inversion Hl1 as [| pi' t1' Hpi Ht1]; subst.
    (* pi divides the right-hand product *)
    assert (Hdvd : edvd pi (prodl l2)).
    { exists (emul u (prodl t1)). rewrite <- Hprod. simpl. ring. }
    destruct (irred_dvd_prodl pi l2 Hpi Hdvd) as [x [Hxin [w Hw]]].
    (* x is irreducible and pi divides it, so w is a unit *)
    assert (Hxirr : eirred x) by (rewrite Forall_forall in Hl2; apply Hl2; exact Hxin).
    assert (Hwu : eunit w).
    { destruct Hxirr as [_ [_ Hx3]].
      destruct (Hx3 pi w Hw) as [Hc | Hc]; [ exfalso; exact (proj1 Hpi Hc) | exact Hc ]. }
    (* split l2 around x *)
    destruct (in_split x l2 Hxin) as [la [lb Hl2eq]].
    set (l2'' := la ++ lb).
    assert (Hperm : Permutation (x :: l2'') l2)
      by (rewrite Hl2eq; unfold l2''; apply Permutation_middle).
    assert (Hl2'' : Forall eirred l2'').
    { rewrite Hl2eq in Hl2. apply Forall_app in Hl2. destruct Hl2 as [Hla Hrest].
      inversion Hrest as [| x' lb' Hx' Hlb]; subst.
      unfold l2''. apply Forall_app. split; assumption. }
    (* cancel pi *)
    assert (Hcancel : emul pi (emul u (prodl t1)) = emul pi (emul w (prodl l2''))).
    { transitivity (emul u (prodl (pi :: t1))); [ simpl; ring | ].
      rewrite Hprod, <- (prodl_perm _ _ Hperm). simpl. rewrite Hw. ring. }
    assert (Hpi0 : pi <> ezero) by (destruct Hpi as [_ [H _]]; exact H).
    pose proof (emul_cancel pi _ _ Hpi0 Hcancel) as Heq.
    (* recurse with the leftover unit w^{-1} u *)
    pose proof Hwu as Hwu0. destruct Hwu0 as [wi Hwi].
    assert (Hwiu : eunit (emul wi u))
      by (apply eunit_mul; [ apply (eunit_inv_unit w wi Hwi) | exact Hu ]).
    assert (Hrec : emul (emul wi u) (prodl t1) = prodl l2'').
    { transitivity (emul wi (emul u (prodl t1))); [ ring | ].
      rewrite Heq.
      transitivity (emul (emul w wi) (prodl l2'')); [ ring | ].
      rewrite Hwi. ring. }
    apply (aperm_trans _ (x :: l2'') _).
    + apply aperm_cons; [ exists w; split; assumption | ].
      exact (IH l2'' (emul wi u) Hwiu Ht1 Hl2'' Hrec).
    + apply perm_aperm. exact Hperm.
Qed.

Theorem unique_factorization : forall l1 l2,
  Forall eirred l1 -> Forall eirred l2 ->
  prodl l1 = prodl l2 -> aperm l1 l2.
Proof.
  intros l1 l2 Hl1 Hl2 H.
  apply (unique_aux l1 l2 eone eunit_one Hl1 Hl2).
  rewrite <- H. ring.
Qed.

Print Assumptions unique_factorization.
