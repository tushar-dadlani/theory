(* ================================================================= *)
(*  INFProduct.v                                                     *)
(*                                                                    *)
(*  MANY OBSERVERS: the n-fold product of the 3-symbol algebra         *)
(*  {I,N,F}, built by induction over a LIST of observers.             *)
(*                                                                    *)
(*  Each observer carries a state in Sym = {I,N,F} (INFMonoid).  A     *)
(*  configuration of n observers is a list of length n; two           *)
(*  configurations "observe each other" by the componentwise product   *)
(*  op_n.  This is the n-fold commutative monoid ({I,N,F})^n, and the   *)
(*  extension is genuinely inductive (append one observer at a time):   *)
(*  identity = repeat I n, and op_n is commutative/associative.        *)
(*                                                                    *)
(*  The sign of a whole configuration is the PRODUCT of the per-        *)
(*  observer signs, val_n l = prod_i val(l_i) in {+1,-1,0}:            *)
(*    - val_n_op : val_n (op_n a b) = val_n a * val_n b   (observers    *)
(*        combine multiplicatively -- the n-fold homomorphism);        *)
(*    - val_n_app : val_n (a ++ b) = val_n a * val_n b   (THE ARBITRARY *)
(*        SPLIT: partition the observer list any way into observers-vs- *)
(*        observed and the total sign factors -- multiplicativity /     *)
(*        coprime-split freedom, no length condition);                 *)
(*    - val_n_zero_iff : val_n l = 0  <->  In F l   (the VETO: a single *)
(*        F-observer collapses the whole configuration -- the absorbing *)
(*        zero, one dimension up = the squarefree obstruction);        *)
(*    - val_n_mu : val_n (map sym_of ks) = prod_i mu_pp(k_i), i.e. n     *)
(*        prime-observers whose product-sign is exactly the Mobius       *)
(*        value mu(prod p_i^{k_i}) (multiplicativity, INFMonoid).       *)
(*                                                                    *)
(*  Axiom-free (induction over lists + Z).                            *)
(* ================================================================= *)

Require Import INFMonoid MobiusReciprocal.
From Stdlib Require Import List ZArith Lia.
Import ListNotations.
Open Scope Z_scope.

(* ----------------------------------------------------------------- *)
(*  1.  THE n-FOLD MONOID:  componentwise product of observers        *)
(* ----------------------------------------------------------------- *)

Fixpoint op_n (a b : list Sym) : list Sym :=
  match a, b with
  | x :: a', y :: b' => op x y :: op_n a' b'
  | _, _ => nil
  end.

Lemma op_n_comm : forall a b, op_n a b = op_n b a.
Proof.
  induction a as [|x a IH]; intros [|y b]; simpl; try reflexivity.
  rewrite op_comm, IH; reflexivity.
Qed.

Lemma op_n_assoc : forall a b c, op_n (op_n a b) c = op_n a (op_n b c).
Proof.
  induction a as [|x a IH]; intros [|y b] [|z c]; simpl; try reflexivity.
  rewrite op_assoc, IH; reflexivity.
Qed.

(* identity of the n-fold monoid is the all-I configuration *)
Lemma op_n_id_l : forall a, op_n (repeat I (length a)) a = a.
Proof.
  induction a as [|x a IH]; [ reflexivity | ].
  cbn [length repeat op_n]; rewrite op_id_l, IH; reflexivity.
Qed.

(* ----------------------------------------------------------------- *)
(*  2.  THE PRODUCT SIGN AND ITS HOMOMORPHISM PROPERTIES              *)
(* ----------------------------------------------------------------- *)

Definition val_n (l : list Sym) : Z := fold_right Z.mul 1 (map val l).

Lemma val_n_cons : forall x l, val_n (x :: l) = val x * val_n l.
Proof. intros x l; unfold val_n; reflexivity. Qed.

(* observers combine multiplicatively (the n-fold homomorphism) *)
Lemma val_n_op : forall a b, length a = length b -> val_n (op_n a b) = val_n a * val_n b.
Proof.
  induction a as [|x a IH]; intros [|y b] Hlen; simpl in Hlen; try discriminate.
  - reflexivity.
  - cbn [op_n]; rewrite !val_n_cons, val_hom, (IH b) by lia; ring.
Qed.

(* THE ARBITRARY SPLIT: the total sign factors over ANY partition of    *)
(* the observer list -- observers vs observed is a free choice.         *)
Lemma val_n_app : forall a b, val_n (a ++ b) = val_n a * val_n b.
Proof.
  induction a as [|x a IH]; intro b; [ unfold val_n; cbn [map fold_right app]; ring | ].
  change ((x :: a) ++ b) with (x :: (a ++ b)); rewrite !val_n_cons, IH; ring.
Qed.

(* ----------------------------------------------------------------- *)
(*  3.  THE VETO: one F-observer collapses everything                 *)
(* ----------------------------------------------------------------- *)

Lemma val_zero_iff : forall x, val x = 0 <-> x = F.
Proof. destruct x; simpl; split; (reflexivity || discriminate). Qed.

Lemma val_n_zero_iff : forall l, val_n l = 0 <-> In F l.
Proof.
  induction l as [|x l IH]; [ unfold val_n; simpl; split; [ discriminate | intros [] ] | ].
  rewrite val_n_cons; simpl In; rewrite Z.mul_eq_0, val_zero_iff, IH; reflexivity.
Qed.

(* ----------------------------------------------------------------- *)
(*  4.  THE MOBIUS BRIDGE FOR n PRIME-OBSERVERS                       *)
(* ----------------------------------------------------------------- *)

(* n prime-observers with exponents ks give the product of their        *)
(* Mobius signs = mu(prod p_i^{k_i}) (multiplicativity, INFMonoid).      *)
Lemma val_n_mu : forall ks,
  val_n (map sym_of ks) = fold_right Z.mul 1 (map mu_pp ks).
Proof.
  intro ks; unfold val_n; rewrite map_map.
  f_equal; apply map_ext; intro k; apply sym_of_mu.
Qed.

(* ----------------------------------------------------------------- *)
(*  MASTER THEOREM                                                   *)
(* ----------------------------------------------------------------- *)

Theorem INF_many_observers :
  (* the n-fold structure is a commutative monoid (identity repeat I) *)
  (forall a b, op_n a b = op_n b a)
  /\ (forall a b c, op_n (op_n a b) c = op_n a (op_n b c))
  /\ (forall a, op_n (repeat I (length a)) a = a)
  (* observers combine multiplicatively; the total sign factors over *)
  (* ANY partition (arbitrary observer/observed ratio) *)
  /\ (forall a b, length a = length b -> val_n (op_n a b) = val_n a * val_n b)
  /\ (forall a b, val_n (a ++ b) = val_n a * val_n b)
  (* one F-observer vetoes the whole configuration to 0 *)
  /\ (forall l, val_n l = 0 <-> In F l)
  (* n prime-observers -> the Mobius value of their product *)
  /\ (forall ks, val_n (map sym_of ks) = fold_right Z.mul 1 (map mu_pp ks)).
Proof.
  split; [ exact op_n_comm | ].
  split; [ exact op_n_assoc | ].
  split; [ exact op_n_id_l | ].
  split; [ exact val_n_op | ].
  split; [ exact val_n_app | ].
  split; [ exact val_n_zero_iff | exact val_n_mu ].
Qed.

Print Assumptions INF_many_observers.

(* ================================================================= *)
(*  END INFProduct.v                                                 *)
(*  The 3-symbol algebra inducted to n observers: the n-fold monoid    *)
(*  ({I,N,F})^n with product-sign val_n, whose homomorphism factors     *)
(*  over any observer/observed split (val_n_app), whose single-F veto   *)
(*  is the absorbing zero one dimension up, and which realises the       *)
(*  Mobius value of a product of n prime-powers.  Axiom-free.          *)
(* ================================================================= *)
