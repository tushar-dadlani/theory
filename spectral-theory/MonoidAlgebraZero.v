(* ================================================================= *)
(*  MonoidAlgebraZero.v  —  Brick 2: the zero-adjunction monoid Adj G.  *)
(*                                                                    *)
(*  Adj G = AZero | AElt g  adjoins an absorbing zero to a commutative  *)
(*  monoid G.  It IS a commutative monoid (aop_*, discharging exactly    *)
(*  Brick 1's MonoidAlgebra hypotheses), with |Adj G| = |G| + 1 -- so    *)
(*  prime length <-> |G| = p - 1.  This is the carrier over which the    *)
(*  monoid algebra Z[Adj G] (Brick 1's MonoidAlgebra, now inv-free) is    *)
(*  formed, and the p=3 case Adj bool = {I,N,F}.  Axiom-free.            *)
(* ================================================================= *)

From Stdlib Require Import List Arith FinFun.
Import ListNotations.
Open Scope nat_scope.

Section ZeroAdjunction.

Variable G : Type.
Variable Geq : G -> G -> bool.
Hypothesis Geq_spec : forall x y, reflect (x = y) (Geq x y).
Variable gelts : list G.
Hypothesis gelts_nodup : NoDup gelts.
Hypothesis gelts_all : forall x, In x gelts.
Variable gop : G -> G -> G.
Variable geG : G.
Hypothesis gop_assoc : forall x y z, gop (gop x y) z = gop x (gop y z).
Hypothesis gop_comm : forall x y, gop x y = gop y x.
Hypothesis gop_id_l : forall x, gop geG x = x.

Inductive Adj : Type := AZero | AElt (g : G).

Definition aop (x y : Adj) : Adj :=
  match x, y with
  | AElt a, AElt b => AElt (gop a b)
  | _, _ => AZero
  end.

Definition ae : Adj := AElt geG.

Definition aAeq (x y : Adj) : bool :=
  match x, y with
  | AZero, AZero => true
  | AElt a, AElt b => Geq a b
  | _, _ => false
  end.

Definition aelts : list Adj := AZero :: map AElt gelts.

(* ---- the MonoidAlgebra hypotheses, discharged ---- *)

Lemma aAeq_spec : forall x y, reflect (x = y) (aAeq x y).
Proof.
  intros [|a] [|b]; simpl.
  - left; reflexivity.
  - right; discriminate.
  - right; discriminate.
  - destruct (Geq_spec a b) as [-> | Hne].
    + left; reflexivity.
    + right; intro H; apply Hne; injection H; auto.
Qed.

Lemma aelts_nodup : NoDup aelts.
Proof.
  unfold aelts; constructor.
  - rewrite in_map_iff; intros [g [H _]]; discriminate.
  - apply Injective_map_NoDup; [ intros x y H; injection H; auto | exact gelts_nodup ].
Qed.

Lemma aelts_all : forall x, In x aelts.
Proof.
  intros [|g]; unfold aelts.
  - left; reflexivity.
  - right; apply in_map, gelts_all.
Qed.

Lemma aop_assoc : forall x y z, aop (aop x y) z = aop x (aop y z).
Proof. intros [|a] [|b] [|c]; simpl; try reflexivity; rewrite gop_assoc; reflexivity. Qed.

Lemma aop_comm : forall x y, aop x y = aop y x.
Proof. intros [|a] [|b]; simpl; try reflexivity; rewrite gop_comm; reflexivity. Qed.

Lemma aop_id_l : forall x, aop ae x = x.
Proof. intros [|a]; unfold ae; simpl; try reflexivity; rewrite gop_id_l; reflexivity. Qed.

(* ---- prime-length count:  |Adj G| = |G| + 1 ---- *)
Lemma adj_card : length aelts = S (length gelts).
Proof. unfold aelts; simpl; rewrite length_map; reflexivity. Qed.

(* ---- the honest negative:  Adj G is NOT a group ----
   AZero has no inverse (aop _ AZero = AZero <> ae), so Brick 1's GroupPart --
   inv, ginv, the inversion antipode -- cannot be instantiated on Adj G.  This
   is the structural reason a monoid algebra with an absorbing zero is a
   bialgebra but never Hopf, i.e. why the {I,N,F} thread never produced one. *)
Lemma adj_no_inverse : ~ exists inv : Adj -> Adj, forall x, aop (inv x) x = ae.
Proof.
  intros [inv H]; specialize (H AZero); unfold ae in H.
  destruct (inv AZero); simpl in H; discriminate.
Qed.

End ZeroAdjunction.

Print Assumptions aop_assoc.
Print Assumptions adj_card.

(* ================================================================= *)
(*  END MonoidAlgebraZero.v (Brick 2 core: Adj G is a comm. monoid).   *)
(* ================================================================= *)
