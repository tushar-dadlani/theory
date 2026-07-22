(* ================================================================= *)
(*  INFMonoid.v                                                      *)
(*                                                                    *)
(*  THE 3-SYMBOL ALGEBRA {I, N, F} AS THE MOBIUS / SIGN VALUE MONOID. *)
(*                                                                    *)
(*  The Cayley table                                                  *)
(*      o | I  N  F                                                   *)
(*      --+---------                                                  *)
(*      I | I  N  F                                                   *)
(*      N | N  I  F                                                   *)
(*      F | F  F  F                                                   *)
(*  defines a commutative monoid: I is the identity, N an involution   *)
(*  (N o N = I, so the units {I,N} form Z/2), and F an absorbing zero. *)
(*                                                                    *)
(*  This file proves the two identifications that POSITION it against   *)
(*  the recent Euler-product / Mobius / Walsh work:                    *)
(*                                                                    *)
(*    (1) val : Sym -> Z  (I |-> 1, N |-> -1, F |-> 0) is a monoid      *)
(*        HOMOMORPHISM (val_hom: the table is integer multiplication    *)
(*        of signs) and INJECTIVE (val_inj), so                        *)
(*            ({I,N,F}, o)  ~=  ({+1,-1,0}, x)  =  (F_3, x).           *)
(*        Its unit group {I,N} is the Walsh sign group Z/2 (val on      *)
(*        units mirrors WalshHadamard.signb_xorb).                     *)
(*                                                                    *)
(*    (2) sym_of : nat -> Sym  (0 |-> I, 1 |-> N, >=2 |-> F) satisfies   *)
(*        val (sym_of k) = mu_pp k  (sym_of_mu), i.e. {I,N,F} is        *)
(*        EXACTLY the value-monoid of the Mobius function on prime      *)
(*        powers (MobiusReciprocal.mu_pp): I = mu(p^0), N = mu(p^1),    *)
(*        F = mu(p^{>=2}), and F's absorption is the squarefree         *)
(*        collapse.  So this algebra is the alphabet of the reciprocal   *)
(*        Euler factor (1-x) = sum_k mu(p^k) x^k and of all Mobius       *)
(*        inversion downstream.                                        *)
(*                                                                    *)
(*  Axiom-free (finite case analysis + Z).                            *)
(* ================================================================= *)

Require Import MobiusReciprocal.
From Stdlib Require Import ZArith.
Open Scope Z_scope.

(* the three symbols and the table operation *)
Inductive Sym : Type := I | N | F.

Definition op (a b : Sym) : Sym :=
  match a, b with
  | I, I => I | I, N => N | I, F => F
  | N, I => N | N, N => I | N, F => F
  | F, I => F | F, N => F | F, F => F
  end.

(* ----------------------------------------------------------------- *)
(*  1.  COMMUTATIVE MONOID LAWS (I identity, N involution, F zero)    *)
(* ----------------------------------------------------------------- *)

Lemma op_id_l   : forall a, op I a = a.            Proof. destruct a; reflexivity. Qed.
Lemma op_id_r   : forall a, op a I = a.            Proof. destruct a; reflexivity. Qed.
Lemma op_comm   : forall a b, op a b = op b a.     Proof. destruct a, b; reflexivity. Qed.
Lemma op_assoc  : forall a b c, op (op a b) c = op a (op b c).
                                                   Proof. destruct a, b, c; reflexivity. Qed.
Lemma N_involution : op N N = I.                   Proof. reflexivity. Qed.
Lemma F_absorb_l   : forall a, op F a = F.         Proof. destruct a; reflexivity. Qed.
Lemma F_absorb_r   : forall a, op a F = F.         Proof. destruct a; reflexivity. Qed.

(* units: exactly I and N; F is the non-invertible zero *)
Definition is_unit (a : Sym) : Prop := exists b, op a b = I.
Lemma I_unit : is_unit I.        Proof. exists I; reflexivity. Qed.
Lemma N_unit : is_unit N.        Proof. exists N; reflexivity. Qed.
Lemma F_not_unit : ~ is_unit F.  Proof. intros [b Hb]; destruct b; discriminate. Qed.

(* ----------------------------------------------------------------- *)
(*  2.  THE SIGN EMBEDDING:  ~= ({+1,-1,0}, x)                        *)
(* ----------------------------------------------------------------- *)

Definition val (a : Sym) : Z := match a with I => 1 | N => -1 | F => 0 end.

Lemma val_hom : forall a b, val (op a b) = val a * val b.
Proof. destruct a, b; reflexivity. Qed.

Lemma val_inj : forall a b, val a = val b -> a = b.
Proof. intros a b H; destruct a, b; simpl in H; first [ reflexivity | discriminate ]. Qed.

Lemma val_image : forall a, val a = 1 \/ val a = -1 \/ val a = 0.
Proof. destruct a; simpl; auto. Qed.

(* ----------------------------------------------------------------- *)
(*  3.  THE MOBIUS BRIDGE:  {I,N,F} = value-monoid of mu on p^k       *)
(* ----------------------------------------------------------------- *)

Definition sym_of (k : nat) : Sym :=
  match k with O => I | S O => N | S (S _) => F end.

Lemma sym_of_mu : forall k, val (sym_of k) = mu_pp k.
Proof. intros [|[|k]]; reflexivity. Qed.

(* ----------------------------------------------------------------- *)
(*  MASTER THEOREM                                                   *)
(* ----------------------------------------------------------------- *)

Theorem INF_is_mobius_value_monoid :
  (* a commutative monoid: I identity, N involution, F absorbing zero *)
  (forall a, op I a = a) /\ (forall a, op a I = a)
  /\ (forall a b, op a b = op b a)
  /\ (forall a b c, op (op a b) c = op a (op b c))
  /\ op N N = I /\ (forall a, op F a = F)
  (* val is an injective monoid hom -> iso onto ({+1,-1,0}, x) *)
  /\ (forall a b, val (op a b) = val a * val b)
  /\ (forall a b, val a = val b -> a = b)
  (* and {I,N,F} is exactly the value-monoid of mu on prime powers *)
  /\ (forall k, val (sym_of k) = mu_pp k).
Proof.
  split; [ exact op_id_l | ].
  split; [ exact op_id_r | ].
  split; [ exact op_comm | ].
  split; [ exact op_assoc | ].
  split; [ exact N_involution | ].
  split; [ exact F_absorb_l | ].
  split; [ exact val_hom | ].
  split; [ exact val_inj | exact sym_of_mu ].
Qed.

Print Assumptions INF_is_mobius_value_monoid.

(* ================================================================= *)
(*  END INFMonoid.v                                                  *)
(*  The 3-symbol algebra {I,N,F} is the commutative monoid            *)
(*  ({+1,-1,0}, x) = (F_3, x) -- unit group Z/2 = {I,N} (the Walsh     *)
(*  sign group), absorbing zero F -- and it is the value-monoid of      *)
(*  the Mobius function on prime powers (mu_pp), the alphabet of the    *)
(*  reciprocal Euler factor and of Mobius inversion.  Axiom-free.       *)
(* ================================================================= *)
