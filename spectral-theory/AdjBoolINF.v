(* ================================================================= *)
(*  AdjBoolINF.v  —  Brick 2 tie-back:  Adj bool  ~=  INFMonoid.Sym.  *)
(*                                                                    *)
(*  The zero-adjunction of (bool, xorb) -- the 2-element group Z/2 --  *)
(*  is EXACTLY the {I,N,F} monoid of INFMonoid:                        *)
(*      AElt false = I  (the identity),                               *)
(*      AElt true  = N  (the involution, N o N = I),                  *)
(*      AZero      = F  (the absorbing zero).                         *)
(*                                                                    *)
(*  phi : Adj bool -> Sym is a BIJECTION carrying  aop bool xorb  to   *)
(*  INFMonoid.op.  So at |G| = 2 (prime length p = 3) the abstract     *)
(*  Adj construction of Brick 2 recovers the original Mobius            *)
(*  value-monoid {I,N,F} -- the abstraction is not vacuous, and the     *)
(*  {I,N,F} thread is the p=3 instance of  Z[Adj G] = Z[G] |x Z*d0.    *)
(*  Axiom-free (finite case analysis).                                *)
(* ================================================================= *)

From Stdlib Require Import Bool FinFun.
Require Import HopfGroupAlgebraGen MonoidAlgebraZero INFMonoid.

(* the carrier bijection *)
Definition phi (x : Adj bool) : Sym :=
  match x with
  | AZero _ => F
  | AElt _ b => if b then N else I
  end.

Definition psi (s : Sym) : Adj bool :=
  match s with
  | I => AElt bool false
  | N => AElt bool true
  | F => AZero bool
  end.

Lemma phi_psi : forall s, phi (psi s) = s.
Proof. intros [| |]; reflexivity. Qed.

Lemma psi_phi : forall x, psi (phi x) = x.
Proof. intros [|b]; [ reflexivity | destruct b; reflexivity ]. Qed.

Lemma phi_bijective : Bijective phi.
Proof. exists psi; split; [ exact psi_phi | exact phi_psi ]. Qed.

(* phi carries the Adj-operation (over the group (bool,xorb)) to op *)
Lemma phi_hom : forall x y, phi (aop bool xorb x y) = op (phi x) (phi y).
Proof. intros [|bx] [|by']; try destruct bx; try destruct by'; reflexivity. Qed.

(* ----------------------------------------------------------------- *)
(*  MASTER THEOREM:  the p=3 non-vacuity                              *)
(* ----------------------------------------------------------------- *)

Theorem Adj_bool_iso_INF :
  Bijective phi
  /\ (forall x y, phi (aop bool xorb x y) = op (phi x) (phi y))
  /\ phi (AZero bool) = F
  /\ phi (AElt bool false) = I
  /\ phi (AElt bool true) = N.
Proof.
  split; [ exact phi_bijective | ].
  split; [ exact phi_hom | ].
  split; [ reflexivity | ].
  split; reflexivity.
Qed.

Print Assumptions Adj_bool_iso_INF.

(* ================================================================= *)
(*  END AdjBoolINF.v                                                 *)
(*  Adj bool = INFMonoid.Sym: the p=3 instance of the zero-adjunction *)
(*  monoid.  AElt false = I, AElt true = N, AZero = F; aop = op.       *)
(* ================================================================= *)
