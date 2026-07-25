(* ================================================================= *)
(*  HopfGrouplike.v                                                   *)
(*                                                                    *)
(*  THE MULTIPLICATIVE BIALGEBRA on ℤ[X]  (coordinate ring of the     *)
(*  multiplicative monoid 𝔸¹, ×), and GROUP-LIKE ELEMENTS.           *)
(*                                                                    *)
(*  Dual to HopfPoly: same underlying ℤ[X], same concrete tensor      *)
(*  model (list poly with the faithful bivariate `beval`), but now     *)
(*     coproduct   Δ×(p) = p(X·Y)        (Δ× : H → H⊗H)              *)
(*     counit      ε(p)  = p(1)                                       *)
(*  makes X a GROUP-LIKE element (Δ× X = X⊗X, ε X = 1) — contrast      *)
(*  HopfPoly, where the additive coproduct p(X+Y) makes X PRIMITIVE.  *)
(*                                                                    *)
(*  This is the group-algebra / group-like side of the duality:       *)
(*  group-like elements form the group (the multiplicative monoid of  *)
(*  monomials Xᵏ) sitting inside the bialgebra, exactly as primitive  *)
(*  elements form its (abelian) Lie algebra.                          *)
(*                                                                    *)
(*  (Over ℤ[X] this is a bialgebra, not a full Hopf algebra: the      *)
(*  antipode would need X⁻¹.  Passing to ℤ[X]/(Xⁿ−1) = k[ℤ/nℤ], the   *)
(*  finite group algebra, restores the antipode S(X)=Xⁿ⁻¹ — the next  *)
(*  brick.)  AXIOM-FREE.                                              *)
(* ================================================================= *)

From Stdlib Require Import ZArith Lia List.
Import ListNotations.
Require Import IntPoly HopfPoly.
Open Scope Z_scope.

(* ================================================================= *)
(*  The multiplicative coproduct  Δ×(p) = p(X·Y)                      *)
(*  (Δ×(c :: p') = c⊗1 + (X⊗Y)·Δ×(p'), reusing HopfPoly's tensors.)   *)
(* ================================================================= *)
Fixpoint Deltam (p : poly) : tensor :=
  match p with
  | [] => []
  | c :: p' => badd (bconst c) (bshiftX (bshiftY (Deltam p')))
  end.

(* THE MASTER LEMMA: the multiplicative coproduct evaluates to p(x·y). *)
Theorem beval_Deltam : forall p x y, beval (Deltam p) x y = eval p (x * y).
Proof.
  induction p as [|c p' IH]; intros x y.
  - unfold beval; simpl; ring.
  - cbn [Deltam].
    rewrite beval_badd, beval_bconst, beval_bshiftX, beval_bshiftY, IH.
    simpl; ring.
Qed.

(* ================================================================= *)
(*  Bialgebra: Δ× is an algebra morphism                             *)
(* ================================================================= *)
Theorem Deltam_mult : forall p q x y,
  beval (Deltam (pmul p q)) x y = beval (Deltam p) x y * beval (Deltam q) x y.
Proof. intros; rewrite !beval_Deltam, eval_mul; reflexivity. Qed.

Theorem Deltam_unit : forall x y, beval (Deltam (pconst 1)) x y = 1.
Proof. intros; rewrite beval_Deltam, eval_const; reflexivity. Qed.

(* ================================================================= *)
(*  Coassociativity  and  cocommutativity                            *)
(*  (both instances of associativity / commutativity of ·)           *)
(* ================================================================= *)
Theorem coassocm : forall p x y z,
  beval (Deltam p) (x * y) z = beval (Deltam p) x (y * z).
Proof. intros; rewrite !beval_Deltam; f_equal; ring. Qed.

Theorem Deltam_cocomm : forall p x y,
  beval (Deltam p) x y = beval (Deltam p) y x.
Proof. intros; rewrite !beval_Deltam; f_equal; ring. Qed.

(* ================================================================= *)
(*  Counit  ε(p) = p(1):   (ε⊗id)∘Δ× = id = (id⊗ε)∘Δ×                *)
(* ================================================================= *)
Theorem counitm_left : forall p y, beval (Deltam p) 1 y = eval p y.
Proof. intros; rewrite beval_Deltam; f_equal; ring. Qed.

Theorem counitm_right : forall p x, beval (Deltam p) x 1 = eval p x.
Proof. intros; rewrite beval_Deltam; f_equal; ring. Qed.

(* ================================================================= *)
(*  GROUP-LIKE ELEMENTS:  Δ×(a) = a⊗a  and  ε(a) = 1.                 *)
(*  They form the group inside the algebra (dual to primitives).      *)
(* ================================================================= *)
Definition grouplike (a : poly) : Prop :=
  (forall x y, beval (Deltam a) x y = eval a x * eval a y) /\ eval a 1 = 1.

(* Every monomial Xᵏ is group-like — these ARE the group elements. *)
Theorem grouplike_monom : forall k, grouplike (pmonom k).
Proof.
  intro k; split.
  - intros x y; rewrite beval_Deltam, !eval_monom, Z.pow_mul_l; reflexivity.
  - rewrite eval_monom, Z.pow_1_l by lia; reflexivity.
Qed.

(* In particular X = X¹ is group-like:  Δ×(X) = X⊗X.  (Contrast:      *)
(* under HopfPoly's additive coproduct, X is PRIMITIVE, X⊗1+1⊗X.)     *)
Corollary X_grouplike : grouplike (pmonom 1).
Proof. apply grouplike_monom. Qed.

(* Group-likes are closed under the product: the group structure.     *)
Theorem grouplike_mul : forall a b,
  grouplike a -> grouplike b -> grouplike (pmul a b).
Proof.
  intros a b [Ha Ha1] [Hb Hb1]; split.
  - intros x y; rewrite beval_Deltam, eval_mul.
    rewrite <- (beval_Deltam a), <- (beval_Deltam b), Ha, Hb, !eval_mul; ring.
  - rewrite eval_mul, Ha1, Hb1; ring.
Qed.

(* The unit 1 is group-like: the identity of the group. *)
Theorem grouplike_one : grouplike (pconst 1).
Proof.
  split.
  - intros x y; rewrite beval_Deltam, !eval_const; ring.
  - rewrite eval_const; reflexivity.
Qed.

Print Assumptions beval_Deltam.
Print Assumptions grouplike_mul.
Print Assumptions X_grouplike.

(* ================================================================= *)
(*  END HopfGrouplike.v                                               *)
(*  ℤ[X] as the multiplicative bialgebra: Δ×(p)=p(X·Y) is a           *)
(*  coassociative, cocommutative algebra morphism with counit p↦p(1); *)
(*  X and all monomials are group-like, closed under product — the    *)
(*  group inside the algebra, dual to HopfPoly's primitives.          *)
(*  Closed under the global context (axiom-free).                     *)
(* ================================================================= *)
