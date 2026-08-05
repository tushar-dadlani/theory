(* ================================================================= *)
(*  AdjProduct.v  —  Brick 2, item 5:  Adj does NOT commute with       *)
(*  products.  Adj G x Adj H is not (iso to) any Adj K.                *)
(*                                                                    *)
(*  Structural reason:  in Adj K with K a group, the absorbing zero    *)
(*  AZero is the UNIQUE non-unit -- every AElt k is invertible          *)
(*  (witness AElt (invK k)).  But the product monoid Adj G x Adj H      *)
(*  has TWO distinct non-units, (AZero,AZero) and (AZero, AElt h):      *)
(*  neither is invertible (the first coordinate AZero can never reach   *)
(*  the identity AElt eG).  A monoid iso would carry non-units to        *)
(*  non-units bijectively, forcing the two distinct product non-units    *)
(*  onto the single AZero K -- impossible.                              *)
(*                                                                    *)
(*  Hence the zero-adjunction functor does not commute with products;   *)
(*  primorial (composite) moduli need the TENSOR product of Brick 5,    *)
(*  not another Adj.  Axiom-free.                                       *)
(* ================================================================= *)

Require Import HopfGroupAlgebraGen MonoidAlgebraZero.

Section AdjProduct.

(* two nonempty carriers (values of gopG/gopH are irrelevant here) *)
Variable G : Type.  Variable gopG : G -> G -> G.  Variable eG : G.
Variable H : Type.  Variable gopH : H -> H -> H.  Variable eH : H.
Variable h : H.

(* the target: a GROUP K (identity eK, inverses invK) *)
Variable K : Type.  Variable gopK : K -> K -> K.  Variable eK : K.
Variable invK : K -> K.
Hypothesis gopK_inv_r : forall k, gopK k (invK k) = eK.

(* the product monoid operation and identity *)
Definition pop (p q : Adj G * Adj H) : Adj G * Adj H :=
  (aop G gopG (fst p) (fst q), aop H gopH (snd p) (snd q)).
Definition pe : Adj G * Adj H := (AElt G eG, AElt H eH).

(* ---- Adj K has a UNIQUE non-unit:  every AElt k is invertible ---- *)

Lemma aopK_unit : forall k,
  aop K gopK (AElt K k) (AElt K (invK k)) = AElt K eK.
Proof. intros k; cbn [aop]; rewrite gopK_inv_r; reflexivity. Qed.

Lemma adjK_nonunit_is_zero : forall z : Adj K,
  ~ (exists w, aop K gopK z w = AElt K eK) -> z = AZero K.
Proof.
  intros [|k] Hnu.
  - reflexivity.
  - exfalso; apply Hnu; exists (AElt K (invK k)); apply aopK_unit.
Qed.

(* ---- the product has TWO distinct non-units ---- *)

Lemma prod_zz_nonunit : ~ exists w, pop (AZero G, AZero H) w = pe.
Proof.
  intros [[w1 w2] Hw].
  apply (f_equal (@fst (Adj G) (Adj H))) in Hw.
  unfold pop, pe in Hw; cbn in Hw; discriminate Hw.
Qed.

Lemma prod_zh_nonunit : ~ exists w, pop (AZero G, AElt H h) w = pe.
Proof.
  intros [[w1 w2] Hw].
  apply (f_equal (@fst (Adj G) (Adj H))) in Hw.
  unfold pop, pe in Hw; cbn in Hw; discriminate Hw.
Qed.

(* ----------------------------------------------------------------- *)
(*  THE OBSTRUCTION.  No monoid iso  Adj G x Adj H  ~=  Adj K.        *)
(*  The hypotheses on (f,g) are implied by ANY monoid isomorphism      *)
(*  (g a homomorphism, g o f = id, g preserves the identity), so       *)
(*  deriving False rules out every such iso.                          *)
(* ----------------------------------------------------------------- *)

Theorem adj_not_closed_under_product :
  forall (f : Adj G * Adj H -> Adj K) (g : Adj K -> Adj G * Adj H),
    (forall x, g (f x) = x) ->
    (forall a b, g (aop K gopK a b) = pop (g a) (g b)) ->
    g (AElt K eK) = pe ->
    False.
Proof.
  intros f g gf ghom g_ae.
  (* both product-zeros are non-units in Adj K, hence collapse to AZero K *)
  assert (Hzh : f (AZero G, AElt H h) = AZero K).
  { apply adjK_nonunit_is_zero; intros [u Hu].
    apply prod_zh_nonunit; exists (g u).
    rewrite <- (gf (AZero G, AElt H h)), <- ghom, Hu; exact g_ae. }
  assert (Hzz : f (AZero G, AZero H) = AZero K).
  { apply adjK_nonunit_is_zero; intros [u Hu].
    apply prod_zz_nonunit; exists (g u).
    rewrite <- (gf (AZero G, AZero H)), <- ghom, Hu; exact g_ae. }
  (* injectivity then forces (AZero,AElt h) = (AZero,AZero) -- absurd *)
  assert (Heq : f (AZero G, AElt H h) = f (AZero G, AZero H))
    by (rewrite Hzh, Hzz; reflexivity).
  apply (f_equal g) in Heq; rewrite !gf in Heq.
  injection Heq as Hbad; discriminate Hbad.
Qed.

End AdjProduct.

Print Assumptions adj_not_closed_under_product.

(* ================================================================= *)
(*  END AdjProduct.v  (Brick 2 complete: Adj is a bialgebra functor    *)
(*  with a splitting Z[Adj G]=Z[G]|xZd0, never Hopf, and NOT           *)
(*  product-preserving -- so many primes need Brick 5's tensor.)       *)
(* ================================================================= *)
