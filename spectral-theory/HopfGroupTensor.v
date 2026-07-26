(* ================================================================= *)
(*  HopfGroupTensor.v                                                *)
(*                                                                    *)
(*  MONOIDALITY of the group algebra:  k[G × H] ≅ k[G] ⊗ k[H].        *)
(*                                                                    *)
(*  The isomorphism is currying:  f : A×B → ℤ  ↔  F : A → B → ℤ.       *)
(*  Its content is that currying is an ALGEBRA morphism — it carries  *)
(*  the product-group convolution on k[G×H] to the tensor-product     *)
(*  convolution on k[G]⊗k[H]:                                        *)
(*                                                                    *)
(*     gconvGH f f' (g,h) = tconv (curry f) (curry f') g h           *)
(*                                                                    *)
(*  and the unit factors (gunitGH (g,h) = gunitA g · gunitB h), and   *)
(*  the tensor convolution really is the tensor product of the two    *)
(*  convolutions (it factors on elementary tensors u⊗v).              *)
(*                                                                    *)
(*  Purely combinatorial: needs only `Σ over list_prod = nested Σ`,   *)
(*  an indicator factorisation, and one Fubini swap — no group        *)
(*  axioms.  Closed under the global context (axiom-free).            *)
(* ================================================================= *)

From Stdlib Require Import ZArith List.
Import ListNotations.
Open Scope Z_scope.

(* ================================================================= *)
(*  Polymorphic finite-sum toolkit                                   *)
(* ================================================================= *)
Definition sumf {T} (l : list T) (f : T -> Z) : Z :=
  fold_right (fun k acc => f k + acc) 0%Z l.

Lemma sumf_ext {T} : forall (l : list T) f g,
  (forall k, In k l -> f k = g k) -> sumf l f = sumf l g.
Proof.
  induction l as [|a l IH]; intros f g H; simpl; [ reflexivity | ].
  rewrite (H a (or_introl eq_refl)), (IH f g); [ reflexivity | ].
  intros k Hk; apply H; right; exact Hk.
Qed.

Lemma sumf_zero {T} : forall (l : list T), sumf l (fun _ => 0%Z) = 0%Z.
Proof. induction l as [|a l IH]; simpl; [ reflexivity | rewrite IH; ring ]. Qed.

Lemma sumf_add {T} : forall (l : list T) f g,
  sumf l (fun k => f k + g k) = sumf l f + sumf l g.
Proof. induction l as [|a l IH]; intros f g; simpl; [ ring | rewrite IH; ring ]. Qed.

Lemma sumf_scal {T} : forall (l : list T) c f, sumf l (fun k => c * f k) = c * sumf l f.
Proof. induction l as [|a l IH]; intros c f; simpl; [ ring | rewrite IH; ring ]. Qed.

Lemma sumf_mul_const_r {T} : forall (l : list T) f c, sumf l (fun i => f i * c) = sumf l f * c.
Proof.
  intros l f c; rewrite (sumf_ext l (fun i => f i * c) (fun i => c * f i)) by (intros; ring).
  rewrite sumf_scal; ring.
Qed.

Lemma sumf_swap {T U} : forall (l1 : list T) (l2 : list U) F,
  sumf l1 (fun i => sumf l2 (fun j => F i j))
  = sumf l2 (fun j => sumf l1 (fun i => F i j)).
Proof.
  induction l1 as [|a l1 IH]; intros l2 F; simpl.
  - symmetry; apply sumf_zero.
  - rewrite IH, <- sumf_add; reflexivity.
Qed.

Lemma sumf_app {T} : forall (l1 l2 : list T) f, sumf (l1 ++ l2) f = sumf l1 f + sumf l2 f.
Proof. induction l1 as [|a l1 IH]; intros l2 f; simpl; [ ring | rewrite IH; ring ]. Qed.

Lemma sumf_map {T U} : forall (l : list T) (g : T -> U) f,
  sumf (map g l) f = sumf l (fun x => f (g x)).
Proof. induction l as [|a l IH]; intros g f; simpl; [ reflexivity | rewrite IH; reflexivity ]. Qed.

Lemma sumf_list_prod {T U} : forall (lT : list T) (lU : list U) F,
  sumf (list_prod lT lU) F = sumf lT (fun a => sumf lU (fun b => F (a, b))).
Proof.
  induction lT as [|a lT IH]; intros lU F; simpl; [ reflexivity | ].
  rewrite sumf_app, sumf_map, IH; reflexivity.
Qed.

Section Tensor.

(* two finite abelian groups, given by their data (no axioms needed) *)
Context {A B : Type}.
Variable AeqA : A -> A -> bool.
Variable BeqB : B -> B -> bool.
Variable eltsA : list A.
Variable eltsB : list B.
Variable opA : A -> A -> A.
Variable opB : B -> B -> B.
Variable eA : A.
Variable eB : B.

(* convolutions on the two group algebras k[G], k[H] *)
Definition convA (a a' : A -> Z) (g : A) : Z :=
  sumf eltsA (fun x => sumf eltsA (fun y => if AeqA (opA x y) g then a x * a' y else 0)).
Definition convB (b b' : B -> Z) (h : B) : Z :=
  sumf eltsB (fun x => sumf eltsB (fun y => if BeqB (opB x y) h then b x * b' y else 0)).

(* the product group G × H, and its group algebra k[G×H] *)
Definition ABeq (p q : A * B) : bool := AeqA (fst p) (fst q) && BeqB (snd p) (snd q).
Definition opAB (p q : A * B) : A * B := (opA (fst p) (fst q), opB (snd p) (snd q)).
Definition eltsAB : list (A * B) := list_prod eltsA eltsB.
Definition gconvGH (f f' : A * B -> Z) (r : A * B) : Z :=
  sumf eltsAB (fun p => sumf eltsAB (fun q => if ABeq (opAB p q) r then f p * f' q else 0)).

(* the tensor-product convolution on k[G] ⊗ k[H] = (A -> B -> Z) *)
Definition tconv (F F' : A -> B -> Z) (g : A) (h : B) : Z :=
  sumf eltsA (fun g1 => sumf eltsA (fun g2 => sumf eltsB (fun h1 => sumf eltsB (fun h2 =>
    if AeqA (opA g1 g2) g then (if BeqB (opB h1 h2) h then F g1 h1 * F' g2 h2 else 0) else 0)))).

Definition gunitA : A -> Z := fun g => if AeqA eA g then 1 else 0.
Definition gunitB : B -> Z := fun h => if BeqB eB h then 1 else 0.
Definition gunitGH : A * B -> Z := fun r => if ABeq (eA, eB) r then 1 else 0.

(* ================================================================= *)
(*  THE COMPATIBILITY:  currying carries ⋆_{G×H} to the tensor ⋆.     *)
(* ================================================================= *)
Theorem gconv_prod_tensor : forall f f' g h,
  gconvGH f f' (g, h) = tconv (fun a b => f (a, b)) (fun a b => f' (a, b)) g h.
Proof.
  intros f f' g h; unfold gconvGH, eltsAB.
  rewrite sumf_list_prod.
  transitivity (sumf eltsA (fun p1 => sumf eltsB (fun p2 =>
    sumf eltsA (fun q1 => sumf eltsB (fun q2 =>
      if AeqA (opA p1 q1) g then (if BeqB (opB p2 q2) h then f (p1, p2) * f' (q1, q2) else 0) else 0))))).
  { apply sumf_ext; intros p1 _; apply sumf_ext; intros p2 _.
    rewrite sumf_list_prod.
    apply sumf_ext; intros q1 _; apply sumf_ext; intros q2 _.
    unfold ABeq, opAB; simpl.
    destruct (AeqA (opA p1 q1) g); destruct (BeqB (opB p2 q2) h); reflexivity. }
  unfold tconv.
  apply sumf_ext; intros p1 _.
  rewrite sumf_swap; reflexivity.
Qed.

(* the unit factors as a pure tensor  e_{G×H} = e_G ⊗ e_H *)
Theorem gunit_prod_tensor : forall g h, gunitGH (g, h) = gunitA g * gunitB h.
Proof.
  intros g h; unfold gunitGH, gunitA, gunitB, ABeq; simpl.
  destruct (AeqA eA g); destruct (BeqB eB h); reflexivity.
Qed.

(* tconv really is the tensor product of the two convolutions:        *)
(* on elementary tensors, (u⊗v) ⋆ (u'⊗v') = (u ⋆_A u') ⊗ (v ⋆_B v').  *)
Theorem tconv_elementary : forall u u' v v' g h,
  tconv (fun a b => u a * v b) (fun a b => u' a * v' b) g h
  = convA u u' g * convB v v' h.
Proof.
  intros u u' v v' g h; unfold tconv, convA, convB.
  transitivity (sumf eltsA (fun g1 => sumf eltsA (fun g2 =>
      (if AeqA (opA g1 g2) g then u g1 * u' g2 else 0)
      * sumf eltsB (fun h1 => sumf eltsB (fun h2 =>
          if BeqB (opB h1 h2) h then v h1 * v' h2 else 0))))).
  { apply sumf_ext; intros g1 _; apply sumf_ext; intros g2 _.
    rewrite <- sumf_scal; apply sumf_ext; intros h1 _.
    rewrite <- sumf_scal; apply sumf_ext; intros h2 _.
    destruct (AeqA (opA g1 g2) g); destruct (BeqB (opB h1 h2) h); ring. }
  rewrite <- sumf_mul_const_r; apply sumf_ext; intros g1 _.
  rewrite <- sumf_mul_const_r; reflexivity.
Qed.

End Tensor.

Print Assumptions gconv_prod_tensor.
Print Assumptions gunit_prod_tensor.
Print Assumptions tconv_elementary.

(* ================================================================= *)
(*  END HopfGroupTensor.v                                             *)
(*  k[G×H] ≅ k[G]⊗k[H]: currying intertwines the product-group        *)
(*  convolution with the tensor-product convolution, the unit is a    *)
(*  pure tensor, and the tensor convolution factors on elementary     *)
(*  tensors — so the group-algebra functor is monoidal.  Closed under *)
(*  the global context (axiom-free).                                  *)
(* ================================================================= *)
