(* ================================================================= *)
(*  ZmodMultCounterex.v  —  Brick 3, the composite counterexamples.   *)
(*                                                                    *)
(*  (Z/n, x) is NOT iso to any Adj G when n is composite, because      *)
(*  Adj G has NO nonzero zero-divisors: aop x y = AZero forces x or y   *)
(*  to be AZero (a product of two AElt's is again an AElt).  A          *)
(*  composite modulus has a nonzero zero-divisor -- 2.2 = 0 (mod 4),    *)
(*  2.3 = 0 (mod 6) -- so no bijective monoid homomorphism             *)
(*  f : (Z/n, x) -> Adj G can exist.                                   *)
(*                                                                    *)
(*  n = 4 fails by NON-SQUAREFREENESS (2 is nilpotent, 2.2 = 0).        *)
(*  n = 6 = p1.p2 is SQUAREFREE yet still fails (2.3 = 0), so the        *)
(*  obstruction is COMPOSITENESS, not squares -- which is why the        *)
(*  primorial needs Brick 5's tensor, not another Adj.  The Coq          *)
(*  obstruction (a nonzero zero-divisor) is uniform across both.        *)
(*                                                                    *)
(*  Carrier-light: raw-nat source, guarded by x < n; the three           *)
(*  hypotheses on f are EXACTLY "f is a bijective monoid hom", and       *)
(*  f 0 = AZero is DERIVED, not assumed.  Axiom-free.                    *)
(* ================================================================= *)

From Stdlib Require Import Arith Lia.
Require Import HopfGroupAlgebraGen MonoidAlgebraZero.

Definition mmul (n x y : nat) : nat := (x * y) mod n.

(* ---- Adj G has no nonzero zero-divisors ---- *)
Lemma aop_no_zero_div : forall (G : Type) (gop : G -> G -> G) (x y : Adj G),
  aop G gop x y = AZero G -> x = AZero G \/ y = AZero G.
Proof.
  intros G gop [|a] [|b] H;
    try (left; reflexivity); try (right; reflexivity);
    cbn in H; discriminate H.
Qed.

(* ---- AZero is the unique absorbing element of Adj G ---- *)
Lemma absorbing_unique : forall (G : Type) (gop : G -> G -> G) (z : Adj G),
  (forall x, aop G gop z x = z) -> z = AZero G.
Proof.
  intros G gop [|a] Hz; [ reflexivity | ].
  specialize (Hz (AZero G)); cbn in Hz; discriminate Hz.
Qed.

(* ---- the general obstruction ----
   a nonzero zero-divisor (a.b = 0, a<>0, b<>0) blocks every bijective
   monoid hom  f : (Z/n, x) -> Adj G. *)
Theorem no_iso_of_zero_divisor :
  forall (G : Type) (gop : G -> G -> G) (n a b : nat) (f : nat -> Adj G),
    0 < n -> a < n -> b < n -> a <> 0 -> b <> 0 -> mmul n a b = 0 ->
    (forall x y, x < n -> y < n -> f (mmul n x y) = aop G gop (f x) (f y)) ->
    (forall x y, x < n -> y < n -> f x = f y -> x = y) ->
    (forall z : Adj G, exists x, x < n /\ f x = z) ->
    False.
Proof.
  intros G gop n a b f H0n Han Hbn Ha0 Hb0 Hab Hhom Hinj Hsurj.
  (* f 0 = AZero: the image of the absorbing 0 is absorbing, hence AZero *)
  assert (Hzero : f 0 = AZero G).
  { apply (absorbing_unique G gop). intros z.
    destruct (Hsurj z) as [x [Hx Hfx]].
    rewrite <- Hfx, <- (Hhom 0 x H0n Hx).
    assert (Hm0 : mmul n 0 x = 0)
      by (unfold mmul; rewrite Nat.mul_0_l, Nat.Div0.mod_0_l; reflexivity).
    rewrite Hm0; reflexivity. }
  (* f a . f b = f (a.b) = f 0 = AZero, so f a or f b = AZero = f 0 *)
  assert (Hprod : aop G gop (f a) (f b) = AZero G).
  { rewrite <- (Hhom a b Han Hbn), Hab; exact Hzero. }
  destruct (aop_no_zero_div G gop (f a) (f b) Hprod) as [Hfa | Hfb].
  - apply Ha0. apply (Hinj a 0 Han H0n). rewrite Hfa, Hzero; reflexivity.
  - apply Hb0. apply (Hinj b 0 Hbn H0n). rewrite Hfb, Hzero; reflexivity.
Qed.

(* ---- the two named counterexamples ---- *)

(* Z/4: 2.2 = 0.  Fails by NON-SQUAREFREENESS. *)
Theorem zmod4_not_adj :
  forall (G : Type) (gop : G -> G -> G) (f : nat -> Adj G),
    (forall x y, x < 4 -> y < 4 -> f (mmul 4 x y) = aop G gop (f x) (f y)) ->
    (forall x y, x < 4 -> y < 4 -> f x = f y -> x = y) ->
    (forall z : Adj G, exists x, x < 4 /\ f x = z) ->
    False.
Proof.
  intros G gop f Hhom Hinj Hsurj.
  apply (no_iso_of_zero_divisor G gop 4 2 2 f);
    first [ lia | reflexivity | assumption ].
Qed.

(* Z/6 = p1.p2 (SQUAREFREE): 2.3 = 0.  Fails by COMPOSITENESS. *)
Theorem zmod6_not_adj :
  forall (G : Type) (gop : G -> G -> G) (f : nat -> Adj G),
    (forall x y, x < 6 -> y < 6 -> f (mmul 6 x y) = aop G gop (f x) (f y)) ->
    (forall x y, x < 6 -> y < 6 -> f x = f y -> x = y) ->
    (forall z : Adj G, exists x, x < 6 /\ f x = z) ->
    False.
Proof.
  intros G gop f Hhom Hinj Hsurj.
  apply (no_iso_of_zero_divisor G gop 6 2 3 f);
    first [ lia | reflexivity | assumption ].
Qed.

Print Assumptions zmod4_not_adj.
Print Assumptions zmod6_not_adj.

(* ================================================================= *)
(*  END ZmodMultCounterex.v  (Brick 3 negatives: composite moduli are  *)
(*  not zero-adjunctions -- 4 by nilpotence, 6 by compositeness.)      *)
(* ================================================================= *)
