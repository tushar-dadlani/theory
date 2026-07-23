(* ================================================================= *)
(*  SumTwoSquares.v                                                  *)
(*                                                                    *)
(*  SUMS OF TWO SQUARES, through the Gaussian-integer norm bridge.     *)
(*                                                                    *)
(*  A number n is a sum of two squares iff it is a NORM from Z[i]:     *)
(*      sum2 n  <->  exists z : ZI, n = N(z) = Re z^2 + Im z^2.        *)
(*                                                                    *)
(*  TWO PILLARS toward Fermat's two-square theorem:                   *)
(*                                                                    *)
(*   1.  BRAHMAGUPTA-FIBONACCI (sum2_mul): the sums of two squares     *)
(*       are closed under multiplication,                             *)
(*         (a^2+b^2)(c^2+d^2) = (ac-bd)^2 + (ad+bc)^2,                 *)
(*       which is EXACTLY the multiplicativity of the Gaussian norm    *)
(*       N(x y) = N(x) N(y) (GaussianIntegers.ZInorm_mul).  Axiom-free. *)
(*                                                                    *)
(*   2.  -1 IS A QUADRATIC RESIDUE mod p when p = 1 (mod 4)            *)
(*       (neg1_QR): there is an x with x^2 + 1 = 0 (mod p).  Proved     *)
(*       from the repo's from-scratch cyclicity of (Z/pZ)^*            *)
(*       (PrimitiveRoot.units_cyclic): take x = g^((p-1)/4) for a       *)
(*       primitive root g; then x^2 = g^((p-1)/2) is the unique         *)
(*       element of order 2, namely -1 (a square root of 1 that is not  *)
(*       1, via pow_inj_below + the "sqrt of 1 are +-1" fact sqrt1,     *)
(*       itself Euclid's lemma over Z[i]-free Z).                      *)
(*                                                                    *)
(*  Together these are the ingredients of  p = 1 (mod 4) => p = a^2+b^2 *)
(*  (Fermat): (2) gives p | x^2+1 = N(x+i), and a descent (Thue /       *)
(*  Euler, using (1) as its engine) forces p itself to be a norm.  The  *)
(*  descent (the deep step) is the next target; the two pillars here    *)
(*  are complete, genuine theorems.  Pillar 1 axiom-free; pillar 2      *)
(*  axiom-free (nat + Znumtheory, via the cyclicity tower).            *)
(* ================================================================= *)

From Stdlib Require Import ZArith Znumtheory Arith Lia.
Require Import GaussianIntegers ZmodPStar ZmodOrder PrimitiveRoot.

(* ================================================================= *)
(*  PILLAR 1.  Sums of two squares via the Gaussian norm (over Z)     *)
(* ================================================================= *)

Open Scope Z_scope.

Definition sum2 (n : Z) : Prop := exists a b : Z, n = a * a + b * b.

(* n is a sum of two squares  <=>  n is a norm from Z[i] *)
Lemma sum2_norm : forall n, sum2 n <-> exists z, n = ZInorm (-1) z.
Proof.
  intro n; split.
  - intros [a [b Hn]]; exists (mkZI a b); rewrite ZInorm_neg1; cbn [zRe zIm]; exact Hn.
  - intros [z Hz]; exists (zRe z), (zIm z); rewrite Hz, ZInorm_neg1; reflexivity.
Qed.

(* BRAHMAGUPTA-FIBONACCI: sums of two squares are closed under product *)
(* -- this IS the multiplicativity of the Gaussian norm.               *)
Theorem sum2_mul : forall m n, sum2 m -> sum2 n -> sum2 (m * n).
Proof.
  intros m n Hm Hn.
  apply sum2_norm in Hm as [x Hx]; apply sum2_norm in Hn as [y Hy].
  apply sum2_norm; exists (ZImul x y).
  unfold ZImul; rewrite ZInorm_mul, <- Hx, <- Hy; reflexivity.
Qed.

(* the explicit identity, for the record *)
Corollary brahmagupta_fibonacci : forall a b c d : Z,
  (a * a + b * b) * (c * c + d * d)
  = (a * c - b * d) * (a * c - b * d) + (a * d + b * c) * (a * d + b * c).
Proof. intros; ring. Qed.

(* ================================================================= *)
(*  PILLAR 2.  -1 is a QR mod p for p = 1 (mod 4)   (over nat)        *)
(* ================================================================= *)

Open Scope nat_scope.

(* the square roots of 1 mod a prime are exactly 1 and p-1 (= -1).     *)
(* Euclid's lemma over Z: p | y^2 - 1 = (y-1)(y+1) => p|(y-1) or (y+1). *)
Lemma sqrt1 : forall p y, prime (Z.of_nat p) -> 1 <= y <= p - 1 ->
  (y * y) mod p = 1 -> y = 1 \/ y = p - 1.
Proof.
  intros p y Hp Hy Hmod; assert (Hp2 : 2 <= p) by (destruct Hp; lia).
  pose proof (Nat.div_mod_eq (y * y) p) as Hdm; rewrite Hmod in Hdm.
  (* p | (y-1)*(y+1) = y*y - 1 *)
  assert (Hexp : (y - 1) * (y + 1) = y * y - 1) by nia.
  assert (Hpq : y * y - 1 = (y * y / p) * p) by nia.
  assert (Hd : Nat.divide p ((y - 1) * (y + 1)))
    by (exists (y * y / p); rewrite Hexp, Hpq; reflexivity).
  destruct (prime_mult_nat p (y - 1) (y + 1) Hp Hd) as [He|He].
  - left; destruct He as [k Hk].
    assert (k < 1) by nia; assert (k = 0) by lia; subst k; lia.
  - right; destruct He as [k Hk].
    assert (1 <= k) by nia; assert (k <= 1) by nia; assert (k = 1) by lia; subst k; lia.
Qed.

(* -1 is a quadratic residue: some x has x^2 + 1 = 0 (mod p) *)
Lemma neg1_QR : forall p, prime (Z.of_nat p) -> Nat.divide 4 (p - 1) ->
  exists x, (x * x + 1) mod p = 0.
Proof.
  intros p Hp Hdiv; assert (Hp2 : 2 <= p) by (destruct Hp; lia).
  destruct Hdiv as [c Hc].                 (* p - 1 = c * 4 *)
  assert (Hc1 : 1 <= c) by nia.
  destruct (units_cyclic p Hp) as [g [Hg Hord]].
  exists (pw p g c).
  (* (x*x) mod p = pw p g (2*c) *)
  assert (Hxx : (pw p g c * pw p g c) mod p = pw p g (2 * c)).
  { rewrite <- pw_add; f_equal; lia. }
  (* pw p g (2*c) is a square root of 1 *)
  assert (Hyy : (pw p g (2 * c) * pw p g (2 * c)) mod p = 1).
  { rewrite <- pw_add; replace (2 * c + 2 * c) with (p - 1) by lia.
    rewrite <- Hord; apply ord_period; assumption. }
  (* it is a unit (nonzero mod p) *)
  assert (Hnd : ~ Nat.divide p (g ^ (2 * c)))
    by (apply not_div_pow; [ assumption | apply unit_not_div; exact Hg ]).
  assert (Hy1 : 1 <= pw p g (2 * c)).
  { unfold pw; destruct ((g ^ (2 * c)) mod p) eqn:E; [ | lia ].
    exfalso; apply Hnd, (proj1 (Nat.Lcm0.mod_divide _ p)); exact E. }
  assert (Hyu : pw p g (2 * c) <= p - 1)
    by (unfold pw; pose proof (Nat.mod_upper_bound (g ^ (2 * c)) p ltac:(lia)); lia).
  (* it is not 1 (exponent 2c is in (0, ord) and pw is injective there) *)
  assert (Hyne1 : pw p g (2 * c) <> 1).
  { intro Hy1eq.
    assert (H0 : pw p g (2 * c) = pw p g 0) by (rewrite pw_0 by lia; exact Hy1eq).
    pose proof (pow_inj_below p g (2 * c) 0 Hp Hg
                  ltac:(rewrite Hord; lia) ltac:(rewrite Hord; lia) H0); lia. }
  (* hence it is p-1 *)
  assert (Hyval : pw p g (2 * c) = p - 1)
    by (destruct (sqrt1 p (pw p g (2 * c)) Hp ltac:(lia) Hyy);
          [ contradiction | assumption ]).
  (* conclude (x*x + 1) mod p = 0 *)
  rewrite <- Nat.Div0.add_mod_idemp_l, Hxx, Hyval.
  replace (p - 1 + 1) with p by lia; apply Nat.Div0.mod_same.
Qed.

(* ----------------------------------------------------------------- *)
(*  MASTER: the two pillars                                          *)
(* ----------------------------------------------------------------- *)

Theorem sum_two_squares_pillars :
  (* Brahmagupta-Fibonacci: sum2 is multiplicative (= norm mult.) *)
     (forall m n, sum2 m -> sum2 n -> sum2 (m * n)%Z)
  (* -1 is a QR mod p for p = 1 (mod 4) *)
  /\ (forall p, prime (Z.of_nat p) -> Nat.divide 4 (p - 1) ->
        exists x, (x * x + 1) mod p = 0).
Proof. split; [ exact sum2_mul | exact neg1_QR ]. Qed.

Print Assumptions sum_two_squares_pillars.

(* ================================================================= *)
(*  END SumTwoSquares.v                                              *)
(*  Pillar 1 (sum2_mul / brahmagupta_fibonacci): sums of two squares   *)
(*  closed under multiplication, = Gaussian-norm multiplicativity;     *)
(*  axiom-free.  Pillar 2 (neg1_QR): -1 a QR mod p for p = 1 (mod 4),   *)
(*  from the from-scratch cyclicity of (Z/pZ)^* (units_cyclic) + the    *)
(*  sqrt-of-1 fact (sqrt1); axiom-free.  These are the ingredients of   *)
(*  Fermat's p = a^2 + b^2; the descent assembling them is the next     *)
(*  target.  Closed under the global context.                         *)
(* ================================================================= *)
