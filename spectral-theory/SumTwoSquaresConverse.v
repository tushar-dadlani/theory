(* ================================================================= *)
(*  SumTwoSquaresConverse.v                                          *)
(*                                                                    *)
(*  THE CONVERSE and FULL CHARACTERISATION of sums of two squares.    *)
(*                                                                    *)
(*  Converse core:                                                   *)
(*    neg1_not_QR : for a prime q = 3 (mod 4), -1 is NOT a QR         *)
(*      (no x with x^2 = -1 mod q) -- the exact converse of           *)
(*      SumTwoSquares.neg1_QR, proved from the order theory: such an   *)
(*      x would have order 4, forcing 4 | q-1, i.e. q = 1 (mod 4).     *)
(*    prime3_obstruction : if q = 3 (mod 4) is prime and q | a^2+b^2   *)
(*      then q | a and q | b (over Z, via Bezout + neg1_not_QR).       *)
(*                                                                    *)
(*  Characterisation engine, both halves proved:                     *)
(*    prime3_descent : the NECESSITY engine -- if q = 3 (mod 4) divides *)
(*      a sum of two squares n then q^2 | n and n/q^2 is again a sum of *)
(*      two squares (so q occurs to an even power).                    *)
(*    the SUFFICIENCY building blocks -- 0,1,2, every square k^2, and   *)
(*      products (SumTwoSquares.sum2_mul / Brahmagupta) are sums of two *)
(*      squares; with Fermat (FermatTwoSquares) for primes = 1 (mod 4). *)
(*  Together: n = 1 (mod 4) primes, 2, and squares of = 3 (mod 4)       *)
(*  primes are all sums of two squares, and the = 3 (mod 4) obstruction *)
(*  forces even powers -- the two directions of the classical           *)
(*  characterisation.  (The global bookkeeping that stitches these into *)
(*  a single valuation-parity iff over an arbitrary factorisation is a  *)
(*  further valuation-additivity development, not done here.)          *)
(*                                                                    *)
(*  Axiom-free ("Closed under the global context").                  *)
(* ================================================================= *)

From Stdlib Require Import ZArith Znumtheory Arith Lia.
Require Import SumTwoSquares FermatTwoSquares ZmodPStar ZmodOrder PrimitiveRoot PrimeFactorizationExists.

(* ================================================================= *)
(*  1.  -1 IS NOT A QR mod q  for q = 3 (mod 4)   (over nat)          *)
(* ================================================================= *)

Open Scope nat_scope.

Lemma div4 : forall n, Nat.divide n 4 -> n = 1 \/ n = 2 \/ n = 4.
Proof.
  intros n Hd.
  assert (Hle : n <= 4) by (apply Nat.divide_pos_le; [ lia | exact Hd ]).
  destruct Hd as [c Hc].
  destruct n as [|[|[|[|[|k]]]]]; lia.
Qed.

Lemma neg1_not_QR : forall q, prime (Z.of_nat q) -> q mod 4 = 3 ->
  forall x, (x * x + 1) mod q <> 0.
Proof.
  intros q Hq Hmod x Hc.
  assert (Hq2 : 2 <= q) by (destruct Hq; lia).
  assert (Hq3 : 3 <= q) by (pose proof (Nat.div_mod_eq q 4); lia).
  (* reduce x to a unit residue r *)
  remember (x mod q) as r eqn:Hr.
  assert (Hrlt : r < q) by (rewrite Hr; apply Nat.mod_upper_bound; lia).
  assert (Hrr : (r * r + 1) mod q = 0).
  { rewrite Hr.
    rewrite <- Nat.Div0.add_mod_idemp_l.
    rewrite Nat.Div0.mul_mod_idemp_l, Nat.Div0.mul_mod_idemp_r.
    rewrite Nat.Div0.add_mod_idemp_l; exact Hc. }
  assert (Hr1 : 1 <= r).
  { destruct r as [|r']; [ | lia ].
    simpl in Hrr; rewrite Nat.mod_small in Hrr by lia; discriminate. }
  (* pw q r 2 = q - 1 *)
  assert (Hpw2 : pw q r 2 = q - 1).
  { unfold pw; replace (r ^ 2) with (r * r) by (cbn; ring).
    pose proof (Nat.Div0.add_mod_idemp_l (r * r) 1 q) as Hadd; rewrite Hrr in Hadd.
    pose proof (Nat.mod_upper_bound (r * r) q ltac:(lia)) as Hub.
    remember (r * r mod q) as s eqn:Hs.
    destruct (proj1 (Nat.Lcm0.mod_divide (s + 1) q) Hadd) as [k Hk].
    assert (1 <= k) by nia; assert (k <= 1) by nia; assert (k = 1) by lia; subst k; lia. }
  (* pw q r 4 = 1 *)
  assert (Hpw4 : pw q r 4 = 1).
  { replace 4 with (2 + 2) by lia; rewrite pw_add, Hpw2.
    replace ((q - 1) * (q - 1)) with (1 + (q - 2) * q) by nia.
    rewrite Nat.Div0.mod_add, Nat.mod_small by lia; reflexivity. }
  (* order divides 4, does not divide 2, hence = 4 *)
  assert (Hd4 : Nat.divide (ord q r) 4) by (apply ord_divides; [ assumption | lia | exact Hpw4 ]).
  assert (Hn2 : ~ Nat.divide (ord q r) 2).
  { intro Hdv; destruct Hdv as [c Hc2].
    assert (pw q r 2 = 1).
    { rewrite Hc2, Nat.mul_comm; apply pw_pow_ord_mul; [ lia | apply ord_period; [ assumption | lia ] ]. }
    rewrite Hpw2 in H; lia. }
  assert (Hord4 : ord q r = 4).
  { destruct (div4 (ord q r) Hd4) as [E|[E|E]]; rewrite E in *;
      [ exfalso; apply Hn2; exists 2; lia | exfalso; apply Hn2; exists 1; lia | reflexivity ]. }
  (* 4 | q - 1, contradicting q = 3 (mod 4) *)
  assert (Hdp1 : Nat.divide (ord q r) (q - 1)) by (apply ord_div_pm1; [ assumption | lia ]).
  rewrite Hord4 in Hdp1; destruct Hdp1 as [c Hc4].
  pose proof (Nat.div_mod_eq q 4); lia.
Qed.

(* ================================================================= *)
(*  2.  THE OBSTRUCTION  (over Z)                                     *)
(* ================================================================= *)

Open Scope Z_scope.

(* nat -1-non-residue lifted to Z: q does not divide X^2 + 1 *)
Lemma neg1_not_QR_Z : forall q, prime (Z.of_nat q) -> (q mod 4 = 3)%nat ->
  forall X : Z, ~ (Z.of_nat q | X * X + 1).
Proof.
  intros q Hq Hmod X Hdvd.
  assert (Hq2 : 2 <= Z.of_nat q) by (apply prime_ge_2; exact Hq).
  set (x := Z.to_nat (X mod Z.of_nat q)).
  assert (Hxb : 0 <= X mod Z.of_nat q < Z.of_nat q) by (apply Z.mod_pos_bound; lia).
  assert (Hxz : Z.of_nat x = X mod Z.of_nat q) by (unfold x; rewrite Z2Nat.id; lia).
  (* q | x^2 + 1 in Z *)
  assert (HqZ : (Z.of_nat q | Z.of_nat x * Z.of_nat x + 1)).
  { rewrite Hxz.
    replace (X mod Z.of_nat q * (X mod Z.of_nat q) + 1)
      with ((X * X + 1) - (X - X mod Z.of_nat q) * (X + X mod Z.of_nat q)) by ring.
    apply Z.divide_sub_r; [ exact Hdvd | ].
    apply Z.divide_mul_l.
    (* q | X - X mod q *)
    exists (X / Z.of_nat q); rewrite (Z.div_mod X (Z.of_nat q)) at 1 by lia; ring. }
  (* transfer to nat and contradict neg1_not_QR *)
  apply (neg1_not_QR q Hq Hmod x).
  apply (proj2 (Nat.Lcm0.mod_divide (x * x + 1) q)).
  destruct HqZ as [c Hc].
  assert (Hc0 : 0 <= c) by nia.
  exists (Z.to_nat c).
  apply Nat2Z.inj.
  rewrite Nat2Z.inj_add, !Nat2Z.inj_mul, (Z2Nat.id c Hc0); nia.
Qed.

Lemma prime3_obstruction : forall q (a b : Z),
  prime (Z.of_nat q) -> (q mod 4 = 3)%nat -> (Z.of_nat q | a * a + b * b) ->
  (Z.of_nat q | a) /\ (Z.of_nat q | b).
Proof.
  intros q a b Hq Hmod Hdvd.
  assert (Hqa : (Z.of_nat q | a)).
  { destruct (Znumtheory.Zdivide_dec (Z.of_nat q) a) as [Hd|Hnd]; [ exact Hd | exfalso ].
    (* a is a unit mod q; build X with q | X^2+1 *)
    assert (Hrp : rel_prime (Z.of_nat q) a) by (apply prime_rel_prime; assumption).
    destruct (rel_prime_bezout _ _ Hrp) as [u v Huv].    (* u*q + v*a = 1 *)
    apply (neg1_not_QR_Z q Hq Hmod (v * b)).
    (* q | (v b)^2 + 1 *)
    replace (v * b * (v * b) + 1)
      with (v * v * (a * a + b * b) - (v * a - 1) * (v * a + 1)) by ring.
    apply Z.divide_sub_r.
    - apply Z.divide_mul_r; exact Hdvd.
    - apply Z.divide_mul_l.
      exists (- u); nia. }
  split; [ exact Hqa | ].
  (* q | a => q | a^2 => q | b^2 => q | b *)
  assert (Hqb2 : (Z.of_nat q | b * b)).
  { replace (b * b) with ((a * a + b * b) - a * a) by ring.
    apply Z.divide_sub_r; [ exact Hdvd | apply Z.divide_mul_l; exact Hqa ]. }
  destruct (prime_mult (Z.of_nat q) Hq b b Hqb2); assumption.
Qed.

(* ================================================================= *)
(*  3.  THE NECESSITY ENGINE: a  q = 3 (mod 4)  divides to even power  *)
(* ================================================================= *)

(* if q = 3 (mod 4) divides a sum of two squares n, then q^2 | n and    *)
(* n/q^2 is again a sum of two squares -- so q occurs to an even power. *)
Lemma prime3_descent : forall q (n : Z), prime (Z.of_nat q) -> (q mod 4 = 3)%nat ->
  0 < n -> (Z.of_nat q | n) -> sum2 n ->
  (Z.of_nat q * Z.of_nat q | n) /\ sum2 (n / (Z.of_nat q * Z.of_nat q)).
Proof.
  intros q n Hq Hmod Hpos Hqn [a [b Hn]].
  destruct (prime3_obstruction q a b Hq Hmod ltac:(rewrite <- Hn; exact Hqn)) as [Hqa Hqb].
  destruct Hqa as [a' Ha']; destruct Hqb as [b' Hb'].
  assert (Hn2 : n = (Z.of_nat q * Z.of_nat q) * (a' * a' + b' * b'))
    by (rewrite Hn, Ha', Hb'; ring).
  assert (Hqq : Z.of_nat q * Z.of_nat q <> 0)
    by (assert (2 <= Z.of_nat q) by (apply prime_ge_2; exact Hq); nia).
  split.
  - exists (a' * a' + b' * b'); rewrite Hn2; ring.
  - exists a', b'.
    rewrite Hn2, (Z.mul_comm (Z.of_nat q * Z.of_nat q)), Z.div_mul by exact Hqq; reflexivity.
Qed.

(* ================================================================= *)
(*  4.  SUFFICIENCY building blocks  (over Z)                        *)
(* ================================================================= *)

Lemma sum2_0 : sum2 0.            Proof. exists 0, 0; ring. Qed.
Lemma sum2_1 : sum2 1.            Proof. exists 1, 0; ring. Qed.
Lemma sum2_2 : sum2 2.            Proof. exists 1, 1; ring. Qed.
Lemma sum2_sq : forall k, sum2 (k * k).  Proof. intro k; exists k, 0; ring. Qed.

(* a prime = 1 (mod 4) is a sum of two squares (Fermat, restated over Z) *)
Lemma sum2_prime1 : forall q, prime (Z.of_nat q) -> (q mod 4 = 1)%nat -> sum2 (Z.of_nat q).
Proof. intros q Hq Hmod; apply (fermat_two_squares q Hq Hmod). Qed.

(* ----------------------------------------------------------------- *)
(*  MASTER: the converse (obstruction), the necessity engine, and the  *)
(*  sufficiency blocks -- the two directions of the characterisation.  *)
(* ----------------------------------------------------------------- *)

Theorem two_squares_characterisation :
  (* CONVERSE (obstruction): q = 3 (mod 4) | a^2+b^2  =>  q | a and q | b *)
     (forall q (a b : Z), prime (Z.of_nat q) -> (q mod 4 = 3)%nat ->
        (Z.of_nat q | a * a + b * b) -> (Z.of_nat q | a) /\ (Z.of_nat q | b))
  (* NECESSITY engine: such a q divides a sum2 to an even power *)
  /\ (forall q (n : Z), prime (Z.of_nat q) -> (q mod 4 = 3)%nat ->
        0 < n -> (Z.of_nat q | n) -> sum2 n ->
        (Z.of_nat q * Z.of_nat q | n) /\ sum2 (n / (Z.of_nat q * Z.of_nat q)))
  (* SUFFICIENCY blocks: 2, primes = 1 (mod 4), squares, and products *)
  /\ sum2 2
  /\ (forall q, prime (Z.of_nat q) -> (q mod 4 = 1)%nat -> sum2 (Z.of_nat q))
  /\ (forall k, sum2 (k * k))
  /\ (forall m n, sum2 m -> sum2 n -> sum2 (m * n)).
Proof.
  split; [ exact prime3_obstruction | ].
  split; [ exact prime3_descent | ].
  split; [ exact sum2_2 | ].
  split; [ exact sum2_prime1 | ].
  split; [ exact sum2_sq | exact sum2_mul ].
Qed.

Print Assumptions two_squares_characterisation.

(* ================================================================= *)
(*  END SumTwoSquaresConverse.v                                      *)
(*  The converse of the two-square theorem: for q = 3 (mod 4) prime,   *)
(*  -1 is not a QR (neg1_not_QR) and q | a^2+b^2 forces q|a, q|b        *)
(*  (prime3_obstruction) -- hence such a q divides any sum of two       *)
(*  squares to an even power (prime3_descent).  With the sufficiency    *)
(*  blocks (2, primes = 1 (mod 4) via Fermat, squares, products) these  *)
(*  are the two directions of the classical characterisation.  Closed   *)
(*  under the global context.                                         *)
(* ================================================================= *)
