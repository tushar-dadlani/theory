(* ================================================================= *)
(*  LegendreSymbol.v                                                 *)
(*                                                                    *)
(*  THE LEGENDRE SYMBOL and EULER'S CRITERION, over an odd prime p.   *)
(*                                                                    *)
(*  Working in the residue arithmetic pw p a k = a^k mod p, the       *)
(*  half-power  a^((p-1)/2)  is a square root of  a^(p-1) = 1         *)
(*  (Fermat), hence is 1 or p-1 (sqrt1).  We DEFINE                   *)
(*                                                                    *)
(*      (a/p) = 0        if p | a,                                    *)
(*            = 1        if a^((p-1)/2) = 1  mod p,                   *)
(*            = -1       otherwise (a^((p-1)/2) = p-1  mod p),        *)
(*                                                                    *)
(*  and prove EULER'S CRITERION  a^((p-1)/2) = (a/p)  (mod p) and     *)
(*  COMPLETE MULTIPLICATIVITY  (ab/p) = (a/p)(b/p) on units.  This is *)
(*  the foundation for Gauss's lemma / quadratic reciprocity.  Reuses *)
(*  Fermat + sqrt1 + the unit/order machinery.  AXIOM-FREE.          *)
(* ================================================================= *)

From Stdlib Require Import ZArith Znumtheory Arith Lia.
Require Import ZmodPStar ZmodOrder SumTwoSquares.
Open Scope nat_scope.

Definition hlf (p : nat) : nat := (p - 1) / 2.

Lemma two_hlf : forall p, p mod 2 = 1 -> 2 <= p -> 2 * hlf p = p - 1.
Proof.
  intros p Hodd Hp; unfold hlf.
  pose proof (Nat.div_mod_eq (p - 1) 2).
  pose proof (Nat.div_mod_eq p 2).
  pose proof (Nat.mod_upper_bound (p - 1) 2).
  pose proof (Nat.mod_upper_bound p 2).
  lia.
Qed.

(* ================================================================= *)
(*  §1  a couple of pw facts                                         *)
(* ================================================================= *)

(* (a mod n)^k = a^k  (mod n) *)
Lemma pow_mod_base : forall n a k, (a mod n) ^ k mod n = a ^ k mod n.
Proof.
  intros n a k; induction k as [|k IH]; [ reflexivity | ].
  cbn [Nat.pow].
  rewrite Nat.Div0.mul_mod_idemp_l.
  rewrite <- Nat.Div0.mul_mod_idemp_r, IH, Nat.Div0.mul_mod_idemp_r; reflexivity.
Qed.

(* pw depends only on the base mod p, and is multiplicative in the base *)
Lemma pw_mul_base : forall p a b k,
  pw p ((a * b) mod p) k = (pw p a k * pw p b k) mod p.
Proof.
  intros p a b k; unfold pw.
  rewrite pow_mod_base, Nat.pow_mul_l, Nat.Div0.mul_mod; reflexivity.
Qed.

(* Fermat for any a coprime to p (a need not be a least residue) *)
Lemma fermat_gen : forall p a, prime (Z.of_nat p) -> ~ Nat.divide p a ->
  a ^ (p - 1) mod p = 1.
Proof.
  intros p a Hp Hnd.
  assert (Hp2 : 2 <= p) by (pose proof (prime_ge_2 _ Hp); lia).
  rewrite <- pow_mod_base.
  assert (Ham : 1 <= a mod p <= p - 1).
  { pose proof (Nat.mod_upper_bound a p ltac:(lia)).
    assert (a mod p <> 0) by (intro E; apply Hnd, Nat.Lcm0.mod_divide; exact E).
    lia. }
  apply fermat; [ exact Hp | exact Ham ].
Qed.

(* ================================================================= *)
(*  §2  EULER'S CRITERION: a^((p-1)/2) is 1 or p-1                    *)
(* ================================================================= *)

Lemma euler_pm1 : forall p a, prime (Z.of_nat p) -> p mod 2 = 1 ->
  ~ Nat.divide p a -> pw p a (hlf p) = 1 \/ pw p a (hlf p) = p - 1.
Proof.
  intros p a Hp Hodd Hnd.
  assert (Hp2 : 2 <= p) by (pose proof (prime_ge_2 _ Hp); lia).
  assert (Hlo : pw p a (hlf p) <> 0).
  { unfold pw; intro Hz.
    apply (not_div_pow p a (hlf p) Hp Hnd), Nat.Lcm0.mod_divide; exact Hz. }
  assert (Hhi : pw p a (hlf p) < p)
    by (unfold pw; apply Nat.mod_upper_bound; lia).
  assert (Hsq : (pw p a (hlf p) * pw p a (hlf p)) mod p = 1).
  { rewrite <- pw_add.
    replace (hlf p + hlf p) with (p - 1) by (pose proof (two_hlf p Hodd Hp2); lia).
    unfold pw; apply fermat_gen; [ exact Hp | exact Hnd ]. }
  apply (sqrt1 p (pw p a (hlf p)) Hp); [ lia | exact Hsq ].
Qed.

(* ================================================================= *)
(*  §3  the Legendre symbol                                          *)
(* ================================================================= *)

Definition legendre (p a : nat) : Z :=
  if a mod p =? 0 then 0%Z
  else if pw p a (hlf p) =? 1 then 1%Z else (-1)%Z.

Lemma legendre_cases : forall p a,
  legendre p a = 0%Z \/ legendre p a = 1%Z \/ legendre p a = (-1)%Z.
Proof.
  intros p a; unfold legendre.
  destruct (a mod p =? 0); [ left; reflexivity | ].
  destruct (pw p a (hlf p) =? 1); [ right; left | right; right ]; reflexivity.
Qed.

Lemma legendre_unit : forall p a, ~ Nat.divide p a ->
  legendre p a = (if pw p a (hlf p) =? 1 then 1%Z else (-1)%Z).
Proof.
  intros p a Hnd; unfold legendre.
  replace (a mod p =? 0) with false; [ reflexivity | ].
  symmetry; apply Nat.eqb_neq; intro E; apply Hnd, Nat.Lcm0.mod_divide; exact E.
Qed.

Lemma legendre_pm1 : forall p a, ~ Nat.divide p a ->
  legendre p a = 1%Z \/ legendre p a = (-1)%Z.
Proof.
  intros p a Hnd; rewrite (legendre_unit p a Hnd).
  destruct (pw p a (hlf p) =? 1); [ left | right ]; reflexivity.
Qed.

(* ================================================================= *)
(*  §4  EULER'S CRITERION in congruence form:  a^((p-1)/2) = (a/p)    *)
(* ================================================================= *)

Lemma legendre_euler : forall p a, prime (Z.of_nat p) -> p mod 2 = 1 ->
  ~ Nat.divide p a ->
  Z.modulo (Z.of_nat (pw p a (hlf p))) (Z.of_nat p)
  = Z.modulo (legendre p a) (Z.of_nat p).
Proof.
  intros p a Hp Hodd Hnd.
  assert (Hp3 : 3 <= p).
  { destruct (Nat.eq_dec p 2) as [->|Hne]; [ discriminate Hodd |
      pose proof (prime_ge_2 _ Hp); lia ]. }
  rewrite (legendre_unit p a Hnd).
  destruct (euler_pm1 p a Hp Hodd Hnd) as [E | E]; rewrite E.
  - cbn [Nat.eqb]; reflexivity.
  - replace (p - 1 =? 1) with false by (symmetry; apply Nat.eqb_neq; lia).
    rewrite Nat2Z.inj_sub by lia; cbn [Z.of_nat].
    symmetry.
    rewrite <- (Z_mod_plus_full (-1) 1 (Z.of_nat p)).
    f_equal; ring.
Qed.

(* ================================================================= *)
(*  §5  a sign is determined by its residue mod p                    *)
(* ================================================================= *)

Lemma sign_mod_inj : forall p s t, 3 <= p ->
  (s = 1%Z \/ s = (-1)%Z) -> (t = 1%Z \/ t = (-1)%Z) ->
  Z.modulo s (Z.of_nat p) = Z.modulo t (Z.of_nat p) -> s = t.
Proof.
  intros p s t Hp Hs Ht Hmod.
  destruct Hs as [-> | ->]; destruct Ht as [-> | ->]; try reflexivity; exfalso;
    rewrite (Z.mod_1_l (Z.of_nat p) ltac:(lia)) in Hmod;
    rewrite <- (Z_mod_plus_full (-1) 1 (Z.of_nat p)) in Hmod;
    replace (-1 + 1 * Z.of_nat p)%Z with (Z.of_nat p - 1)%Z in Hmod by ring;
    rewrite (Z.mod_small (Z.of_nat p - 1) (Z.of_nat p) ltac:(lia)) in Hmod; lia.
Qed.

(* ================================================================= *)
(*  §6  legendre(1) = 1, and COMPLETE MULTIPLICATIVITY on units      *)
(* ================================================================= *)

Lemma legendre_1 : forall p, prime (Z.of_nat p) -> p mod 2 = 1 -> legendre p 1 = 1%Z.
Proof.
  intros p Hp Hodd.
  assert (Hp2 : 2 <= p) by (pose proof (prime_ge_2 _ Hp); lia).
  rewrite (legendre_unit p 1 ltac:(intro Hd; apply Nat.divide_1_r in Hd; lia)),
          (pw_1 p (hlf p) Hp2); reflexivity.
Qed.

Lemma legendre_mult_unit : forall p a b,
  prime (Z.of_nat p) -> p mod 2 = 1 ->
  1 <= a <= p - 1 -> 1 <= b <= p - 1 ->
  legendre p ((a * b) mod p) = (legendre p a * legendre p b)%Z.
Proof.
  intros p a b Hp Hodd Ha Hb.
  assert (Hp2 : 2 <= p) by (pose proof (prime_ge_2 _ Hp); lia).
  assert (Hp3 : 3 <= p).
  { destruct (Nat.eq_dec p 2) as [->|Hne]; [ discriminate Hodd | lia ]. }
  (* the product is again a unit *)
  pose proof (Nat.mod_upper_bound (a * b) p ltac:(lia)) as Hub.
  assert (Hab0 : (a * b) mod p <> 0).
  { intro E.
    assert (Hpab : Nat.divide p (a * b)) by (apply Nat.Lcm0.mod_divide; exact E).
    destruct (prime_mult_nat p a b Hp Hpab) as [H|H];
      [ apply (unit_not_div p a Ha) | apply (unit_not_div p b Hb) ]; exact H. }
  assert (Hab1 : 1 <= (a * b) mod p <= p - 1) by lia.
  assert (Hnab : ~ Nat.divide p ((a * b) mod p)) by (apply (unit_not_div p _ Hab1)).
  apply (sign_mod_inj p _ _ Hp3).
  - apply legendre_pm1; exact Hnab.
  - destruct (legendre_pm1 p a (unit_not_div p a Ha)) as [E|E];
    destruct (legendre_pm1 p b (unit_not_div p b Hb)) as [F|F];
      rewrite E, F; ((left; reflexivity) || (right; reflexivity)).
  - (* both sides congruent to  pw p a h * pw p b h  (mod p) *)
    transitivity (Z.modulo (Z.of_nat (pw p a (hlf p) * pw p b (hlf p))) (Z.of_nat p)).
    + rewrite <- (legendre_euler p ((a * b) mod p) Hp Hodd Hnab),
              (pw_mul_base p a b (hlf p)), Nat2Z.inj_mod, Zmod_mod; reflexivity.
    + rewrite (Zmult_mod (legendre p a) (legendre p b)),
              <- (legendre_euler p a Hp Hodd (unit_not_div p a Ha)),
              <- (legendre_euler p b Hp Hodd (unit_not_div p b Hb)),
              <- Zmult_mod, <- Nat2Z.inj_mul; reflexivity.
Qed.

Print Assumptions legendre_euler.

(* ================================================================= *)
(*  END LegendreSymbol.v                                             *)
(*  The Legendre symbol (a/p) with Euler's criterion                 *)
(*  a^((p-1)/2) = (a/p) (mod p), the sign-injectivity mod p, and     *)
(*  complete multiplicativity on units.  Closed under the global      *)
(*  context (axiom-free).                                            *)
(* ================================================================= *)
