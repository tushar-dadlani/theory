(* ================================================================= *)
(*  CEisensteinSplit.v  —  p = 1 mod 3  =>  p = pi . conj pi.          *)
(*                                                                    *)
(*    order3_elt        : p = 1 mod 3 gives t with t^3 = 1, t <> 1     *)
(*    eisenstein_split  : exists pi in Z[omega] with N(pi) = p         *)
(*    eisenstein_split_conj : p = pi . conj pi                         *)
(*                                                                    *)
(*  This is the statement crypto/PrimeFactorizationTriadic.v:44        *)
(*  asserts in prose and whose only proof (:143) establishes 3 = 3.    *)
(*                                                                    *)
(*  NO QUADRATIC RECIPROCITY IS NEEDED.  The usual route goes through  *)
(*  -3 being a quadratic residue mod p, but that is a detour: what the *)
(*  argument actually wants is a root of X^2 + X + 1 mod p, and since  *)
(*  (Z/p)* is cyclic of order p-1 divisible by 3, an element t of      *)
(*  order 3 is immediate -- t = g^{(p-1)/3} for a primitive root g.    *)
(*  Then p | t^3 - 1 = (t-1)(t^2+t+1) and p does not divide t-1, so    *)
(*  p | t^2 + t + 1.                                                   *)
(*                                                                    *)
(*  The bridge to Z[omega] is that omega satisfies the SAME quadratic: *)
(*      t^2 + t + 1 = (t - omega)(t - omega^2)   exactly,              *)
(*  a one-line ring computation.  So p divides a product of two        *)
(*  elements it divides neither of -- t - omega = (t,-1) and           *)
(*  t - omega^2 = (t+1,1) both have omega-coordinate +-1, and p        *)
(*  cannot divide that.                                               *)
(*                                                                    *)
(*  THE CONCLUSION IS DRAWN CONSTRUCTIVELY, not by contraposing        *)
(*  irreducibility.  Taking g = gcd(p, t - omega) and p = g.h, the two *)
(*  degenerate cases are ruled out directly -- g a unit would make p   *)
(*  divide t - omega^2, h a unit would make p divide t - omega -- so   *)
(*  both are nonunits, N(g).N(h) = p^2 forces N(g) = p, and g is the   *)
(*  pi wanted.  Unit-ness is decidable here (N = 1 is a Z equality),   *)
(*  so no classical logic enters.  Axiom-clean.                        *)
(* ================================================================= *)

From Stdlib Require Import ZArith Znumtheory Arith Lia Ring.
Require Import ZmodPStar ZmodOrder PrimitiveRoot
        CEisenstein CEisensteinUnits CEisensteinDiv CEisensteinGcd.
Open Scope Z_scope.

(* ----------------------------------------------------------------- *)
(*  A.  an element of order 3 mod p                                    *)
(* ----------------------------------------------------------------- *)
Lemma order3_elt : forall p : nat,
  prime (Z.of_nat p) -> Nat.divide 3 (p - 1)%nat -> (7 <= p)%nat ->
  exists t : nat, (2 <= t <= p - 1)%nat /\ ((t ^ 3) mod p = 1)%nat.
Proof.
  intros p Hp Hd Hp7.
  destruct (units_cyclic p Hp) as [g [Hg Hord]].
  destruct Hd as [k Hk].
  assert (Hk2 : (2 <= k)%nat) by lia.
  exists (pw p g k). split.
  - assert (Hu : (1 <= pw p g k <= p - 1)%nat) by (apply pw_unit; assumption).
    assert (Hne : pw p g k <> 1%nat).
    { intro Hc.
      assert (Hle : (ord p g <= k)%nat)
        by (apply ord_least; [ assumption | assumption | lia | exact Hc ]).
      lia. }
    lia.
  - change ((pw p g k ^ 3) mod p = 1)%nat with (pw p (pw p g k) 3 = 1)%nat.
    rewrite <- pw_mul_exp, <- Hk, <- Hord.
    apply ord_period; assumption.
Qed.

(* ----------------------------------------------------------------- *)
(*  B.  hence p divides t^2 + t + 1 in Z                               *)
(* ----------------------------------------------------------------- *)
Lemma p_dvd_quad : forall (p t : nat),
  prime (Z.of_nat p) -> (2 <= t <= p - 1)%nat -> ((t ^ 3) mod p = 1)%nat ->
  (Z.of_nat p | Z.of_nat t ^ 2 + Z.of_nat t + 1).
Proof.
  intros p t Hp Ht Hcube.
  assert (Hp2 : (2 <= p)%nat) by (destruct Hp; lia).
  set (P := Z.of_nat p). set (T := Z.of_nat t).
  assert (HP : 0 < P) by (unfold P; lia).
  assert (HT : 1 < T < P) by (unfold T, P; lia).
  assert (Hdiv3 : (P | T ^ 3 - 1)).
  { assert (Hq : (t ^ 3 = p * (t ^ 3 / p) + 1)%nat).
    { rewrite <- Hcube at 3. apply Nat.div_mod. lia. }
    exists (Z.of_nat (t ^ 3 / p)).
    assert (HZ : Z.of_nat (t ^ 3) = P * Z.of_nat (t ^ 3 / p) + 1).
    { rewrite Hq at 1. rewrite Nat2Z.inj_add, Nat2Z.inj_mul. reflexivity. }
    assert (HT3 : Z.of_nat (t ^ 3) = T ^ 3)
      by (unfold T; rewrite Nat2Z.inj_pow; reflexivity).
    rewrite HT3 in HZ. lia. }
  assert (Hfac : T ^ 3 - 1 = (T - 1) * (T ^ 2 + T + 1)) by ring.
  rewrite Hfac in Hdiv3.
  destruct (prime_mult P Hp _ _ Hdiv3) as [Hbad | Hgood]; [ | exact Hgood ].
  exfalso.
  pose proof (Z.divide_pos_le P (T - 1) ltac:(lia) Hbad). lia.
Qed.

(* ----------------------------------------------------------------- *)
(*  C.  the coprime-divisor step, extracted                            *)
(* ----------------------------------------------------------------- *)
Lemma dvd_mul_coprime : forall c x y u v,
  eadd (emul u c) (emul v x) = eone ->
  edvd c (emul x y) -> edvd c y.
Proof.
  intros c x y u v Hone [w Hw].
  exists (eadd (emul u y) (emul v w)).
  assert (Hy : y = eadd (emul (emul u y) c) (emul v (emul x y))).
  { transitivity (emul (eadd (emul u c) (emul v x)) y);
      [ rewrite Hone; ring | ring ]. }
  rewrite Hy at 1. rewrite Hw. ring.
Qed.

(* ----------------------------------------------------------------- *)
(*  D.  THE SPLITTING                                                  *)
(* ----------------------------------------------------------------- *)
Theorem eisenstein_split : forall p : nat,
  prime (Z.of_nat p) -> Nat.divide 3 (p - 1)%nat -> (7 <= p)%nat ->
  exists pi : Eis, enorm pi = Z.of_nat p.
Proof.
  intros p Hp Hd Hp7.
  destruct (order3_elt p Hp Hd Hp7) as [t [Ht Hcube]].
  destruct (p_dvd_quad p t Hp Ht Hcube) as [c Hc].
  set (P := Z.of_nat p) in *. set (T := Z.of_nat t) in *.
  assert (HP : 7 <= P) by (unfold P; lia).
  set (Pe := mkEis P 0).
  set (A := mkEis T (-1)).
  set (B := mkEis (T + 1) 1).
  assert (Hprod : emul A B = mkEis (T ^ 2 + T + 1) 0)
    by (unfold A, B, emul; cbn [ea eb]; apply Eis_eq; ring).
  assert (HdvdAB : edvd Pe (emul A B)).
  { exists (mkEis c 0). rewrite Hprod.
    unfold Pe, emul; cbn [ea eb]. apply Eis_eq; [ rewrite Hc; ring | ring ]. }
  assert (HnA : ~ edvd Pe A).
  { intros [q Hq]. unfold Pe, A, emul in Hq.
    apply (f_equal eb) in Hq. cbn [ea eb] in Hq.
    destruct (Z.eq_dec (eb q) 0) as [E | E]; nia. }
  assert (HnB : ~ edvd Pe B).
  { intros [q Hq]. unfold Pe, B, emul in Hq.
    apply (f_equal eb) in Hq. cbn [ea eb] in Hq.
    destruct (Z.eq_dec (eb q) 0) as [E | E]; nia. }
  destruct (ebezout Pe A) as [g [u [v [Hgp [Hga [Hg _]]]]]].
  destruct Hgp as [h Hh].
  assert (HPe0 : enorm Pe = P * P)
    by (unfold Pe, enorm; cbn [ea eb]; ring).
  assert (Hnorms : enorm g * enorm h = P * P)
    by (rewrite <- HPe0, Hh, enorm_mul; reflexivity).
  destruct (Z.eq_dec (enorm g) 1) as [Hgu | Hgnu].
  { exfalso. apply HnB.
    destruct (norm_eunit g Hgu) as [gi Hgi].
    apply (dvd_mul_coprime Pe A B (emul u gi) (emul v gi));
      [ rewrite <- Hgi, Hg; ring | exact HdvdAB ]. }
  destruct (Z.eq_dec (enorm h) 1) as [Hhu | Hhnu].
  { exfalso. apply HnA.
    destruct (norm_eunit h Hhu) as [hi Hhi].
    apply (edvd_trans Pe g A); [ | exact Hga ].
    exists hi. rewrite Hh, emul_assoc, Hhi. ring. }
  exists g.
  assert (Hg0 : 0 <= enorm g) by apply enorm_nonneg.
  assert (Hh0 : 0 <= enorm h) by apply enorm_nonneg.
  assert (HdvdP : (P | enorm g * enorm h)) by (exists P; lia).
  destruct (prime_mult P Hp _ _ HdvdP) as [[m Hm] | [m Hm]].
  - assert (Hmdvd : (m | P)) by (exists (enorm h); nia).
    destruct (prime_divisors P Hp m Hmdvd) as [E | [E | [E | E]]]; nia.
  - assert (Hmdvd : (m | P)) by (exists (enorm g); nia).
    destruct (prime_divisors P Hp m Hmdvd) as [E | [E | [E | E]]]; nia.
Qed.

Corollary eisenstein_split_conj : forall p : nat,
  prime (Z.of_nat p) -> Nat.divide 3 (p - 1)%nat -> (7 <= p)%nat ->
  exists pi : Eis, emul pi (econj pi) = mkEis (Z.of_nat p) 0.
Proof.
  intros p Hp Hd Hp7.
  destruct (eisenstein_split p Hp Hd Hp7) as [pi Hpi].
  exists pi. rewrite emul_econj, Hpi. reflexivity.
Qed.

Print Assumptions eisenstein_split.
Print Assumptions eisenstein_split_conj.
