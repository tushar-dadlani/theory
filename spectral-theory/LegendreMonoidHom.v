(* ================================================================= *)
(*  LegendreMonoidHom.v  —  Brick 4:  {I,N,F} as the universal          *)
(*  quadratic quotient of M_p.                                          *)
(*                                                                    *)
(*  The Legendre symbol IS a monoid homomorphism  (Z/p, x) -> {I,N,F}:  *)
(*      leg_sym p a = F  if p | a,  else  I / N  by the half-power test  *)
(*  so that  val (leg_sym p a) = legendre p a  (matching legendre's own  *)
(*  case split definitionally).  Then:                                  *)
(*    - leg_sym_hom  : leg_sym p ((a*b) mod p) = op (leg_sym p a)(...)   *)
(*      (INFMonoid.val_inj + legendre multiplicativity, zero case incl.) *)
(*    - leg_sym_surjective : onto {I,N,F} for odd p -- F from 0, I from  *)
(*      legendre_1, N from a primitive root (units_cyclic) whose         *)
(*      half-power is <> 1.                                             *)
(*                                                                    *)
(*  So {I,N,F} = the order-2 character surviving because 2 | p-1: the    *)
(*  universal quadratic quotient of every M_p, and functorially an       *)
(*  algebra map Z[M_p] -> Z[Sym].  (val_inj forcing Z/(p-1) into {+-1}   *)
(*  is a p=3 accident; the SURJECTION is what generalises.)  Axiom-free.  *)
(* ================================================================= *)

From Stdlib Require Import Arith Lia ZArith Znumtheory.
Require Import ZmodOrder LegendreSymbol INFMonoid PrimitiveRoot.
Open Scope nat_scope.

(* the Legendre symbol as a value in the sign monoid {I,N,F} *)
Definition leg_sym (p a : nat) : Sym :=
  if a mod p =? 0 then F
  else if pw p a (hlf p) =? 1 then I else N.

Section Legendre.

Variable p : nat.
Hypothesis Hp : prime (Z.of_nat p).
Hypothesis Hodd : p mod 2 = 1.

Lemma p_ge3 : 3 <= p.
Proof.
  pose proof (prime_ge_2 _ Hp) as Hge.
  assert (p <> 2) by (intro He; subst p; discriminate Hodd). lia.
Qed.

(* val o leg_sym = legendre, definitionally (same case split) *)
Lemma leg_sym_val : forall a, val (leg_sym p a) = legendre p a.
Proof.
  intros a; unfold leg_sym, legendre.
  destruct (a mod p =? 0); [ reflexivity | ].
  destruct (pw p a (hlf p) =? 1); reflexivity.
Qed.

(* ---- multiplicativity of legendre, including the zero case ---- *)
Lemma legendre_zero : forall a, a mod p = 0 -> legendre p a = 0%Z.
Proof. intros a Ha; unfold legendre; rewrite Ha; reflexivity. Qed.

Lemma mul_mod_zero_l : forall a b, a mod p = 0 -> (a * b) mod p = 0.
Proof.
  intros a b Ha.
  rewrite Nat.Div0.mul_mod, Ha, Nat.mul_0_l, Nat.Div0.mod_0_l; reflexivity.
Qed.

Lemma mul_mod_zero_r : forall a b, b mod p = 0 -> (a * b) mod p = 0.
Proof. intros a b Hb; rewrite Nat.mul_comm; apply mul_mod_zero_l; exact Hb. Qed.

Lemma legendre_mult : forall a b, a < p -> b < p ->
  legendre p ((a * b) mod p) = (legendre p a * legendre p b)%Z.
Proof.
  intros a b Ha Hb.
  destruct (Nat.eq_dec (a mod p) 0) as [Ha0 | Han].
  - rewrite (legendre_zero a Ha0), (mul_mod_zero_l a b Ha0).
    rewrite (legendre_zero 0) by apply Nat.Div0.mod_0_l; ring.
  - destruct (Nat.eq_dec (b mod p) 0) as [Hb0 | Hbn].
    + rewrite (legendre_zero b Hb0), (mul_mod_zero_r a b Hb0).
      rewrite (legendre_zero 0) by apply Nat.Div0.mod_0_l; ring.
    + apply legendre_mult_unit.
      * exact Hp.
      * exact Hodd.
      * assert (Hma : a mod p = a) by (apply Nat.mod_small; exact Ha).
        rewrite Hma in Han; split; lia.
      * assert (Hmb : b mod p = b) by (apply Nat.mod_small; exact Hb).
        rewrite Hmb in Hbn; split; lia.
Qed.

(* ---- THE HOMOMORPHISM ---- *)
Theorem leg_sym_hom : forall a b, a < p -> b < p ->
  leg_sym p ((a * b) mod p) = op (leg_sym p a) (leg_sym p b).
Proof.
  intros a b Ha Hb; apply val_inj.
  rewrite val_hom, !leg_sym_val; apply legendre_mult; assumption.
Qed.

(* ---- SURJECTIVITY: N needs a non-residue (a primitive root) ---- *)
Lemma hlf_double : 2 * hlf p = p - 1.
Proof.
  unfold hlf.
  pose proof (Nat.div_mod p 2 ltac:(lia)) as Hdm; rewrite Hodd in Hdm.
  assert (Hp1 : p - 1 = 2 * (p / 2)) by lia.
  rewrite Hp1, (Nat.mul_comm 2 (p / 2)), Nat.div_mul by lia; lia.
Qed.

Lemma exists_nonresidue : exists g, 1 <= g <= p - 1 /\ leg_sym p g = N.
Proof.
  pose proof p_ge3 as Hp3.
  destruct (units_cyclic p Hp) as [g [Hg Hord]].
  exists g; split; [ exact Hg | ].
  unfold leg_sym.
  rewrite Nat.mod_small by lia.
  assert (Hg0 : (g =? 0) = false) by (apply Nat.eqb_neq; lia).
  rewrite Hg0.
  assert (Hpw : pw p g (hlf p) <> 1).
  { intro Hc.
    pose proof (ord_divides p g (hlf p) Hp Hg Hc) as Hd.
    rewrite Hord in Hd.
    pose proof hlf_double.
    pose proof (Nat.divide_pos_le (p - 1) (hlf p) ltac:(lia) Hd); lia. }
  assert (Hpwb : (pw p g (hlf p) =? 1) = false) by (apply Nat.eqb_neq; exact Hpw).
  rewrite Hpwb; reflexivity.
Qed.

Theorem leg_sym_surjective : forall s : Sym, exists a, a < p /\ leg_sym p a = s.
Proof.
  pose proof p_ge3 as Hp3.
  intros [ | | ].
  - exists 1; split; [ lia | ].
    apply val_inj; rewrite leg_sym_val, (legendre_1 p Hp Hodd); reflexivity.
  - destruct exists_nonresidue as [g [Hg HN]]; exists g; split; [ lia | exact HN ].
  - exists 0; split; [ lia | ].
    unfold leg_sym; rewrite Nat.Div0.mod_0_l; reflexivity.
Qed.

(* ----------------------------------------------------------------- *)
(*  MASTER THEOREM:  {I,N,F} is the universal quadratic quotient       *)
(* ----------------------------------------------------------------- *)
Theorem legendre_universal_quotient :
  (forall a, val (leg_sym p a) = legendre p a)
  /\ (forall a b, a < p -> b < p ->
        leg_sym p ((a * b) mod p) = op (leg_sym p a) (leg_sym p b))
  /\ (forall s, exists a, a < p /\ leg_sym p a = s).
Proof.
  split; [ exact leg_sym_val | ].
  split; [ exact leg_sym_hom | exact leg_sym_surjective ].
Qed.

End Legendre.

Print Assumptions legendre_universal_quotient.

(* ================================================================= *)
(*  END LegendreMonoidHom.v  (Brick 4: the Legendre symbol is the      *)
(*  monoid hom M_p ->> {I,N,F}; {I,N,F} is the universal quadratic      *)
(*  quotient of every prime-length monoid.)                            *)
(* ================================================================= *)
