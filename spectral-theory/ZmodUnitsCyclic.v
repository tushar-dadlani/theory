(* ================================================================= *)
(*  ZmodUnitsCyclic.v  —  Brick 3c:  (Z/p)^x  is cyclic  =  Z/(p-1).   *)
(*                                                                    *)
(*  A primitive root g (PrimitiveRoot.units_cyclic) makes the discrete  *)
(*  exponential  expg k = g^k mod p  an ISOMORPHISM of monoids          *)
(*      (Z/(p-1), +)  ~=  ((Z/p)^x, x),                                 *)
(*  carrying addition mod p-1 to multiplication mod p:                  *)
(*    expg_hom  : expg ((i+j) mod (p-1)) = (expg i * expg j) mod p      *)
(*    expg_unit : 1 <= expg i <= p-1        (lands in the units)        *)
(*    expg_inj  : injective on [0, p-2]     (ZmodOrder.pow_inj_below)   *)
(*    expg_surj : onto the units [1, p-1]   (root_is_power + Fermat)    *)
(*                                                                    *)
(*  So the group half of  Z[M_p] = Z[(Z/p)^x] |x Z*d0  is  Z[Z/(p-1)],  *)
(*  a cyclic group algebra -- the entry point to the cyclotomic          *)
(*  factorisation.  Axiom-free.                                         *)
(* ================================================================= *)

From Stdlib Require Import Arith Lia ZArith Znumtheory.
Require Import ZmodOrder ZmodPStar PrimitiveRoot.
Open Scope nat_scope.

Section UnitsCyclic.

Variable p : nat.
Hypothesis Hp : prime (Z.of_nat p).
Variable g : nat.
Hypothesis Hg : 1 <= g <= p - 1.
Hypothesis Hord : ord p g = p - 1.

Lemma p_ge2 : 2 <= p.
Proof. pose proof (prime_ge_2 _ Hp); lia. Qed.

Definition expg (k : nat) : nat := pw p g k.

(* g^(p-1) = 1 *)
Lemma g_pow_ord : pw p g (p - 1) = 1.
Proof. rewrite <- Hord; apply ord_period; [ exact Hp | exact Hg ]. Qed.

(* the exponent only matters mod (p-1) *)
Lemma pw_mod : forall k, pw p g k = pw p g (k mod (p - 1)).
Proof.
  intros k. pose proof p_ge2 as Hp2.
  rewrite (Nat.div_mod k (p - 1)) at 1 by lia.
  rewrite pw_add.
  rewrite (pw_pow_ord_mul p g (p - 1) (k / (p - 1)) ltac:(lia) g_pow_ord).
  rewrite Nat.mul_1_l. unfold pw. rewrite Nat.Div0.mod_mod. reflexivity.
Qed.

(* ---- the four iso properties ---- *)

Theorem expg_hom : forall i j, expg ((i + j) mod (p - 1)) = (expg i * expg j) mod p.
Proof. intros i j; unfold expg; rewrite <- pw_mod; apply pw_add. Qed.

Theorem expg_unit : forall i, 1 <= expg i <= p - 1.
Proof. intros i; unfold expg; apply pw_unit; [ exact Hp | exact Hg ]. Qed.

Theorem expg_inj : forall i j, i < p - 1 -> j < p - 1 -> expg i = expg j -> i = j.
Proof.
  intros i j Hi Hj Heq; unfold expg in Heq.
  apply (pow_inj_below p g i j Hp Hg); [ rewrite Hord; lia | rewrite Hord; lia | exact Heq ].
Qed.

Theorem expg_surj : forall b, 1 <= b <= p - 1 -> exists i, i < p - 1 /\ expg i = b.
Proof.
  intros b Hb.
  destruct (root_is_power p g (p - 1) b Hp Hg Hord Hb (fermat p b Hp Hb)) as [i [Hi Hpi]].
  exists i; split; [ exact Hi | exact Hpi ].
Qed.

(* ----------------------------------------------------------------- *)
(*  MASTER (for this primitive root g)                                *)
(* ----------------------------------------------------------------- *)
Theorem units_cyclic_iso_g :
  (forall i j, expg ((i + j) mod (p - 1)) = (expg i * expg j) mod p)
  /\ (forall i, 1 <= expg i <= p - 1)
  /\ (forall i j, i < p - 1 -> j < p - 1 -> expg i = expg j -> i = j)
  /\ (forall b, 1 <= b <= p - 1 -> exists i, i < p - 1 /\ expg i = b).
Proof.
  split; [ exact expg_hom | ].
  split; [ exact expg_unit | ].
  split; [ exact expg_inj | exact expg_surj ].
Qed.

End UnitsCyclic.

(* ----------------------------------------------------------------- *)
(*  TOP-LEVEL:  the unit group of Z/p is cyclic of order p-1.         *)
(*  There is a discrete exponential  k |-> g^k mod p  that is a monoid  *)
(*  iso  (Z/(p-1), +)  ~=  ((Z/p)^x, x).                               *)
(* ----------------------------------------------------------------- *)
Theorem zmod_units_cyclic : forall p, prime (Z.of_nat p) ->
  exists g, 1 <= g <= p - 1 /\
    (forall i j, pw p g ((i + j) mod (p - 1)) = (pw p g i * pw p g j) mod p)
    /\ (forall i, 1 <= pw p g i <= p - 1)
    /\ (forall i j, i < p - 1 -> j < p - 1 -> pw p g i = pw p g j -> i = j)
    /\ (forall b, 1 <= b <= p - 1 -> exists i, i < p - 1 /\ pw p g i = b).
Proof.
  intros p Hp; destruct (units_cyclic p Hp) as [g [Hg Hord]].
  exists g; split; [ exact Hg | ].
  destruct (units_cyclic_iso_g p Hp g Hg Hord) as [H1 [H2 [H3 H4]]].
  split; [ exact H1 | ]. split; [ exact H2 | ]. split; [ exact H3 | exact H4 ].
Qed.

Print Assumptions zmod_units_cyclic.

(* ================================================================= *)
(*  END ZmodUnitsCyclic.v  (Brick 3c: (Z/p)^x ~= Z/(p-1) cyclic via    *)
(*  the discrete exponential; the group half of Z[M_p] is a cyclic      *)
(*  group algebra Z[Z/(p-1)].)                                         *)
(* ================================================================= *)
