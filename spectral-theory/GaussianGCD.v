(* ================================================================= *)
(*  GaussianGCD.v                                                    *)
(*                                                                    *)
(*  DIVISIBILITY, gcd and BEZOUT in Z[i].                            *)
(*                                                                    *)
(*  Using Euclidean division (GaussianDivision.ZI_euclid), any pair   *)
(*  x, y has a gcd expressible as a Z[i]-linear combination:          *)
(*                                                                    *)
(*      exists g u v,  g = u*x + v*y,  g | x,  g | y,                 *)
(*                     and every common divisor of x,y divides g.     *)
(*                                                                    *)
(*  Proof: well-founded induction on N(y) (the Euclidean algorithm    *)
(*  gcd(x,y) = gcd(y, x mod y)), no recursive function needed.        *)
(*                                                                    *)
(*  This is the ideal-theoretic heart of unique factorisation: it     *)
(*  gives Euclid's lemma (irreducible => prime) next.  AXIOM-FREE.    *)
(* ================================================================= *)

From Stdlib Require Import ZArith Lia Wf_nat.
Require Import GaussianIntegers GaussianDivision.
Open Scope Z_scope.

(* ================================================================= *)
(*  §1  divisibility in Z[i]                                          *)
(* ================================================================= *)

Definition ZIdvd (a b : ZI) : Prop := exists c, b = ZImul a c.

Lemma ZIdvd_refl : forall a, ZIdvd a a.
Proof. intro a; exists ZI1; ring. Qed.

Lemma ZIdvd_0_r : forall a, ZIdvd a ZI0.
Proof. intro a; exists ZI0; ring. Qed.

Lemma ZIdvd_mul_r : forall a b c, ZIdvd a b -> ZIdvd a (ZImul c b).
Proof. intros a b c [e He]; exists (ZImul c e); rewrite He; ring. Qed.

Lemma ZIdvd_add : forall a b c, ZIdvd a b -> ZIdvd a c -> ZIdvd a (ZIadd b c).
Proof. intros a b c [e He] [f Hf]; exists (ZIadd e f); rewrite He, Hf; ring. Qed.

Lemma ZIdvd_sub : forall a b c, ZIdvd a b -> ZIdvd a c -> ZIdvd a (ZIsub b c).
Proof. intros a b c [e He] [f Hf]; exists (ZIsub e f); rewrite He, Hf; ring. Qed.

Lemma ZIdvd_trans : forall a b c, ZIdvd a b -> ZIdvd b c -> ZIdvd a c.
Proof. intros a b c [e He] [f Hf]; exists (ZImul e f); rewrite Hf, He; ring. Qed.

Definition ZI_eq_dec : forall a b : ZI, {a = b} + {a <> b}.
Proof. decide equality; apply Z.eq_dec. Defined.

(* ================================================================= *)
(*  §2  BEZOUT / gcd via well-founded induction on the norm          *)
(* ================================================================= *)

Theorem ZI_bezout : forall y x, exists g,
     (ZIdvd g x /\ ZIdvd g y)
  /\ (exists u v, g = ZIadd (ZImul u x) (ZImul v y))
  /\ (forall c, ZIdvd c x -> ZIdvd c y -> ZIdvd c g).
Proof.
  intro y; induction y as [y IH] using
    (well_founded_induction (well_founded_ltof _ (fun z => Z.to_nat (ZInorm (-1) z)))).
  intro x.
  destruct (ZI_eq_dec y ZI0) as [->|Hy].
  - (* y = 0 : gcd = x *)
    exists x; repeat split.
    + apply ZIdvd_refl.
    + apply ZIdvd_0_r.
    + exists ZI1, ZI0; ring.
    + intros c Hcx _; exact Hcx.
  - (* y <> 0 : recurse on x mod y *)
    destruct (ZI_euclid x y Hy) as [Hdm Hlt].
    assert (Hltof : ltof _ (fun z => Z.to_nat (ZInorm (-1) z)) (ZImod x y) y).
    { unfold ltof;
        apply (proj1 (Z2Nat.inj_lt _ _ (ZInorm_nonneg (ZImod x y)) (ZInorm_nonneg y)));
        exact Hlt. }
    destruct (IH (ZImod x y) Hltof y) as [g [[Hgy Hgr] [[u [v Huv]] Huniv]]].
    exists g; repeat split.
    + (* g | x : x = q*y + (x mod y) *)
      rewrite Hdm; apply ZIdvd_add; [ apply ZIdvd_mul_r; exact Hgy | exact Hgr ].
    + exact Hgy.
    + (* g = v*x + (u - v*q)*y *)
      exists v, (ZIsub u (ZImul v (ZIdiv x y))).
      rewrite Huv; unfold ZImod; ring.
    + (* universality: c | x, c | y => c | (x mod y) => c | g *)
      intros c Hcx Hcy; apply Huniv; [ exact Hcy | ].
      unfold ZImod; apply ZIdvd_sub; [ exact Hcx | apply ZIdvd_mul_r; exact Hcy ].
Qed.

(* A convenient packaging: the gcd as a common divisor that is a       *)
(* Z[i]-linear combination (hence divisible by every common divisor).  *)
Corollary ZI_gcd_lincomb : forall x y, exists g u v,
  g = ZIadd (ZImul u x) (ZImul v y) /\ ZIdvd g x /\ ZIdvd g y /\
  (forall c, ZIdvd c x -> ZIdvd c y -> ZIdvd c g).
Proof.
  intros x y; destruct (ZI_bezout y x) as [g [[Hgx Hgy] [[u [v Huv]] Huniv]]].
  exists g, u, v; repeat split; assumption.
Qed.

Print Assumptions ZI_bezout.

(* ================================================================= *)
(*  END GaussianGCD.v                                                *)
(*  Divisibility in Z[i] and the Bezout property: every pair x, y has  *)
(*  a gcd g = u*x + v*y dividing both, with every common divisor       *)
(*  dividing g, by well-founded induction on N(y).  The step from      *)
(*  Euclidean domain to Euclid's lemma / unique factorisation.         *)
(*  Closed under the global context (axiom-free).                     *)
(* ================================================================= *)
