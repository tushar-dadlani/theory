(* ================================================================= *)
(*  GaussianPrimes.v                                                 *)
(*                                                                    *)
(*  THE GAUSSIAN-PRIME CLASSIFICATION.                               *)
(*                                                                    *)
(*  The engine: if N(pi) is a rational prime then pi is irreducible   *)
(*  (norm_prime_irreducible).  The three cases over a rational prime:  *)
(*                                                                    *)
(*    - 2 RAMIFIES:  2 = (1+i)(1-i),  and (1+i) is a Gaussian prime    *)
(*      of norm 2.                                                    *)
(*    - p = 1 (mod 4) SPLITS:  p = a^2+b^2 = (a+bi)(a-bi) (Fermat),    *)
(*      with (a+bi) a Gaussian prime of norm p.                       *)
(*    - p = 3 (mod 4) is INERT:  p itself stays a Gaussian prime       *)
(*      (norm p^2), because a factor of norm p would make p a sum of   *)
(*      two squares -- impossible for p = 3 (mod 4).                   *)
(*                                                                    *)
(*  Builds on the Z[i] UFD tower (norm, irreducible) + Fermat's two-   *)
(*  square theorem (TwoSquaresFull).  AXIOM-FREE.                     *)
(* ================================================================= *)

From Stdlib Require Import ZArith Znumtheory Arith Lia.
Require Import GaussianIntegers GaussianDivision GaussianIrreducible
        SumTwoSquares SumTwoSquaresConverse TwoSquaresFull.
Open Scope Z_scope.

Lemma norm_ZI0 : ZInorm (-1) ZI0 = 0.
Proof. reflexivity. Qed.

(* ================================================================= *)
(*  §1  the engine: prime norm  =>  irreducible                       *)
(* ================================================================= *)

Lemma norm_prime_irreducible : forall pi,
  prime (ZInorm (-1) pi) -> ZIirreducible pi.
Proof.
  intros pi Hp; pose proof (prime_ge_2 _ Hp) as Hp2.
  assert (Hpi0 : pi <> ZI0) by (intro Heq; subst pi; rewrite norm_ZI0 in Hp2; lia).
  split; [ rewrite ZIunit_norm; lia | split; [ exact Hpi0 | ] ].
  intros a b Hab.
  assert (Ha : a <> ZI0) by (intro Heq; apply Hpi0; rewrite Hab, Heq; ring).
  assert (Hb : b <> ZI0) by (intro Heq; apply Hpi0; rewrite Hab, Heq; ring).
  pose proof (norm_pos a Ha); pose proof (norm_pos b Hb).
  assert (Hn : ZInorm (-1) a * ZInorm (-1) b = ZInorm (-1) pi)
    by (rewrite Hab; unfold ZImul; symmetry; apply ZInorm_mul).
  assert (Hdvd : (ZInorm (-1) a | ZInorm (-1) pi))
    by (exists (ZInorm (-1) b); rewrite <- Hn; ring).
  destruct (prime_divisors _ Hp _ Hdvd) as [E|[E|[E|E]]];
    first [ left; apply ZIunit_norm; exact E | right; apply ZIunit_norm; nia ].
Qed.

(* ================================================================= *)
(*  §2  2 ramifies                                                    *)
(* ================================================================= *)

Lemma two_ramifies : ZIirreducible (mkZI 1 1).
Proof.
  apply norm_prime_irreducible;
    replace (ZInorm (-1) (mkZI 1 1)) with 2 by reflexivity; exact prime_2.
Qed.

Lemma two_eq : ZtoZI 2 = ZImul (mkZI 1 1) (ZIconj (mkZI 1 1)).
Proof. apply ZIeq; reflexivity. Qed.

(* ================================================================= *)
(*  §3  p = 1 (mod 4) splits                                          *)
(* ================================================================= *)

Lemma prime1_splits : forall p, prime (Z.of_nat p) -> (p mod 4 = 1)%nat ->
  exists a b,
    ZIirreducible (mkZI a b)
    /\ ZInorm (-1) (mkZI a b) = Z.of_nat p
    /\ ZtoZI (Z.of_nat p) = ZImul (mkZI a b) (ZIconj (mkZI a b)).
Proof.
  intros p Hp Hmod.
  destruct (sum2_prime1 p Hp Hmod) as [a [b Hab]].
  exists a, b.
  assert (Hnpi : ZInorm (-1) (mkZI a b) = Z.of_nat p)
    by (rewrite ZInorm_neg1; cbn [zRe zIm]; lia).
  split; [ | split ].
  - apply norm_prime_irreducible; rewrite Hnpi; exact Hp.
  - exact Hnpi.
  - symmetry; unfold ZImul; rewrite ZImulg_conj, Hnpi; reflexivity.
Qed.

(* ================================================================= *)
(*  §4  p = 3 (mod 4) is inert                                        *)
(* ================================================================= *)

Lemma prime3_inert : forall p, prime (Z.of_nat p) -> (p mod 4 = 3)%nat ->
  ZIirreducible (ZtoZI (Z.of_nat p)).
Proof.
  intros p Hp Hmod; pose proof (prime_ge_2 _ Hp) as Hp2.
  assert (HN : ZInorm (-1) (ZtoZI (Z.of_nat p)) = Z.of_nat p * Z.of_nat p)
    by (apply ZInorm_ZtoZI).
  assert (Hp0 : ZtoZI (Z.of_nat p) <> ZI0)
    by (intro Heq; apply (f_equal (ZInorm (-1))) in Heq; rewrite HN, norm_ZI0 in Heq; nia).
  split; [ rewrite ZIunit_norm, HN; nia | split; [ exact Hp0 | ] ].
  intros a b Hab.
  assert (Ha : a <> ZI0) by (intro Heq; apply Hp0; rewrite Hab, Heq; ring).
  assert (Hb : b <> ZI0) by (intro Heq; apply Hp0; rewrite Hab, Heq; ring).
  pose proof (norm_pos a Ha); pose proof (norm_pos b Hb).
  assert (Hn : ZInorm (-1) a * ZInorm (-1) b = Z.of_nat p * Z.of_nat p)
    by (rewrite <- HN, Hab; unfold ZImul; symmetry; apply ZInorm_mul).
  destruct (Z.eq_dec (ZInorm (-1) a) 1) as [Hua|Hna];
    [ left; apply ZIunit_norm; exact Hua | ].
  destruct (Z.eq_dec (ZInorm (-1) b) 1) as [Hub|Hnb];
    [ right; apply ZIunit_norm; exact Hub | ].
  exfalso.
  (* both non-units: some factor has norm p, so p is a sum of two squares *)
  assert (Hsum : sum2 (Z.of_nat p)).
  { assert (Hpab : (Z.of_nat p | ZInorm (-1) a * ZInorm (-1) b))
      by (rewrite Hn; exists (Z.of_nat p); ring).
    destruct (prime_mult (Z.of_nat p) Hp _ _ Hpab) as [Hpa|Hpb].
    - (* p | N a  =>  N a = p *)
      destruct Hpa as [k Hk].
      assert (Hk1 : k * ZInorm (-1) b = Z.of_nat p) by nia.
      assert (Hkdiv : (k | Z.of_nat p)) by (exists (ZInorm (-1) b); nia).
      assert (Hkval : k = 1) by (destruct (prime_divisors _ Hp _ Hkdiv) as [?|[?|[?|?]]]; nia).
      assert (Hap : ZInorm (-1) a = Z.of_nat p) by nia.
      exists (zRe a), (zIm a); rewrite <- Hap, ZInorm_neg1; ring.
    - (* p | N b  =>  N b = p *)
      destruct Hpb as [k Hk].
      assert (Hk1 : k * ZInorm (-1) a = Z.of_nat p) by nia.
      assert (Hkdiv : (k | Z.of_nat p)) by (exists (ZInorm (-1) a); nia).
      assert (Hkval : k = 1) by (destruct (prime_divisors _ Hp _ Hkdiv) as [?|[?|[?|?]]]; nia).
      assert (Hbp : ZInorm (-1) b = Z.of_nat p) by nia.
      exists (zRe b), (zIm b); rewrite <- Hbp, ZInorm_neg1; ring. }
  (* sum2 p  =>  q3even p, but p = 3 (mod 4) prime divides itself to odd power *)
  pose proof (proj1 (two_squares_iff (Z.of_nat p) ltac:(lia)) Hsum) as Hq3.
  assert (Heven1 : Nat.Even 1).
  { apply (Hq3 p Hp Hmod 1%nat 1).
    - change (Z.of_nat 1) with 1; rewrite Z.pow_1_r; ring.
    - intro Hdiv; pose proof (Z.divide_pos_le _ 1 ltac:(lia) Hdiv); lia. }
  destruct Heven1 as [m Hm]; lia.
Qed.

(* ================================================================= *)
(*  §5  MASTER: the classification of rational primes in Z[i]         *)
(* ================================================================= *)

Theorem gaussian_prime_classification :
  (* engine *)
  (forall pi, prime (ZInorm (-1) pi) -> ZIirreducible pi)
  (* 2 ramifies *)
  /\ ZIirreducible (mkZI 1 1) /\ ZtoZI 2 = ZImul (mkZI 1 1) (ZIconj (mkZI 1 1))
  (* p = 1 mod 4 splits into two Gaussian primes of norm p *)
  /\ (forall p, prime (Z.of_nat p) -> (p mod 4 = 1)%nat ->
        exists a b, ZIirreducible (mkZI a b) /\ ZInorm (-1) (mkZI a b) = Z.of_nat p
                    /\ ZtoZI (Z.of_nat p) = ZImul (mkZI a b) (ZIconj (mkZI a b)))
  (* p = 3 mod 4 stays inert *)
  /\ (forall p, prime (Z.of_nat p) -> (p mod 4 = 3)%nat ->
        ZIirreducible (ZtoZI (Z.of_nat p))).
Proof.
  split; [ exact norm_prime_irreducible | ].
  split; [ exact two_ramifies | ].
  split; [ exact two_eq | ].
  split; [ exact prime1_splits | exact prime3_inert ].
Qed.

Print Assumptions gaussian_prime_classification.

(* ================================================================= *)
(*  END GaussianPrimes.v                                             *)
(*  The Gaussian-prime classification: N(pi) prime => pi irreducible; *)
(*  2 = (1+i)(1-i) ramifies; p = 1 mod 4 splits as (a+bi)(a-bi)       *)
(*  (Fermat); p = 3 mod 4 stays inert (a factor of norm p would make   *)
(*  p a sum of two squares).  Closed under the global context.        *)
(* ================================================================= *)
