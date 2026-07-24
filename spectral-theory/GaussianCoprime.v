(* ================================================================= *)
(*  GaussianCoprime.v                                                *)
(*                                                                    *)
(*  THE COPRIME SPLIT in Z[i]: if N(z) = m*n with gcd(m,n) = 1 then   *)
(*  z factors as z = x*y with N(x) = m and N(y) = n.                  *)
(*                                                                    *)
(*  This is the surjectivity core of r2-multiplicativity: a norm-mn   *)
(*  Gaussian integer splits into a norm-m and a norm-n factor.        *)
(*                                                                    *)
(*  Take x = gcd_{Z[i]}(z, m) (ZI_bezout).  Then N(x) | m two ways:    *)
(*    - N(x) | N(z) = mn  and  N(x) | N(m as ZI) = m^2,  so N(x) | m; *)
(*    - CONJUGATING the Bezout identity x = u*z + v*m shows           *)
(*      (m as ZI) | x*conj(x) = ZtoZI(N x), i.e. m | N(x).            *)
(*  Hence N(x) = m, and the cofactor y = z/x has norm n.  AXIOM-FREE. *)
(* ================================================================= *)

From Stdlib Require Import ZArith Znumtheory Arith Lia.
Require Import GaussianIntegers GaussianDivision GaussianGCD GaussianIrreducible.
Open Scope Z_scope.

Lemma norm_ZI0 : ZInorm (-1) ZI0 = 0.
Proof. reflexivity. Qed.

(* ================================================================= *)
(*  §1  nat / Z bridges                                              *)
(* ================================================================= *)

Lemma natdiv_Z : forall (a b : nat), Nat.divide a b -> (Z.of_nat a | Z.of_nat b).
Proof. intros a b [k Hk]; exists (Z.of_nat k); rewrite Hk, Nat2Z.inj_mul; ring. Qed.

Lemma Zdiv_nat : forall (a b : nat), (Z.of_nat a | Z.of_nat b) -> Nat.divide a b.
Proof.
  intros a b H; destruct (Nat.eq_dec a 0) as [->|Ha].
  - destruct H as [z Hz]; simpl in Hz; rewrite Z.mul_0_r in Hz.
    assert (b = 0)%nat by lia; subst; exists 0%nat; reflexivity.
  - apply Nat.Lcm0.mod_divide.
    assert (H0 : Z.of_nat a <> 0) by lia.
    pose proof (proj2 (Z.mod_divide (Z.of_nat b) (Z.of_nat a) H0) H) as Hm.
    rewrite <- Nat2Z.inj_mod in Hm; lia.
Qed.

Lemma Zgcd_of_nat : forall m n,
  Z.of_nat (Nat.gcd m n) = Z.gcd (Z.of_nat m) (Z.of_nat n).
Proof.
  intros m n; apply Z.divide_antisym_nonneg; [ lia | apply Z.gcd_nonneg | | ].
  - apply Z.gcd_greatest; apply natdiv_Z;
      [ apply Nat.gcd_divide_l | apply Nat.gcd_divide_r ].
  - set (g := Z.gcd (Z.of_nat m) (Z.of_nat n)).
    assert (Hg0 : 0 <= g) by apply Z.gcd_nonneg.
    apply (Z.divide_trans _ (Z.of_nat (Z.to_nat g))).
    + rewrite Z2Nat.id by exact Hg0; apply Z.divide_refl.
    + apply natdiv_Z; apply Nat.gcd_greatest;
        apply Zdiv_nat; rewrite Z2Nat.id by exact Hg0;
        [ apply Z.gcd_divide_l | apply Z.gcd_divide_r ].
Qed.

Lemma nat_gcd_Z : forall m n, Nat.gcd m n = 1%nat ->
  Z.gcd (Z.of_nat m) (Z.of_nat n) = 1.
Proof. intros m n H; rewrite <- Zgcd_of_nat, H; reflexivity. Qed.

(* ================================================================= *)
(*  §2  norm / conjugate helpers                                     *)
(* ================================================================= *)

Lemma ZInorm_ZImul : forall x y,
  ZInorm (-1) (ZImul x y) = ZInorm (-1) x * ZInorm (-1) y.
Proof. intros x y; unfold ZImul; apply ZInorm_mul. Qed.

Lemma dvd_norm : forall a b, ZIdvd a b -> (ZInorm (-1) a | ZInorm (-1) b).
Proof. intros a b [c Hc]; exists (ZInorm (-1) c); rewrite Hc, ZInorm_ZImul; ring. Qed.

Lemma ZIconj_ZtoZI : forall a, ZIconj (ZtoZI a) = ZtoZI a.
Proof. intro a; apply ZIeq; reflexivity. Qed.

(* ZtoZI m | ZtoZI k  =>  m | k  (read off the real coordinate) *)
Lemma ZtoZI_dvd : forall m k, ZIdvd (ZtoZI m) (ZtoZI k) -> (m | k).
Proof.
  intros m k [c Hc]; apply (f_equal zRe) in Hc.
  unfold ZtoZI, ZImul, ZImulg in Hc; cbn [zRe zIm] in Hc.
  exists (zRe c); lia.
Qed.

(* x * conj x = ZtoZI (N x) *)
Lemma ZImul_conj_norm : forall x, ZImul x (ZIconj x) = ZtoZI (ZInorm (-1) x).
Proof. intro x; unfold ZImul; apply ZImulg_conj. Qed.

(* ================================================================= *)
(*  §3  THE COPRIME SPLIT                                            *)
(* ================================================================= *)

Lemma gaussian_split : forall m n z, Nat.gcd m n = 1%nat -> (1 <= m)%nat -> (1 <= n)%nat ->
  ZInorm (-1) z = Z.of_nat m * Z.of_nat n ->
  exists x y, ZInorm (-1) x = Z.of_nat m /\ ZInorm (-1) y = Z.of_nat n /\ z = ZImul x y.
Proof.
  intros m n z Hco Hm Hn Hnz.
  set (M := ZtoZI (Z.of_nat m)); set (Nn := ZtoZI (Z.of_nat n)).
  (* z * conj z = M * Nn *)
  assert (Hzz : ZImul z (ZIconj z) = ZImul M Nn).
  { rewrite ZImul_conj_norm, Hnz; unfold M, Nn; apply ZtoZI_mul. }
  (* x = gcd(z, M) with a Bezout witness *)
  destruct (ZI_bezout M z) as [x [[Hxz HxM] [[u [v Hbez]] _]]].
  (* N(x) | m *)
  assert (HNxm : (ZInorm (-1) x | Z.of_nat m)).
  { assert (Hd2 : (ZInorm (-1) x | Z.of_nat m * Z.of_nat m)).
    { pose proof (dvd_norm x M HxM) as HdM; unfold M in HdM;
        rewrite ZInorm_ZtoZI in HdM; exact HdM. }
    assert (Hdmn : (ZInorm (-1) x | Z.of_nat m * Z.of_nat n)).
    { pose proof (dvd_norm x z Hxz) as Hdz; rewrite Hnz in Hdz; exact Hdz. }
    assert (Hgcd : Z.gcd (Z.of_nat m * Z.of_nat m) (Z.of_nat m * Z.of_nat n) = Z.of_nat m).
    { rewrite Z.gcd_mul_mono_l, (nat_gcd_Z m n Hco), Z.abs_eq by lia; ring. }
    rewrite <- Hgcd; apply Z.gcd_greatest; assumption. }
  (* m | N(x) : conjugate the Bezout identity *)
  assert (HmNx : (Z.of_nat m | ZInorm (-1) x)).
  { apply ZtoZI_dvd; fold M.
    rewrite <- ZImul_conj_norm.
    (* conj x = conj u * conj z + conj v * M *)
    assert (Hconjx : ZIconj x
      = ZIadd (ZImul (ZIconj u) (ZIconj z)) (ZImul (ZIconj v) M)).
    { rewrite Hbez, ZIconj_add, !ZIconj_mul; unfold M; rewrite ZIconj_ZtoZI; reflexivity. }
    exists (ZIadd (ZImul (ZImul u (ZIconj u)) Nn)
           (ZIadd (ZImul (ZImul v (ZIconj u)) (ZIconj z))
           (ZIadd (ZImul (ZImul u (ZIconj v)) z)
                  (ZImul (ZImul v (ZIconj v)) M)))).
    rewrite Hbez at 1; rewrite Hconjx.
    transitivity (ZIadd
       (ZImul M (ZIadd (ZImul (ZImul u (ZIconj u)) Nn)
                (ZIadd (ZImul (ZImul v (ZIconj u)) (ZIconj z))
                (ZIadd (ZImul (ZImul u (ZIconj v)) z)
                       (ZImul (ZImul v (ZIconj v)) M)))))
       (ZImul (ZImul u (ZIconj u)) (ZIsub (ZImul z (ZIconj z)) (ZImul M Nn)))).
    - ring.
    - rewrite Hzz.
      replace (ZIsub (ZImul M Nn) (ZImul M Nn)) with ZI0 by ring; ring. }
  (* N(x) = m *)
  assert (HNx : ZInorm (-1) x = Z.of_nat m)
    by (apply Z.divide_antisym_nonneg;
        [ apply ZInorm_nonneg | lia | exact HNxm | exact HmNx ]).
  (* cofactor y = z / x *)
  destruct Hxz as [y Hy].
  assert (HNy : ZInorm (-1) y = Z.of_nat n).
  { assert (Hprod : ZInorm (-1) x * ZInorm (-1) y = Z.of_nat m * Z.of_nat n)
      by (rewrite <- ZInorm_ZImul, <- Hy; exact Hnz).
    rewrite HNx in Hprod; apply (Z.mul_reg_l _ _ (Z.of_nat m)); [ lia | ].
    rewrite Hprod; ring. }
  exists x, y; repeat split; [ exact HNx | exact HNy | exact Hy ].
Qed.

Print Assumptions gaussian_split.

(* ================================================================= *)
(*  END GaussianCoprime.v                                            *)
(*  The coprime split: N(z) = m*n with gcd(m,n)=1 gives z = x*y with  *)
(*  N(x) = m, N(y) = n -- the surjectivity core of r2-multiplicativity.*)
(*  Closed under the global context (axiom-free).                    *)
(* ================================================================= *)
