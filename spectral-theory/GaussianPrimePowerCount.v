(* ================================================================= *)
(*  GaussianPrimePowerCount.v                                        *)
(*                                                                    *)
(*  Toward the PRIME-POWER COUNTS of r2 via Z[i]:                     *)
(*                                                                    *)
(*      r2(2^k)   = 4,                                               *)
(*      r2(p^k)   = 4*(k+1)         (p = 1 mod 4),                   *)
(*      r2(p^k)   = 4*[k even]      (p = 3 mod 4).                   *)
(*                                                                    *)
(*  These three values determine the general Jacobi identity          *)
(*  r2(n) = 4*S(n) (both sides multiplicative).                      *)
(*                                                                    *)
(*  THIS FILE (part 1): the SHARED MACHINERY every case needs --      *)
(*  Gaussian powers ZIpow and their norm, extraction of an            *)
(*  irreducible factor, and the prime-power divisibility lemma        *)
(*  (irreducible pi | a^m => pi | a).  Built on the Z[i] UFD tower.   *)
(*  AXIOM-FREE.                                                       *)
(* ================================================================= *)

From Stdlib Require Import ZArith Znumtheory Arith Lia List Bool.
Require Import GaussianIntegers GaussianDivision GaussianGCD GaussianIrreducible
        GaussianFactorization GaussianPrimes.
Import ListNotations.
Open Scope Z_scope.

Lemma norm_ZI0 : ZInorm (-1) ZI0 = 0.
Proof. reflexivity. Qed.

(* ================================================================= *)
(*  §1  Gaussian powers                                              *)
(* ================================================================= *)

Fixpoint ZIpow (a : ZI) (m : nat) : ZI :=
  match m with O => ZI1 | S m' => ZImul a (ZIpow a m') end.

Lemma ZIpow_S : forall a m, ZIpow a (S m) = ZImul a (ZIpow a m).
Proof. reflexivity. Qed.

Lemma ZIpow_add : forall a m n, ZIpow a (m + n) = ZImul (ZIpow a m) (ZIpow a n).
Proof.
  intros a m n; induction m as [|m IH]; simpl; [ ring | rewrite IH; ring ].
Qed.

Lemma ZIpow_norm : forall a m, ZInorm (-1) (ZIpow a m) = (ZInorm (-1) a) ^ Z.of_nat m.
Proof.
  intros a m; induction m as [|m IH].
  - simpl; rewrite ZInorm_1; reflexivity.
  - rewrite ZIpow_S; unfold ZImul; rewrite ZInorm_mul, IH.
    rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia; reflexivity.
Qed.

Lemma ZIpow_nonzero : forall a m, a <> ZI0 -> ZIpow a m <> ZI0.
Proof.
  intros a m Ha Heq.
  assert (Hn : ZInorm (-1) (ZIpow a m) = 0) by (rewrite Heq; apply norm_ZI0).
  rewrite ZIpow_norm in Hn.
  pose proof (norm_pos a Ha) as Hp.
  assert (0 < (ZInorm (-1) a) ^ Z.of_nat m) by (apply Z.pow_pos_nonneg; lia).
  lia.
Qed.

(* ================================================================= *)
(*  §2  extraction of an irreducible factor                          *)
(* ================================================================= *)

Lemma irr_factor_exists : forall z, z <> ZI0 -> ~ ZIunit z ->
  exists pi, ZIirreducible pi /\ ZIdvd pi z.
Proof.
  intros z Hz Hu.
  destruct (factor_exists z Hz Hu) as [l [Hall Hprod]].
  destruct l as [|pi t].
  - (* empty product would make z = 1, a unit -- contradiction *)
    simpl in Hprod; exfalso; apply Hu; rewrite Hprod; exists ZI1; ring.
  - exists pi; split.
    + apply Hall; left; reflexivity.
    + exists (ZIprod t); rewrite Hprod; reflexivity.
Qed.

(* ================================================================= *)
(*  §3  prime-power divisibility:  pi | a^m  =>  pi | a              *)
(* ================================================================= *)

Lemma irr_not_dvd_unit : forall pi u, ZIirreducible pi -> ZIunit u -> ~ ZIdvd pi u.
Proof.
  intros pi u [Hnu [_ _]] [w Hw] [c Hc].
  (* pi | u and u*w = 1  =>  pi | 1  =>  pi is a unit, contra *)
  apply Hnu; exists (ZImul c w).
  replace (ZImul pi (ZImul c w)) with (ZImul (ZImul pi c) w) by ring.
  rewrite <- Hc; exact Hw.
Qed.

Lemma prime_pow_dvd : forall pi a m,
  ZIirreducible pi -> ZIdvd pi (ZIpow a m) -> ZIdvd pi a.
Proof.
  intros pi a m Hpi; induction m as [|m IH]; intro Hd.
  - (* pi | a^0 = 1 : impossible *)
    exfalso; apply (irr_not_dvd_unit pi ZI1 Hpi); [ exists ZI1; ring | exact Hd ].
  - rewrite ZIpow_S in Hd.
    destruct (ZI_euclid_lemma pi a (ZIpow a m) Hpi Hd) as [H|H];
      [ exact H | apply IH; exact H ].
Qed.

(* ================================================================= *)
(*  §4  norm of an irreducible factor of a rational-prime power       *)
(* ================================================================= *)

(* If pi is irreducible and pi | (ZtoZI p)^k with p a rational prime,   *)
(* then pi divides ZtoZI p.  (Peels the power down to the base.)        *)
Lemma irr_dvd_ratprime_pow : forall pi p k,
  ZIirreducible pi -> ZIdvd pi (ZIpow (ZtoZI (Z.of_nat p)) k) ->
  ZIdvd pi (ZtoZI (Z.of_nat p)).
Proof.
  intros pi p k Hpi Hd; apply (prime_pow_dvd pi (ZtoZI (Z.of_nat p)) k Hpi Hd).
Qed.

Print Assumptions prime_pow_dvd.

(* ================================================================= *)
(*  END GaussianPrimePowerCount.v (part 1: shared machinery)         *)
(*  Gaussian powers ZIpow (norm N(a^m)=(N a)^m, nonzero), extraction  *)
(*  of an irreducible factor (irr_factor_exists), and prime-power     *)
(*  divisibility pi | a^m => pi | a (prime_pow_dvd) via Euclid's       *)
(*  lemma.  The reusable base for the three prime-power counts of r2.  *)
(*  Closed under the global context (axiom-free).                     *)
(* ================================================================= *)
