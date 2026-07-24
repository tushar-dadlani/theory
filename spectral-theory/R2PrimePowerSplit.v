(* ================================================================= *)
(*  R2PrimePowerSplit.v                                              *)
(*                                                                    *)
(*  MILESTONE B: the split prime-power count                         *)
(*                                                                    *)
(*      r2(p^k) = 4*(k+1)      for  p = 1 (mod 4).                    *)
(*                                                                    *)
(*  For p = 1 (mod 4), p = a^2+b^2 = q0 * q1 with q0 = a+bi and its    *)
(*  conjugate q1 = a-bi TWO DISTINCT (non-associate) Gaussian primes   *)
(*  of norm p.  A norm-p^k element is uniquely (up to the 4 units)     *)
(*      z = unit * q0^i * q1^(k-i),   0 <= i <= k,                    *)
(*  giving 4*(k+1) elements, all distinct because q0 and q1 are not    *)
(*  associates (else p would be a square or twice a square).          *)
(*                                                                    *)
(*  This file (part 1): the non-associate lemma and the DECOMPOSITION. *)
(*  Built on the Z[i] UFD tower + R2PrimePower.  AXIOM-FREE.          *)
(* ================================================================= *)

From Stdlib Require Import ZArith Znumtheory Arith Lia List Bool Wf_nat Permutation.
Require Import GaussianIntegers GaussianDivision GaussianGCD GaussianIrreducible
        GaussianPrimes GaussianPrimePowerCount GaussianNormCount R2Count R2PrimePower.
Import ListNotations.
Open Scope Z_scope.

(* a prime is never a perfect square *)
Lemma prime_not_sq : forall q, prime q -> forall c, q <> c * c.
Proof.
  intros q Hq c E; pose proof (prime_ge_2 _ Hq) as H2.
  assert (Hdvd : (c | q)) by (exists c; rewrite E; ring).
  destruct (prime_divisors q Hq c Hdvd) as [E1|[E1|[E1|E1]]]; subst c; nia.
Qed.

Section SplitCount.

Variable p : nat.
Variables a b : Z.
Hypothesis Hp : prime (Z.of_nat p).
Hypothesis Hmod : (p mod 4 = 1)%nat.
Hypothesis Hirr0 : ZIirreducible (mkZI a b).
Hypothesis HN0 : ZInorm (-1) (mkZI a b) = Z.of_nat p.
Hypothesis Hfact : ZtoZI (Z.of_nat p) = ZImul (mkZI a b) (ZIconj (mkZI a b)).

Local Notation q0 := (mkZI a b).
Local Notation q1 := (ZIconj (mkZI a b)).

Lemma HP2 : 2 <= Z.of_nat p.
Proof. pose proof (prime_ge_2 _ Hp); lia. Qed.

Lemma HN1 : ZInorm (-1) q1 = Z.of_nat p.
Proof. rewrite ZInorm_conj; exact HN0. Qed.

Lemma Hq0_0 : q0 <> ZI0.
Proof. intro Heq; rewrite Heq, norm_ZI0 in HN0; pose proof HP2; lia. Qed.

Lemma Hq1_0 : q1 <> ZI0.
Proof. intro Heq; pose proof HN1 as H; rewrite Heq, norm_ZI0 in H; pose proof HP2; lia. Qed.

Lemma Hirr1 : ZIirreducible q1.
Proof. apply norm_prime_irreducible; rewrite HN1; exact Hp. Qed.

(* ================================================================= *)
(*  §1  q0 and q1 = conj q0 are NOT associates                       *)
(* ================================================================= *)

Lemma q0_not_assoc_q1 : ~ ZIassoc q0 q1.
Proof.
  intros [u [Hu Heq]].
  (* p is odd: p = 4*(p/4) + 1 *)
  assert (Hpodd : Z.of_nat p = 4 * Z.of_nat (p / 4) + 1).
  { pose proof (Nat.div_mod_eq p 4) as Hdm; rewrite Hmod in Hdm.
    rewrite Hdm at 1; rewrite Nat2Z.inj_add, Nat2Z.inj_mul; simpl; ring. }
  pose proof HN0 as HNab; rewrite ZInorm_neg1 in HNab; cbn [zRe zIm] in HNab.
  destruct (ZIunit_cases u Hu) as [E|[E|[E|E]]]; rewrite E in Heq;
    (* extract the two coordinate equations, normalised *)
    assert (Hr := f_equal zRe Heq); assert (Hi := f_equal zIm Heq);
    cbn [zRe zIm ZImul ZImulg ZIconj ZI1 ZIopp ZIi] in Hr, Hi;
    ring_simplify in Hr; ring_simplify in Hi.
  - (* u = 1 : -b = b, so b = 0, p = a^2 *)
    assert (b = 0) by lia; subst b.
    apply (prime_not_sq (Z.of_nat p) Hp a); nia.
  - (* u = -1 : a = -a, so a = 0, p = b^2 *)
    assert (a = 0) by lia; subst a.
    apply (prime_not_sq (Z.of_nat p) Hp b); nia.
  - (* u = i : a = -b, so p = 2b^2 (even), contra p odd *)
    assert (a = - b) by lia; subst a; nia.
  - (* u = -i : a = b, so p = 2a^2 (even), contra p odd *)
    assert (a = b) by lia; subst a; nia.
Qed.

(* ================================================================= *)
(*  §2  DECOMPOSITION:  N(z) = p^k  =>  z = unit * q0^i * q1^(k-i)    *)
(* ================================================================= *)

Lemma decomp_p1 : forall z k, ZInorm (-1) z = (Z.of_nat p) ^ (Z.of_nat k) ->
  exists u i, ZIunit u /\ (i <= k)%nat
              /\ z = ZImul u (ZImul (ZIpow q0 i) (ZIpow q1 (k - i))).
Proof.
  pose proof HP2 as HP2'.
  intro z; revert z.
  induction z as [z IH] using
    (well_founded_induction (well_founded_ltof _ (fun w => Z.to_nat (ZInorm (-1) w)))).
  intros k Hn.
  assert (Hpk_pos : 0 < (Z.of_nat p) ^ Z.of_nat k) by (apply Z.pow_pos_nonneg; lia).
  assert (Hz0 : z <> ZI0) by (intro Heq; subst z; rewrite norm_ZI0 in Hn; lia).
  destruct (Z.eq_dec (ZInorm (-1) z) 1) as [Hu1 | Hnu1].
  - (* unit : k = 0 *)
    exists z, 0%nat; repeat split.
    + apply ZIunit_norm; exact Hu1.
    + lia.
    + rewrite Hu1 in Hn.
      assert (Z.of_nat k = 0).
      { destruct (Z.eq_dec (Z.of_nat k) 0) as [E|E]; [ exact E | exfalso ].
        pose proof (proj1 (Z.pow_gt_1 (Z.of_nat p) (Z.of_nat k) ltac:(lia)) ltac:(lia)); lia. }
      assert (k = 0)%nat by lia; subst k; simpl; ring.
  - (* non-unit : peel a prime factor, associate to q0 or q1 *)
    assert (Hznu : ~ ZIunit z) by (rewrite ZIunit_norm; exact Hnu1).
    destruct (irr_factor_exists z Hz0 Hznu) as [pi [Hpi Hpiz]].
    (* pi | z*conj z = (q0*q1)^k = q0^k * q1^k *)
    assert (Hzz : ZImul (ZIpow q0 k) (ZIpow q1 k) = ZImul z (ZIconj z)).
    { rewrite <- ZIpow_mul_distr, <- Hfact, <- ZtoZI_pow, <- Hn.
      unfold ZImul; rewrite (ZImulg_conj (-1) z); reflexivity. }
    assert (Hpik : ZIdvd pi (ZImul (ZIpow q0 k) (ZIpow q1 k))).
    { rewrite Hzz.
      replace (ZImul z (ZIconj z)) with (ZImul (ZIconj z) z) by ring.
      apply ZIdvd_mul_r; exact Hpiz. }
    (* pi | q0 or pi | q1 *)
    assert (Hbase : ZIdvd pi q0 \/ ZIdvd pi q1).
    { destruct (ZI_euclid_lemma pi (ZIpow q0 k) (ZIpow q1 k) Hpi Hpik) as [H|H];
        [ left; apply (prime_pow_dvd pi q0 k Hpi H)
        | right; apply (prime_pow_dvd pi q1 k Hpi H) ]. }
    (* in either case k >= 1 and z = base * w with N(w) = p^(k-1) *)
    assert (Hk1 : (1 <= k)%nat).
    { destruct k as [|k']; [ | lia ].
      rewrite Z.pow_0_r in Hn; exfalso; apply Hnu1; exact Hn. }
    destruct Hbase as [Hb0 | Hb1].
    + (* pi ~ q0, so q0 | z *)
      assert (Hq0z : ZIdvd q0 z)
        by (apply (assoc_dvd_r pi q0 z);
            [ apply irr_dvd_irr_assoc; [ exact Hpi | exact Hirr0 | exact Hb0 ] | exact Hpiz ]).
      destruct Hq0z as [w Hw].
      assert (Hw0 : w <> ZI0) by (intro Heq; apply Hz0; rewrite Hw, Heq; ring).
      assert (Hnorms : (Z.of_nat p) ^ Z.of_nat k = Z.of_nat p * ZInorm (-1) w).
      { rewrite <- Hn, Hw; unfold ZImul at 1; rewrite ZInorm_mul, HN0; reflexivity. }
      assert (HNw_eq : ZInorm (-1) w = (Z.of_nat p) ^ Z.of_nat (k - 1)).
      { apply (Z.mul_reg_l _ _ (Z.of_nat p)); [ lia | ].
        rewrite <- Hnorms; replace (Z.of_nat k) with (1 + Z.of_nat (k - 1)) by lia.
        rewrite Z.pow_add_r by lia; ring. }
      assert (Hlt : ltof _ (fun w => Z.to_nat (ZInorm (-1) w)) w z).
      { unfold ltof; apply (proj1 (Z2Nat.inj_lt _ _ (ZInorm_nonneg w) (ZInorm_nonneg z))).
        rewrite Hn, HNw_eq; replace (Z.of_nat k) with (1 + Z.of_nat (k - 1)) by lia.
        rewrite Z.pow_add_r by lia; nia. }
      destruct (IH w Hlt (k - 1)%nat HNw_eq) as [u [i [Hu [Hik Hwd]]]].
      exists u, (S i); repeat split; [ exact Hu | lia | ].
      rewrite Hw, Hwd, ZIpow_S.
      replace (k - S i)%nat with (k - 1 - i)%nat by lia; ring.
    + (* pi ~ q1, so q1 | z *)
      assert (Hq1z : ZIdvd q1 z)
        by (apply (assoc_dvd_r pi q1 z);
            [ apply irr_dvd_irr_assoc; [ exact Hpi | exact Hirr1 | exact Hb1 ] | exact Hpiz ]).
      destruct Hq1z as [w Hw].
      assert (Hw0 : w <> ZI0) by (intro Heq; apply Hz0; rewrite Hw, Heq; ring).
      assert (Hnorms : (Z.of_nat p) ^ Z.of_nat k = Z.of_nat p * ZInorm (-1) w).
      { rewrite <- Hn, Hw; unfold ZImul at 1; rewrite ZInorm_mul, HN1; reflexivity. }
      assert (HNw_eq : ZInorm (-1) w = (Z.of_nat p) ^ Z.of_nat (k - 1)).
      { apply (Z.mul_reg_l _ _ (Z.of_nat p)); [ lia | ].
        rewrite <- Hnorms; replace (Z.of_nat k) with (1 + Z.of_nat (k - 1)) by lia.
        rewrite Z.pow_add_r by lia; ring. }
      assert (Hlt : ltof _ (fun w => Z.to_nat (ZInorm (-1) w)) w z).
      { unfold ltof; apply (proj1 (Z2Nat.inj_lt _ _ (ZInorm_nonneg w) (ZInorm_nonneg z))).
        rewrite Hn, HNw_eq; replace (Z.of_nat k) with (1 + Z.of_nat (k - 1)) by lia.
        rewrite Z.pow_add_r by lia; nia. }
      destruct (IH w Hlt (k - 1)%nat HNw_eq) as [u [i [Hu [Hik Hwd]]]].
      exists u, i; repeat split; [ exact Hu | lia | ].
      rewrite Hw, Hwd.
      replace (k - i)%nat with (S (k - 1 - i)) by lia.
      rewrite ZIpow_S; ring.
Qed.

End SplitCount.

Print Assumptions decomp_p1.
