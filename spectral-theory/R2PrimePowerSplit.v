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
        GaussianPrimes GaussianPrimePowerCount GaussianFactorization
        GaussianNormCount R2Count R2PrimePower.
Import ListNotations.
Open Scope Z_scope.

(* a prime is never a perfect square *)
Lemma prime_not_sq : forall q, prime q -> forall c, q <> c * c.
Proof.
  intros q Hq c E; pose proof (prime_ge_2 _ Hq) as H2.
  assert (Hdvd : (c | q)) by (exists c; rewrite E; ring).
  destruct (prime_divisors q Hq c Hdvd) as [E1|[E1|[E1|E1]]]; subst c; nia.
Qed.

(* ================================================================= *)
(*  Generic helpers (norm-count of an explicit list; products)        *)
(* ================================================================= *)

Lemma ZInorm_ZImul : forall x y,
  ZInorm (-1) (ZImul x y) = ZInorm (-1) x * ZInorm (-1) y.
Proof. intros x y; unfold ZImul; apply ZInorm_mul. Qed.

Lemma ZImul_nonzero : forall x y, x <> ZI0 -> y <> ZI0 -> ZImul x y <> ZI0.
Proof. intros x y Hx Hy Heq; apply Hy; exact (ZI_no_zero_div x y Heq Hx). Qed.

Lemma length_list_prod : forall (X Y : Type) (l1 : list X) (l2 : list Y),
  length (list_prod l1 l2) = (length l1 * length l2)%nat.
Proof.
  intros X Y l1 l2; induction l1 as [|a l1 IH]; simpl; [ reflexivity | ].
  rewrite length_app, length_map, IH; reflexivity.
Qed.

(* if the norm-n elements are exactly the (NoDup) list L, r2 n = |L| *)
Lemma count_eq_list : forall n L, NoDup L ->
  (forall x, ZInorm (-1) x = n <-> In x L) -> r2 n = length L.
Proof.
  intros n L HND Hchar; rewrite r2_as_gnorm.
  apply Permutation_length, NoDup_Permutation.
  - apply NoDup_filter, gbox_NoDup.
  - exact HND.
  - intro x; rewrite filter_In, Z.eqb_eq; split.
    + intros [_ Hn]; apply Hchar; exact Hn.
    + intro Hin.
      assert (Hn : ZInorm (-1) x = n) by (apply Hchar; exact Hin).
      split; [ | exact Hn ].
      pose proof (in_gbox_of_norm_le x x (Z.le_refl _)) as Hbox.
      rewrite Hn in Hbox; exact Hbox.
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

(* ================================================================= *)
(*  §3  the base elements  q0^i * q1^(k-i)  and their distinctness    *)
(* ================================================================= *)

Definition base (k i : nat) : ZI := ZImul (ZIpow q0 i) (ZIpow q1 (k - i)).

Lemma base_nonzero : forall k i, base k i <> ZI0.
Proof.
  intros k i; apply ZImul_nonzero; apply ZIpow_nonzero; [ apply Hq0_0 | apply Hq1_0 ].
Qed.

Lemma base_norm : forall k i, (i <= k)%nat ->
  ZInorm (-1) (base k i) = (Z.of_nat p) ^ (Z.of_nat k).
Proof.
  intros k i Hik; unfold base.
  rewrite ZInorm_ZImul, !ZIpow_norm, HN0, HN1, <- Z.pow_add_r by lia.
  rewrite <- Nat2Z.inj_add; f_equal; lia.
Qed.

(* the crux: distinct exponents give non-associate (indeed unequal even    *)
(* after any unit twist) products, because q0 and q1 are not associates.   *)
Lemma base_distinct : forall k i i' v w, (i < i')%nat -> (i' <= k)%nat ->
  ZIunit v -> ZIunit w -> ZImul v (base k i) <> ZImul w (base k i').
Proof.
  intros k i i' v w Hlt Hik Hv Hw Heq.
  set (d := (i' - i)%nat).
  assert (Hd1 : (1 <= d)%nat) by lia.
  assert (E0 : ZIpow q0 i' = ZImul (ZIpow q0 i) (ZIpow q0 d))
    by (rewrite <- ZIpow_add; f_equal; lia).
  assert (E1 : ZIpow q1 (k - i) = ZImul (ZIpow q1 (k - i')) (ZIpow q1 d))
    by (rewrite <- ZIpow_add; f_equal; lia).
  unfold base in Heq; rewrite E0, E1 in Heq.
  set (A := ZImul (ZIpow q0 i) (ZIpow q1 (k - i'))).
  assert (HA0 : A <> ZI0)
    by (apply ZImul_nonzero; apply ZIpow_nonzero; [ apply Hq0_0 | apply Hq1_0 ]).
  (* cancel A: v*q1^d = w*q0^d *)
  assert (Hcanc : ZImul A (ZImul v (ZIpow q1 d)) = ZImul A (ZImul w (ZIpow q0 d))).
  { transitivity (ZImul v (ZImul (ZIpow q0 i) (ZImul (ZIpow q1 (k - i')) (ZIpow q1 d)))).
    - unfold A; ring.
    - rewrite Heq; unfold A; ring. }
  pose proof (ZImul_cancel_l A _ _ HA0 Hcanc) as Hvw.
  (* q0 | w*q0^d = v*q1^d *)
  assert (Hdvd : ZIdvd q0 (ZImul v (ZIpow q1 d))).
  { rewrite Hvw.
    assert (Hpow : ZIpow q0 d = ZImul q0 (ZIpow q0 (d - 1)))
      by (replace d with (S (d - 1)) at 1 by lia; rewrite ZIpow_S; reflexivity).
    rewrite Hpow; exists (ZImul w (ZIpow q0 (d - 1))); ring. }
  destruct (ZI_euclid_lemma q0 v (ZIpow q1 d) Hirr0 Hdvd) as [Hqv | Hqd].
  - exact (irr_not_dvd_unit q0 v Hirr0 Hv Hqv).
  - apply q0_not_assoc_q1; apply irr_dvd_irr_assoc;
      [ exact Hirr0 | apply Hirr1 | apply (prime_pow_dvd q0 q1 d Hirr0 Hqd) ].
Qed.

(* ================================================================= *)
(*  §4  the explicit list of the 4*(k+1) norm-p^k elements           *)
(* ================================================================= *)

Definition splitlist (k : nat) : list ZI :=
  map (fun iu => ZImul (snd iu) (base k (fst iu)))
      (list_prod (seq 0 (S k)) unit4).

Lemma splitlist_NoDup : forall k, NoDup (splitlist k).
Proof.
  intro k; unfold splitlist; apply Totient.NoDup_map_inj.
  - intros [i u] [i' u'] Hin Hin' Hf.
    apply in_prod_iff in Hin; destruct Hin as [Hi Hu].
    apply in_prod_iff in Hin'; destruct Hin' as [Hi' Hu'].
    apply in_seq in Hi; apply in_seq in Hi'.
    assert (HuU : ZIunit u) by (apply unit4_units; exact Hu).
    assert (Hu'U : ZIunit u') by (apply unit4_units; exact Hu').
    cbn [fst snd] in Hf.
    destruct (Nat.lt_trichotomy i i') as [Hlt|[Heq|Hlt]].
    + exfalso; apply (base_distinct k i i' u u' Hlt ltac:(lia) HuU Hu'U); exact Hf.
    + subst i'.
      assert (u = u').
      { apply (ZImul_cancel_l (base k i) u u' (base_nonzero k i)).
        transitivity (ZImul u (base k i)); [ ring | rewrite Hf; ring ]. }
      subst u'; reflexivity.
    + exfalso; apply (base_distinct k i' i u' u Hlt ltac:(lia) Hu'U HuU); symmetry; exact Hf.
  - apply NoDup_list_prod; [ apply seq_NoDup | apply unit4_NoDup ].
Qed.

Lemma splitlist_char : forall k x,
  In x (splitlist k) <-> ZInorm (-1) x = (Z.of_nat p) ^ (Z.of_nat k).
Proof.
  intros k x; unfold splitlist; rewrite in_map_iff; split.
  - intros [[i u] [Hxeq Hin]]; cbn [fst snd] in Hxeq.
    apply in_prod_iff in Hin; destruct Hin as [Hi Hu]; apply in_seq in Hi.
    subst x; rewrite ZInorm_ZImul, (proj1 (ZIunit_norm u) (unit4_units u Hu)),
      (base_norm k i ltac:(lia)); ring.
  - intro Hn.
    destruct (decomp_p1 x k Hn) as [u [i [Hu [Hik Hxd]]]].
    exists (i, u); cbn [fst snd]; split.
    + rewrite Hxd; unfold base; reflexivity.
    + apply in_prod_iff; split; [ apply in_seq; lia | apply unit_in_unit4; exact Hu ].
Qed.

Lemma r2_1pow_sec : forall k,
  r2 ((Z.of_nat p) ^ (Z.of_nat k)) = (4 * S k)%nat.
Proof.
  intro k.
  rewrite (count_eq_list _ (splitlist k) (splitlist_NoDup k)
             (fun x => iff_sym (splitlist_char k x))).
  unfold splitlist; rewrite length_map, length_list_prod, length_seq.
  change (length unit4) with 4%nat; lia.
Qed.

End SplitCount.

(* ================================================================= *)
(*  §5  MASTER: the split prime-power count                          *)
(* ================================================================= *)

Theorem r2_1pow : forall p k, prime (Z.of_nat p) -> (p mod 4 = 1)%nat ->
  r2 ((Z.of_nat p) ^ (Z.of_nat k)) = (4 * (k + 1))%nat.
Proof.
  intros p k Hp Hmod.
  destruct (prime1_splits p Hp Hmod) as [a [b [Hirr [HN Hfact]]]].
  rewrite (r2_1pow_sec p a b Hp Hmod Hirr HN Hfact k); lia.
Qed.

Print Assumptions r2_1pow.

(* ================================================================= *)
(*  END R2PrimePowerSplit.v                                          *)
(*  Milestone B: r2(p^k) = 4*(k+1) for p = 1 (mod 4), via the split   *)
(*  p = q0*q1 into distinct conjugate Gaussian primes.  Every norm-   *)
(*  p^k element is unit * q0^i * q1^(k-i) (decomp_p1); the 4*(k+1)     *)
(*  such elements are distinct because q0, q1 are not associates      *)
(*  (q0_not_assoc_q1) -- distinct exponents cannot coincide even up    *)
(*  to a unit (base_distinct) -- so a NoDup_Permutation count gives    *)
(*  the value.  Closed under the global context (axiom-free).         *)
(* ================================================================= *)
