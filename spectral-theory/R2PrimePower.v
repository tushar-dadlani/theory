(* ================================================================= *)
(*  R2PrimePower.v                                                   *)
(*                                                                    *)
(*  THE PRIME-POWER STRUCTURE of norm-p^k Gaussian integers, toward   *)
(*  the r2 prime-power counts                                        *)
(*                                                                    *)
(*      r2(2^k)   = 4,                                               *)
(*      r2(p^k)   = 4*(k+1)         (p = 1 mod 4),                   *)
(*      r2(p^k)   = 4*[k even]      (p = 3 mod 4).                   *)
(*                                                                    *)
(*  This file (Milestone A): the shared associate/unit/power helpers  *)
(*  and the DECOMPOSITION lemmas for the "single prime family" cases   *)
(*  p = 3 (mod 4) (inert) and p = 2 (ramified):                      *)
(*                                                                    *)
(*    p = 3:  N(z) = p^k  =>  z = unit * (ZtoZI p)^j  with  k = 2j.   *)
(*    p = 2:  N(z) = 2^k  =>  z = unit * (1+i)^k.                     *)
(*                                                                    *)
(*  Every irreducible factor of such a z is (via z*conj z = base^k     *)
(*  and prime_pow_dvd) an associate of the single Gaussian prime over  *)
(*  p, so z is a unit times a power of it.  AXIOM-FREE.               *)
(* ================================================================= *)

From Stdlib Require Import ZArith Znumtheory Arith Lia List Bool Wf_nat Permutation.
Require Import GaussianIntegers GaussianDivision GaussianGCD GaussianIrreducible
        GaussianPrimes GaussianPrimePowerCount GaussianFactorization
        GaussianNormCount R2Count.
Import ListNotations.
Open Scope Z_scope.

(* ================================================================= *)
(*  §1  unit and power helpers                                       *)
(* ================================================================= *)

Lemma ZIunit_1 : ZIunit ZI1.
Proof. exists ZI1; ring. Qed.

Lemma ZIunit_mul : forall u v, ZIunit u -> ZIunit v -> ZIunit (ZImul u v).
Proof.
  intros u v [a Ha] [b Hb]; exists (ZImul b a).
  replace (ZImul (ZImul u v) (ZImul b a)) with (ZImul (ZImul u a) (ZImul v b)) by ring.
  rewrite Ha, Hb; ring.
Qed.

Lemma ZIunit_i : ZIunit ZIi.
Proof. exists (ZIopp ZIi); apply ZIeq; reflexivity. Qed.

Lemma ZIunit_pow : forall u m, ZIunit u -> ZIunit (ZIpow u m).
Proof.
  intros u m Hu; induction m as [|m IH]; simpl;
    [ apply ZIunit_1 | apply ZIunit_mul; [ exact Hu | exact IH ] ].
Qed.

Lemma ZIpow_mul_distr : forall a b m,
  ZIpow (ZImul a b) m = ZImul (ZIpow a m) (ZIpow b m).
Proof.
  intros a b m; induction m as [|m IH]; simpl; [ ring | rewrite IH; ring ].
Qed.

(* dividing out a unit factor *)
Lemma dvd_unit_mul_r : forall pi u w, ZIunit u -> ZIdvd pi (ZImul u w) -> ZIdvd pi w.
Proof.
  intros pi u w [v Hv] Hd.
  assert (Hw : w = ZImul v (ZImul u w))
    by (replace (ZImul v (ZImul u w)) with (ZImul (ZImul u v) w) by ring;
        rewrite Hv; ring).
  rewrite Hw; apply ZIdvd_mul_r; exact Hd.
Qed.

(* ================================================================= *)
(*  §2  associate helpers                                            *)
(* ================================================================= *)

(* an irreducible dividing an irreducible is an associate of it *)
Lemma irr_dvd_irr_assoc : forall pi q,
  ZIirreducible pi -> ZIirreducible q -> ZIdvd pi q -> ZIassoc pi q.
Proof.
  intros pi q [Hnpi _] [_ [_ Hfac]] [c Hc].
  destruct (Hfac pi c Hc) as [Hu | Hu];
    [ exfalso; apply Hnpi; exact Hu | exists c; split; [ exact Hu | exact Hc ] ].
Qed.

(* associates divide the same elements *)
Lemma assoc_dvd_r : forall a b z, ZIassoc a b -> ZIdvd a z -> ZIdvd b z.
Proof.
  intros a b z [u [[w Hw] Hb]] [c Hc].
  exists (ZImul w c).
  rewrite Hb.
  replace (ZImul (ZImul a u) (ZImul w c)) with (ZImul (ZImul a c) (ZImul u w)) by ring.
  rewrite Hw, <- Hc; ring.
Qed.

(* ================================================================= *)
(*  §3  z * conj z = (base)^k as a Gaussian integer                  *)
(* ================================================================= *)

Lemma ZtoZI_pow : forall n k, ZtoZI (n ^ Z.of_nat k) = ZIpow (ZtoZI n) k.
Proof.
  intros n k; induction k as [|k IH]; [ reflexivity | ].
  rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
  rewrite ZtoZI_mul, IH; reflexivity.
Qed.

Lemma z_conj_pow : forall z n k, ZInorm (-1) z = n ^ Z.of_nat k ->
  ZImul z (ZIconj z) = ZIpow (ZtoZI n) k.
Proof.
  intros z n k Hn.
  unfold ZImul; rewrite (ZImulg_conj (-1) z); fold (ZInorm (-1) z).
  rewrite Hn, ZtoZI_pow; reflexivity.
Qed.

(* ================================================================= *)
(*  §4  DECOMPOSITION for  p = 3 (mod 4)  (inert)                     *)
(* ================================================================= *)

Lemma decomp_p3 : forall p, prime (Z.of_nat p) -> (p mod 4 = 3)%nat ->
  forall z k, ZInorm (-1) z = (Z.of_nat p) ^ (Z.of_nat k) ->
  exists u j, ZIunit u /\ k = (2 * j)%nat
              /\ z = ZImul u (ZIpow (ZtoZI (Z.of_nat p)) j).
Proof.
  intros p Hp Hmod.
  set (P := Z.of_nat p).
  assert (HP2 : 2 <= P) by (unfold P; pose proof (prime_ge_2 _ Hp); lia).
  intro z; revert z.
  induction z as [z IH] using
    (well_founded_induction (well_founded_ltof _ (fun w => Z.to_nat (ZInorm (-1) w)))).
  intros k Hn.
  assert (Hpk_pos : 0 < P ^ Z.of_nat k) by (apply Z.pow_pos_nonneg; lia).
  assert (Hz0 : z <> ZI0) by (intro Heq; subst z; rewrite norm_ZI0 in Hn; lia).
  destruct (Z.eq_dec (ZInorm (-1) z) 1) as [Hu1 | Hnu1].
  - (* z is a unit: P^k = 1 forces k = 0 *)
    exists z, 0%nat; repeat split.
    + apply ZIunit_norm; exact Hu1.
    + rewrite Hu1 in Hn.
      assert (Z.of_nat k = 0).
      { destruct (Z.eq_dec (Z.of_nat k) 0) as [E|E]; [ exact E | exfalso ].
        pose proof (proj1 (Z.pow_gt_1 P (Z.of_nat k) ltac:(lia)) ltac:(lia)); lia. }
      lia.
    + simpl; ring.
  - (* z not a unit: extract a prime factor, associate to ZtoZI P *)
    assert (Hznu : ~ ZIunit z) by (rewrite ZIunit_norm; exact Hnu1).
    destruct (irr_factor_exists z Hz0 Hznu) as [pi [Hpi Hpiz]].
    (* pi | z*conj z = (ZtoZI P)^k, so pi | ZtoZI P *)
    assert (Hpibase : ZIdvd pi (ZtoZI P)).
    { apply (prime_pow_dvd pi (ZtoZI P) k Hpi).
      rewrite <- (z_conj_pow z P k Hn).
      replace (ZImul z (ZIconj z)) with (ZImul (ZIconj z) z) by ring.
      apply ZIdvd_mul_r; exact Hpiz. }
    (* ZtoZI P is irreducible (inert) *)
    assert (HbaseIrr : ZIirreducible (ZtoZI P)) by (apply prime3_inert; assumption).
    (* pi ~ ZtoZI P, and pi | z, so ZtoZI P | z *)
    assert (Hbasez : ZIdvd (ZtoZI P) z).
    { apply (assoc_dvd_r pi (ZtoZI P) z);
        [ apply irr_dvd_irr_assoc; assumption | exact Hpiz ]. }
    destruct Hbasez as [w Hw].
    (* norms: P^k = N(ZtoZI P) * N(w) = P^2 * N(w) *)
    assert (Hw0 : w <> ZI0) by (intro Heq; apply Hz0; rewrite Hw, Heq; ring).
    pose proof (norm_pos w Hw0) as HNw.
    assert (HNbase : ZInorm (-1) (ZtoZI P) = P * P) by (apply ZInorm_ZtoZI).
    assert (Hnorms : P ^ Z.of_nat k = P * P * ZInorm (-1) w).
    { rewrite <- Hn, Hw; unfold ZImul; rewrite ZInorm_mul, HNbase; reflexivity. }
    (* k >= 2 *)
    assert (Hk2 : (2 <= k)%nat).
    { destruct k as [|[|k]]; [ | | lia ].
      - rewrite Z.pow_0_r in Hnorms; nia.
      - rewrite Z.pow_1_r in Hnorms; nia. }
    (* N(w) = P^(k-2) *)
    assert (HNw_eq : ZInorm (-1) w = P ^ Z.of_nat (k - 2)).
    { apply (Z.mul_reg_l _ _ (P * P)); [ nia | ].
      rewrite <- Hnorms.
      replace (Z.of_nat k) with (2 + Z.of_nat (k - 2)) by lia.
      rewrite Z.pow_add_r by lia; ring. }
    (* recurse on w *)
    assert (Hlt : ltof _ (fun w => Z.to_nat (ZInorm (-1) w)) w z).
    { unfold ltof; apply (proj1 (Z2Nat.inj_lt _ _ (ZInorm_nonneg w) (ZInorm_nonneg z))).
      rewrite Hn, HNw_eq.
      replace (Z.of_nat k) with (2 + Z.of_nat (k - 2)) by lia.
      rewrite Z.pow_add_r by lia; nia. }
    destruct (IH w Hlt (k - 2)%nat HNw_eq) as [u' [j' [Hu' [Hk' Hwd]]]].
    exists u', (S j'); repeat split.
    + exact Hu'.
    + lia.
    + rewrite Hw, Hwd, ZIpow_S; ring.
Qed.

(* ================================================================= *)
(*  §5  DECOMPOSITION for  p = 2  (ramified),  base prime  1+i        *)
(* ================================================================= *)

Lemma ZIunit_negi : ZIunit (ZIopp ZIi).
Proof. exists ZIi; apply ZIeq; reflexivity. Qed.

(* 2 = (-i) * (1+i)^2 *)
Lemma two_eq_sq :
  ZtoZI 2 = ZImul (ZIopp ZIi) (ZImul (mkZI 1 1) (mkZI 1 1)).
Proof. apply ZIeq; reflexivity. Qed.

Lemma decomp_p2 : forall z k, ZInorm (-1) z = 2 ^ (Z.of_nat k) ->
  exists u, ZIunit u /\ z = ZImul u (ZIpow (mkZI 1 1) k).
Proof.
  intro z; revert z.
  induction z as [z IH] using
    (well_founded_induction (well_founded_ltof _ (fun w => Z.to_nat (ZInorm (-1) w)))).
  intros k Hn.
  assert (Hpk_pos : 0 < 2 ^ Z.of_nat k) by (apply Z.pow_pos_nonneg; lia).
  assert (Hz0 : z <> ZI0) by (intro Heq; subst z; rewrite norm_ZI0 in Hn; lia).
  destruct (Z.eq_dec (ZInorm (-1) z) 1) as [Hu1 | Hnu1].
  - (* unit: 2^k = 1 forces k = 0 *)
    exists z; split; [ apply ZIunit_norm; exact Hu1 | ].
    rewrite Hu1 in Hn.
    assert (Z.of_nat k = 0).
    { destruct (Z.eq_dec (Z.of_nat k) 0) as [E|E]; [ exact E | exfalso ].
      pose proof (proj1 (Z.pow_gt_1 2 (Z.of_nat k) ltac:(lia)) ltac:(lia)); lia. }
    assert (k = 0)%nat by lia; subst k; simpl; ring.
  - (* non-unit: prime factor pi ~ (1+i) *)
    assert (Hznu : ~ ZIunit z) by (rewrite ZIunit_norm; exact Hnu1).
    destruct (irr_factor_exists z Hz0 Hznu) as [pi [Hpi Hpiz]].
    (* pi | z*conj z = (ZtoZI 2)^k *)
    assert (Hpi2k : ZIdvd pi (ZIpow (ZtoZI 2) k)).
    { rewrite <- (z_conj_pow z 2 k Hn).
      replace (ZImul z (ZIconj z)) with (ZImul (ZIconj z) z) by ring.
      apply ZIdvd_mul_r; exact Hpiz. }
    (* (ZtoZI 2)^k = unit * ((1+i)^2)^k, so pi | (1+i)^2, hence pi | (1+i) *)
    assert (Hpibb : ZIdvd pi (ZImul (mkZI 1 1) (mkZI 1 1))).
    { apply (prime_pow_dvd pi (ZImul (mkZI 1 1) (mkZI 1 1)) k Hpi).
      apply (dvd_unit_mul_r pi (ZIpow (ZIopp ZIi) k));
        [ apply ZIunit_pow, ZIunit_negi | ].
      rewrite <- ZIpow_mul_distr, <- two_eq_sq; exact Hpi2k. }
    assert (Hpib : ZIdvd pi (mkZI 1 1)).
    { destruct (ZI_euclid_lemma pi (mkZI 1 1) (mkZI 1 1) Hpi Hpibb) as [H|H]; exact H. }
    (* pi ~ (1+i), so (1+i) | z *)
    assert (Hbz : ZIdvd (mkZI 1 1) z).
    { apply (assoc_dvd_r pi (mkZI 1 1) z);
        [ apply irr_dvd_irr_assoc; [ exact Hpi | exact two_ramifies | exact Hpib ]
        | exact Hpiz ]. }
    destruct Hbz as [w Hw].
    assert (Hw0 : w <> ZI0) by (intro Heq; apply Hz0; rewrite Hw, Heq; ring).
    pose proof (norm_pos w Hw0) as HNw.
    assert (HNb : ZInorm (-1) (mkZI 1 1) = 2) by reflexivity.
    assert (Hnorms : 2 ^ Z.of_nat k = 2 * ZInorm (-1) w).
    { rewrite <- Hn, Hw; unfold ZImul; rewrite ZInorm_mul, HNb; reflexivity. }
    assert (Hk1 : (1 <= k)%nat).
    { destruct k as [|k]; [ rewrite Z.pow_0_r in Hnorms; nia | lia ]. }
    assert (HNw_eq : ZInorm (-1) w = 2 ^ Z.of_nat (k - 1)).
    { apply (Z.mul_reg_l _ _ 2); [ lia | ].
      rewrite <- Hnorms; replace (Z.of_nat k) with (1 + Z.of_nat (k - 1)) by lia.
      rewrite Z.pow_add_r by lia; ring. }
    assert (Hlt : ltof _ (fun w => Z.to_nat (ZInorm (-1) w)) w z).
    { unfold ltof; apply (proj1 (Z2Nat.inj_lt _ _ (ZInorm_nonneg w) (ZInorm_nonneg z))).
      rewrite Hn, HNw_eq; replace (Z.of_nat k) with (1 + Z.of_nat (k - 1)) by lia.
      rewrite Z.pow_add_r by lia; nia. }
    destruct (IH w Hlt (k - 1)%nat HNw_eq) as [u' [Hu' Hwd]].
    exists u'; split; [ exact Hu' | ].
    replace k with (S (k - 1)) by lia.
    rewrite Hw, Hwd, ZIpow_S; ring.
Qed.

(* ================================================================= *)
(*  §6  counting infrastructure: the 4 associates                    *)
(* ================================================================= *)

Definition unit4 : list ZI := [ZI1; ZIopp ZI1; ZIi; ZIopp ZIi].
Definition assoc4 (a : ZI) : list ZI := map (ZImul a) unit4.

Lemma unit4_units : forall u, In u unit4 -> ZIunit u.
Proof.
  intros u H; simpl in H; destruct H as [<-|[<-|[<-|[<-|[]]]]].
  - apply ZIunit_1.
  - exists (ZIopp ZI1); apply ZIeq; reflexivity.
  - apply ZIunit_i.
  - apply ZIunit_negi.
Qed.

Lemma unit_in_unit4 : forall u, ZIunit u -> In u unit4.
Proof.
  intros u Hu; destruct (ZIunit_cases u Hu) as [E|[E|[E|E]]]; rewrite E;
    unfold unit4; simpl; tauto.
Qed.

Lemma unit4_NoDup : NoDup unit4.
Proof.
  unfold unit4;
    repeat (apply NoDup_cons;
      [ simpl; intro H; repeat (destruct H as [H|H]);
        solve [ discriminate H | injection H; lia | exact H ] | ]).
  apply NoDup_nil.
Qed.

Lemma assoc4_length : forall a, length (assoc4 a) = 4%nat.
Proof. intro a; unfold assoc4; rewrite length_map; reflexivity. Qed.

Lemma assoc4_NoDup : forall a, a <> ZI0 -> NoDup (assoc4 a).
Proof.
  intros a Ha; unfold assoc4; apply Totient.NoDup_map_inj;
    [ intros x y _ _ H; exact (ZImul_cancel_l a x y Ha H) | apply unit4_NoDup ].
Qed.

Lemma in_assoc4 : forall a x,
  In x (assoc4 a) <-> exists u, ZIunit u /\ x = ZImul a u.
Proof.
  intros a x; unfold assoc4; rewrite in_map_iff; split.
  - intros [u [Hu Hin]]; exists u; split; [ apply unit4_units; exact Hin | symmetry; exact Hu ].
  - intros [u [Hu ->]]; exists u; split; [ reflexivity | apply unit_in_unit4; exact Hu ].
Qed.

(* gbox has no duplicates *)
Lemma zrange_NoDup : forall B, NoDup (zrange B).
Proof.
  intro B; unfold zrange; apply Totient.NoDup_map_inj;
    [ intros x y _ _ H; lia | apply seq_NoDup ].
Qed.

Lemma gbox_NoDup : forall B, NoDup (gbox B).
Proof.
  intro B; unfold gbox; apply Totient.NoDup_map_inj.
  - intros [x1 y1] [x2 y2] _ _ H; cbn [fst snd] in H;
      injection H as Hr Hi; subst; reflexivity.
  - apply NoDup_list_prod; apply zrange_NoDup.
Qed.

Lemma filter_all_false : forall (g : ZI -> bool) l,
  (forall x, In x l -> g x = false) -> filter g l = [].
Proof.
  intros g l; induction l as [|a l IH]; intro H; simpl; [ reflexivity | ].
  rewrite (H a (or_introl eq_refl)); apply IH; intros x Hx; apply H; right; exact Hx.
Qed.

(* ================================================================= *)
(*  §7  the two counts via the norm-characterisation                 *)
(* ================================================================= *)

(* if the norm-n elements are exactly the unit-multiples of a<>0, r2 n = 4 *)
Lemma count_via_assoc4 : forall n a, a <> ZI0 ->
  (forall x, ZInorm (-1) x = n <-> exists u, ZIunit u /\ x = ZImul a u) ->
  r2 n = 4%nat.
Proof.
  intros n a Ha Hchar.
  rewrite r2_as_gnorm.
  transitivity (length (assoc4 a)); [ | apply assoc4_length ].
  apply Permutation_length, NoDup_Permutation.
  - apply NoDup_filter, gbox_NoDup.
  - apply assoc4_NoDup; exact Ha.
  - intro x; rewrite filter_In, Z.eqb_eq; split.
    + intros [_ Hnx]; apply in_assoc4, Hchar; exact Hnx.
    + intro Hin.
      assert (Hnx : ZInorm (-1) x = n) by (apply Hchar, in_assoc4; exact Hin).
      split; [ | exact Hnx ].
      pose proof (in_gbox_of_norm_le x x (Z.le_refl _)) as Hbox.
      rewrite Hnx in Hbox; exact Hbox.
Qed.

(* if no element has norm n, r2 n = 0 *)
Lemma count_empty : forall n, (forall x, ZInorm (-1) x <> n) -> r2 n = 0%nat.
Proof.
  intros n Hno; rewrite r2_as_gnorm.
  rewrite filter_all_false; [ reflexivity | ].
  intros x _; apply Z.eqb_neq, Hno.
Qed.

(* --- p = 2 : r2(2^k) = 4 --- *)
Theorem r2_2pow : forall k, r2 (2 ^ Z.of_nat k) = 4%nat.
Proof.
  intro k.
  apply (count_via_assoc4 _ (ZIpow (mkZI 1 1) k)).
  - apply ZIpow_nonzero; intro H; discriminate H.
  - intro x; split.
    + intro Hx; destruct (decomp_p2 x k Hx) as [u [Hu Hxd]].
      exists u; split; [ exact Hu | rewrite Hxd; ring ].
    + intros [u [Hu ->]].
      unfold ZImul at 1; rewrite ZInorm_mul, ZIpow_norm.
      replace (ZInorm (-1) (mkZI 1 1)) with 2 by reflexivity.
      rewrite (proj1 (ZIunit_norm u) Hu); ring.
Qed.

(* --- p = 3 (mod 4) : r2(p^k) = 4 * [k even] --- *)
Theorem r2_3pow : forall p k, prime (Z.of_nat p) -> (p mod 4 = 3)%nat ->
  r2 ((Z.of_nat p) ^ Z.of_nat k) = (if Nat.even k then 4 else 0)%nat.
Proof.
  intros p k Hp Hmod.
  assert (HP2 : 2 <= Z.of_nat p) by (pose proof (prime_ge_2 _ Hp); lia).
  destruct (Nat.even k) eqn:Ek.
  - (* k even : k = 2j *)
    destruct (Nat.even_spec k) as [Hev _]; specialize (Hev Ek); destruct Hev as [j Hj].
    apply (count_via_assoc4 _ (ZIpow (ZtoZI (Z.of_nat p)) j)).
    + apply ZIpow_nonzero; intro H;
        apply (f_equal (ZInorm (-1))) in H; rewrite ZInorm_ZtoZI, norm_ZI0 in H; nia.
    + intro x; split.
      * intro Hx; destruct (decomp_p3 p Hp Hmod x k Hx) as [u [j' [Hu [Hk Hxd]]]].
        assert (j' = j) by lia; subst j'.
        exists u; split; [ exact Hu | rewrite Hxd; ring ].
      * intros [u [Hu ->]].
        unfold ZImul at 1;
          rewrite ZInorm_mul, ZIpow_norm, ZInorm_ZtoZI, (proj1 (ZIunit_norm u) Hu), Z.mul_1_r.
        replace (Z.of_nat k) with (2 * Z.of_nat j) by (rewrite Hj; lia).
        rewrite Z.pow_mul_r by lia; rewrite Z.pow_2_r; reflexivity.
  - (* k odd : no element has norm p^k (decomp forces even) *)
    apply count_empty; intros x Hx.
    destruct (decomp_p3 p Hp Hmod x k Hx) as [u [j [_ [Hk _]]]].
    assert (Nat.even k = true) by (rewrite Hk, Nat.even_mul; reflexivity).
    rewrite Ek in H; discriminate.
Qed.

(* ================================================================= *)
(*  §8  MASTER: two of the three prime-power counts of r2             *)
(* ================================================================= *)

Theorem r2_prime_power_2_3 :
     (forall k, r2 (2 ^ Z.of_nat k) = 4%nat)
  /\ (forall p k, prime (Z.of_nat p) -> (p mod 4 = 3)%nat ->
        r2 ((Z.of_nat p) ^ Z.of_nat k) = (if Nat.even k then 4 else 0)%nat).
Proof. split; [ exact r2_2pow | exact r2_3pow ]. Qed.

Print Assumptions r2_prime_power_2_3.

(* ================================================================= *)
(*  END R2PrimePower.v                                               *)
(*  Milestone A of the r2 prime-power counts, via the Z[i] UFD tower  *)
(*  and the r2 = #{N(z)=n} bridge:                                    *)
(*    r2(2^k)   = 4         (ramified: z = unit*(1+i)^k),             *)
(*    r2(p^k)   = 4*[k even] (p=3 mod 4 inert: z = unit*(ZtoZI p)^j,  *)
(*                            k=2j).                                  *)
(*  Each norm-p^k element is a unit times a power of the single       *)
(*  Gaussian prime over p (decomp_p2 / decomp_p3); counting the 4      *)
(*  associates (assoc4) via NoDup_Permutation over the norm-filtered   *)
(*  box gives the value.  The split case p=1 mod 4 (r2=4(k+1)) is      *)
(*  Milestone B.  Closed under the global context (axiom-free).       *)
(* ================================================================= *)
