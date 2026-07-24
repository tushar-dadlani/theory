(* ================================================================= *)
(*  R2Multiplicative.v                                               *)
(*                                                                    *)
(*  r2 IS MULTIPLICATIVE (up to the factor 4):                       *)
(*                                                                    *)
(*      gcd(m,n) = 1   =>   r2(m) * r2(n) = 4 * r2(m*n).             *)
(*                                                                    *)
(*  Via r2(n) = #{ z : N(z)=n }: the map (x,y) |-> x*y from norm-m     *)
(*  times norm-n pairs to norm-mn elements is SURJECTIVE (the coprime  *)
(*  split, GaussianCoprime.gaussian_split) and exactly 4-TO-1 (each    *)
(*  norm-mn z has precisely its unit orbit {(x0*u, y0*conj u)} of      *)
(*  splits, split_unique).  A generic key-partition count             *)
(*  (count_by_key) turns "every fibre has size 4" into                *)
(*  |domain| = 4*|image|.  AXIOM-FREE.                               *)
(* ================================================================= *)

From Stdlib Require Import ZArith Znumtheory Arith Lia List Bool Permutation.
Require Import GaussianIntegers GaussianDivision GaussianGCD GaussianIrreducible
        GaussianCoprime GaussianFactorization GaussianNormCount R2Count
        R2PrimePower R2PrimePowerSplit.
Import ListNotations.
Open Scope Z_scope.

(* ================================================================= *)
(*  §1  generic "count by key" over lists                           *)
(* ================================================================= *)

Lemma filter_subsumed : forall (A : Type) (g h : A -> bool) l,
  (forall e, g e = true -> h e = true) -> filter g (filter h l) = filter g l.
Proof.
  intros A g h l Hgh; induction l as [|a l IH]; [ reflexivity | ].
  cbn [filter]; destruct (h a) eqn:Ha; cbn [filter].
  - destruct (g a) eqn:Ga; rewrite IH; reflexivity.
  - destruct (g a) eqn:Ga; [ specialize (Hgh a Ga); rewrite Ha in Hgh; discriminate | exact IH ].
Qed.

Lemma count_by_key : forall (A : Type) (key : A -> ZI) (c : nat) (K : list ZI) (L : list A),
  NoDup K ->
  (forall e, In e L -> In (key e) K) ->
  (forall k, In k K -> length (filter (fun e => ZIeqb (key e) k) L) = c) ->
  length L = (c * length K)%nat.
Proof.
  intros A key c K; induction K as [|k K IH]; intros L HND Hin Hcnt.
  - destruct L as [|e L]; [ simpl; lia | exfalso; exact (Hin e (or_introl eq_refl)) ].
  - assert (Hsplit : (length (filter (fun e => ZIeqb (key e) k) L)
                      + length (filter (fun e => negb (ZIeqb (key e) k)) L)
                      = length L)%nat) by apply filter_length.
    inversion HND as [|kk KK Hknotin HND' Heq]; subst.
    set (L' := filter (fun e => negb (ZIeqb (key e) k)) L).
    assert (Hin' : forall e, In e L' -> In (key e) K).
    { intros e He; unfold L' in He; apply filter_In in He; destruct He as [HeL Hneg].
      destruct (Hin e HeL) as [Hek | HinK']; [ | exact HinK' ].
      exfalso; assert (Hee : ZIeqb (key e) k = true)
        by (apply ZIeqb_eq; symmetry; exact Hek).
      rewrite Hee in Hneg; discriminate. }
    assert (Hcnt' : forall k', In k' K ->
              length (filter (fun e => ZIeqb (key e) k') L') = c).
    { intros k' Hk'.
      assert (Hkk' : k <> k') by (intro E; subst k'; contradiction).
      assert (Hsub : filter (fun e => ZIeqb (key e) k') L'
                     = filter (fun e => ZIeqb (key e) k') L).
      { unfold L'; apply filter_subsumed; intros e Hg.
        apply ZIeqb_eq in Hg.
        destruct (ZIeqb (key e) k) eqn:Ek; [ | reflexivity ].
        apply ZIeqb_eq in Ek; exfalso; apply Hkk'; rewrite <- Ek, Hg; reflexivity. }
      rewrite Hsub; apply Hcnt; right; exact Hk'. }
    rewrite <- Hsplit, (Hcnt k (or_introl eq_refl)).
    fold L'; rewrite (IH L' HND' Hin' Hcnt').
    cbn [length]; lia.
Qed.

(* ================================================================= *)
(*  §2  units:  conj is the inverse; norm-count list Lnorm            *)
(* ================================================================= *)

Lemma unit_mul_conj : forall u, ZIunit u -> ZImul u (ZIconj u) = ZI1.
Proof.
  intros u Hu; rewrite ZImul_conj_norm, (proj1 (ZIunit_norm u) Hu); reflexivity.
Qed.

Lemma ZImul_nz : forall x y, x <> ZI0 -> y <> ZI0 -> ZImul x y <> ZI0.
Proof. intros x y Hx Hy Heq; apply Hy; exact (ZI_no_zero_div x y Heq Hx). Qed.

Definition Lnorm (n : Z) : list ZI :=
  filter (fun z => ZInorm (-1) z =? n) (gbox (Z.to_nat (Z.sqrt n))).

Lemma Lnorm_NoDup : forall n, NoDup (Lnorm n).
Proof. intro n; apply NoDup_filter, gbox_NoDup. Qed.

Lemma in_Lnorm : forall n z, In z (Lnorm n) <-> ZInorm (-1) z = n.
Proof.
  intros n z; unfold Lnorm; rewrite filter_In, Z.eqb_eq; split.
  - intros [_ H]; exact H.
  - intro H; split; [ | exact H ].
    pose proof (in_gbox_of_norm_le z z (Z.le_refl _)) as Hb; rewrite H in Hb; exact Hb.
Qed.

Lemma r2_Lnorm : forall n, r2 n = length (Lnorm n).
Proof. intro n; unfold Lnorm; apply r2_as_gnorm. Qed.

(* ================================================================= *)
(*  §3  the split is unique up to a unit                            *)
(* ================================================================= *)

Lemma split_unique : forall m n x y x0 y0, Nat.gcd m n = 1%nat ->
  (1 <= m)%nat -> (1 <= n)%nat ->
  ZInorm (-1) x = Z.of_nat m -> ZInorm (-1) y = Z.of_nat n ->
  ZInorm (-1) x0 = Z.of_nat m -> ZInorm (-1) y0 = Z.of_nat n ->
  ZImul x y = ZImul x0 y0 ->
  exists u, ZIunit u /\ x = ZImul x0 u /\ y = ZImul y0 (ZIconj u).
Proof.
  intros m n x y x0 y0 Hco Hm Hn HNx HNy HNx0 HNy0 Hk.
  assert (Hx0 : x0 <> ZI0) by (intro E; rewrite E, norm_ZI0 in HNx0; lia).
  assert (Hx : x <> ZI0) by (intro E; rewrite E, norm_ZI0 in HNx; lia).
  assert (Hy0 : y0 <> ZI0) by (intro E; rewrite E, norm_ZI0 in HNy0; lia).
  (* gcd(x, y0) is a unit, because gcd(m,n)=1 *)
  destruct (ZI_bezout y0 x) as [g [[Hgx Hgy0] [[a [b Hbez]] _]]].
  assert (HNg1 : ZInorm (-1) g = 1).
  { assert (Hgm : (ZInorm (-1) g | Z.of_nat m)) by (rewrite <- HNx; apply dvd_norm; exact Hgx).
    assert (Hgn : (ZInorm (-1) g | Z.of_nat n)) by (rewrite <- HNy0; apply dvd_norm; exact Hgy0).
    assert (Hg1 : (ZInorm (-1) g | 1))
      by (rewrite <- (nat_gcd_Z m n Hco); apply Z.gcd_greatest; assumption).
    pose proof (ZInorm_nonneg g) as Hge.
    assert (Hle : ZInorm (-1) g <= 1) by (apply Z.divide_pos_le; [ lia | exact Hg1 ]).
    destruct (Z.eq_dec (ZInorm (-1) g) 0) as [E|E];
      [ rewrite E in Hg1; destruct Hg1 as [q Hq]; lia | lia ]. }
  destruct (proj2 (ZIunit_norm g) HNg1) as [w Hgw].
  (* x | x0 *)
  assert (Hxx0 : ZIdvd x x0).
  { exists (ZImul w (ZIadd (ZImul a x0) (ZImul b y))).
    transitivity (ZImul x0 (ZImul g w)); [ rewrite Hgw; ring | ].
    rewrite Hbez.
    transitivity (ZImul w (ZIadd (ZImul a (ZImul x0 x)) (ZImul b (ZImul x0 y0))));
      [ ring | ].
    rewrite <- Hk; ring. }
  (* x0 = x*c with c a unit, so x = x0 * conj c *)
  destruct Hxx0 as [c Hc].
  assert (HNc1 : ZInorm (-1) c = 1).
  { assert (Hp : Z.of_nat m * ZInorm (-1) c = Z.of_nat m).
    { transitivity (ZInorm (-1) x0); [ | exact HNx0 ].
      rewrite Hc, ZInorm_ZImul, HNx; reflexivity. }
    apply (Z.mul_reg_l _ _ (Z.of_nat m)); [ lia | rewrite Z.mul_1_r; exact Hp ]. }
  assert (Hcu : ZIunit c) by (apply ZIunit_norm; exact HNc1).
  exists (ZIconj c).
  assert (Hcc : ZImul c (ZIconj c) = ZI1) by (apply unit_mul_conj; exact Hcu).
  assert (Hxeq : x = ZImul x0 (ZIconj c)).
  { rewrite Hc.
    transitivity (ZImul x (ZImul c (ZIconj c))); [ rewrite Hcc; ring | ring ]. }
  repeat split.
  - apply ZIunit_norm; rewrite ZInorm_conj; exact HNc1.
  - exact Hxeq.
  - (* y = y0 * conj(conj c) = y0 * c *)
    rewrite ZIconj_involutive.
    (* from x*y = x0*y0 and x = x0*conj c : conj c * y = y0, so y = c*y0 *)
    assert (Hcy : ZImul x0 (ZImul (ZIconj c) y) = ZImul x0 y0)
      by (rewrite <- Hk, Hxeq; ring).
    pose proof (ZImul_cancel_l x0 _ _ Hx0 Hcy) as Hcy2.
    transitivity (ZImul c (ZImul (ZIconj c) y));
      [ | rewrite Hcy2 ].
    + transitivity (ZImul (ZImul c (ZIconj c)) y); [ rewrite Hcc; ring | ring ].
    + ring.
Qed.

(* ================================================================= *)
(*  §4  every fibre has exactly 4 elements                          *)
(* ================================================================= *)

Definition fiberlist (x0 y0 : ZI) : list (ZI * ZI) :=
  map (fun u => (ZImul x0 u, ZImul y0 (ZIconj u))) unit4.

Lemma fiber_length_4 : forall m n k, Nat.gcd m n = 1%nat -> (1 <= m)%nat -> (1 <= n)%nat ->
  ZInorm (-1) k = Z.of_nat m * Z.of_nat n ->
  length (filter (fun e => ZIeqb (ZImul (fst e) (snd e)) k)
                 (list_prod (Lnorm (Z.of_nat m)) (Lnorm (Z.of_nat n)))) = 4%nat.
Proof.
  intros m n k Hco Hm Hn HNk.
  destruct (gaussian_split m n k Hco Hm Hn HNk) as [x0 [y0 [HNx0 [HNy0 Hk]]]].
  assert (Hx0 : x0 <> ZI0) by (intro E; rewrite E, norm_ZI0 in HNx0; lia).
  assert (Hy0 : y0 <> ZI0) by (intro E; rewrite E, norm_ZI0 in HNy0; lia).
  transitivity (length (fiberlist x0 y0)); [ | unfold fiberlist; rewrite length_map; reflexivity ].
  apply Permutation_length, NoDup_Permutation.
  - apply NoDup_filter, NoDup_list_prod; apply Lnorm_NoDup.
  - unfold fiberlist; apply Totient.NoDup_map_inj; [ | apply unit4_NoDup ].
    intros u v _ _ Heq.
    apply (ZImul_cancel_l x0 u v Hx0); exact (f_equal (@fst ZI ZI) Heq).
  - intros [x y]; rewrite filter_In; cbn [fst snd]; split.
    + intros [Hin Heqk]; apply in_prod_iff in Hin; destruct Hin as [Hxm Hyn].
      apply in_Lnorm in Hxm; apply in_Lnorm in Hyn; apply ZIeqb_eq in Heqk.
      destruct (split_unique m n x y x0 y0 Hco Hm Hn Hxm Hyn HNx0 HNy0
                  ltac:(rewrite Heqk, Hk; reflexivity)) as [u [Hu [Hxu Hyu]]].
      unfold fiberlist; apply in_map_iff; exists u; split;
        [ rewrite <- Hxu, <- Hyu; reflexivity | apply unit_in_unit4; exact Hu ].
    + intros Hin; unfold fiberlist in Hin; apply in_map_iff in Hin.
      destruct Hin as [u [Heq Hu]]; injection Heq as Hx Hy.
      assert (HuU : ZIunit u) by (apply unit4_units; exact Hu).
      split.
      * apply in_prod_iff; split; apply in_Lnorm; subst x y.
        -- rewrite ZInorm_ZImul, (proj1 (ZIunit_norm u) HuU); rewrite HNx0; ring.
        -- rewrite ZInorm_ZImul, ZInorm_conj, (proj1 (ZIunit_norm u) HuU); rewrite HNy0; ring.
      * apply ZIeqb_eq; subst x y.
        transitivity (ZImul (ZImul x0 y0) (ZImul u (ZIconj u)));
          [ ring | rewrite (unit_mul_conj u HuU), Hk; ring ].
Qed.

(* ================================================================= *)
(*  §5  MASTER: r2 is multiplicative up to the factor 4              *)
(* ================================================================= *)

Theorem r2_mult : forall m n, Nat.gcd m n = 1%nat -> (1 <= m)%nat -> (1 <= n)%nat ->
  (r2 (Z.of_nat m) * r2 (Z.of_nat n))%nat = (4 * r2 (Z.of_nat m * Z.of_nat n))%nat.
Proof.
  intros m n Hco Hm Hn.
  rewrite !r2_Lnorm.
  transitivity (length (list_prod (Lnorm (Z.of_nat m)) (Lnorm (Z.of_nat n))));
    [ rewrite length_list_prod; reflexivity | ].
  apply (count_by_key _ (fun e => ZImul (fst e) (snd e)) 4
                      (Lnorm (Z.of_nat m * Z.of_nat n))).
  - apply Lnorm_NoDup.
  - intros [x y] Hin; apply in_prod_iff in Hin; destruct Hin as [Hxm Hyn].
    apply in_Lnorm in Hxm; apply in_Lnorm in Hyn.
    apply in_Lnorm; cbn [fst snd]; rewrite ZInorm_ZImul, Hxm, Hyn; reflexivity.
  - intros k Hk; apply in_Lnorm in Hk.
    apply (fiber_length_4 m n k Hco Hm Hn Hk).
Qed.

Print Assumptions r2_mult.

(* ================================================================= *)
(*  END R2Multiplicative.v                                           *)
(*  r2(m)*r2(n) = 4*r2(m*n) for gcd(m,n)=1: the (x,y) |-> x*y map on   *)
(*  norm-m x norm-n pairs is surjective onto norm-mn elements         *)
(*  (gaussian_split) and exactly 4-to-1 (split_unique -> each fibre    *)
(*  is a unit orbit of size 4), so the key-partition count            *)
(*  (count_by_key) gives |domain| = 4*|image|.                       *)
(*  Closed under the global context (axiom-free).                    *)
(* ================================================================= *)
