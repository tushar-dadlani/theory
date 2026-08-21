(* ================================================================= *)
(*  CEisensteinJPrimary.v  —  the Jacobi sum is PRIMARY.               *)
(*                                                                    *)
(*    good, Esum_free3 : a FREE Z/3 action makes an invariant sum      *)
(*                       divisible by 3                                *)
(*    rr t            : the substitution t |-> 1/(1-t)                 *)
(*    rr_cycle        : it has order three                             *)
(*    rr_fix_iff      : its fixed points are the roots of x^2 - x + 1  *)
(*    roots_exist     : there are exactly two of them                  *)
(*    FJ_inv          : the Jacobi summand is invariant                *)
(*    Jsum_primary    : J = -1 mod 3                                   *)
(*    Jsum_assoc      : J is an associate of pi or of conj pi          *)
(*                                                                    *)
(*  THE ORDER-3 SUBGROUP IS ENOUGH, and that is the design decision    *)
(*  that makes this file tractable.  The classical argument uses the   *)
(*  full S_3 acting by the six cross-ratio maps, and then has to sort  *)
(*  orbits of size 6, 3, 2 and 1.  Only the cyclic subgroup generated  *)
(*  by t |-> 1/(1-t) is needed: its orbits have size 3 or 1, size-1    *)
(*  orbits are exactly the fixed points, and everything else cancels   *)
(*  mod 3.  Half the case analysis disappears.                         *)
(*                                                                    *)
(*  NO ORBIT-PARTITION MACHINERY IS BUILT.  Esum_free3 peels one       *)
(*  orbit at a time -- take the head t, delete {t, rr t, rr rr t},     *)
(*  recurse on a list three shorter -- with strong induction on the    *)
(*  length.  The three deleted points contribute F t + F t + F t, so   *)
(*  divisibility by 3 falls out of the peeling itself rather than out  *)
(*  of any counting.  No choice principle is needed to pick orbit      *)
(*  representatives, because the head of the list is one.              *)
(*                                                                    *)
(*  INVARIANCE OF THE SUMMAND is where the earlier bricks are spent.   *)
(*  chi(1/(1-t)) chi(t/(t-1)) = chi(t) chi(1-t) needs chi(-1) = 1      *)
(*  (brick 3) to drop the sign, and needs conj(z)^2 = z on cube roots  *)
(*  to fold the two conjugates back into one.                          *)
(*                                                                    *)
(*  THE ACTION IS NEVER COMPUTED, only characterised: rr t is the      *)
(*  unique r with (1 - t) r = 1 mod p, and rr_unique turns that into   *)
(*  a proof principle.  rr_cycle is then a three-step congruence       *)
(*  chain -- multiply the relation for u by (1-t), then the one for v  *)
(*  by that -- and no inverse is ever evaluated.                       *)
(*                                                                    *)
(*  WHERE THE -1 COMES FROM: the two fixed points are the primitive    *)
(*  6th roots of unity, the roots of x^2 - x + 1, which exist exactly  *)
(*  because p = 1 mod 3 (they are the negatives of the order-3         *)
(*  elements supplied by order3_elt).  At such a point t(1-t) = 1, so  *)
(*  1 - t = 1/t and the summand is chi(t) chi(1/t) = 1.  Two fixed     *)
(*  points, each contributing 1, and everything else a multiple of 3:  *)
(*  J = 2 = -1 mod 3.                                                  *)
(*                                                                    *)
(*  WHAT IS STILL OPEN.  With N(J) = p from the previous brick,        *)
(*  Jsum_assoc gets J to an associate of pi or of conj pi, and         *)
(*  Jsum_eq_primary sharpens that to J = the primary associate once    *)
(*  pi | J is known.  DECIDING BETWEEN pi AND conj pi is not done      *)
(*  here; the standard argument expands chi(t) = t^{(p-1)/3} mod pi    *)
(*  and evaluates sum_t t^k (1-t)^k by the binomial theorem, using     *)
(*  that sum_t t^m vanishes unless (p-1) | m -- and k + j never        *)
(*  reaches 3k for j <= k, so the whole sum is 0 mod pi.  That needs   *)
(*  power sums over F_p, which this development does not have.         *)
(*  Axiom-clean.                                                       *)
(* ================================================================= *)

From Stdlib Require Import ZArith Znumtheory Arith Lia List Bool Permutation Ring.
Require Import ZmodPStar ZmodOrder PrimitiveRoot FpField
        CEisenstein CEisensteinUnits CEisensteinDiv CEisensteinGcd
        CEisensteinSplit CEisensteinUFD CEisensteinResidue CEisensteinFermat
        CEisensteinCubicMul CEisensteinCubicSupp CEisensteinCubicFun
        CEisensteinPrimary CEisensteinSum CEisensteinJacobi CEisensteinNormJ.
Import ListNotations.
Open Scope Z_scope.

Lemma emul_eZ3 : forall z, emul (eZ 3) z = eadd z (eadd z z).
Proof. intros [a b]. unfold eZ, emul, eadd; cbn [ea eb]. apply Eis_eq; ring. Qed.

(* ----------------------------------------------------------------- *)
(*  A.  a FREE Z/3 action makes an invariant sum divisible by 3        *)
(* ----------------------------------------------------------------- *)
Section Free3.

Variable rho : nat -> nat.
Variable F : nat -> Eis.

Definition good (L : list nat) : Prop :=
  NoDup L
  /\ (forall x, In x L -> In (rho x) L)
  /\ (forall x, In x L -> rho (rho (rho x)) = x)
  /\ (forall x, In x L -> rho x <> x)
  /\ (forall x, In x L -> F (rho x) = F x).

Lemma good_inj : forall L, good L ->
  forall x y, In x L -> In y L -> rho x = rho y -> x = y.
Proof.
  intros L [_ [_ [Hcyc _]]] x y Hx Hy He.
  rewrite <- (Hcyc x Hx), <- (Hcyc y Hy), He. reflexivity.
Qed.

Lemma Esum_free3_aux : forall n L, (length L <= n)%nat -> good L ->
  exists q, Esum F L = emul (eZ 3) q.
Proof.
  induction n as [| n IH]; intros L Hlen HG.
  - destruct L as [| x L]; [ | cbn [length] in Hlen; lia ].
    exists ezero. rewrite Esum_nil. ring.
  - destruct L as [| t L0].
    { exists ezero. rewrite Esum_nil. ring. }
    set (L := t :: L0) in *.
    destruct HG as [Hnd [Hstab [Hcyc [Hnf Hinv]]]].
    assert (HG : good L) by (unfold good; repeat split; assumption).
    assert (Ht : In t L) by (unfold L; left; reflexivity).
    set (r1 := rho t). set (r2 := rho r1).
    assert (Hr1 : In r1 L) by (apply Hstab; exact Ht).
    assert (Hr2 : In r2 L) by (unfold r2; apply Hstab; exact Hr1).
    assert (Hback : rho r2 = t) by (unfold r2, r1; apply Hcyc; exact Ht).
    (* the three points of the orbit are distinct *)
    assert (D1 : t <> r1) by (intro Hc; apply (Hnf t Ht); symmetry; exact Hc).
    assert (D2 : r1 <> r2) by (intro Hc; apply (Hnf r1 Hr1); symmetry; exact Hc).
    assert (D3 : t <> r2).
    { intro Hc. apply (Hnf t Ht).
      transitivity (rho r2); [ rewrite <- Hc; reflexivity | exact Hback ]. }
    (* peel them off *)
    assert (E1 : Esum F L = eadd (F t) (Esum F (del t L)))
      by (apply Esum_del; assumption).
    assert (Hnd1 : NoDup (del t L)) by (apply NoDup_del; exact Hnd).
    assert (Hin1 : In r1 (del t L))
      by (apply In_del; split; [ exact Hr1 | intro Hc; apply D1; symmetry; exact Hc ]).
    assert (E2 : Esum F (del t L) = eadd (F r1) (Esum F (del r1 (del t L))))
      by (apply Esum_del; assumption).
    assert (Hnd2 : NoDup (del r1 (del t L))) by (apply NoDup_del; exact Hnd1).
    assert (Hin2 : In r2 (del r1 (del t L))).
    { apply In_del. split;
        [ apply In_del; split;
          [ exact Hr2 | intro Hc; apply D3; symmetry; exact Hc ]
        | intro Hc; apply D2; symmetry; exact Hc ]. }
    assert (E3 : Esum F (del r1 (del t L))
                 = eadd (F r2) (Esum F (del r2 (del r1 (del t L)))))
      by (apply Esum_del; assumption).
    set (L' := del r2 (del r1 (del t L))).
    (* the sum over the orbit is 3 F t *)
    assert (F1 : F r1 = F t) by (unfold r1; apply Hinv; exact Ht).
    assert (F2 : F r2 = F t) by (unfold r2; rewrite (Hinv r1 Hr1); exact F1).
    (* L' inherits the hypotheses *)
    assert (HmemL' : forall x, In x L' -> In x L /\ x <> t /\ x <> r1 /\ x <> r2).
    { intros x Hx. unfold L' in Hx.
      apply In_del in Hx as [Hx Hx2]. apply In_del in Hx as [Hx Hx1].
      apply In_del in Hx as [Hx Hx0]. tauto. }
    assert (HG' : good L').
    { unfold good. repeat split.
      - unfold L'. apply NoDup_del, NoDup_del, NoDup_del. exact Hnd.
      - intros x Hx. destruct (HmemL' x Hx) as [HxL [Hx0 [Hx1 Hx2]]].
        assert (HrL : In (rho x) L) by (apply Hstab; exact HxL).
        assert (N0 : rho x <> t).
        { intro Hc. apply Hx2. apply (good_inj L HG x r2 HxL Hr2).
          rewrite Hc, Hback. reflexivity. }
        assert (N1 : rho x <> r1).
        { intro Hc. apply Hx0. apply (good_inj L HG x t HxL Ht). exact Hc. }
        assert (N2 : rho x <> r2).
        { intro Hc. apply Hx1. apply (good_inj L HG x r1 HxL Hr1). exact Hc. }
        unfold L'. apply In_del. split; [ | exact N2 ].
        apply In_del. split; [ | exact N1 ].
        apply In_del. split; [ exact HrL | exact N0 ].
      - intros x Hx. apply Hcyc. exact (proj1 (HmemL' x Hx)).
      - intros x Hx. apply Hnf. exact (proj1 (HmemL' x Hx)).
      - intros x Hx. apply Hinv. exact (proj1 (HmemL' x Hx)). }
    (* lengths drop by exactly three *)
    assert (Hlen' : (length L' <= n)%nat).
    { pose proof (length_del t L Hnd Ht) as A1.
      pose proof (length_del r1 (del t L) Hnd1 Hin1) as A2.
      pose proof (length_del r2 (del r1 (del t L)) Hnd2 Hin2) as A3.
      unfold L' in *. lia. }
    destruct (IH L' Hlen' HG') as [q' Hq'].
    exists (eadd (F t) q').
    rewrite E1, E2, E3, F1, F2. fold L'. rewrite Hq', !emul_eZ3. ring.
Qed.

Theorem Esum_free3 : forall L, good L -> exists q, Esum F L = emul (eZ 3) q.
Proof. intros L HG. exact (Esum_free3_aux (length L) L (Nat.le_refl _) HG). Qed.

End Free3.

(* ----------------------------------------------------------------- *)
(*  B.  the action t |-> 1/(1-t) on F_p \ {0,1}                        *)
(* ----------------------------------------------------------------- *)
Section JPrimary.

Variable p : nat.
Variable pi : Eis.
Variable t0 : Z.
Hypothesis Hp : prime (Z.of_nat p).
Hypothesis Hp7 : (7 <= p)%nat.
Hypothesis Hdiv : Nat.divide 3 (p - 1)%nat.
Hypothesis Hn : enorm pi = Z.of_nat p.
Hypothesis Ht : edvd pi (esub (eZ t0) eom).

Notation ch := (chn p pi).
Notation P := (Z.of_nat p).

Definition dd (t : nat) : nat := (1 + p - t)%nat.
Definition rr (t : nat) : nat := finv p (dd t).
Definition FJ (t : nat) : Eis := emul (ch t) (ch (dd t)).

(* ---- congruence helpers ------------------------------------------ *)
Lemma ndvdP : forall z, 0 < z < P -> ~ (P | z).
Proof.
  intros z Hz [c Hc].
  destruct (Z.le_gt_cases c 0) as [H | H].
  - assert (c * P <= 0 * P) by (apply Z.mul_le_mono_nonneg_r; lia). lia.
  - assert (1 * P <= c * P) by (apply Z.mul_le_mono_nonneg_r; lia). lia.
Qed.

Lemma eqP : forall a b : nat, (a < p)%nat -> (b < p)%nat ->
  (P | Z.of_nat a - Z.of_nat b) -> a = b.
Proof.
  intros a b Ha Hb H.
  destruct (Nat.compare_spec a b) as [E | E | E]; [ exact E | | ].
  - exfalso. apply (ndvdP (Z.of_nat b - Z.of_nat a)); [ lia | ].
    destruct H as [c Hc]. exists (- c). lia.
  - exfalso. apply (ndvdP (Z.of_nat a - Z.of_nat b)); [ lia | exact H ].
Qed.

Lemma cancelP : forall (X Y : Z) (b : nat), (1 <= b <= p - 1)%nat ->
  (P | (X - Y) * Z.of_nat b) -> (P | X - Y).
Proof.
  intros X Y b Hb Hd.
  destruct (prime_mult P Hp _ _ Hd) as [H | H]; [ exact H | exfalso ].
  apply (ndvdP (Z.of_nat b)); [ lia | exact H ].
Qed.

Lemma chP : forall a b : nat, (P | Z.of_nat a - Z.of_nat b) -> ch a = ch b.
Proof.
  intros a b H. unfold chn.
  apply (chiv_cong_eq p pi t0 Hp Hp7 Hdiv Hn Ht).
  apply (econg_eZ_of_dvd p pi Hp Hn). exact H.
Qed.

Lemma dd_range : forall t, (2 <= t <= p - 1)%nat -> (2 <= dd t <= p - 1)%nat.
Proof. intros t Hts. unfold dd. lia. Qed.

Lemma cg_dd : forall t, (t <= p)%nat -> (P | Z.of_nat (dd t) - (1 - Z.of_nat t)).
Proof. intros t Hts. unfold dd. exists 1. lia. Qed.

(* r . (1-t) = 1 characterises rr t *)
Lemma rr_inv : forall t, (2 <= t <= p - 1)%nat ->
  (P | Z.of_nat (dd t) * Z.of_nat (rr t) - 1).
Proof.
  intros t Hts.
  assert (Hd : (1 <= dd t <= p - 1)%nat) by (pose proof (dd_range t Hts); lia).
  destruct (cg_inv p Hp Hp7 (dd t) Hd) as [c Hc].
  rewrite Nat2Z.inj_mul in Hc. exists c. unfold rr. lia.
Qed.

Lemma rr_lt : forall t, (2 <= t <= p - 1)%nat -> (1 <= rr t <= p - 1)%nat.
Proof.
  intros t Hts. unfold rr. apply finv_unit; [ exact Hp | ].
  pose proof (dd_range t Hts). lia.
Qed.

Lemma rr_range : forall t, (2 <= t <= p - 1)%nat -> (2 <= rr t <= p - 1)%nat.
Proof.
  intros t Hts.
  pose proof (rr_lt t Hts) as Hl.
  assert (Hne : rr t <> 1%nat).
  { intro Hc.
    destruct (rr_inv t Hts) as [c Hc2]. rewrite Hc in Hc2.
    replace (Z.of_nat 1) with 1 in Hc2 by reflexivity.
    pose proof (dd_range t Hts) as Hd.
    (* dd t - 1 is a nonzero multiple of P, but 0 < dd t - 1 < P *)
    apply (ndvdP (Z.of_nat (dd t) - 1)); [ lia | exists c; lia ]. }
  lia.
Qed.

(* uniqueness of the inverse *)
Lemma rr_unique : forall t x, (2 <= t <= p - 1)%nat -> (x < p)%nat ->
  (P | Z.of_nat (dd t) * Z.of_nat x - 1) -> x = rr t.
Proof.
  intros t x Hts Hx Hinv.
  assert (Hd : (1 <= dd t <= p - 1)%nat) by (pose proof (dd_range t Hts); lia).
  apply eqP; [ exact Hx | pose proof (rr_lt t Hts); lia | ].
  apply (cancelP _ _ (dd t) Hd).
  destruct Hinv as [c Hc]. destruct (rr_inv t Hts) as [e He].
  exists (c - e). lia.
Qed.

(* ---- the action has order three ---------------------------------- *)
Lemma rr_step : forall t, (2 <= t <= p - 1)%nat ->
  (P | (1 - Z.of_nat t) * Z.of_nat (rr t) - 1).
Proof.
  intros t Hts.
  destruct (rr_inv t Hts) as [a Ha].
  destruct (cg_dd t ltac:(lia)) as [d Hd].
  exists (a - d * Z.of_nat (rr t)).
  assert (E : (1 - Z.of_nat t) * Z.of_nat (rr t)
              = (Z.of_nat (dd t) - d * P) * Z.of_nat (rr t))
    by (rewrite <- Hd; ring).
  rewrite E. lia.
Qed.

Lemma rr_cycle : forall t, (2 <= t <= p - 1)%nat -> rr (rr (rr t)) = t.
Proof.
  intros t Hts.
  set (u := rr t). set (v := rr u).
  assert (Hu : (2 <= u <= p - 1)%nat) by (unfold u; apply rr_range; exact Hts).
  assert (Hv : (2 <= v <= p - 1)%nat) by (unfold v; apply rr_range; exact Hu).
  symmetry. apply (rr_unique v t Hv ltac:(lia)).
  (* first, the key congruence  (1 - v) t = 1 *)
  assert (KEY : (P | (1 - Z.of_nat v) * Z.of_nat t - 1)).
  { destruct (rr_step t Hts) as [a Ha]. fold u in Ha.
    destruct (rr_step u Hu) as [b Hb]. fold v in Hb.
    set (T := Z.of_nat t) in *. set (U := Z.of_nat u) in *.
    set (V := Z.of_nat v) in *.
    assert (R1 : T * U = U - 1 - a * P) by lia.
    assert (R2 : U * V = V - 1 - b * P) by lia.
    assert (R3 : T * (U * V) = (T * U) * V) by ring.
    rewrite R1, R2 in R3.
    assert (R4 : (U - 1 - a * P) * V = U * V - V - a * P * V) by ring.
    rewrite R4, R2 in R3.
    exists (b + a * V - T * b). lia. }
  destruct KEY as [k Hk].
  destruct (cg_dd v ltac:(lia)) as [e He].
  exists (k + e * Z.of_nat t).
  assert (E : Z.of_nat (dd v) * Z.of_nat t
              = ((1 - Z.of_nat v) + e * P) * Z.of_nat t) by (rewrite <- He; ring).
  rewrite E. lia.
Qed.

(* ---- fixed points are exactly the roots of x^2 - x + 1 ------------ *)
Lemma rr_fix_iff : forall t, (2 <= t <= p - 1)%nat ->
  (rr t = t <-> (P | Z.of_nat t * Z.of_nat t - Z.of_nat t + 1)).
Proof.
  intros t Hts. split.
  - intro Hf.
    destruct (rr_step t Hts) as [a Ha]. rewrite Hf in Ha.
    exists (- a). lia.
  - intros [c Hc].
    symmetry. apply (rr_unique t t Hts ltac:(lia)).
    destruct (cg_dd t ltac:(lia)) as [d Hd].
    exists (- c + d * Z.of_nat t).
    assert (E : Z.of_nat (dd t) * Z.of_nat t
                = ((1 - Z.of_nat t) + d * P) * Z.of_nat t) by (rewrite <- Hd; ring).
    rewrite E. lia.
Qed.

(* ---- there are exactly two fixed points -------------------------- *)
Lemma cgmod : forall a : nat, (P | Z.of_nat (a mod p) - Z.of_nat a).
Proof.
  intro a. exists (- Z.of_nat (a / p)).
  assert (E : (a = p * (a / p) + a mod p)%nat) by apply Nat.div_mod_eq. lia.
Qed.

Lemma root_neg : forall z : Z, (P | z * z + z + 1) ->
  (P | (P - z) * (P - z) - (P - z) + 1).
Proof. intros z [c Hc]. exists (c + P - 2 * z - 1). lia. Qed.

Lemma roots_exist : exists a b : nat,
  (2 <= a <= p - 1)%nat /\ (2 <= b <= p - 1)%nat /\ a <> b
  /\ (P | Z.of_nat a * Z.of_nat a - Z.of_nat a + 1)
  /\ (P | Z.of_nat b * Z.of_nat b - Z.of_nat b + 1)
  /\ (forall x, (x < p)%nat ->
        (P | Z.of_nat x * Z.of_nat x - Z.of_nat x + 1) -> x = a \/ x = b).
Proof.
  destruct (order3_elt p Hp Hdiv Hp7) as [s [Hs Hs3]].
  set (S := Z.of_nat s) in *.
  assert (HSr : 1 < S < P) by (unfold S; lia).
  assert (Hquad : (P | S * S + S + 1)).
  { pose proof (p_dvd_quad p s Hp Hs Hs3) as H. rewrite Z.pow_2_r in H. exact H. }
  assert (Hcube : (P | S * S * S - 1)).
  { destruct Hquad as [c Hc]. exists ((S - 1) * c).
    replace (S * S * S - 1) with ((S - 1) * (S * S + S + 1)) by ring.
    rewrite Hc. ring. }
  assert (HnS : ~ (P | S)) by (apply ndvdP; lia).
  set (s2 := ((s * s) mod p)%nat).
  assert (Hs2lt : (s2 < p)%nat) by (unfold s2; apply Nat.mod_upper_bound; lia).
  assert (Hm : (P | Z.of_nat s2 - S * S)).
  { destruct (cgmod (s * s)%nat) as [m Hm]. exists m.
    rewrite Nat2Z.inj_mul in Hm. unfold s2, S. lia. }
  assert (Hs2ne0 : s2 <> 0%nat).
  { intro Hc. rewrite Hc in Hm. cbn [Z.of_nat] in Hm.
    destruct (prime_mult P Hp S S ltac:(destruct Hm as [m Hm]; exists (- m); lia))
      as [H | H]; exact (HnS H). }
  (* the two roots *)
  assert (Hane : s <> (p - 1)%nat).
  { intro Hc. apply (ndvdP 1); [ lia | ].
    destruct Hquad as [c Hc2]. exists (c - P + 1). unfold S in Hc2. rewrite Hc in Hc2. lia. }
  assert (Hs2ne : s2 <> (p - 1)%nat).
  { intro Hc. apply HnS.
    destruct Hquad as [c Hc2]. destruct Hm as [m Hm2].
    exists (c - 1 + m). rewrite Hc in Hm2. lia. }
  exists (p - s)%nat, (p - s2)%nat.
  assert (Hav : Z.of_nat (p - s) = P - S) by (unfold S; lia).
  assert (Hbv : Z.of_nat (p - s2) = P - Z.of_nat s2) by lia.
  assert (Hs2quad : (P | Z.of_nat s2 * Z.of_nat s2 + Z.of_nat s2 + 1)).
  { destruct Hquad as [c Hc]. destruct Hcube as [k Hk]. destruct Hm as [m Hm2].
    assert (HS2 : Z.of_nat s2 = S * S + m * P) by lia.
    assert (Hq4 : S * S * (S * S) = S * (S * S * S)) by ring.
    assert (Hc3 : S * S * S = 1 + k * P) by lia.
    rewrite Hc3 in Hq4.
    exists (S * k + c + 2 * (S * S) * m + m * m * P + m).
    rewrite HS2. lia. }
  split; [ lia | ]. split; [ lia | ]. split; [ | split; [ | split ] ].
  - (* a <> b *)
    intro Hc.
    assert (Hss : Z.of_nat s2 = S) by (unfold S; lia).
    destruct Hm as [m Hm2]. rewrite Hss in Hm2.
    (* Hm2 : S - S*S = m P, i.e. P divides S (1 - S) *)
    destruct (prime_mult P Hp S (1 - S) ltac:(exists m; lia))
      as [H | H]; [ exact (HnS H) | ].
    apply (ndvdP (S - 1)); [ lia | destruct H as [c Hc2]; exists (- c); lia ].
  - rewrite Hav. apply root_neg. exact Hquad.
  - rewrite Hbv. apply root_neg. exact Hs2quad.
  - (* the only roots *)
    intros x Hx [c2 Hc2].
    set (X := Z.of_nat x) in *.
    set (A := P - S). set (B := P - Z.of_nat s2).
    assert (Hsum : (P | A + B - 1)).
    { destruct Hquad as [c Hc]. destruct Hm as [m Hm2].
      unfold A, B. exists (2 - c - m). lia. }
    assert (Hprod : (P | A * B - 1)).
    { destruct Hcube as [k Hk]. destruct Hm as [m Hm2].
      unfold A, B.
      assert (E : (P - S) * (P - Z.of_nat s2)
                  = P * P - P * Z.of_nat s2 - S * P + S * Z.of_nat s2) by ring.
      rewrite E.
      assert (E2 : S * Z.of_nat s2 = S * (S * S) + S * (m * P))
        by (assert (Q : Z.of_nat s2 = S * S + m * P) by lia; rewrite Q; ring).
      rewrite E2.
      exists (P - Z.of_nat s2 - S + k + S * m). lia. }
    assert (Hfac : (P | (X - A) * (X - B))).
    { destruct Hsum as [u Hu]. destruct Hprod as [v Hv].
      exists (c2 - u * X + v).
      assert (E : (X - A) * (X - B)
                  = (X * X - X + 1) - (A + B - 1) * X + (A * B - 1)) by ring.
      rewrite E, Hu, Hv, Hc2. ring. }
    destruct (prime_mult P Hp _ _ Hfac) as [H | H].
    + left. apply eqP; [ exact Hx | lia | rewrite Hav; exact H ].
    + right. apply eqP; [ exact Hx | lia | rewrite Hbv; exact H ].
Qed.

(* ---- the summand is invariant under the action -------------------- *)
Lemma econj_invol : forall z, econj (econj z) = z.
Proof. intros [a b]. unfold econj; cbn [ea eb]. apply Eis_eq; ring. Qed.

Lemma cuberoot_conj : forall z, cuberoot z -> cuberoot (econj z).
Proof.
  intros z [-> | [-> | ->]]; unfold cuberoot;
    [ left | right; right | right; left ]; reflexivity.
Qed.

Lemma ch_neg : forall t, (1 <= t <= p - 1)%nat -> ch (p - t)%nat = ch t.
Proof.
  intros t Hts.
  assert (E : ch (p - t)%nat = ch (((p - 1) * t) mod p)%nat).
  { apply chP.
    destruct (cgmod ((p - 1) * t)%nat) as [m Hm].
    rewrite Nat2Z.inj_mul in Hm.
    exists (1 - Z.of_nat t - m). lia. }
  rewrite E, (chn_mul p pi t0 Hp Hp7 Hdiv Hn Ht).
  rewrite (chn_minus_one p pi t0 Hp Hp7 Hdiv Hn Ht). ring.
Qed.

Lemma ch_rr : forall t, (2 <= t <= p - 1)%nat -> ch (rr t) = econj (ch (dd t)).
Proof.
  intros t Hts.
  assert (Hd : (1 <= dd t <= p - 1)%nat) by (pose proof (dd_range t Hts); lia).
  unfold rr. symmetry. exact (chn_conj p pi t0 Hp Hp7 Hdiv Hn Ht (dd t) Hd).
Qed.

Lemma ch_dd_rr : forall t, (2 <= t <= p - 1)%nat ->
  ch (dd (rr t)) = emul (ch t) (econj (ch (dd t))).
Proof.
  intros t Hts.
  assert (Hu : (2 <= rr t <= p - 1)%nat) by (apply rr_range; exact Hts).
  assert (E : ch (dd (rr t)) = ch (((p - t) * rr t) mod p)%nat).
  { apply chP.
    destruct (rr_step t Hts) as [a Ha].
    destruct (cgmod ((p - t) * rr t)%nat) as [m Hm].
    rewrite Nat2Z.inj_mul in Hm.
    assert (HD : Z.of_nat (dd (rr t)) = 1 + P - Z.of_nat (rr t))
      by (unfold dd; lia).
    exists (1 - Z.of_nat (rr t) - a - m). lia. }
  rewrite E, (chn_mul p pi t0 Hp Hp7 Hdiv Hn Ht).
  rewrite (ch_neg t ltac:(lia)), (ch_rr t Hts). reflexivity.
Qed.

Lemma FJ_inv : forall t, (2 <= t <= p - 1)%nat -> FJ (rr t) = FJ t.
Proof.
  intros t Hts.
  assert (Hd : (2 <= dd t <= p - 1)%nat) by (apply dd_range; exact Hts).
  unfold FJ. rewrite (ch_rr t Hts), (ch_dd_rr t Hts).
  assert (Hcr : cuberoot (ch (dd t)))
    by (apply (chn_cuberoot p pi Hp Hp7 Hn); lia).
  assert (Hsq : emul (econj (ch (dd t))) (econj (ch (dd t))) = ch (dd t)).
  { rewrite (cuberoot_sq (econj (ch (dd t))) (cuberoot_conj _ Hcr)).
    apply econj_invol. }
  transitivity (emul (ch t) (emul (econj (ch (dd t))) (econj (ch (dd t)))));
    [ ring | ].
  rewrite Hsq. reflexivity.
Qed.

(* ---- assembling --------------------------------------------------- *)
Lemma eone_plus_eone : eadd eone eone = eZ 2.
Proof. reflexivity. Qed.

Lemma primary_of_form : forall q, primary (eadd (eZ 2) (emul (eZ 3) q)).
Proof.
  intros [qa qb]. unfold primary, eZ, eadd, emul; cbn [ea eb]. split.
  - replace (2 + (3 * qa - 0 * qb)) with (3 * qa + 2) by ring.
    apply mod3_of; lia.
  - replace (0 + (3 * qb + 0 * qa - 0 * qb)) with (3 * qb + 0) by ring.
    apply mod3_of; lia.
Qed.

Theorem Jsum_primary : primary (Jsum p pi).
Proof.
  destruct roots_exist as [a [b [Ha [Hb [Hab [Hra [Hrb Honly]]]]]]].
  set (XL := seq 2 (p - 2)).
  assert (HinXL : forall x, In x XL <-> (2 <= x <= p - 1)%nat).
  { intro x. unfold XL. rewrite in_seq. lia. }
  (* the value at a fixed point is 1 *)
  assert (Hfix : forall x, (2 <= x <= p - 1)%nat ->
                 (P | Z.of_nat x * Z.of_nat x - Z.of_nat x + 1) -> FJ x = eone).
  { intros x Hx Hr.
    assert (Hrx : rr x = x) by (apply (rr_fix_iff x Hx); exact Hr).
    assert (Hc : econj (ch (dd x)) = ch x)
      by (rewrite <- (ch_rr x Hx), Hrx; reflexivity).
    assert (Hd2 : ch (dd x) = econj (ch x))
      by (rewrite <- Hc, econj_invol; reflexivity).
    unfold FJ. rewrite Hd2, emul_econj.
    assert (Hcr : cuberoot (ch x)) by (apply (chn_cuberoot p pi Hp Hp7 Hn); lia).
    destruct Hcr as [E | [E | E]]; rewrite E; reflexivity. }
  (* peel off the two fixed points *)
  assert (HinB : In b XL) by (apply HinXL; exact Hb).
  assert (HndXL : NoDup XL) by (unfold XL; apply seq_NoDup).
  assert (HinA : In a (del b XL))
    by (apply In_del; split; [ apply HinXL; exact Ha | exact Hab ]).
  assert (Hnd1 : NoDup (del b XL)) by (apply NoDup_del; exact HndXL).
  set (L := del a (del b XL)).
  assert (Hsplit : Esum FJ XL = eadd (FJ b) (eadd (FJ a) (Esum FJ L))).
  { rewrite (Esum_del FJ b XL HndXL HinB).
    rewrite (Esum_del FJ a (del b XL) Hnd1 HinA). reflexivity. }
  (* what is left carries a free action *)
  assert (HmemL : forall x, In x L -> (2 <= x <= p - 1)%nat /\ x <> a /\ x <> b).
  { intros x Hx. unfold L in Hx.
    apply In_del in Hx as [Hx Hxa]. apply In_del in Hx as [Hx Hxb].
    split; [ apply HinXL; exact Hx | tauto ]. }
  assert (Hstab : forall x, In x L -> In (rr x) L).
  { intros x Hx. destruct (HmemL x Hx) as [Hxr [Hxa Hxb]].
    assert (Hrx : (2 <= rr x <= p - 1)%nat) by (apply rr_range; exact Hxr).
    assert (Hfa : rr a = a) by (apply (rr_fix_iff a Ha); exact Hra).
    assert (Hfb : rr b = b) by (apply (rr_fix_iff b Hb); exact Hrb).
    unfold L. apply In_del. split; [ apply In_del; split | ].
    - apply HinXL. exact Hrx.
    - intro Hc. apply Hxb.
      rewrite <- (rr_cycle x Hxr), Hc, Hfb, Hfb. reflexivity.
    - intro Hc. apply Hxa.
      rewrite <- (rr_cycle x Hxr), Hc, Hfa, Hfa. reflexivity. }
  assert (HG : good rr FJ L).
  { unfold good. repeat split.
    - unfold L. apply NoDup_del. exact Hnd1.
    - exact Hstab.
    - intros x Hx. apply rr_cycle. exact (proj1 (HmemL x Hx)).
    - intros x Hx. destruct (HmemL x Hx) as [Hxr [Hxa Hxb]]. intro Hc.
      destruct (Honly x ltac:(lia) (proj1 (rr_fix_iff x Hxr) Hc));
        [ exact (Hxa ltac:(assumption)) | exact (Hxb ltac:(assumption)) ].
    - intros x Hx. apply FJ_inv. exact (proj1 (HmemL x Hx)). }
  destruct (Esum_free3 rr FJ L HG) as [q Hq].
  (* and the two fixed points contribute 1 each *)
  assert (HJ : Jsum p pi = eadd (eZ 2) (emul (eZ 3) q)).
  { change (Jsum p pi) with (Esum FJ XL).
    rewrite Hsplit, (Hfix a Ha Hra), (Hfix b Hb Hrb), Hq.
    assert (E : eadd eone (eadd eone (emul (eZ 3) q))
                = eadd (eadd eone eone) (emul (eZ 3) q)) by ring.
    rewrite E, eone_plus_eone. reflexivity. }
  rewrite HJ. apply primary_of_form.
Qed.

(* ---- and it is an associate of pi or of its conjugate -------------- *)
Lemma unit_of_same_norm : forall z q, enorm z = Z.of_nat p ->
  z = emul pi q -> eunit q.
Proof.
  intros z q Hz Hq. apply norm_eunit.
  assert (E : enorm z = enorm pi * enorm q) by (rewrite Hq, enorm_mul; reflexivity).
  rewrite Hz, Hn in E. nia.
Qed.

Theorem Jsum_assoc :
  (exists u, eunit u /\ Jsum p pi = emul pi u)
  \/ (exists u, eunit u /\ Jsum p pi = emul (econj pi) u).
Proof.
  assert (Hirr : eirred pi) by (apply (norm_prime_eirred pi (Z.of_nat p)); assumption).
  assert (HN : enorm (Jsum p pi) = Z.of_nat p)
    by (apply (norm_Jsum p pi t0); assumption).
  (* pi divides p = J . conj J *)
  assert (Hdvd : edvd pi (emul (Jsum p pi) (econj (Jsum p pi)))).
  { rewrite emul_econj, HN. exact (pi_dvd_p pi (Z.of_nat p) Hn). }
  destruct (irred_prime pi _ _ Hirr Hdvd) as [H | H].
  - left. destruct H as [q Hq]. exists q.
    split; [ exact (unit_of_same_norm _ q HN Hq) | exact Hq ].
  - right. destruct H as [q Hq]. exists (econj q).
    assert (HNc : enorm (econj (Jsum p pi)) = Z.of_nat p)
      by (rewrite enorm_econj; exact HN).
    split.
    + apply eunit_econj. exact (unit_of_same_norm _ q HNc Hq).
    + rewrite <- (econj_invol (Jsum p pi)), Hq, econj_mul. reflexivity.
Qed.

(* the sharp form, once it is known which of pi, conj pi divides J *)
Corollary Jsum_eq_primary : forall u, eunit u ->
  primary (emul pi u) -> edvd pi (Jsum p pi) -> Jsum p pi = emul pi u.
Proof.
  intros u Hu Hpr [q Hq].
  assert (HN : enorm (Jsum p pi) = Z.of_nat p)
    by (apply (norm_Jsum p pi t0); assumption).
  assert (Hqu : eunit q) by exact (unit_of_same_norm _ q HN Hq).
  rewrite Hq.
  apply (primary_unique pi q u Hqu Hu); [ rewrite <- Hq | exact Hpr ].
  apply Jsum_primary.
Qed.

End JPrimary.

Print Assumptions Esum_free3.
Print Assumptions rr_cycle.
Print Assumptions roots_exist.
Print Assumptions Jsum_primary.
Print Assumptions Jsum_assoc.
