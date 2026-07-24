(* ================================================================= *)
(*  GaussianIrreducible.v                                            *)
(*                                                                    *)
(*  UNITS, ASSOCIATES, and EUCLID'S LEMMA in Z[i].                    *)
(*                                                                    *)
(*  Units are the norm-1 elements {1,-1,i,-i}; Z[i] is an integral    *)
(*  domain (multiplicative norm, N(z)=0 iff z=0), so multiplication    *)
(*  cancels.  The payoff is EUCLID'S LEMMA:                           *)
(*                                                                    *)
(*      p irreducible,  p | a*b   =>   p | a  or  p | b.              *)
(*                                                                    *)
(*  Proof (constructive, via Bezout): let g = gcd(p,a) = u*p + v*a.    *)
(*  Since g | p and p is irreducible, p = g*k gives (unit g) or        *)
(*  (unit k) -- the case split is on the factorisation, NOT on         *)
(*  decidability of p|a.  If unit k then p and g are associates so     *)
(*  p | g | a, giving p | a.  If unit g then 1 = U*p + V*a, so         *)
(*  b = U*p*b + V*(a*b) is divisible by p, giving p | b.              *)
(*                                                                    *)
(*  Builds on GaussianGCD (Bezout) + GaussianDivision + Gaussian       *)
(*  units.  AXIOM-FREE.  This is the uniqueness half of UFD.          *)
(* ================================================================= *)

From Stdlib Require Import ZArith Lia.
Require Import GaussianIntegers GaussianDivision GaussianGCD.
Open Scope Z_scope.

(* ================================================================= *)
(*  §1  units                                                        *)
(* ================================================================= *)

Definition ZIunit (u : ZI) : Prop := exists v, ZImul u v = ZI1.

Lemma ZIunit_norm : forall u, ZIunit u <-> ZInorm (-1) u = 1.
Proof.
  intro u; split.
  - intros [v Hv]; exact (unit_norm u v Hv).
  - intro H; exists (ZIconj u); exact (norm1_unit u H).
Qed.

Lemma ZIunit_cases : forall u, ZIunit u ->
  u = ZI1 \/ u = ZIopp ZI1 \/ u = ZIi \/ u = ZIopp ZIi.
Proof. intros u Hu; apply gaussian_units, ZIunit_norm, Hu. Qed.

Lemma ZI1_unit : ZIunit ZI1.
Proof. exists ZI1; ring. Qed.

(* ================================================================= *)
(*  §2  Z[i] is an integral domain: cancellation                     *)
(* ================================================================= *)

Lemma ZI_no_zero_div : forall a z, ZImul a z = ZI0 -> a <> ZI0 -> z = ZI0.
Proof.
  intros a z Haz Ha.
  assert (Hmul : ZInorm (-1) (ZImul a z) = ZInorm (-1) a * ZInorm (-1) z)
    by (unfold ZImul; apply ZInorm_mul).
  rewrite Haz in Hmul.
  pose proof (norm_pos a Ha) as Hpa.
  assert (H0 : ZInorm (-1) ZI0 = 0) by reflexivity.
  apply norm0_zero; nia.
Qed.

Lemma ZImul_cancel_l : forall a x y, a <> ZI0 -> ZImul a x = ZImul a y -> x = y.
Proof.
  intros a x y Ha H.
  assert (Hd : ZImul a (ZIsub x y) = ZI0)
    by (replace (ZImul a (ZIsub x y)) with (ZIsub (ZImul a x) (ZImul a y)) by ring;
        rewrite H; ring).
  pose proof (ZI_no_zero_div a (ZIsub x y) Hd Ha) as Hxy.
  transitivity (ZIadd (ZIsub x y) y); [ ring | rewrite Hxy; ring ].
Qed.

(* ================================================================= *)
(*  §3  associates                                                   *)
(* ================================================================= *)

Definition ZIassoc (a b : ZI) : Prop := exists u, ZIunit u /\ b = ZImul a u.

Lemma ZIassoc_dvd : forall a b, ZIassoc a b -> ZIdvd a b /\ ZIdvd b a.
Proof.
  intros a b [u [[w Hw] Hb]]; split.
  - exists u; exact Hb.
  - exists w; rewrite Hb.
    replace (ZImul (ZImul a u) w) with (ZImul a (ZImul u w)) by ring.
    rewrite Hw; ring.
Qed.

(* mutual divisibility of nonzero elements => associates *)
Lemma dvd_antisym_assoc : forall a b, a <> ZI0 ->
  ZIdvd a b -> ZIdvd b a -> ZIassoc a b.
Proof.
  intros a b Ha [s Hs] [t Ht].
  (* a = b*t = (a*s)*t = a*(s*t), cancel a => 1 = s*t, so s is a unit *)
  assert (Haa : ZImul a ZI1 = ZImul a (ZImul s t))
    by (rewrite Ht at 1; rewrite Hs; ring).
  pose proof (ZImul_cancel_l a ZI1 (ZImul s t) Ha Haa) as Hst.
  exists s; split; [ exists t; symmetry; exact Hst | exact Hs ].
Qed.

(* ================================================================= *)
(*  §4  irreducibles and EUCLID'S LEMMA                              *)
(* ================================================================= *)

Definition ZIirreducible (p : ZI) : Prop :=
  ~ ZIunit p /\ p <> ZI0 /\
  (forall a b, p = ZImul a b -> ZIunit a \/ ZIunit b).

Theorem ZI_euclid_lemma : forall p a b,
  ZIirreducible p -> ZIdvd p (ZImul a b) -> ZIdvd p a \/ ZIdvd p b.
Proof.
  intros p a b [_ [_ Hfac]] Hpab.
  destruct (ZI_bezout a p) as [g [[Hgp Hga] [[u [v Huv]] _]]].
  (* Hgp : g | p ; Hga : g | a ; Huv : g = u*p + v*a *)
  destruct Hgp as [k Hk].          (* p = g*k *)
  destruct (Hfac g k Hk) as [Hug | Huk].
  - (* g is a unit : 1 = U*p + V*a, so p | b *)
    right.
    destruct Hug as [w Hw].        (* g*w = 1 *)
    assert (Hone : ZI1 = ZIadd (ZImul (ZImul u w) p) (ZImul (ZImul v w) a))
      by (rewrite <- Hw, Huv; ring).
    assert (Hb : b = ZIadd (ZImul p (ZImul (ZImul u w) b))
                           (ZImul (ZImul v w) (ZImul a b)))
      by (transitivity (ZImul ZI1 b); [ ring | rewrite Hone; ring ]).
    rewrite Hb; apply ZIdvd_add.
    + exists (ZImul (ZImul u w) b); reflexivity.
    + apply ZIdvd_mul_r; exact Hpab.
  - (* k is a unit : p and g are associates, so p | g | a, hence p | a *)
    left.
    apply (ZIdvd_trans p g a); [ | exact Hga ].
    destruct Huk as [w Hw].        (* k*w = 1 *)
    exists w.                      (* g = p*w *)
    rewrite Hk.
    replace (ZImul (ZImul g k) w) with (ZImul g (ZImul k w)) by ring.
    rewrite Hw; ring.
Qed.

Print Assumptions ZI_euclid_lemma.

(* ================================================================= *)
(*  END GaussianIrreducible.v                                        *)
(*  Units = norm-1 = {1,-1,i,-i}; Z[i] an integral domain (cancel);   *)
(*  associates via units; and EUCLID'S LEMMA: an irreducible dividing  *)
(*  a product divides a factor -- proved constructively from Bezout,   *)
(*  the uniqueness half of unique factorisation in Z[i].              *)
(*  Closed under the global context (axiom-free).                     *)
(* ================================================================= *)
