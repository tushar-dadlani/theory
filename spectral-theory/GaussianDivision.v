(* ================================================================= *)
(*  GaussianDivision.v                                               *)
(*                                                                    *)
(*  Z[i] IS A EUCLIDEAN DOMAIN under the norm.  The cornerstone of     *)
(*  unique factorisation: for b <> 0 there exist q, r with            *)
(*                                                                    *)
(*      a = q * b + r     and     N(r) < N(b).                        *)
(*                                                                    *)
(*  Construction: round a * conj(b) / N(b) to the nearest Gaussian     *)
(*  integer coordinatewise.  If p = a*conj(b) = (X,Y) and d = N(b),    *)
(*  take q = (round(X/d), round(Y/d)); then                           *)
(*      r * conj(b) = (X - qx*d, Y - qy*d)                            *)
(*  has each coordinate of absolute value <= d/2, so                  *)
(*      N(r)*d = N(r*conj b) = (X-qx d)^2 + (Y-qy d)^2 <= d^2/2 < d^2, *)
(*  giving N(r) < d = N(b).                                           *)
(*                                                                    *)
(*  Builds on GaussianIntegers.v (ring, multiplicative norm N,         *)
(*  conjugate, a*conj a = N(a)).  AXIOM-FREE.                          *)
(* ================================================================= *)

From Stdlib Require Import ZArith Lia.
Require Import GaussianIntegers.
Open Scope Z_scope.

(* ================================================================= *)
(*  §1  nearest-integer quotient over Z                              *)
(* ================================================================= *)

(* round(x/d) for d > 0 : the integer q with |x - q*d| <= d/2 *)
Definition znear (x d : Z) : Z := (2 * x + d) / (2 * d).

Lemma znear_spec : forall x d, 0 < d -> - d <= 2 * (x - znear x d * d) <= d.
Proof.
  intros x d Hd; unfold znear.
  pose proof (Z.div_mod (2 * x + d) (2 * d) ltac:(lia)) as Hdm.
  pose proof (Z.mod_pos_bound (2 * x + d) (2 * d) ltac:(lia)) as Hb.
  nia.
Qed.

(* ================================================================= *)
(*  §2  conjugate preserves the norm                                 *)
(* ================================================================= *)

Lemma ZInorm_conj : forall a, ZInorm (-1) (ZIconj a) = ZInorm (-1) a.
Proof. intro a; unfold ZInorm, ZIconj; cbn [zRe zIm]; ring. Qed.

Lemma norm0_zero : forall b, ZInorm (-1) b = 0 -> b = ZI0.
Proof.
  intro b; rewrite ZInorm_neg1; intro H.
  apply ZIeq; cbn [zRe zIm ZI0]; nia.
Qed.

Lemma norm_pos : forall b, b <> ZI0 -> 0 < ZInorm (-1) b.
Proof.
  intro b; intro Hb; pose proof (ZInorm_nonneg b).
  destruct (Z.eq_dec (ZInorm (-1) b) 0) as [E|E]; [ exfalso; apply Hb, norm0_zero, E | lia ].
Qed.

(* ================================================================= *)
(*  §3  the quotient, remainder, and the Euclidean property          *)
(* ================================================================= *)

Definition ZIdiv (a b : ZI) : ZI :=
  mkZI (znear (zRe (ZImul a (ZIconj b))) (ZInorm (-1) b))
       (znear (zIm (ZImul a (ZIconj b))) (ZInorm (-1) b)).

Definition ZImod (a b : ZI) : ZI := ZIsub a (ZImul (ZIdiv a b) b).

Lemma ZI_div_mod : forall a b, a = ZIadd (ZImul (ZIdiv a b) b) (ZImod a b).
Proof. intros a b; unfold ZImod; ring. Qed.

Theorem ZI_euclid_norm : forall a b, b <> ZI0 ->
  ZInorm (-1) (ZImod a b) < ZInorm (-1) b.
Proof.
  intros a b Hb.
  set (d := ZInorm (-1) b).
  set (p := ZImul a (ZIconj b)).
  set (qx := znear (zRe p) d).
  set (qy := znear (zIm p) d).
  assert (Hd : 0 < d) by (apply norm_pos; exact Hb).
  (* the quotient and remainder *)
  set (q := ZIdiv a b).
  assert (Hq : q = mkZI qx qy) by reflexivity.
  set (r := ZImod a b).
  (* b * conj b = N(b) as a Gaussian integer *)
  assert (Hbc : ZImul b (ZIconj b) = ZtoZI d)
    by (unfold d, ZImul; exact (ZImulg_conj (-1) b)).
  (* r * conj b = p - q * (d) as coordinates *)
  assert (Hrc : ZImul r (ZIconj b) = mkZI (zRe p - qx * d) (zIm p - qy * d)).
  { assert (Hstep : ZImul r (ZIconj b) = ZIsub p (ZImul q (ZtoZI d))).
    { unfold r, ZImod, p; rewrite <- Hbc; fold q; ring. }
    rewrite Hstep, Hq; apply ZIeq; cbn [zRe zIm ZIsub ZImul ZImulg ZtoZI]; ring. }
  (* N(r) * d = (X - qx d)^2 + (Y - qy d)^2 *)
  assert (Hprod : ZInorm (-1) r * d
                  = (zRe p - qx * d) * (zRe p - qx * d)
                    + (zIm p - qy * d) * (zIm p - qy * d)).
  { transitivity (ZInorm (-1) (ZImul r (ZIconj b))).
    - unfold ZImul; rewrite ZInorm_mul, ZInorm_conj; reflexivity.
    - rewrite Hrc, ZInorm_neg1; cbn [zRe zIm]; ring. }
  (* each coordinate is bounded by d/2 *)
  pose proof (znear_spec (zRe p) d Hd) as Hx.
  pose proof (znear_spec (zIm p) d Hd) as Hy.
  pose proof (ZInorm_nonneg r) as Hrn.
  fold d in Hrn.
  nia.
Qed.

Theorem ZI_euclid : forall a b, b <> ZI0 ->
  a = ZIadd (ZImul (ZIdiv a b) b) (ZImod a b)
  /\ ZInorm (-1) (ZImod a b) < ZInorm (-1) b.
Proof.
  intros a b Hb; split; [ apply ZI_div_mod | apply ZI_euclid_norm; exact Hb ].
Qed.

Print Assumptions ZI_euclid.

(* ================================================================= *)
(*  END GaussianDivision.v                                           *)
(*  Z[i] is a Euclidean domain: nearest-integer rounding of           *)
(*  a*conj(b)/N(b) yields q, r with a = q*b + r and N(r) < N(b).      *)
(*  The cornerstone for gcd / Bezout / unique factorisation in Z[i].  *)
(*  Closed under the global context (axiom-free).                     *)
(* ================================================================= *)
