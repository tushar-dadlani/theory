(* ================================================================= *)
(*  GaussianIntegers.v                                               *)
(*                                                                    *)
(*  BRIDGE INTO Z: the ring of integers of the complex field, built    *)
(*  by running ComplexField's parametric ring core over Z instead of   *)
(*  R.  The generator squares to a PARAMETER d (i^2 = d), so           *)
(*                                                                    *)
(*      ZI = Z[e]/(e^2 = d) = Z x Z                                    *)
(*                                                                    *)
(*  is the same weak ring core as ComplexField.Cmulg -- but over Z it   *)
(*  is entirely AXIOM-FREE ("Closed under the global context"): no      *)
(*  classical-Reals machinery is needed, so this is a strictly cleaner  *)
(*  footprint than the R version.  d = -1 is the Gaussian integers      *)
(*  Z[i]; d = 0 the dual integers; d > 0 the split integers.           *)
(*                                                                    *)
(*  THE BRIDGE is the multiplicative NORM  N_d : ZI -> Z,              *)
(*      N_d(a) = Re a ^2 - d * Im a ^2,                                *)
(*  a ring-to-Z map with N_d(a*b) = N_d(a) * N_d(b) (ZInorm_mul) and    *)
(*  a * conj a = N_d(a) as an integer (ZImulg_conj).  For d = -1 this   *)
(*  is N(a) = Re^2 + Im^2 >= 0, and the units are exactly {1,-1,i,-i}   *)
(*  (the elements of norm 1): gaussian_units.                          *)
(*                                                                    *)
(*  So the whole 2-dimensional algebra we proved over R descends to Z   *)
(*  with a genuine homomorphism into Z -- the arithmetic shadow of      *)
(*  ComplexField, and the entry point for sums-of-two-squares /         *)
(*  Gaussian-prime / |Gauss sum|^2 = p style number theory.            *)
(*                                                                    *)
(*  AXIOM-FREE.                                                        *)
(* ================================================================= *)

From Stdlib Require Import ZArith Lia.
Open Scope Z_scope.

(* ----------------------------------------------------------------- *)
(*  Carrier and operations (projection-style, like ComplexField)      *)
(* ----------------------------------------------------------------- *)

Record ZI : Set := mkZI { zRe : Z; zIm : Z }.

Definition ZIadd (a b : ZI) : ZI := mkZI (zRe a + zRe b) (zIm a + zIm b).
Definition ZIopp (a : ZI)   : ZI := mkZI (- zRe a) (- zIm a).
Definition ZIsub (a b : ZI) : ZI := mkZI (zRe a - zRe b) (zIm a - zIm b).
Definition ZI0 : ZI := mkZI 0 0.
Definition ZI1 : ZI := mkZI 1 0.
Definition ZIi : ZI := mkZI 0 1.
Definition ZIconj (a : ZI) : ZI := mkZI (zRe a) (- zIm a).
Definition ZtoZI (n : Z) : ZI := mkZI n 0.

(* the parametric product:  e^2 = d  couples Im*Im by d *)
Definition ZImulg (d : Z) (a b : ZI) : ZI :=
  mkZI (zRe a * zRe b + d * (zIm a * zIm b)) (zRe a * zIm b + zIm a * zRe b).

(* the Gaussian product is the d = -1 instance *)
Definition ZImul (a b : ZI) : ZI := ZImulg (-1) a b.

(* the norm-form:  N_d(a) = Re^2 - d*Im^2  (into Z) *)
Definition ZInorm (d : Z) (a : ZI) : Z := zRe a * zRe a - d * (zIm a * zIm a).

(* extensionality: a Gaussian integer is its two integer coordinates *)
Lemma ZIeq : forall a b : ZI, zRe a = zRe b -> zIm a = zIm b -> a = b.
Proof. intros [ar ai] [br bi]; simpl; intros -> ->; reflexivity. Qed.

(* ================================================================= *)
(*  §1  THE RING CORE  (WEAK LAYER: a commutative ring for every d)   *)
(* ================================================================= *)

(* Z[e]/(e^2 = d) is a commutative ring for EVERY integer d -- the same *)
(* weak core as over R, now AXIOM-FREE.  Proof never mentions i / -1.   *)
Lemma ZIring_theory_g : forall d,
  ring_theory ZI0 ZI1 ZIadd (ZImulg d) ZIsub ZIopp (@eq ZI).
Proof. intro d; constructor; intros; apply ZIeq; cbn [zRe zIm ZIadd ZIopp ZIsub ZImulg ZImul ZIconj ZI0 ZI1 ZIi ZtoZI ZInorm]; ring. Qed.

(* our Gaussian product is the d = -1 point *)
Lemma ZImul_is_gen : forall a b, ZImul a b = ZImulg (-1) a b.
Proof. intros; reflexivity. Qed.

Lemma ZI_ring_theory : ring_theory ZI0 ZI1 ZIadd ZImul ZIsub ZIopp (@eq ZI).
Proof. constructor; intros; apply ZIeq; cbn [zRe zIm ZIadd ZIopp ZIsub ZImulg ZImul ZIconj ZI0 ZI1 ZIi ZtoZI ZInorm]; ring. Qed.

Add Ring ZIRing : ZI_ring_theory.

(* the generator squares to the parameter: e^2 = d *)
Lemma ZIi_sq_g : forall d, ZImulg d ZIi ZIi = ZtoZI d.
Proof. intro d; apply ZIeq; cbn [zRe zIm ZIadd ZIopp ZIsub ZImulg ZImul ZIconj ZI0 ZI1 ZIi ZtoZI ZInorm]; ring. Qed.

(* i^2 = -1 : a DOWNSTREAM d = -1 fact, not a foundation *)
Lemma ZIi_sq : ZImul ZIi ZIi = ZIopp ZI1.
Proof. unfold ZImul; rewrite (ZIi_sq_g (-1)); apply ZIeq; cbn [zRe zIm ZIadd ZIopp ZIsub ZImulg ZImul ZIconj ZI0 ZI1 ZIi ZtoZI ZInorm]; ring. Qed.

(* ================================================================= *)
(*  §2  THE BRIDGE INTO Z : the multiplicative norm  N_d : ZI -> Z    *)
(* ================================================================= *)

(* THE BRIDGE HOMOMORPHISM: the norm carries the product of the        *)
(* 2-D algebra to the product in Z.  Polynomial identity, all d.       *)
Lemma ZInorm_mul : forall d a b,
  ZInorm d (ZImulg d a b) = ZInorm d a * ZInorm d b.
Proof. intros d a b; unfold ZInorm, ZImulg; cbn [zRe zIm]; ring. Qed.

(* a * conj a = N_d(a), landed in Z via ZtoZI *)
Lemma ZImulg_conj : forall d a, ZImulg d a (ZIconj a) = ZtoZI (ZInorm d a).
Proof. intros d a; unfold ZImulg, ZIconj, ZInorm, ZtoZI; apply ZIeq; cbn [zRe zIm ZIadd ZIopp ZIsub ZImulg ZImul ZIconj ZI0 ZI1 ZIi ZtoZI ZInorm]; ring. Qed.

(* basic norm values *)
Lemma ZInorm_ZtoZI : forall d n, ZInorm d (ZtoZI n) = n * n.
Proof. intros d n; unfold ZInorm, ZtoZI; cbn [zRe zIm]; ring. Qed.

Lemma ZInorm_1 : forall d, ZInorm d ZI1 = 1.
Proof. intro d; unfold ZInorm, ZI1; cbn [zRe zIm]; ring. Qed.

(* for the Gaussian case d = -1 the norm is Re^2 + Im^2 >= 0 *)
Lemma ZInorm_neg1 : forall a, ZInorm (-1) a = zRe a * zRe a + zIm a * zIm a.
Proof. intro a; unfold ZInorm; ring. Qed.

Lemma ZInorm_nonneg : forall a, 0 <= ZInorm (-1) a.
Proof. intro a; rewrite ZInorm_neg1; nia. Qed.

(* ================================================================= *)
(*  §3  Z ↪ ZI : injective ring homomorphism, and conjugation        *)
(* ================================================================= *)

Lemma ZtoZI_add : forall m n, ZtoZI (m + n) = ZIadd (ZtoZI m) (ZtoZI n).
Proof. intros; apply ZIeq; cbn [zRe zIm ZIadd ZIopp ZIsub ZImulg ZImul ZIconj ZI0 ZI1 ZIi ZtoZI ZInorm]; ring. Qed.

Lemma ZtoZI_mul : forall m n, ZtoZI (m * n) = ZImul (ZtoZI m) (ZtoZI n).
Proof. intros; apply ZIeq; cbn [zRe zIm ZIadd ZIopp ZIsub ZImulg ZImul ZIconj ZI0 ZI1 ZIi ZtoZI ZInorm]; ring. Qed.

Lemma ZtoZI_inj : forall m n, ZtoZI m = ZtoZI n -> m = n.
Proof. intros m n H; exact (f_equal zRe H). Qed.

Lemma ZIconj_involutive : forall a, ZIconj (ZIconj a) = a.
Proof. intro a; apply ZIeq; cbn [zRe zIm ZIadd ZIopp ZIsub ZImulg ZImul ZIconj ZI0 ZI1 ZIi ZtoZI ZInorm]; ring. Qed.

Lemma ZIconj_add : forall a b, ZIconj (ZIadd a b) = ZIadd (ZIconj a) (ZIconj b).
Proof. intros; apply ZIeq; cbn [zRe zIm ZIadd ZIopp ZIsub ZImulg ZImul ZIconj ZI0 ZI1 ZIi ZtoZI ZInorm]; ring. Qed.

Lemma ZIconj_mul : forall a b, ZIconj (ZImul a b) = ZImul (ZIconj a) (ZIconj b).
Proof. intros; apply ZIeq; cbn [zRe zIm ZIadd ZIopp ZIsub ZImulg ZImul ZIconj ZI0 ZI1 ZIi ZtoZI ZInorm]; ring. Qed.

(* ================================================================= *)
(*  §4  UNITS of the Gaussian integers = elements of norm 1           *)
(* ================================================================= *)

(* if a*b = 1 then N(a) N(b) = 1, and (norms are >= 0) so N(a) = 1 *)
Lemma unit_norm : forall a b, ZImul a b = ZI1 -> ZInorm (-1) a = 1.
Proof.
  intros a b H.
  assert (Hp : ZInorm (-1) a * ZInorm (-1) b = 1).
  { rewrite <- ZInorm_mul; unfold ZImul in H; rewrite H; apply ZInorm_1. }
  assert (HNa := ZInorm_nonneg a); assert (HNb := ZInorm_nonneg b).
  assert (HNa1 : 1 <= ZInorm (-1) a).
  { destruct (Z.eq_dec (ZInorm (-1) a) 0) as [E|E];
      [ rewrite E, Z.mul_0_l in Hp; lia | lia ]. }
  assert (HNb1 : 1 <= ZInorm (-1) b).
  { destruct (Z.eq_dec (ZInorm (-1) b) 0) as [E|E];
      [ rewrite E, Z.mul_0_r in Hp; lia | lia ]. }
  nia.
Qed.

(* the norm-1 elements are exactly {1, -1, i, -i} *)
Lemma gaussian_units : forall a, ZInorm (-1) a = 1 ->
  a = ZI1 \/ a = ZIopp ZI1 \/ a = ZIi \/ a = ZIopp ZIi.
Proof.
  intros a HN; rewrite ZInorm_neg1 in HN.
  assert (Hr2 : 0 <= zRe a * zRe a) by nia.
  assert (Hi2 : 0 <= zIm a * zIm a) by nia.
  assert (Hru : zRe a <= 1) by nia.
  assert (Hrl : -1 <= zRe a) by nia.
  assert (Hiu : zIm a <= 1) by nia.
  assert (Hil : -1 <= zIm a) by nia.
  destruct a as [x y]; simpl in *.
  assert (Hx : x = -1 \/ x = 0 \/ x = 1) by lia.
  assert (Hy : y = -1 \/ y = 0 \/ y = 1) by lia.
  destruct Hx as [ -> | [ -> | -> ] ]; destruct Hy as [ -> | [ -> | -> ] ];
    first [ exfalso; lia
          | left; reflexivity
          | right; left; reflexivity
          | right; right; left; reflexivity
          | right; right; right; reflexivity ].
Qed.

(* every element of norm 1 is a genuine unit: it has an inverse (its    *)
(* conjugate), so norm-1 <=> unit for the Gaussian integers.           *)
Lemma norm1_unit : forall a, ZInorm (-1) a = 1 -> ZImul a (ZIconj a) = ZI1.
Proof.
  intros a HN; unfold ZImul; rewrite (ZImulg_conj (-1) a), HN; reflexivity.
Qed.

(* ----------------------------------------------------------------- *)
(*  MASTER THEOREM — the Z bridge, axiom-free                        *)
(* ----------------------------------------------------------------- *)

Theorem gaussian_integers :
  (* WEAK ring core: Z[e]/(e^2 = d) a commutative ring for every d *)
     (forall d, ring_theory ZI0 ZI1 ZIadd (ZImulg d) ZIsub ZIopp (@eq ZI))
  (* generator squares to the parameter; Gaussian i^2 = -1 is d = -1 *)
  /\ (forall d, ZImulg d ZIi ZIi = ZtoZI d)
  /\ ZImul ZIi ZIi = ZIopp ZI1
  (* THE BRIDGE: the norm is a multiplicative map ZI -> Z *)
  /\ (forall d a b, ZInorm d (ZImulg d a b) = ZInorm d a * ZInorm d b)
  /\ (forall d a, ZImulg d a (ZIconj a) = ZtoZI (ZInorm d a))
  (* Z ↪ ZI injective ring homomorphism *)
  /\ (forall m n, ZtoZI (m + n) = ZIadd (ZtoZI m) (ZtoZI n))
  /\ (forall m n, ZtoZI (m * n) = ZImul (ZtoZI m) (ZtoZI n))
  /\ (forall m n, ZtoZI m = ZtoZI n -> m = n)
  (* Gaussian units = norm-1 elements = {1,-1,i,-i} *)
  /\ (forall a b, ZImul a b = ZI1 -> ZInorm (-1) a = 1)
  /\ (forall a, ZInorm (-1) a = 1 ->
        a = ZI1 \/ a = ZIopp ZI1 \/ a = ZIi \/ a = ZIopp ZIi).
Proof.
  split; [ exact ZIring_theory_g | ].
  split; [ exact ZIi_sq_g | ].
  split; [ exact ZIi_sq | ].
  split; [ exact ZInorm_mul | ].
  split; [ exact ZImulg_conj | ].
  split; [ exact ZtoZI_add | ].
  split; [ exact ZtoZI_mul | ].
  split; [ exact ZtoZI_inj | ].
  split; [ exact unit_norm | exact gaussian_units ].
Qed.

Print Assumptions gaussian_integers.

(* ================================================================= *)
(*  END GaussianIntegers.v                                           *)
(*  The ring of integers Z[e]/(e^2 = d) = Z x Z: ComplexField's weak   *)
(*  ring core run over Z (AXIOM-FREE), with the multiplicative norm     *)
(*  N_d : ZI -> Z (ZInorm_mul) as the bridge into Z, a * conj a = N_d   *)
(*  (ZImulg_conj), the Z-subring embedding, conjugation, and the        *)
(*  Gaussian units {1,-1,i,-i} = norm-1 elements.  d=-1/0/>0 =          *)
(*  Gaussian / dual / split integers.  Closed under the global context. *)
(* ================================================================= *)
