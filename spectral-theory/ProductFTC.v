(* ================================================================= *)
(*  ProductFTC.v                                                      *)
(*                                                                    *)
(*  GAP-FILL: the 2D PRODUCT-OF-CHAINS Mobius inversion / discrete      *)
(*  Fundamental Theorem of Calculus -- the single-prime to product      *)
(*  lattice step for PosetMobiusFTC (two primes, i.e. divisors of       *)
(*  p^m q^n, a product of two chains).  Axiom-free over Q.             *)
(*                                                                    *)
(*  The 2D transforms are the compositions of the 1D zeta/Mobius        *)
(*  transforms (PosetMobiusFTC) in each coordinate:                    *)
(*    Z2 f m n = sum_{i<=m} sum_{j<=n} f i j     (double divisor sum)   *)
(*    M2 g m n = 2D backward difference           (double Mobius)       *)
(*  and they are mutually inverse:                                     *)
(*    ftc2_1 : M2 (Z2 f) = f                                           *)
(*    ftc2_2 : Z2 (M2 g) = g                                           *)
(*                                                                    *)
(*  The one genuinely new ingredient is that the 1D transforms COMMUTE  *)
(*  across independent coordinates (mobius_t is linear, zeta_t is a      *)
(*  finite sum): mobius_zeta_comm / zeta_mobius_comm.  Then each 2D FTC  *)
(*  is two applications of the 1D FTC (Fubini-style).                  *)
(* ================================================================= *)

Require Import PosetMobiusFTC.
Require Import PrimonGas.
From Stdlib Require Import QArith Lqa List.
Import ListNotations.
Open Scope Q_scope.

(* ================================================================= *)
(*  1.  LINEARITY OF THE 1D TRANSFORMS                               *)
(* ================================================================= *)

Lemma qsum_sub : forall (a b : nat -> Q) l,
  qsum (map (fun i => a i - b i) l) == qsum (map a l) - qsum (map b l).
Proof.
  intros a b; induction l as [|x l IH]; simpl; [ ring | rewrite IH; ring ].
Qed.

Lemma zeta_t_sub : forall (a b : nat -> Q) m,
  zeta_t (fun i => a i - b i) m == zeta_t a m - zeta_t b m.
Proof. intros a b m; unfold zeta_t; apply qsum_sub. Qed.

Lemma zeta_t_ext : forall (a b : nat -> Q) m,
  (forall k, a k == b k) -> zeta_t a m == zeta_t b m.
Proof. intros a b m H; unfold zeta_t; apply qsum_map_ext; exact H. Qed.

Lemma mobius_t_ext : forall (a b : nat -> Q) n,
  (forall k, a k == b k) -> mobius_t a n == mobius_t b n.
Proof.
  intros a b n H; destruct n as [|m]; cbn [mobius_t];
    [ exact (H 0%nat) | rewrite (H (S m)), (H m); reflexivity ].
Qed.

(* ================================================================= *)
(*  2.  THE 1D TRANSFORMS COMMUTE ACROSS INDEPENDENT COORDINATES     *)
(* ================================================================= *)

(* mobius_t (in the k-variable) commutes with zeta_t (in the i-variable) *)
Lemma mobius_zeta_comm : forall (h : nat -> nat -> Q) (a c : nat),
  mobius_t (fun k => zeta_t (fun i => h i k) a) c
  == zeta_t (fun i => mobius_t (fun k => h i k) c) a.
Proof.
  intros h a c; destruct c as [|d]; cbn [mobius_t];
    [ reflexivity | rewrite zeta_t_sub; reflexivity ].
Qed.

(* zeta_t (in the k-variable) commutes with mobius_t (in the i-variable) *)
Lemma zeta_mobius_comm : forall (h : nat -> nat -> Q) (a c : nat),
  zeta_t (fun k => mobius_t (fun i => h i k) c) a
  == mobius_t (fun i => zeta_t (fun k => h i k) a) c.
Proof.
  intros h a c; destruct c as [|d]; cbn [mobius_t];
    [ reflexivity | rewrite zeta_t_sub; reflexivity ].
Qed.

(* ================================================================= *)
(*  3.  THE 2D TRANSFORMS AND THE 2D FTC                             *)
(* ================================================================= *)

Definition Z2 (f : nat -> nat -> Q) : nat -> nat -> Q :=
  fun m n => zeta_t (fun i => zeta_t (fun j => f i j) n) m.

Definition M2 (g : nat -> nat -> Q) : nat -> nat -> Q :=
  fun m n => mobius_t (fun i => mobius_t (fun j => g i j) n) m.

(* differentiating (in j) the double integral collapses the inner sum *)
Lemma inner1 : forall f i n,
  mobius_t (fun j => Z2 f i j) n == zeta_t (fun i' => f i' n) i.
Proof.
  intros f i n; unfold Z2.
  rewrite (mobius_zeta_comm (fun i' j => zeta_t (fun j' => f i' j') j) i n).
  apply zeta_t_ext; intro i'.
  apply (ftc_1 (fun j' => f i' j') n).
Qed.

(* M2 (Z2 f) = f : differentiate the double integral *)
Theorem ftc2_1 : forall f m n, M2 (Z2 f) m n == f m n.
Proof.
  intros f m n; unfold M2.
  rewrite (mobius_t_ext (fun i => mobius_t (fun j => Z2 f i j) n)
                        (fun i => zeta_t (fun i' => f i' n) i) m)
    by (intro i; apply inner1).
  apply (ftc_1 (fun i' => f i' n) m).
Qed.

(* integrating (in j) the double difference collapses the inner sum *)
Lemma inner2 : forall g i n,
  zeta_t (fun j => M2 g i j) n == mobius_t (fun i' => g i' n) i.
Proof.
  intros g i n; unfold M2.
  rewrite (zeta_mobius_comm (fun i' j => mobius_t (fun j' => g i' j') j) n i).
  apply mobius_t_ext; intro i'.
  apply (ftc_2 (fun j' => g i' j') n).
Qed.

(* Z2 (M2 g) = g : integrate the double difference (telescoping) *)
Theorem ftc2_2 : forall g m n, Z2 (M2 g) m n == g m n.
Proof.
  intros g m n; unfold Z2.
  rewrite (zeta_t_ext (fun i => zeta_t (fun j => M2 g i j) n)
                      (fun i => mobius_t (fun i' => g i' n) i) m)
    by (intro i; apply inner2).
  apply (ftc_2 (fun i' => g i' n) m).
Qed.

(* ----------------------------------------------------------------- *)
(*  MASTER THEOREM — the 2D product-of-chains FTC, axiom-free        *)
(* ----------------------------------------------------------------- *)

Theorem product_ftc :
  (forall f m n, M2 (Z2 f) m n == f m n)
  /\ (forall g m n, Z2 (M2 g) m n == g m n).
Proof. split; [ exact ftc2_1 | exact ftc2_2 ]. Qed.

Print Assumptions product_ftc.

(* ================================================================= *)
(*  END ProductFTC.v                                                  *)
(*  2D product-of-chains Mobius inversion: the double divisor-sum       *)
(*  (Z2) and double backward-difference (M2) transforms are mutually    *)
(*  inverse, from the 1D FTC plus the transforms commuting across        *)
(*  independent coordinates.  ZERO Admitted; Closed under global ctx.   *)
(* ================================================================= *)
