(* ================================================================= *)
(*  ZetaZeroPairing.v  —  the symmetry structure of the zeros of the   *)
(*  completed zeta about the critical line.                           *)
(*                                                                    *)
(*  The functional equation XiC z = XiC (1 - z) (XiC_symmetric,        *)
(*  RiemannXiEntire.v) reflects the zeros of the entire completed zeta *)
(*  through the centre 1/2: if z is a zero, so is 1 - z.              *)
(*                                                                    *)
(*  So the zeros come in pairs { z, 1 - z } whose real parts average   *)
(*  to 1/2 — a zero at Re = 1/2 + d is mirrored by one at Re = 1/2 - d. *)
(*  RH is exactly the statement that every such pair DEGENERATES onto   *)
(*  the line (d = 0).  This file records that pairing structure,        *)
(*  unconditionally and axiom-clean.                                  *)
(*                                                                    *)
(*  (The complementary reflection about the real axis, z |-> conj z,   *)
(*  would complete the zero-QUADRUPLE picture, but requires proving     *)
(*  TC / XiC commute with complex conjugation — not yet built.)        *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra.
Require Import ComplexField RiemannXiEntire.
Open Scope R_scope.

Lemma Re_one_minus : forall z, Re (Cminus C1 z) = 1 - Re z.
Proof. intro z; unfold Cminus, Cadd, Copp, C1; simpl; ring. Qed.

(* ----------------------------------------------------------------- *)
(*  THE ZERO-PAIRING LEMMA                                           *)
(*  Zeros of the completed zeta are symmetric under z |-> 1 - z.      *)
(* ----------------------------------------------------------------- *)

Theorem XiC_zero_reflect : forall z, XiC z = C0 -> XiC (Cminus C1 z) = C0.
Proof. intros z Hz; rewrite <- (XiC_symmetric z); exact Hz. Qed.

(* the reflected pair straddles the critical line: the two real parts  *)
(* average to 1/2                                                     *)
Lemma zero_pair_straddle : forall z, Re z + Re (Cminus C1 z) = 1.
Proof. intro z; rewrite Re_one_minus; ring. Qed.

(* explicitly: a zero at Re = 1/2 + d is paired with one at 1/2 - d    *)
Lemma zero_pair_symmetric : forall z d,
  Re z = / 2 + d -> Re (Cminus C1 z) = / 2 - d.
Proof. intros z d H; rewrite Re_one_minus, H; lra. Qed.

(* the pairing is trivial (z = 1 - z) exactly at the centre z = 1/2;   *)
(* RH is the stronger claim that all zeros lie on the whole LINE        *)
(* Re z = 1/2 (which needs the conjugate reflection, not just this      *)
(* point reflection)                                                   *)
Lemma reflect_fixed_point : forall z, Cminus C1 z = z -> Re z = / 2.
Proof.
  intros z H; assert (HR : Re (Cminus C1 z) = Re z) by (rewrite H; reflexivity).
  rewrite Re_one_minus in HR; lra.
Qed.

Print Assumptions XiC_zero_reflect.

(* ================================================================= *)
(*  END ZetaZeroPairing.v                                             *)
(*  The zeros of XiC are symmetric about Re = 1/2 under z |-> 1 - z.   *)
(*  RH = every such pair collapses onto the critical line.            *)
(* ================================================================= *)
