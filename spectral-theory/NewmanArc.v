(* ================================================================= *)
(*  NewmanArc.v  —  Newman A3: the right-semicircle integrand bound.      *)
(*                                                                    *)
(*  The heart of Newman's O(1/R) contour estimate.  On the circle         *)
(*  |z| = R with Re z > 0, the Newman integrand                          *)
(*    (g(z) - g_T(z)) * e^{zT} * K_R(z),   K_R(z) = 1/z + z/R^2,          *)
(*  has modulus <= 4B/R^2 -- a constant, from the exact cancellation       *)
(*                                                                    *)
(*    |g - g_T| <= 2B e^{-(Re z)T}/(Re z)   (gfull_tail),                 *)
(*    |e^{zT}|   = e^{(Re z)T}              (Cmod_cexpzt),                 *)
(*    |K_R(z)|   = 2|Re z|/R^2              (Cmod_newman_kernel),          *)
(*                                                                    *)
(*  whose product is (2B e^{-xT}/x)(e^{xT})(2x/R^2) = 4B/R^2.  Integrated  *)
(*  over the arc (length pi R) this gives the O(B/R) right-semicircle       *)
(*  contribution.  right_arc_bound is this pointwise estimate.            *)
(*  Axiom-clean.                                                         *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import ComplexField Cmodulus CIntegral2 CExpKernel CNewmanKernel LaplaceFull.
Open Scope R_scope.

Theorem right_arc_bound :
  forall (f : R -> C) (Hfc : Ccont f) (B : R) (Hfb : forall t, Cmod (f t) <= B)
         z (Hz : 0 < Re z) (T : R) (HT : 0 <= T) (R : R) (HR : 0 < R)
         (Hcirc : Cnorm2 z = R * R),
  Cmod (Cmul (Cminus (gfull f Hfc B Hfb z Hz) (LT f Hfc z T))
             (Cmul (cexpzt z T) (newman_kernel R z)))
  <= 4 * B / (R * R).
Proof.
  intros f Hfc B Hfb z Hz T HT R HR Hcirc.
  assert (HRne : R <> 0) by (apply Rgt_not_eq; exact HR).
  assert (HRR : R * R <> 0) by (intro Hc; nra).
  assert (Hzne : Re z <> 0) by (apply Rgt_not_eq; exact Hz).
  assert (Hex : exp (Re z * T) <> 0) by (apply Rgt_not_eq; apply exp_pos).
  rewrite !Cmod_mul, (Cmod_cexpzt z T), (Cmod_newman_kernel R z HR Hcirc).
  eapply Rle_trans.
  - apply Rmult_le_compat_r; [ | apply gfull_tail; exact HT ].
    apply Rmult_le_pos; [ left; apply exp_pos | ].
    unfold Rdiv; apply Rmult_le_pos;
      [ apply Rmult_le_pos; [ lra | apply Rabs_pos ]
      | left; apply Rinv_0_lt_compat; nra ].
  - rewrite (Rabs_pos_eq (Re z)) by (left; exact Hz).
    rewrite exp_Ropp.
    apply Req_le; field; repeat split; assumption.
Qed.

Print Assumptions right_arc_bound.

(* ================================================================= *)
(*  END NewmanArc.v — the pointwise right-semicircle bound 4B/R^2.        *)
(*  Next in the contour estimate: integrate this over the arc (O(B/R)),   *)
(*  bound the left (Re z < 0) contributions of g (analytic continuation,  *)
(*  e^{zT} -> 0) and of g_T (entire, kernel decay), and take T -> oo then  *)
(*  R -> oo to conclude g(0) = int_0^oo f converges (Newman's theorem).   *)
(* ================================================================= *)
