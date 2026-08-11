(* ================================================================= *)
(*  NewmanLimits.v  —  Newman A3: the limit-taking atoms of the contour. *)
(*                                                                    *)
(*  The two limits that drive Newman's triple limit:                     *)
(*    exp_decay_T_cv0 : C e^{-delta T} -> 0 as T -> oo   (kills the         *)
(*                      away-from-axis g-left part, gleft_arc_decay),      *)
(*    bound_over_R_cv0: C / R -> 0 as R -> oo   (kills the O(B/R) arc        *)
(*                      contributions, newman_arc_ML / left_arc_bound).    *)
(*  Axiom-clean.                                                         *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import LaplaceFull PerronSeriesInt GammaFunction.
Open Scope R_scope.

(*  the T -> oo decay: C e^{-delta T} -> 0  (delta > 0)  *)
Lemma exp_decay_T_cv0 : forall delta C, 0 < delta ->
  Un_cv (fun n => C * exp (- (delta * INR n))) 0.
Proof.
  intros delta C Hd; replace 0 with (C * 0) by ring.
  apply Un_cv_cscal_R, exp_neg_cv0, cv_infty_scal_pos;
    [ exact Hd | apply cv_infty_INR_loc ].
Qed.

(*  the R -> oo decay: C / R -> 0  (along R = INR (S n))  *)
Lemma bound_over_R_cv0 : forall C, Un_cv (fun n => C / INR (S n)) 0.
Proof.
  intro C; exact (Un_cv_shift (fun N => C / INR N) 0 1 (Un_cv_C_over_N C)).
Qed.

Print Assumptions exp_decay_T_cv0.
Print Assumptions bound_over_R_cv0.

(* ================================================================= *)
(*  END NewmanLimits.v — the T->oo and R->oo limit atoms.                 *)
(*  With all the modulus estimates (right_arc_bound, left_arc_bound,       *)
(*  gleft_decay, gleft_nearaxis) these are the limits Newman takes: fix R,  *)
(*  send delta->0 (near-axis O(delta)) then T->oo (away e^{-delta T}) to    *)
(*  bound g(0)-g_T(0) by O(B/R), then R->oo.  What remains is Cauchy's      *)
(*  formula on the contour and g's analytic continuation (Phi via zeta).    *)
(* ================================================================= *)
