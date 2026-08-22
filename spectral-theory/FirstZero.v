(* ================================================================= *)
(*  FirstZero.v  --  a nontrivial zero of Xi ON the critical line.     *)
(*                                                                    *)
(*    first_zero_exists :                                              *)
(*      exists t, 12 < t < 16 /\ XiC (crit t) = C0                     *)
(*             /\ ccollapses (ceta_partial (crit t))                   *)
(*                                                                    *)
(*  This is the first theorem in the tree asserting that a zeta zero   *)
(*  EXISTS.  Everything before it -- counting, density, Hadamard       *)
(*  factorisation, reflection symmetry, depth -- is about zeros        *)
(*  without ever establishing that the set is nonempty.                *)
(*                                                                    *)
(*  It costs nothing: the two sign changes are proved in FirstZeroT12  *)
(*  and FirstZeroT16 (those are the expensive files), and              *)
(*  CritLineZeroCollapse.crit_sign_change_gives_zero_collapse turns a  *)
(*  sign change of xir into a Xi zero, a zeta zero and the alternating *)
(*  -sum collapse, all at once, all on the critical line.              *)
(*  Axiom-clean.                                                       *)
(* ================================================================= *)

From Stdlib Require Import QArith Qreals Reals Lra Lia.
Require Import ComplexField RiemannXiEntire CoherenceSingularity CritLineZeroCollapse
        EtaZetaStripC FirstZeroT12 FirstZeroT16.
Local Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  C.  THE ZERO                                                      *)
(* ----------------------------------------------------------------- *)
Theorem first_zero_exists :
  exists t, 12 < t < 16
         /\ XiC (crit t) = C0
         /\ ccollapses (ceta_partial (crit t)).
Proof.
  assert (Hsign : xir 12 * xir 16 < 0).
  { pose proof xir_12_pos. pose proof xir_16_neg. nra. }
  destruct (crit_sign_change_gives_zero_collapse 12 16 ltac:(lra) Hsign)
    as [t [Ht [HX [_ HC]]]].
  exists t. repeat split; try tauto; try apply Ht.
Qed.

Print Assumptions xir_12_pos.
Print Assumptions xir_16_neg.
Print Assumptions first_zero_exists.
