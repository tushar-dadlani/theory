(* ================================================================= *)
(*  SecondZero.v  --  TWO DISTINCT nontrivial zeros of Xi on the line. *)
(*                                                                    *)
(*    second_zero_exists : exists t, 16 < t < 22 /\ XiC (crit t) = C0  *)
(*    two_distinct_zeros_exist                                         *)
(*                                                                    *)
(*  Costs nothing: the three sign facts are proved elsewhere           *)
(*  (xir_10_pos, xir_16_neg, xir_22_pos), and                          *)
(*  crit_sign_change_gives_zero_collapse turns each sign change into a *)
(*  Xi zero, a zeta zero and the alternating-sum collapse at once.     *)
(*  Applying it on [10,16] and on [16,22] gives t1 < 16 < t2, so the   *)
(*  two zeros are distinct without any further argument.               *)
(*                                                                    *)
(*  WHAT THE COMPARISON SHOWED.  The second zero is far harder than    *)
(*  the first, and for a structural reason: Xi(1/2+it) decays like     *)
(*  e^{-pi t/4}, and the margin the proof consumes carries a further   *)
(*  1/t^2, so between the 2nd and 3rd zeros the peak of |xir| is       *)
(*  7.8e-6 against 8.0e-4 between the 1st and 2nd -- and the Re TC     *)
(*  margin 1.6e-8 against 3.3e-6, a factor 200.  At the midpoint       *)
(*  rule's O(h^2) that is ~32000 panels; the O(h^4) rule built for     *)
(*  this needs 512.                                                    *)
(*  Axiom-clean.                                                       *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra.
Require Import ComplexField RiemannXiEntire CoherenceSingularity
        CritLineZeroCollapse EtaZetaStripC
        FirstZeroT10 FirstZeroT16 SecondZeroT22.
Local Open Scope R_scope.

Theorem second_zero_exists :
  exists t, 16 < t < 22
         /\ XiC (crit t) = C0
         /\ ccollapses (ceta_partial (crit t)).
Proof.
  assert (Hsign : xir 16 * xir 22 < 0).
  { pose proof xir_16_neg. pose proof xir_22_pos. nra. }
  destruct (crit_sign_change_gives_zero_collapse 16 22 ltac:(lra) Hsign)
    as [t [Ht [HX [_ HC]]]].
  exists t. repeat split; try tauto; try apply Ht.
Qed.

Theorem two_distinct_zeros_exist :
  exists t1 t2, (10 < t1 < 16) /\ (16 < t2 < 22)
         /\ XiC (crit t1) = C0 /\ XiC (crit t2) = C0
         /\ ccollapses (ceta_partial (crit t1))
         /\ ccollapses (ceta_partial (crit t2)).
Proof.
  assert (Hs1 : xir 10 * xir 16 < 0).
  { pose proof xir_10_pos. pose proof xir_16_neg. nra. }
  assert (Hs2 : xir 16 * xir 22 < 0).
  { pose proof xir_16_neg. pose proof xir_22_pos. nra. }
  destruct (crit_sign_change_gives_zero_collapse 10 16 ltac:(lra) Hs1)
    as [t1 [Ht1 [HX1 [_ HC1]]]].
  destruct (crit_sign_change_gives_zero_collapse 16 22 ltac:(lra) Hs2)
    as [t2 [Ht2 [HX2 [_ HC2]]]].
  exists t1, t2. repeat split; try tauto; try apply Ht1; try apply Ht2.
Qed.

Print Assumptions second_zero_exists.
Print Assumptions two_distinct_zeros_exist.
