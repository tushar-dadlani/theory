(* ================================================================= *)
(*  ThirdZero.v  --  THREE distinct nontrivial zeros on the line.      *)
(*                                                                    *)
(*    third_zero_exists : exists t, 22 < t < 26 /\ XiC (crit t) = C0   *)
(*    three_distinct_zeros_exist                                       *)
(*                                                                    *)
(*  The three brackets [10,16], [16,22], [22,26] share only their      *)
(*  excluded endpoints, so the zeros are pairwise distinct with no     *)
(*  further argument; each carries the full payload (Xi zero, zeta     *)
(*  zero, alternating-sum collapse).                                   *)
(*                                                                    *)
(*  THE COST CURVE, now measured at three heights rather than two:     *)
(*                                                                    *)
(*     t    Re TC margin   rule       panels   enclosure width         *)
(*    16       3.0e-06     midpoint      768        --                 *)
(*    22       1.6e-08     Simpson       512      5.9e-09              *)
(*    26       9.6e-10     Simpson      1024      1.8e-11              *)
(*                                                                    *)
(*  The margin falls by a factor ~200 from t=16 to t=22 and another    *)
(*  ~17 to t=26, tracking |Xi(1/2+it)| ~ t^{7/4} e^{-pi t/4}.  The     *)
(*  panel count does NOT track it, because the order was raised from   *)
(*  2 to 4 in between -- which is exactly the point: for a fixed order *)
(*  2k the count grows like exp(pi t/(8k)), and raising k divides the  *)
(*  exponent without removing it.  Axiom-clean.                        *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra.
Require Import ComplexField RiemannXiEntire CoherenceSingularity
        CritLineZeroCollapse EtaZetaStripC
        FirstZeroT10 FirstZeroT16 SecondZeroT22 ThirdZeroT26.
Local Open Scope R_scope.

Theorem third_zero_exists :
  exists t, 22 < t < 26
         /\ XiC (crit t) = C0
         /\ ccollapses (ceta_partial (crit t)).
Proof.
  assert (Hsign : xir 22 * xir 26 < 0).
  { pose proof xir_22_pos. pose proof xir_26_neg. nra. }
  destruct (crit_sign_change_gives_zero_collapse 22 26 ltac:(lra) Hsign)
    as [t [Ht [HX [_ HC]]]].
  exists t. repeat split; try tauto; try apply Ht.
Qed.

Theorem three_distinct_zeros_exist :
  exists t1 t2 t3,
       (10 < t1 < 16) /\ (16 < t2 < 22) /\ (22 < t3 < 26)
    /\ XiC (crit t1) = C0 /\ XiC (crit t2) = C0 /\ XiC (crit t3) = C0
    /\ ccollapses (ceta_partial (crit t1))
    /\ ccollapses (ceta_partial (crit t2))
    /\ ccollapses (ceta_partial (crit t3)).
Proof.
  assert (Hs1 : xir 10 * xir 16 < 0).
  { pose proof xir_10_pos. pose proof xir_16_neg. nra. }
  assert (Hs2 : xir 16 * xir 22 < 0).
  { pose proof xir_16_neg. pose proof xir_22_pos. nra. }
  assert (Hs3 : xir 22 * xir 26 < 0).
  { pose proof xir_22_pos. pose proof xir_26_neg. nra. }
  destruct (crit_sign_change_gives_zero_collapse 10 16 ltac:(lra) Hs1)
    as [t1 [Ht1 [HX1 [_ HC1]]]].
  destruct (crit_sign_change_gives_zero_collapse 16 22 ltac:(lra) Hs2)
    as [t2 [Ht2 [HX2 [_ HC2]]]].
  destruct (crit_sign_change_gives_zero_collapse 22 26 ltac:(lra) Hs3)
    as [t3 [Ht3 [HX3 [_ HC3]]]].
  exists t1, t2, t3.
  repeat split; try tauto; try apply Ht1; try apply Ht2; try apply Ht3.
Qed.

Print Assumptions third_zero_exists.
Print Assumptions three_distinct_zeros_exist.
