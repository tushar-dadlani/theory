(* ================================================================= *)
(*  DepthBound.v  --  pushing the depth bound down.                    *)
(*                                                                    *)
(*    depth_bounded_on_disk      : |depth| <= D on every disk          *)
(*    zero_free_substrip_on_disk : hence a STRICT sub-strip            *)
(*        1 - s0 <= Re z <= s0   with  1/2 <= s0 < 1                   *)
(*                                                                    *)
(*  WHAT THE ZERO-FREE REGION ALONE GIVES: NOTHING.  This is worth     *)
(*  saying plainly, because it is the whole reason this file needs a   *)
(*  second ingredient.  zero_free_iff_depth_bound converts a region    *)
(*  Re z <= s0 into a depth bound logit s0.  The region we have        *)
(*  unconditionally is Re z < 1 (ZetaOpenStrip), i.e. s0 = 1 -- and    *)
(*  logit is +infinity there.  The one zero-free region this repo      *)
(*  possesses is precisely the one that is vacuous in depth            *)
(*  coordinates.  A finite depth bound is equivalent to a zero-free    *)
(*  strip Re z <= s0 with s0 < 1 FIXED, which is quasi-RH: far         *)
(*  stronger than anything known.                                     *)
(*                                                                    *)
(*  WHAT DOES WORK is to spend a second, independent resource --       *)
(*  FINITENESS.  XiZeroCount.xi_zero_count produces, for every radius, *)
(*  a finite list containing every zero in that disk (its completeness *)
(*  clause).  Finitely many zeros, each strictly inside the strip, ==> *)
(*  a maximum strictly inside the strip.  So the bound is finite at    *)
(*  every height even though it is not uniform in height.             *)
(*                                                                    *)
(*  This is a genuine sharpening: ZetaOpenStrip gives 0 < Re z < 1     *)
(*  pointwise with no uniformity, and no s0 < 1 that works for even    *)
(*  one zero is exhibited by it.  Here s0 < 1 is produced explicitly   *)
(*  as expit D, uniformly over a whole disk.                          *)
(*                                                                    *)
(*  What it does NOT do, and must not be read as doing: D depends on   *)
(*  the radius, and nothing here bounds its growth.  RH is D = 0 for   *)
(*  every radius.  Axiom-clean.                                        *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra List.
Import ListNotations.
Require Import ComplexField Cmodulus RiemannXiEntire XiZeroCount
        ZetaOpenStrip SpectralReflectionBridge CriticalDepth.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  A.  the maximum depth over a finite list                           *)
(* ----------------------------------------------------------------- *)
Fixpoint dmax (l : list C) : R :=
  match l with
  | [] => 0
  | z :: t => Rmax (Rabs (depth z)) (dmax t)
  end.

Lemma abs_le_split : forall x a, Rabs x <= a -> - a <= x <= a.
Proof.
  intros x a H. split.
  - pose proof (Rle_abs (- x)) as H1; rewrite Rabs_Ropp in H1; lra.
  - pose proof (Rle_abs x); lra.
Qed.

Lemma dmax_nonneg : forall l, 0 <= dmax l.
Proof.
  induction l as [| a t IH]; simpl; [ lra | ].
  eapply Rle_trans; [ exact IH | apply Rmax_r ].
Qed.

Lemma dmax_ub : forall l z, In z l -> Rabs (depth z) <= dmax l.
Proof.
  induction l as [| a t IH]; simpl; [ contradiction | ].
  intros z [Heq | Hin].
  - subst a. apply Rmax_l.
  - eapply Rle_trans; [ apply IH; exact Hin | apply Rmax_r ].
Qed.

(* ----------------------------------------------------------------- *)
(*  B.  the depth is bounded on every disk                             *)
(* ----------------------------------------------------------------- *)
Theorem depth_bounded_on_disk : forall r, 0 < r ->
  exists D, 0 <= D /\ forall z, XiC z = C0 -> Cmod z < r -> Rabs (depth z) <= D.
Proof.
  intros r Hr.
  destruct (xi_zero_count (8 * (r + 1)) ltac:(lra))
    as [l [Rj [HRj0 [HRjb [HRjlo [_ [_ [Hcomp _]]]]]]]].
  exists (dmax l). split; [ apply dmax_nonneg | ].
  intros z Hz Hmod. apply dmax_ub. apply Hcomp; [ lra | exact Hz ].
Qed.

(* ----------------------------------------------------------------- *)
(*  C.  hence a STRICT sub-strip, symmetric about the critical line    *)
(* ----------------------------------------------------------------- *)
Theorem zero_free_substrip_on_disk : forall r, 0 < r ->
  exists s0, / 2 <= s0 < 1 /\
    forall z, XiC z = C0 -> Cmod z < r -> 1 - s0 <= Re z <= s0.
Proof.
  intros r Hr.
  destruct (depth_bounded_on_disk r Hr) as [D [HD0 HD]].
  exists (expit D). split.
  { split.
    - rewrite <- expit_zero. apply expit_le_iff. exact HD0.
    - apply expit_range. }
  intros z Hz Hmod.
  pose proof (XiC_zeros_in_open_strip z Hz) as Hstrip.
  pose proof (HD z Hz Hmod) as Habs.
  pose proof (abs_le_split (depth z) D Habs) as [Hlo Hhi].
  unfold depth in Hlo, Hhi.
  split.
  - rewrite <- (expit_odd D). apply value_le_depth; [ exact Hstrip | exact Hlo ].
  - apply depth_le_value; [ exact Hstrip | exact Hhi ].
Qed.

(* ----------------------------------------------------------------- *)
(*  D.  the same statement read back as a zero-free region             *)
(* ----------------------------------------------------------------- *)
Theorem zero_free_region_on_disk : forall r, 0 < r ->
  exists s0, / 2 <= s0 < 1 /\
    forall z, s0 < Re z -> Cmod z < r -> XiC z <> C0.
Proof.
  intros r Hr.
  destruct (zero_free_substrip_on_disk r Hr) as [s0 [Hs0 H]].
  exists s0. split; [ exact Hs0 | ].
  intros z Hgt Hmod Hz. destruct (H z Hz Hmod) as [_ Hle]. lra.
Qed.

(* RH is exactly: the bound is 0, at every radius. *)
Theorem RH_iff_depth_bound_zero :
  RiemannHypothesis <->
  (forall r, 0 < r -> forall z, XiC z = C0 -> Cmod z < r -> Rabs (depth z) <= 0).
Proof.
  rewrite RH_iff_depth_zero. split.
  - intros H r Hr z Hz _. rewrite (H z Hz), Rabs_R0. lra.
  - intros H z Hz.
    assert (Hr : 0 < Cmod z + 1)
      by (pose proof (Cmod_nonneg z); lra).
    pose proof (H (Cmod z + 1) Hr z Hz ltac:(lra)) as Hb.
    pose proof (abs_le_split (depth z) 0 Hb) as [H1 H2]. lra.
Qed.

Print Assumptions depth_bounded_on_disk.
Print Assumptions zero_free_substrip_on_disk.
Print Assumptions zero_free_region_on_disk.
Print Assumptions RH_iff_depth_bound_zero.
