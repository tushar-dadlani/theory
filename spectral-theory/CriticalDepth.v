(* ================================================================= *)
(*  CriticalDepth.v  --  the critical line as the ORIGIN.              *)
(*                                                                    *)
(*  A change of coordinate on the critical strip.  sigma in (0,1) are  *)
(*  the VALUES; the DEPTH is the logit                                 *)
(*                                                                    *)
(*      d(sigma) = ln (sigma / (1 - sigma)),                           *)
(*                                                                    *)
(*  which carries (0,1) onto all of R with 1/2 at the origin and the   *)
(*  two edges at infinity:                                            *)
(*                                                                    *)
(*    VALUES   0 --------- 1/2 --------- 1                             *)
(*    DEPTHS -inf -------- 0 --------- +inf                            *)
(*                                                                    *)
(*  The point is not cosmetic.  In value coordinates the functional    *)
(*  equation is the AFFINE involution z |-> 1 - z and the critical     *)
(*  line is a distinguished value.  In depth coordinates it is plain   *)
(*  NEGATION (logit_odd), so the critical line is the fixed point of   *)
(*  a sign -- i.e. the ORIGIN.  The Klein four-group of a zero         *)
(*  {z, 1-z, conj z, 1-conj z} (ZetaZeroQuadruple.XiC_zero_quadruple)  *)
(*  therefore acts on depth through a sign character, whose kernel is  *)
(*  exactly the critical line.                                        *)
(*                                                                    *)
(*  What this buys, concretely: every zero-free region becomes a       *)
(*  FINITE BOUND on |depth| (zero_free_iff_depth_bound), and RH        *)
(*  becomes depth = 0 (RH_iff_depth_zero).  So the target is no        *)
(*  longer "move a line" but "drive one nonnegative real to zero".    *)
(*                                                                    *)
(*  depth is only defined on the OPEN strip, which is why this file    *)
(*  sits on ZetaOpenStrip.XiC_zeros_in_open_strip: that theorem is     *)
(*  what makes depth TOTAL on the zero set, and hence what makes       *)
(*  RH_iff_depth_zero a statement with no side condition.              *)
(*  Axiom-clean.                                                      *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra.
Require Import ComplexField Cmodulus RiemannXiEntire ZetaZeroQuadruple
        SpectralReflectionBridge ZetaOpenStrip.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  A.  the coordinate                                                 *)
(* ----------------------------------------------------------------- *)
Definition logit (s : R) : R := ln (s / (1 - s)).

Definition depth (z : C) : R := logit (Re z).

Lemma logit_pos_arg : forall s, 0 < s < 1 -> 0 < s / (1 - s).
Proof. intros s [H0 H1]; apply Rdiv_lt_0_compat; lra. Qed.

Theorem logit_half : logit (/ 2) = 0.
Proof. unfold logit. replace (/ 2 / (1 - / 2)) with 1 by field. apply ln_1. Qed.

(* the reflection sigma |-> 1 - sigma becomes NEGATION *)
Theorem logit_odd : forall s, 0 < s < 1 -> logit (1 - s) = - logit s.
Proof.
  intros s [H0 H1]. unfold logit.
  replace (1 - (1 - s)) with s by ring.
  rewrite <- ln_Rinv by (apply Rdiv_lt_0_compat; lra).
  f_equal. field. lra.
Qed.

(* it is a genuine coordinate: strictly increasing *)
Theorem logit_incr : forall s t, 0 < s < 1 -> 0 < t < 1 -> s < t -> logit s < logit t.
Proof.
  intros s t [Hs0 Hs1] [Ht0 Ht1] Hst. unfold logit.
  apply ln_increasing; [ apply Rdiv_lt_0_compat; lra | ].
  apply (Rmult_lt_reg_r ((1 - s) * (1 - t))); [ nra | ].
  field_simplify; nra.
Qed.

Lemma logit_lt_iff : forall s t, 0 < s < 1 -> 0 < t < 1 -> (logit s < logit t <-> s < t).
Proof.
  intros s t Hs Ht. split.
  - intro H. destruct (Rlt_le_dec s t) as [E | E]; [ exact E | exfalso ].
    destruct (Rle_lt_or_eq_dec t s E) as [E2 | E2].
    + pose proof (logit_incr t s Ht Hs E2); lra.
    + subst t; lra.
  - apply logit_incr; assumption.
Qed.

Lemma logit_le_iff : forall s t, 0 < s < 1 -> 0 < t < 1 -> (logit s <= logit t <-> s <= t).
Proof.
  intros s t Hs Ht.
  pose proof (logit_lt_iff s t Hs Ht) as H1.
  pose proof (logit_lt_iff t s Ht Hs) as H2. lra.
Qed.

Lemma logit_inj : forall s t, 0 < s < 1 -> 0 < t < 1 -> logit s = logit t -> s = t.
Proof.
  intros s t Hs Ht H.
  pose proof (proj1 (logit_le_iff s t Hs Ht) ltac:(lra)).
  pose proof (proj1 (logit_le_iff t s Ht Hs) ltac:(lra)). lra.
Qed.

(* depth = 0 is EXACTLY the critical line *)
Theorem depth_zero_iff : forall z, 0 < Re z < 1 -> (depth z = 0 <-> Re z = / 2).
Proof.
  intros z Hz. unfold depth. split.
  - intro H. apply (logit_inj (Re z) (/ 2) Hz ltac:(lra)).
    rewrite logit_half; exact H.
  - intro H. rewrite H; exact logit_half.
Qed.

(* ----------------------------------------------------------------- *)
(*  B.  the edges are at infinite depth                                *)
(* ----------------------------------------------------------------- *)
Theorem logit_diverge_right :
  forall M, exists d, 0 < d /\ forall s, 1 - d < s < 1 -> M < logit s.
Proof.
  intro M. set (e := exp M).
  assert (He : 0 < e) by (unfold e; apply exp_pos).
  exists (/ (1 + e)). split; [ apply Rinv_0_lt_compat; lra | ].
  intros s [Hlo Hhi]. unfold logit.
  replace M with (ln e) by (unfold e; apply ln_exp).
  apply ln_increasing; [ exact He | ].
  apply (Rmult_lt_reg_r (1 - s)); [ lra | ].
  unfold Rdiv; rewrite Rmult_assoc, Rinv_l by lra.
  assert (Hs : e / (1 + e) < s).
  { apply (Rmult_lt_reg_r (1 + e)); [ lra | ].
    unfold Rdiv; rewrite Rmult_assoc, Rinv_l by lra.
    assert (H1d : 1 - / (1 + e) = e / (1 + e)) by (field; lra). nra. }
  nra.
Qed.

Theorem logit_diverge_left :
  forall M, exists d, 0 < d /\ forall s, 0 < s < d -> logit s < M.
Proof.
  intro M. set (e := exp M).
  assert (He : 0 < e) by (unfold e; apply exp_pos).
  exists (e / (1 + e)). split; [ apply Rdiv_lt_0_compat; lra | ].
  intros s [H0 Hlt].
  assert (Hd1 : e / (1 + e) < 1).
  { apply (Rmult_lt_reg_r (1 + e)); [ lra | ].
    unfold Rdiv; rewrite Rmult_assoc, Rinv_l by lra. lra. }
  assert (Hs1 : s < 1) by lra.
  assert (Hkey : s * (1 + e) < e).
  { apply (Rmult_lt_reg_r (/ (1 + e))); [ apply Rinv_0_lt_compat; lra | ].
    replace (s * (1 + e) * / (1 + e)) with s by (field; lra).
    replace (e * / (1 + e)) with (e / (1 + e)) by (unfold Rdiv; ring).
    exact Hlt. }
  unfold logit.
  replace M with (ln e) by (unfold e; apply ln_exp).
  apply ln_increasing; [ apply Rdiv_lt_0_compat; lra | ].
  apply (Rmult_lt_reg_r (1 - s)); [ lra | ].
  unfold Rdiv; rewrite Rmult_assoc, Rinv_l by lra. nra.
Qed.

(* ----------------------------------------------------------------- *)
(*  C.  the Klein four-group acts on depth by a SIGN                   *)
(* ----------------------------------------------------------------- *)
Lemma Re_Sbar : forall z, Re (Sbar z) = 1 - Re z.
Proof. intro z; unfold Sbar, Cminus, Cadd, Copp, Cconj, C1; simpl; ring. Qed.

Lemma Re_Cconj : forall z, Re (Cconj z) = Re z.
Proof. intro z; unfold Cconj; reflexivity. Qed.

Theorem depth_Srefl : forall z, 0 < Re z < 1 -> depth (Srefl z) = - depth z.
Proof.
  intros z Hz. unfold depth. rewrite Re_Srefl. apply logit_odd; exact Hz.
Qed.

Theorem depth_Sbar : forall z, 0 < Re z < 1 -> depth (Sbar z) = - depth z.
Proof.
  intros z Hz. unfold depth. rewrite Re_Sbar. apply logit_odd; exact Hz.
Qed.

Theorem depth_conj : forall z, depth (Cconj z) = depth z.
Proof. intro z; unfold depth; rewrite Re_Cconj; reflexivity. Qed.

(* the kernel of the sign is exactly the critical line *)
Theorem depth_fixed_iff : forall z, 0 < Re z < 1 ->
  (depth (Sbar z) = depth z <-> Re z = / 2).
Proof.
  intros z Hz. rewrite (depth_Sbar z Hz).
  rewrite <- (depth_zero_iff z Hz). lra.
Qed.

(* ----------------------------------------------------------------- *)
(*  D.  depth is TOTAL on the zero set                                 *)
(* ----------------------------------------------------------------- *)
Lemma zero_in_open_strip : forall z, XiC z = C0 -> 0 < Re z < 1.
Proof. exact XiC_zeros_in_open_strip. Qed.

(* ----------------------------------------------------------------- *)
(*  E.  RH, in depth coordinates                                       *)
(* ----------------------------------------------------------------- *)
Theorem RH_iff_depth_zero :
  RiemannHypothesis <-> (forall z, XiC z = C0 -> depth z = 0).
Proof.
  split.
  - intros HRH z Hz. apply (depth_zero_iff z (zero_in_open_strip z Hz)).
    exact (HRH z Hz).
  - intros H z Hz.
    apply (depth_zero_iff z (zero_in_open_strip z Hz)). exact (H z Hz).
Qed.

(* the one-sided form: RH is "no zero has negative depth" *)
Theorem RH_iff_depth_nonneg :
  RiemannHypothesis <-> (forall z, XiC z = C0 -> 0 <= depth z).
Proof.
  rewrite RH_iff_no_left. split.
  - intros H z Hz. pose proof (zero_in_open_strip z Hz) as Hs.
    unfold depth. rewrite <- logit_half.
    apply (logit_le_iff (/ 2) (Re z) ltac:(lra) Hs). exact (H z Hz).
  - intros H z Hz. pose proof (zero_in_open_strip z Hz) as Hs.
    apply (logit_le_iff (/ 2) (Re z) ltac:(lra) Hs).
    rewrite logit_half. exact (H z Hz).
Qed.

(* ----------------------------------------------------------------- *)
(*  F.  the dictionary: zero-free region  <->  finite depth bound      *)
(* ----------------------------------------------------------------- *)
Theorem zero_free_iff_depth_bound : forall s0, 0 < s0 < 1 ->
  ((forall z, XiC z = C0 -> Re z <= s0)
   <-> (forall z, XiC z = C0 -> depth z <= logit s0)).
Proof.
  intros s0 Hs0. split.
  - intros H z Hz. pose proof (zero_in_open_strip z Hz) as Hs.
    apply (logit_le_iff (Re z) s0 Hs Hs0). exact (H z Hz).
  - intros H z Hz. pose proof (zero_in_open_strip z Hz) as Hs.
    apply (logit_le_iff (Re z) s0 Hs Hs0). exact (H z Hz).
Qed.

Print Assumptions logit_odd.
Print Assumptions logit_incr.
Print Assumptions depth_zero_iff.
Print Assumptions depth_Sbar.
Print Assumptions depth_fixed_iff.
Print Assumptions RH_iff_depth_zero.
Print Assumptions RH_iff_depth_nonneg.
Print Assumptions zero_free_iff_depth_bound.
