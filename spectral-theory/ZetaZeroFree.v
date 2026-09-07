(* ================================================================= *)
(*  ZetaZeroFree.v  --  a zero-free region for zeta with EXPLICIT     *)
(*  height dependence.                                                *)
(*                                                                    *)
(*      zF (mkC beta g) = C0,  2 <= |g|   ==>                          *)
(*          beta <= 1 - 27 / (256 * Kg g)                              *)
(*                                                                    *)
(*  with Kg g explicit, growing like ln^9 |g|.  This is the classical  *)
(*  de la Vallee Poussin SHAPE.                                        *)
(*                                                                    *)
(*  Both halves already existed and had never been joined -- nothing   *)
(*  in the repository imports ZeroFreeRegion.v at all, and             *)
(*  ZetaDerivBoundExt is used only inside its own file:                *)
(*                                                                    *)
(*    ZeroFreeRegion.region_of_zero'      needs a derivative bound M   *)
(*    ZetaDerivBoundExt.zeta_deriv_log_bound_ext   supplies one        *)
(*                                                                    *)
(*  THE CASE SPLIT is the whole difficulty.  The derivative bound      *)
(*  holds only for Re s >= 1 - d, so it cannot cover the segment       *)
(*  [beta, 1 + 81/(256K)] when beta is small.  But there the           *)
(*  conclusion is free, because 27/(256K) <= d <= 1 - beta.            *)
(*                                                                    *)
(*  d := Rmin (/4) (/ ln (|g|+3)) is what makes B constant (= e) and   *)
(*  so M = O(ln^2 |g|).  Taking d = 1/4 fixed instead would force      *)
(*  B = (|g|+3)^{1/4} and a region of width ~ 1/(|g| ln^9 |g|) --      *)
(*  worse by a factor of |g|.  The Rmin also lets the theorem cover    *)
(*  every |g| >= 2; the existing zeta_deriv_log_bound_below, which     *)
(*  fixes d = /ln|t|, needs 4 <= ln|t| and so only |g| >= 55.          *)
(*                                                                    *)
(*  ON THE SIZE.  The constant is astronomically bad: the region has   *)
(*  width about 5e-16 at |g| = 2 and 1.7e-19 at |g| = 1e6, against     *)
(*  de la Vallee Poussin's ~0.07.  What is bought is the SHAPE and     *)
(*  the fact that it is unconditional and uniform in height -- not     *)
(*  the numbers.  DepthBound.zero_free_region_on_disk already excludes *)
(*  a sub-strip on each disk, but with no control of the exclusion as  *)
(*  the radius grows; this replaces that existential with a formula.   *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import ComplexField Cmodulus Holomorphic ZetaFn ZetaDeriv CZeta
        CriticalDepth ZeroFreeOpt ZeroFreeRegion ZetaDerivBoundExt
        RiemannXiEntire ZetaOpenStrip GammaCNe0.
Open Scope R_scope.

(* ---- two elementary facts about exp ---- *)

Lemma exp_le' : forall a b, a <= b -> exp a <= exp b.
Proof.
  intros a b H; destruct (Rle_lt_or_eq_dec a b H) as [K | K];
    [ left; apply exp_increasing; exact K | subst; apply Rle_refl ].
Qed.

Lemma two_lt_e : 2 < exp 1.
Proof. pose proof (exp_ineq1 1 ltac:(lra)); lra. Qed.

(* ================================================================= *)
(*  The explicit constants.                                           *)
(* ================================================================= *)

Definition dg (g : R) : R := Rmin (/ 4) (/ ln (Rabs g + 3)).

Definition Mg (g : R) : R :=
  exp 1 * (ln (Rabs g) + 4) ^ 2 + 3 * exp 1 + 16 * exp 1 / dg g.

Definition Kg (g : R) : R :=
  16 * (343 * (ln (2 * Rabs g) + 10)) * (Mg g) ^ 4.

(* ---- basic size facts, all from 2 <= |g| ---- *)

Section Sizes.
Variable g : R.
Hypothesis Hg : 2 <= Rabs g.

Lemma ln3_ge1 : 1 <= ln (Rabs g + 3).
Proof.
  rewrite <- ln_exp at 1. apply Rlt_le, ln_increasing; [ apply exp_pos | ].
  pose proof exp_le_3; lra.
Qed.

Lemma dg_pos : 0 < dg g.
Proof.
  unfold dg; apply Rmin_pos; [ lra | ].
  apply Rinv_0_lt_compat; pose proof ln3_ge1; lra.
Qed.

Lemma dg_le4 : dg g <= / 4.
Proof. unfold dg; apply Rmin_l. Qed.

Lemma dg_leL : dg g <= / ln (Rabs g + 3).
Proof. unfold dg; apply Rmin_r. Qed.

Lemma inv_dg_ge4 : 4 <= / dg g.
Proof.
  pose proof dg_pos as H0; pose proof dg_le4 as H4.
  replace 4 with (/ / 4) by field.
  apply Rinv_le_contravar; [ exact H0 | exact H4 ].
Qed.

Lemma inv_dg_geL : ln (Rabs g + 3) <= / dg g.
Proof.
  pose proof dg_pos as H0; pose proof dg_leL as HL; pose proof ln3_ge1 as HL1.
  replace (ln (Rabs g + 3)) with (/ / ln (Rabs g + 3)) by (field; lra).
  apply Rinv_le_contravar; [ exact H0 | exact HL ].
Qed.

(* the exponent choice keeps B constant *)
Lemma rpower_dg : Rpower (Rabs g + 3) (dg g) <= exp 1.
Proof.
  unfold Rpower; apply exp_le'.
  pose proof ln3_ge1 as HL1; pose proof dg_leL as HL; pose proof dg_pos.
  apply Rmult_le_reg_r with (/ ln (Rabs g + 3));
    [ apply Rinv_0_lt_compat; lra | ].
  replace (dg g * ln (Rabs g + 3) * / ln (Rabs g + 3)) with (dg g)
    by (field; lra).
  replace (1 * / ln (Rabs g + 3)) with (/ ln (Rabs g + 3)) by ring.
  exact HL.
Qed.

Lemma Mg_lower : 16 * exp 1 / dg g <= Mg g.
Proof.
  unfold Mg.
  assert (Hln : 0 <= ln (Rabs g)).
  { rewrite <- ln_1; apply Rlt_le, ln_increasing; lra. }
  pose proof (exp_pos 1) as He.
  assert (Hsq : 0 <= (ln (Rabs g) + 4) ^ 2) by nra.
  nra.
Qed.

Lemma Mg_big : 128 <= Mg g.
Proof.
  eapply Rle_trans; [ | apply Mg_lower ].
  pose proof inv_dg_ge4 as H4; pose proof two_lt_e as He; pose proof dg_pos.
  replace (16 * exp 1 / dg g) with (16 * exp 1 * / dg g) by (unfold Rdiv; ring).
  nra.
Qed.

Lemma Mg_pos : 0 < Mg g.
Proof. pose proof Mg_big; lra. Qed.

Lemma ln2g_nonneg : 0 <= ln (2 * Rabs g).
Proof.
  rewrite <- ln_1; apply Rlt_le, ln_increasing; lra.
Qed.

(* Kg * dg is bounded BELOW uniformly -- this is what makes the
   trivial branch work even though dg -> 0 as |g| -> oo *)
Lemma Kg_dg_big : 1 <= Kg g * dg g.
Proof.
  pose proof ln2g_nonneg as HL.
  pose proof Mg_lower as HM.
  pose proof Mg_big as HMb.
  pose proof dg_pos as Hd.
  pose proof two_lt_e as He.
  assert (S1 : 16 * exp 1 <= Mg g * dg g).
  { assert (E : 16 * exp 1 / dg g * dg g = 16 * exp 1) by (field; lra).
    rewrite <- E; apply Rmult_le_compat_r; [ lra | exact HM ]. }
  assert (S2 : 128 ^ 3 <= Mg g ^ 3) by (apply pow_incr; lra).
  assert (S3 : Mg g ^ 4 * dg g = Mg g ^ 3 * (Mg g * dg g)) by ring.
  assert (S4 : 128 ^ 3 * (16 * exp 1) <= Mg g ^ 4 * dg g).
  { rewrite S3; apply Rmult_le_compat;
      [ simpl; lra | lra | exact S2 | exact S1 ]. }
  simpl in S4.
  unfold Kg.
  assert (EK : 16 * (343 * (ln (2 * Rabs g) + 10)) * Mg g ^ 4 * dg g
             = 16 * (343 * (ln (2 * Rabs g) + 10)) * (Mg g ^ 4 * dg g)) by ring.
  rewrite EK.
  assert (HA : 54880 <= 16 * (343 * (ln (2 * Rabs g) + 10))) by lra.
  nra.
Qed.

Lemma Kg_pos : 0 < Kg g.
Proof.
  unfold Kg; pose proof ln2g_nonneg; pose proof Mg_big.
  assert (0 < Mg g ^ 4) by (apply pow_lt; lra). nra.
Qed.

Lemma Kg_ge4 : 4 <= Kg g.
Proof.
  pose proof Kg_dg_big as HD; pose proof Kg_pos as HK;
    pose proof dg_pos as Hd; pose proof dg_le4 as H4.
  nra.
Qed.

Lemma Kg_81 : 81 / (256 * Kg g) <= 1.
Proof.
  pose proof Kg_ge4 as H4; pose proof Kg_pos as HK.
  apply Rmult_le_reg_r with (256 * Kg g); [ nra | ].
  replace (81 / (256 * Kg g) * (256 * Kg g)) with 81 by (field; nra).
  nra.
Qed.

(* the trivial branch: the region is thinner than d *)
Lemma Kg_thin : 27 / (256 * Kg g) <= dg g.
Proof.
  pose proof Kg_dg_big as HD; pose proof Kg_pos as HK; pose proof dg_pos as Hd.
  apply Rmult_le_reg_r with (256 * Kg g); [ nra | ].
  replace (27 / (256 * Kg g) * (256 * Kg g)) with 27 by (field; nra).
  nra.
Qed.

(* ---- the derivative bound on the whole segment ---- *)

Lemma deriv_bound_seg : forall x,
  1 - dg g <= x -> x <= 2 -> Cmod (zDF (mkC x g)) <= Mg g.
Proof.
  intros x Hlo Hhi.
  assert (HIm : Rabs (Im (mkC x g)) = Rabs g) by reflexivity.
  assert (HRe : Re (mkC x g) = x) by reflexivity.
  pose proof dg_pos as Hd; pose proof dg_le4 as H4; pose proof (exp_pos 1) as He.
  assert (Hb := zeta_deriv_log_bound_ext (mkC x g) (dg g) (exp 1)
                  Hd H4 ltac:(rewrite HRe; lra) ltac:(rewrite HRe; lra)
                  ltac:(rewrite HIm; lra)
                  ltac:(pose proof two_lt_e; lra)
                  ltac:(rewrite HIm; apply rpower_dg)).
  rewrite HIm in Hb.
  eapply Rle_trans; [ exact Hb | ].
  unfold Mg; apply Req_le; field; lra.
Qed.

End Sizes.

(* ================================================================= *)
(*  THE ZERO-FREE REGION.                                             *)
(* ================================================================= *)

Theorem zeta_zero_free : forall beta g,
  2 <= Rabs g -> 0 < beta -> beta <= 1 ->
  zF (mkC beta g) = C0 ->
  beta <= 1 - 27 / (256 * Kg g).
Proof.
  intros beta g Hg Hb0 Hb1 Hzero.
  destruct (Rle_lt_dec (1 - dg g) beta) as [Hmain | Htriv].
  - (* the segment is inside the derivative bound's domain *)
    apply (region_of_zero' beta g (Mg g) (Kg g));
      [ apply Mg_pos; exact Hg
      | lra
      | exact Hb0
      | exact Hb1
      | reflexivity
      | exact Hzero
      | apply Kg_81; exact Hg
      | ].
    intros x Hx.
    apply (deriv_bound_seg g Hg x); [ lra | ].
    pose proof (Kg_81 g Hg); lra.
  - (* beta is already far to the left *)
    pose proof (Kg_thin g Hg); lra.
Qed.

(* the same, as a depth bound *)
Corollary zeta_depth_bound : forall beta g,
  2 <= Rabs g -> 0 < beta -> beta <= 1 ->
  zF (mkC beta g) = C0 ->
  depth (mkC beta g) <= ln (256 * Kg g / 27).
Proof.
  intros beta g Hg Hb0 Hb1 Hzero.
  pose proof (Kg_pos g Hg) as HK.
  pose proof (Kg_dg_big g Hg) as HD.
  pose proof (dg_pos g Hg) as Hd; pose proof (dg_le4 g) as H4.
  assert (H54 : 54 <= 256 * Kg g) by nra.
  apply (depth_of_quartic (mkC beta g) (Kg g) HK H54);
    [ cbn [Re]; exact Hb0 | cbn [Re]; apply zeta_zero_free; assumption ].
Qed.

(* ---- non-vacuity: the bound is a genuine constraint, not beta <= 1 ---- *)

Theorem zeta_zero_free_nontrivial : forall g, 2 <= Rabs g ->
  0 < 27 / (256 * Kg g).
Proof.
  intros g Hg; pose proof (Kg_pos g Hg).
  apply Rdiv_lt_0_compat; lra.
Qed.

(* ================================================================= *)
(*  The same in terms of XiC -- i.e. about the NONTRIVIAL zeros, the   *)
(*  object RH is about.                                               *)
(* ================================================================= *)

Lemma mkC_eta : forall z : C, mkC (Re z) (Im z) = z.
Proof. intro z; destruct z; reflexivity. Qed.

Corollary XiC_zero_free : forall z,
  XiC z = C0 -> 2 <= Rabs (Im z) ->
  Re z <= 1 - 27 / (256 * Kg (Im z)).
Proof.
  intros z HXi Hg.
  destruct (XiC_zeros_in_open_strip z HXi) as [Hlo Hhi].
  assert (H1 : Cminus C1 z <> C0).
  { intro Hc; apply (f_equal Re) in Hc; cbn in Hc; lra. }
  assert (Hz : zetaC z Hlo H1 = C0)
    by (apply (XiC_zero_iff_zetaC_zero_final z Hlo H1 Hhi); exact HXi).
  assert (HzF : zF (mkC (Re z) (Im z)) = C0)
    by (rewrite mkC_eta, (zF_eq z Hlo H1); exact Hz).
  assert (Hres : Re z <= 1 - 27 / (256 * Kg (Im z))).
  { apply (zeta_zero_free (Re z) (Im z));
      [ exact Hg | exact Hlo | lra | exact HzF ]. }
  exact Hres.
Qed.

Print Assumptions zeta_zero_free.
Print Assumptions XiC_zero_free.
Print Assumptions zeta_depth_bound.

(* ================================================================= *)
(*  END ZetaZeroFree.v                                                *)
(* ================================================================= *)
