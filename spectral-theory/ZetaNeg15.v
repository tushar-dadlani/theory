(* ================================================================= *)
(*  ZetaNeg15.v  —  ζ(−15) = 3617/8160.                               *)
(*                                                                    *)
(*  The two-sided functional equation at s=16 gives                   *)
(*    π^{−8}·Γ(8)·ζ(16) = π^{15/2}·Γ_ext(−15/2)·ζ_ext(−15).            *)
(*  With Γ(8)=5040 (Gam_8), ζ(16)=3617π¹⁶/325641566250, and            *)
(*  Γ_ext(−15/2)=(256/2027025)·Γ(1/2) (prodshift(−15/2) 8 =            *)
(*  (−1/2)(−3/2)…(−15/2) = 2027025/256), the powers of π cancel:        *)
(*    5040·(3617/325641566250)·(2027025/256) = 3617/8160.              *)
(*  (B₁₆ = −3617/510, so ζ(−15) = −B₁₆/16 = 3617/8160.)                *)
(*  No new axioms (classical Reals only).                            *)
(* ================================================================= *)

From Stdlib Require Import Reals Rpower Lra Lia.
Require Import GammaReal GammaRecur GammaExtend XiReflection XiTwoSided
        GammaHalf BaselZeta16Value ZetaNeg3 ZetaNeg5 ZetaNeg7 ZetaNeg9 ZetaNeg11 ZetaNeg13.
Open Scope R_scope.

Lemma Gam_8 : forall (H : 0 < 8), Gam 8 H = 5040.
Proof.
  intro H; assert (H7 : 0 < 7) by lra; assert (H71 : 0 < 7 + 1) by lra.
  rewrite (Gam_arg_eq 8 (7 + 1) H H71 ltac:(ring)), (Gam_recur 7 H7 H71), (Gam_7 H7); ring.
Qed.

Lemma GamN_neg15half : forall (Hh : 0 < 1 / 2) (H : 0 < - (15 / 2) + INR 8),
  GamN (- (15 / 2)) 8 H = 256 / 2027025 * Gam (1 / 2) Hh.
Proof.
  intros Hh H; unfold GamN; cbn [prodshift].
  rewrite (Gam_arg_eq (- (15 / 2) + INR 8) (1 / 2) H Hh
             ltac:(rewrite S_INR, S_INR, S_INR, S_INR, S_INR, S_INR, S_INR, S_INR, INR_0; lra)).
  rewrite !S_INR, INR_0; field; lra.
Qed.

Lemma GamH_neg_15half : forall (Hh : 0 < 1 / 2), GamH (- (15 / 2)) = 256 / 2027025 * Gam (1 / 2) Hh.
Proof.
  intro Hh; assert (H8 : 0 < - (15 / 2) + INR 8)
    by (rewrite S_INR, S_INR, S_INR, S_INR, S_INR, S_INR, S_INR, S_INR, INR_0; lra).
  rewrite (GamH_eq_GamN (- (15 / 2)) 8 H8); apply GamN_neg15half.
Qed.

Lemma not_nonpos_int_neg15half : not_nonpos_int (- (15 / 2)).
Proof.
  intro n; destruct n as [| [| [| [| [| [| [| [| m]]]]]]]].
  - rewrite INR_0; lra.
  - rewrite S_INR, INR_0; lra.
  - rewrite S_INR, S_INR, INR_0; lra.
  - rewrite S_INR, S_INR, S_INR, INR_0; lra.
  - rewrite S_INR, S_INR, S_INR, S_INR, INR_0; lra.
  - rewrite S_INR, S_INR, S_INR, S_INR, S_INR, INR_0; lra.
  - rewrite S_INR, S_INR, S_INR, S_INR, S_INR, S_INR, INR_0; lra.
  - rewrite S_INR, S_INR, S_INR, S_INR, S_INR, S_INR, S_INR, INR_0; lra.
  - rewrite !S_INR; pose proof (pos_INR m); lra.
Qed.

Theorem zeta_neg15 : forall (Hh : 0 < 1 / 2),
  Gam (1 / 2) Hh = Rpower PI (1 / 2) -> zeta_ext (-15) = 3617 / 8160.
Proof.
  intros Hh HGh.
  assert (Hs0 : 0 < 16) by lra. assert (Hs1 : (16:R) <> 1) by lra.
  assert (Hs2 : 0 < 16 / 2) by lra.
  assert (Hpi : 0 < PI) by apply PI_RGT_0.
  assert (Hpine : PI <> 0) by (apply Rgt_not_eq; exact Hpi).
  assert (H8 : 0 < 8) by lra.
  assert (Hnr : not_nonpos_int ((1 - 16) / 2))
    by (replace ((1 - 16) / 2) with (- (15 / 2)) by lra; apply not_nonpos_int_neg15half).
  pose proof (two_sided_reflection 16 Hs0 Hs1 Hs2 ltac:(lra) Hnr) as HR.
  rewrite (zeta_cont_16 Hs0 Hs1) in HR.
  rewrite (Gam_arg_eq (16 / 2) 8 Hs2 H8 ltac:(lra)), (Gam_8 H8) in HR.
  replace ((1 - 16) / 2) with (- (15 / 2)) in HR by lra.
  replace (1 - 16) with (-15) in HR by lra.
  rewrite (GamH_neg_15half Hh), HGh in HR.
  assert (HP8 : Rpower PI 8 = PI ^ 8)
    by (replace 8 with (INR 8) by (simpl; ring); apply Rpower_pow; exact Hpi).
  rewrite (Rpower_Ropp PI (16 / 2)) in HR.
  replace (16 / 2) with 8 in HR by lra; rewrite HP8 in HR.
  rewrite Ropp_involutive in HR.
  replace (Rpower PI (15 / 2) * (256 / 2027025 * Rpower PI (1 / 2)) * zeta_ext (-15))
    with (256 / 2027025 * (Rpower PI (15 / 2) * Rpower PI (1 / 2)) * zeta_ext (-15)) in HR by ring.
  rewrite <- Rpower_plus in HR; replace (15 / 2 + 1 / 2) with 8 in HR by lra.
  rewrite HP8 in HR.
  assert (HPI8 : 0 < PI ^ 8) by (apply pow_lt; exact Hpi).
  apply (Rmult_eq_reg_l (256 / 2027025 * PI ^ 8));
    [ | apply Rmult_integral_contrapositive_currified; [ lra | apply Rgt_not_eq; exact HPI8 ] ].
  rewrite <- HR; field; exact Hpine.
Qed.

Corollary zeta_ext_neg15 : zeta_ext (-15) = 3617 / 8160.
Proof. assert (Hh : 0 < 1 / 2) by lra; exact (zeta_neg15 Hh (Gam_half_Rpower Hh)). Qed.

Print Assumptions zeta_ext_neg15.

(* ================================================================= *)
(*  END ZetaNeg15.v.  ζ(−15) = 3617/8160.                             *)
(* ================================================================= *)
