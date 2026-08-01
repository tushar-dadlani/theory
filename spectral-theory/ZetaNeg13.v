(* ================================================================= *)
(*  ZetaNeg13.v  —  ζ(−13) = −1/12.                                   *)
(*                                                                    *)
(*  The two-sided functional equation at s=14 gives                   *)
(*    π^{−7}·Γ(7)·ζ(14) = π^{13/2}·Γ_ext(−13/2)·ζ_ext(−13).            *)
(*  With Γ(7)=720 (Gam_7), ζ(14)=2π¹⁴/18243225 (BaselZeta14Value),     *)
(*  and Γ_ext(−13/2)=−(128/135135)·Γ(1/2) (prodshift(−13/2) 7 =        *)
(*  (−1/2)(−3/2)…(−13/2) = −135135/128), the powers of π cancel:        *)
(*    720·(2π¹⁴/18243225)·(−135135/128)/π⁷·π^{−13/2}·/√π = −1/12.       *)
(*  (B₁₄ = 7/6, so ζ(−13) = −B₁₄/14 = −1/12, matching ζ(−1).)          *)
(*  No new axioms (classical Reals only).                            *)
(* ================================================================= *)

From Stdlib Require Import Reals Rpower Lra Lia.
Require Import GammaReal GammaRecur GammaExtend XiReflection XiTwoSided
        GammaHalf BaselZeta14Value ZetaNeg3 ZetaNeg5 ZetaNeg7 ZetaNeg9 ZetaNeg11.
Open Scope R_scope.

Lemma Gam_7 : forall (H : 0 < 7), Gam 7 H = 720.
Proof.
  intro H; assert (H6 : 0 < 6) by lra; assert (H61 : 0 < 6 + 1) by lra.
  rewrite (Gam_arg_eq 7 (6 + 1) H H61 ltac:(ring)), (Gam_recur 6 H6 H61), (Gam_6 H6); ring.
Qed.

Lemma GamN_neg13half : forall (Hh : 0 < 1 / 2) (H : 0 < - (13 / 2) + INR 7),
  GamN (- (13 / 2)) 7 H = - (128 / 135135) * Gam (1 / 2) Hh.
Proof.
  intros Hh H; unfold GamN; cbn [prodshift].
  rewrite (Gam_arg_eq (- (13 / 2) + INR 7) (1 / 2) H Hh
             ltac:(rewrite S_INR, S_INR, S_INR, S_INR, S_INR, S_INR, S_INR, INR_0; lra)).
  rewrite !S_INR, INR_0; field; lra.
Qed.

Lemma GamH_neg_13half : forall (Hh : 0 < 1 / 2), GamH (- (13 / 2)) = - (128 / 135135) * Gam (1 / 2) Hh.
Proof.
  intro Hh; assert (H7 : 0 < - (13 / 2) + INR 7)
    by (rewrite S_INR, S_INR, S_INR, S_INR, S_INR, S_INR, S_INR, INR_0; lra).
  rewrite (GamH_eq_GamN (- (13 / 2)) 7 H7); apply GamN_neg13half.
Qed.

Lemma not_nonpos_int_neg13half : not_nonpos_int (- (13 / 2)).
Proof.
  intro n; destruct n as [| [| [| [| [| [| [| m]]]]]]].
  - rewrite INR_0; lra.
  - rewrite S_INR, INR_0; lra.
  - rewrite S_INR, S_INR, INR_0; lra.
  - rewrite S_INR, S_INR, S_INR, INR_0; lra.
  - rewrite S_INR, S_INR, S_INR, S_INR, INR_0; lra.
  - rewrite S_INR, S_INR, S_INR, S_INR, S_INR, INR_0; lra.
  - rewrite S_INR, S_INR, S_INR, S_INR, S_INR, S_INR, INR_0; lra.
  - rewrite !S_INR; pose proof (pos_INR m); lra.
Qed.

Theorem zeta_neg13 : forall (Hh : 0 < 1 / 2),
  Gam (1 / 2) Hh = Rpower PI (1 / 2) -> zeta_ext (-13) = - (1 / 12).
Proof.
  intros Hh HGh.
  assert (Hs0 : 0 < 14) by lra. assert (Hs1 : (14:R) <> 1) by lra.
  assert (Hs2 : 0 < 14 / 2) by lra.
  assert (Hpi : 0 < PI) by apply PI_RGT_0.
  assert (Hpine : PI <> 0) by (apply Rgt_not_eq; exact Hpi).
  assert (H7 : 0 < 7) by lra.
  assert (Hnr : not_nonpos_int ((1 - 14) / 2))
    by (replace ((1 - 14) / 2) with (- (13 / 2)) by lra; apply not_nonpos_int_neg13half).
  pose proof (two_sided_reflection 14 Hs0 Hs1 Hs2 ltac:(lra) Hnr) as HR.
  rewrite (zeta_cont_14 Hs0 Hs1) in HR.
  rewrite (Gam_arg_eq (14 / 2) 7 Hs2 H7 ltac:(lra)), (Gam_7 H7) in HR.
  replace ((1 - 14) / 2) with (- (13 / 2)) in HR by lra.
  replace (1 - 14) with (-13) in HR by lra.
  rewrite (GamH_neg_13half Hh), HGh in HR.
  assert (HP7 : Rpower PI 7 = PI ^ 7)
    by (replace 7 with (INR 7) by (simpl; ring); apply Rpower_pow; exact Hpi).
  rewrite (Rpower_Ropp PI (14 / 2)) in HR.
  replace (14 / 2) with 7 in HR by lra; rewrite HP7 in HR.
  rewrite Ropp_involutive in HR.
  replace (Rpower PI (13 / 2) * (- (128 / 135135) * Rpower PI (1 / 2)) * zeta_ext (-13))
    with (- (128 / 135135) * (Rpower PI (13 / 2) * Rpower PI (1 / 2)) * zeta_ext (-13)) in HR by ring.
  rewrite <- Rpower_plus in HR; replace (13 / 2 + 1 / 2) with 7 in HR by lra.
  rewrite HP7 in HR.
  assert (HPI7 : 0 < PI ^ 7) by (apply pow_lt; exact Hpi).
  apply (Rmult_eq_reg_l (- (128 / 135135) * PI ^ 7));
    [ | apply Rmult_integral_contrapositive_currified; [ lra | apply Rgt_not_eq; exact HPI7 ] ].
  rewrite <- HR; field; exact Hpine.
Qed.

Corollary zeta_ext_neg13 : zeta_ext (-13) = - (1 / 12).
Proof. assert (Hh : 0 < 1 / 2) by lra; exact (zeta_neg13 Hh (Gam_half_Rpower Hh)). Qed.

Print Assumptions zeta_ext_neg13.

(* ================================================================= *)
(*  END ZetaNeg13.v.  ζ(−13) = −1/12.                                 *)
(* ================================================================= *)
