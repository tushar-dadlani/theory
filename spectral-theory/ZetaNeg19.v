(* ================================================================= *)
(*  ZetaNeg19.v  —  ζ(−19) = 174611/6600.                             *)
(*                                                                    *)
(*  The two-sided functional equation at s=20 gives                   *)
(*    π^{−10}·Γ(10)·ζ(20) = π^{19/2}·Γ_ext(−19/2)·ζ_ext(−19).          *)
(*  With Γ(10)=362880 (Gam_10), ζ(20)=174611π²⁰/1531329465290625, and  *)
(*  Γ_ext(−19/2)=(1024/654729075)·Γ(1/2) (prodshift(−19/2) 10 =        *)
(*  (−1/2)(−3/2)…(−19/2) = 654729075/1024), the powers of π cancel:     *)
(*    362880·(174611/1531329465290625)·(654729075/1024) = 174611/6600. *)
(*  (B₂₀ = −174611/330, so ζ(−19) = −B₂₀/20 = 174611/6600.)            *)
(*  No new axioms (classical Reals only).                            *)
(* ================================================================= *)

From Stdlib Require Import Reals Rpower Lra Lia.
Require Import GammaReal GammaRecur GammaExtend XiReflection XiTwoSided
        GammaHalf BaselZeta20Value ZetaNeg3 ZetaNeg5 ZetaNeg7 ZetaNeg9 ZetaNeg11 ZetaNeg13 ZetaNeg15 ZetaNeg17.
Open Scope R_scope.

Lemma Gam_10 : forall (H : 0 < 10), Gam 10 H = 362880.
Proof.
  intro H; assert (H9 : 0 < 9) by lra; assert (H91 : 0 < 9 + 1) by lra.
  rewrite (Gam_arg_eq 10 (9 + 1) H H91 ltac:(ring)), (Gam_recur 9 H9 H91), (Gam_9 H9); ring.
Qed.

Lemma GamN_neg19half : forall (Hh : 0 < 1 / 2) (H : 0 < - (19 / 2) + INR 10),
  GamN (- (19 / 2)) 10 H = 1024 / 654729075 * Gam (1 / 2) Hh.
Proof.
  intros Hh H; unfold GamN; cbn [prodshift].
  rewrite (Gam_arg_eq (- (19 / 2) + INR 10) (1 / 2) H Hh
             ltac:(rewrite S_INR, S_INR, S_INR, S_INR, S_INR, S_INR, S_INR, S_INR, S_INR, S_INR, INR_0; lra)).
  rewrite !S_INR, INR_0; field; lra.
Qed.

Lemma GamH_neg_19half : forall (Hh : 0 < 1 / 2), GamH (- (19 / 2)) = 1024 / 654729075 * Gam (1 / 2) Hh.
Proof.
  intro Hh; assert (H10 : 0 < - (19 / 2) + INR 10)
    by (rewrite S_INR, S_INR, S_INR, S_INR, S_INR, S_INR, S_INR, S_INR, S_INR, S_INR, INR_0; lra).
  rewrite (GamH_eq_GamN (- (19 / 2)) 10 H10); apply GamN_neg19half.
Qed.

Lemma not_nonpos_int_neg19half : not_nonpos_int (- (19 / 2)).
Proof.
  intro n; destruct n as [| [| [| [| [| [| [| [| [| [| m]]]]]]]]]].
  - rewrite INR_0; lra.
  - rewrite S_INR, INR_0; lra.
  - rewrite S_INR, S_INR, INR_0; lra.
  - rewrite S_INR, S_INR, S_INR, INR_0; lra.
  - rewrite S_INR, S_INR, S_INR, S_INR, INR_0; lra.
  - rewrite S_INR, S_INR, S_INR, S_INR, S_INR, INR_0; lra.
  - rewrite S_INR, S_INR, S_INR, S_INR, S_INR, S_INR, INR_0; lra.
  - rewrite S_INR, S_INR, S_INR, S_INR, S_INR, S_INR, S_INR, INR_0; lra.
  - rewrite S_INR, S_INR, S_INR, S_INR, S_INR, S_INR, S_INR, S_INR, INR_0; lra.
  - rewrite S_INR, S_INR, S_INR, S_INR, S_INR, S_INR, S_INR, S_INR, S_INR, INR_0; lra.
  - rewrite !S_INR; pose proof (pos_INR m); lra.
Qed.

Theorem zeta_neg19 : forall (Hh : 0 < 1 / 2),
  Gam (1 / 2) Hh = Rpower PI (1 / 2) -> zeta_ext (-19) = 174611 / 6600.
Proof.
  intros Hh HGh.
  assert (Hs0 : 0 < 20) by lra. assert (Hs1 : (20:R) <> 1) by lra.
  assert (Hs2 : 0 < 20 / 2) by lra.
  assert (Hpi : 0 < PI) by apply PI_RGT_0.
  assert (Hpine : PI <> 0) by (apply Rgt_not_eq; exact Hpi).
  assert (H10 : 0 < 10) by lra.
  assert (Hnr : not_nonpos_int ((1 - 20) / 2))
    by (replace ((1 - 20) / 2) with (- (19 / 2)) by lra; apply not_nonpos_int_neg19half).
  pose proof (two_sided_reflection 20 Hs0 Hs1 Hs2 ltac:(lra) Hnr) as HR.
  rewrite (zeta_cont_20 Hs0 Hs1) in HR.
  rewrite (Gam_arg_eq (20 / 2) 10 Hs2 H10 ltac:(lra)), (Gam_10 H10) in HR.
  replace ((1 - 20) / 2) with (- (19 / 2)) in HR by lra.
  replace (1 - 20) with (-19) in HR by lra.
  rewrite (GamH_neg_19half Hh), HGh in HR.
  assert (HP10 : Rpower PI 10 = PI ^ 10)
    by (replace 10 with (INR 10) by (simpl; ring); apply Rpower_pow; exact Hpi).
  rewrite (Rpower_Ropp PI (20 / 2)) in HR.
  replace (20 / 2) with 10 in HR by lra; rewrite HP10 in HR.
  rewrite Ropp_involutive in HR.
  replace (Rpower PI (19 / 2) * (1024 / 654729075 * Rpower PI (1 / 2)) * zeta_ext (-19))
    with (1024 / 654729075 * (Rpower PI (19 / 2) * Rpower PI (1 / 2)) * zeta_ext (-19)) in HR by ring.
  rewrite <- Rpower_plus in HR; replace (19 / 2 + 1 / 2) with 10 in HR by lra.
  rewrite HP10 in HR.
  assert (HPI10 : 0 < PI ^ 10) by (apply pow_lt; exact Hpi).
  apply (Rmult_eq_reg_l (1024 / 654729075 * PI ^ 10));
    [ | apply Rmult_integral_contrapositive_currified; [ lra | apply Rgt_not_eq; exact HPI10 ] ].
  rewrite <- HR; field; exact Hpine.
Qed.

Corollary zeta_ext_neg19 : zeta_ext (-19) = 174611 / 6600.
Proof. assert (Hh : 0 < 1 / 2) by lra; exact (zeta_neg19 Hh (Gam_half_Rpower Hh)). Qed.

Print Assumptions zeta_ext_neg19.

(* ================================================================= *)
(*  END ZetaNeg19.v.  ζ(−19) = 174611/6600.                           *)
(* ================================================================= *)
