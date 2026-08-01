(* ================================================================= *)
(*  ZetaNeg11.v  —  ζ(−11) = 691/32760.                               *)
(*                                                                    *)
(*  The two-sided functional equation at s=12 gives                   *)
(*    π^{−6}·Γ(6)·ζ(12) = π^{11/2}·Γ_ext(−11/2)·ζ_ext(−11).            *)
(*  With Γ(6)=120 (Gam_6), ζ(12)=691π¹²/638512875 (BaselZeta12Value),  *)
(*  and Γ_ext(−11/2)=(64/10395)·Γ(1/2) (prodshift(−11/2) 6 =           *)
(*  (−1/2)(−3/2)(−5/2)(−7/2)(−9/2)(−11/2) = 10395/64), π cancels:       *)
(*    120·691/638512875·(10395/64) = 691/32760.  The Bernoulli         *)
(*  irregular prime 691 survives into ζ(−11) as well.                  *)
(*  No new axioms (classical Reals only).                            *)
(* ================================================================= *)

From Stdlib Require Import Reals Rpower Lra Lia.
Require Import GammaReal GammaRecur GammaExtend XiReflection XiTwoSided
        GammaHalf BaselZeta12Value ZetaNeg3 ZetaNeg5 ZetaNeg7 ZetaNeg9.
Open Scope R_scope.

Lemma Gam_6 : forall (H : 0 < 6), Gam 6 H = 120.
Proof.
  intro H; assert (H5 : 0 < 5) by lra; assert (H51 : 0 < 5 + 1) by lra.
  rewrite (Gam_arg_eq 6 (5 + 1) H H51 ltac:(ring)), (Gam_recur 5 H5 H51), (Gam_5 H5); ring.
Qed.

Lemma GamN_neg11half : forall (Hh : 0 < 1 / 2) (H : 0 < - (11 / 2) + INR 6),
  GamN (- (11 / 2)) 6 H = 64 / 10395 * Gam (1 / 2) Hh.
Proof.
  intros Hh H; unfold GamN; cbn [prodshift].
  rewrite (Gam_arg_eq (- (11 / 2) + INR 6) (1 / 2) H Hh
             ltac:(rewrite S_INR, S_INR, S_INR, S_INR, S_INR, S_INR, INR_0; lra)).
  rewrite !S_INR, INR_0; field; lra.
Qed.

Lemma GamH_neg_11half : forall (Hh : 0 < 1 / 2), GamH (- (11 / 2)) = 64 / 10395 * Gam (1 / 2) Hh.
Proof.
  intro Hh; assert (H6 : 0 < - (11 / 2) + INR 6)
    by (rewrite S_INR, S_INR, S_INR, S_INR, S_INR, S_INR, INR_0; lra).
  rewrite (GamH_eq_GamN (- (11 / 2)) 6 H6); apply GamN_neg11half.
Qed.

Lemma not_nonpos_int_neg11half : not_nonpos_int (- (11 / 2)).
Proof.
  intro n; destruct n as [| [| [| [| [| [| m]]]]]].
  - rewrite INR_0; lra.
  - rewrite S_INR, INR_0; lra.
  - rewrite S_INR, S_INR, INR_0; lra.
  - rewrite S_INR, S_INR, S_INR, INR_0; lra.
  - rewrite S_INR, S_INR, S_INR, S_INR, INR_0; lra.
  - rewrite S_INR, S_INR, S_INR, S_INR, S_INR, INR_0; lra.
  - rewrite !S_INR; pose proof (pos_INR m); lra.
Qed.

Theorem zeta_neg11 : forall (Hh : 0 < 1 / 2),
  Gam (1 / 2) Hh = Rpower PI (1 / 2) -> zeta_ext (-11) = 691 / 32760.
Proof.
  intros Hh HGh.
  assert (Hs0 : 0 < 12) by lra. assert (Hs1 : (12:R) <> 1) by lra.
  assert (Hs2 : 0 < 12 / 2) by lra.
  assert (Hpi : 0 < PI) by apply PI_RGT_0.
  assert (Hpine : PI <> 0) by (apply Rgt_not_eq; exact Hpi).
  assert (H6 : 0 < 6) by lra.
  assert (Hnr : not_nonpos_int ((1 - 12) / 2))
    by (replace ((1 - 12) / 2) with (- (11 / 2)) by lra; apply not_nonpos_int_neg11half).
  pose proof (two_sided_reflection 12 Hs0 Hs1 Hs2 ltac:(lra) Hnr) as HR.
  rewrite (zeta_cont_12 Hs0 Hs1) in HR.
  rewrite (Gam_arg_eq (12 / 2) 6 Hs2 H6 ltac:(lra)), (Gam_6 H6) in HR.
  replace ((1 - 12) / 2) with (- (11 / 2)) in HR by lra.
  replace (1 - 12) with (-11) in HR by lra.
  rewrite (GamH_neg_11half Hh), HGh in HR.
  assert (HP6 : Rpower PI 6 = PI ^ 6)
    by (replace 6 with (INR 6) by (simpl; ring); apply Rpower_pow; exact Hpi).
  rewrite (Rpower_Ropp PI (12 / 2)) in HR.
  replace (12 / 2) with 6 in HR by lra; rewrite HP6 in HR.
  rewrite Ropp_involutive in HR.
  replace (Rpower PI (11 / 2) * (64 / 10395 * Rpower PI (1 / 2)) * zeta_ext (-11))
    with (64 / 10395 * (Rpower PI (11 / 2) * Rpower PI (1 / 2)) * zeta_ext (-11)) in HR by ring.
  rewrite <- Rpower_plus in HR; replace (11 / 2 + 1 / 2) with 6 in HR by lra.
  rewrite HP6 in HR.
  assert (HPI6 : 0 < PI ^ 6) by (apply pow_lt; exact Hpi).
  apply (Rmult_eq_reg_l (64 / 10395 * PI ^ 6));
    [ | apply Rmult_integral_contrapositive_currified; [ lra | apply Rgt_not_eq; exact HPI6 ] ].
  rewrite <- HR; field; exact Hpine.
Qed.

Corollary zeta_ext_neg11 : zeta_ext (-11) = 691 / 32760.
Proof. assert (Hh : 0 < 1 / 2) by lra; exact (zeta_neg11 Hh (Gam_half_Rpower Hh)). Qed.

Print Assumptions zeta_ext_neg11.

(* ================================================================= *)
(*  END ZetaNeg11.v.  ζ(−11) = 691/32760.                             *)
(* ================================================================= *)
