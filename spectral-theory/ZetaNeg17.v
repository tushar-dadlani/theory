(* ================================================================= *)
(*  ZetaNeg17.v  —  ζ(−17) = −43867/14364.                            *)
(*                                                                    *)
(*  The two-sided functional equation at s=18 gives                   *)
(*    π^{−9}·Γ(9)·ζ(18) = π^{17/2}·Γ_ext(−17/2)·ζ_ext(−17).            *)
(*  With Γ(9)=40320 (Gam_9), ζ(18)=43867π¹⁸/38979295480125, and        *)
(*  Γ_ext(−17/2)=−(512/34459425)·Γ(1/2) (prodshift(−17/2) 9 =          *)
(*  (−1/2)(−3/2)…(−17/2) = −34459425/512), the powers of π cancel:      *)
(*    40320·(43867/38979295480125)·(−34459425/512) = −43867/14364.     *)
(*  (B₁₈ = 43867/798, so ζ(−17) = −B₁₈/18 = −43867/14364.)             *)
(*  No new axioms (classical Reals only).                            *)
(* ================================================================= *)

From Stdlib Require Import Reals Rpower Lra Lia.
Require Import GammaReal GammaRecur GammaExtend XiReflection XiTwoSided
        GammaHalf BaselZeta18Value ZetaNeg3 ZetaNeg5 ZetaNeg7 ZetaNeg9 ZetaNeg11 ZetaNeg13 ZetaNeg15.
Open Scope R_scope.

Lemma Gam_9 : forall (H : 0 < 9), Gam 9 H = 40320.
Proof.
  intro H; assert (H8 : 0 < 8) by lra; assert (H81 : 0 < 8 + 1) by lra.
  rewrite (Gam_arg_eq 9 (8 + 1) H H81 ltac:(ring)), (Gam_recur 8 H8 H81), (Gam_8 H8); ring.
Qed.

Lemma GamN_neg17half : forall (Hh : 0 < 1 / 2) (H : 0 < - (17 / 2) + INR 9),
  GamN (- (17 / 2)) 9 H = - (512 / 34459425) * Gam (1 / 2) Hh.
Proof.
  intros Hh H; unfold GamN; cbn [prodshift].
  rewrite (Gam_arg_eq (- (17 / 2) + INR 9) (1 / 2) H Hh
             ltac:(rewrite S_INR, S_INR, S_INR, S_INR, S_INR, S_INR, S_INR, S_INR, S_INR, INR_0; lra)).
  rewrite !S_INR, INR_0; field; lra.
Qed.

Lemma GamH_neg_17half : forall (Hh : 0 < 1 / 2), GamH (- (17 / 2)) = - (512 / 34459425) * Gam (1 / 2) Hh.
Proof.
  intro Hh; assert (H9 : 0 < - (17 / 2) + INR 9)
    by (rewrite S_INR, S_INR, S_INR, S_INR, S_INR, S_INR, S_INR, S_INR, S_INR, INR_0; lra).
  rewrite (GamH_eq_GamN (- (17 / 2)) 9 H9); apply GamN_neg17half.
Qed.

Lemma not_nonpos_int_neg17half : not_nonpos_int (- (17 / 2)).
Proof.
  intro n; destruct n as [| [| [| [| [| [| [| [| [| m]]]]]]]]].
  - rewrite INR_0; lra.
  - rewrite S_INR, INR_0; lra.
  - rewrite S_INR, S_INR, INR_0; lra.
  - rewrite S_INR, S_INR, S_INR, INR_0; lra.
  - rewrite S_INR, S_INR, S_INR, S_INR, INR_0; lra.
  - rewrite S_INR, S_INR, S_INR, S_INR, S_INR, INR_0; lra.
  - rewrite S_INR, S_INR, S_INR, S_INR, S_INR, S_INR, INR_0; lra.
  - rewrite S_INR, S_INR, S_INR, S_INR, S_INR, S_INR, S_INR, INR_0; lra.
  - rewrite S_INR, S_INR, S_INR, S_INR, S_INR, S_INR, S_INR, S_INR, INR_0; lra.
  - rewrite !S_INR; pose proof (pos_INR m); lra.
Qed.

Theorem zeta_neg17 : forall (Hh : 0 < 1 / 2),
  Gam (1 / 2) Hh = Rpower PI (1 / 2) -> zeta_ext (-17) = - (43867 / 14364).
Proof.
  intros Hh HGh.
  assert (Hs0 : 0 < 18) by lra. assert (Hs1 : (18:R) <> 1) by lra.
  assert (Hs2 : 0 < 18 / 2) by lra.
  assert (Hpi : 0 < PI) by apply PI_RGT_0.
  assert (Hpine : PI <> 0) by (apply Rgt_not_eq; exact Hpi).
  assert (H9 : 0 < 9) by lra.
  assert (Hnr : not_nonpos_int ((1 - 18) / 2))
    by (replace ((1 - 18) / 2) with (- (17 / 2)) by lra; apply not_nonpos_int_neg17half).
  pose proof (two_sided_reflection 18 Hs0 Hs1 Hs2 ltac:(lra) Hnr) as HR.
  rewrite (zeta_cont_18 Hs0 Hs1) in HR.
  rewrite (Gam_arg_eq (18 / 2) 9 Hs2 H9 ltac:(lra)), (Gam_9 H9) in HR.
  replace ((1 - 18) / 2) with (- (17 / 2)) in HR by lra.
  replace (1 - 18) with (-17) in HR by lra.
  rewrite (GamH_neg_17half Hh), HGh in HR.
  assert (HP9 : Rpower PI 9 = PI ^ 9)
    by (replace 9 with (INR 9) by (simpl; ring); apply Rpower_pow; exact Hpi).
  rewrite (Rpower_Ropp PI (18 / 2)) in HR.
  replace (18 / 2) with 9 in HR by lra; rewrite HP9 in HR.
  rewrite Ropp_involutive in HR.
  replace (Rpower PI (17 / 2) * (- (512 / 34459425) * Rpower PI (1 / 2)) * zeta_ext (-17))
    with (- (512 / 34459425) * (Rpower PI (17 / 2) * Rpower PI (1 / 2)) * zeta_ext (-17)) in HR by ring.
  rewrite <- Rpower_plus in HR; replace (17 / 2 + 1 / 2) with 9 in HR by lra.
  rewrite HP9 in HR.
  assert (HPI9 : 0 < PI ^ 9) by (apply pow_lt; exact Hpi).
  apply (Rmult_eq_reg_l (- (512 / 34459425) * PI ^ 9));
    [ | apply Rmult_integral_contrapositive_currified; [ lra | apply Rgt_not_eq; exact HPI9 ] ].
  rewrite <- HR; field; exact Hpine.
Qed.

Corollary zeta_ext_neg17 : zeta_ext (-17) = - (43867 / 14364).
Proof. assert (Hh : 0 < 1 / 2) by lra; exact (zeta_neg17 Hh (Gam_half_Rpower Hh)). Qed.

Print Assumptions zeta_ext_neg17.

(* ================================================================= *)
(*  END ZetaNeg17.v.  ζ(−17) = −43867/14364.                          *)
(* ================================================================= *)
