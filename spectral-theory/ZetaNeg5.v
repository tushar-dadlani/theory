(* ================================================================= *)
(*  ZetaNeg5.v  —  ζ(−5) = −1/252.                                    *)
(*                                                                    *)
(*  The two-sided functional equation at s=6 gives                    *)
(*    π^{−3}·Γ(3)·ζ(6) = π^{5/2}·Γ_ext(−5/2)·ζ_ext(−5).                *)
(*  With Γ(3)=2 (Gam_3), ζ(6)=π⁶/945 (BaselZeta6Value), and           *)
(*  Γ_ext(−5/2)=−(8/15)·Γ(1/2) (GamH_neg_5half; prodshift(−5/2) 3 =    *)
(*  (−1/2)(−3/2)(−5/2) = −15/8), the powers of π cancel:              *)
(*    π^{−3}·2·(π⁶/945)·π^{−5/2}·(−15/(8√π)) = 2·(−15/8)/945 = −1/252. *)
(*  No new axioms (classical Reals only).                            *)
(* ================================================================= *)

From Stdlib Require Import Reals Rpower Lra Lia.
Require Import GammaReal GammaRecur GammaExtend XiReflection XiTwoSided
        GammaHalf BaselZeta6Value ZetaNeg3.
Open Scope R_scope.

Lemma Gam_3 : forall (H : 0 < 3), Gam 3 H = 2.
Proof.
  intro H; assert (H2 : 0 < 2) by lra; assert (H21 : 0 < 2 + 1) by lra.
  rewrite (Gam_arg_eq 3 (2 + 1) H H21 ltac:(ring)), (Gam_recur 2 H2 H21), (Gam_2 H2); ring.
Qed.

Lemma GamN_neg5half : forall (Hh : 0 < 1 / 2) (H : 0 < - (5 / 2) + INR 3),
  GamN (- (5 / 2)) 3 H = - (8 / 15) * Gam (1 / 2) Hh.
Proof.
  intros Hh H; unfold GamN; cbn [prodshift].
  rewrite (Gam_arg_eq (- (5 / 2) + INR 3) (1 / 2) H Hh
             ltac:(rewrite S_INR, S_INR, S_INR, INR_0; lra)).
  rewrite !S_INR, INR_0; field; lra.
Qed.

Lemma GamH_neg_5half : forall (Hh : 0 < 1 / 2), GamH (- (5 / 2)) = - (8 / 15) * Gam (1 / 2) Hh.
Proof.
  intro Hh; assert (H3 : 0 < - (5 / 2) + INR 3)
    by (rewrite S_INR, S_INR, S_INR, INR_0; lra).
  rewrite (GamH_eq_GamN (- (5 / 2)) 3 H3); apply GamN_neg5half.
Qed.

Lemma not_nonpos_int_neg5half : not_nonpos_int (- (5 / 2)).
Proof.
  intro n; destruct n as [| [| [| m]]].
  - rewrite INR_0; lra.
  - rewrite S_INR, INR_0; lra.
  - rewrite S_INR, S_INR, INR_0; lra.
  - rewrite !S_INR; pose proof (pos_INR m); lra.
Qed.

Theorem zeta_neg5 : forall (Hh : 0 < 1 / 2),
  Gam (1 / 2) Hh = Rpower PI (1 / 2) -> zeta_ext (-5) = - (1 / 252).
Proof.
  intros Hh HGh.
  assert (Hs0 : 0 < 6) by lra. assert (Hs1 : (6:R) <> 1) by lra.
  assert (Hs2 : 0 < 6 / 2) by lra.
  assert (Hpi : 0 < PI) by apply PI_RGT_0.
  assert (Hpine : PI <> 0) by (apply Rgt_not_eq; exact Hpi).
  assert (H3 : 0 < 3) by lra.
  assert (Hnr : not_nonpos_int ((1 - 6) / 2))
    by (replace ((1 - 6) / 2) with (- (5 / 2)) by lra; apply not_nonpos_int_neg5half).
  pose proof (two_sided_reflection 6 Hs0 Hs1 Hs2 ltac:(lra) Hnr) as HR.
  rewrite (zeta_cont_6 Hs0 Hs1) in HR.
  rewrite (Gam_arg_eq (6 / 2) 3 Hs2 H3 ltac:(lra)), (Gam_3 H3) in HR.
  replace ((1 - 6) / 2) with (- (5 / 2)) in HR by lra.
  replace (1 - 6) with (-5) in HR by lra.
  rewrite (GamH_neg_5half Hh), HGh in HR.
  assert (HP3 : Rpower PI 3 = PI ^ 3)
    by (replace 3 with (INR 3) by (simpl; ring); apply Rpower_pow; exact Hpi).
  rewrite (Rpower_Ropp PI (6 / 2)) in HR.
  replace (6 / 2) with 3 in HR by lra; rewrite HP3 in HR.
  rewrite Ropp_involutive in HR.
  replace (Rpower PI (5 / 2) * (- (8 / 15) * Rpower PI (1 / 2)) * zeta_ext (-5))
    with (- (8 / 15) * (Rpower PI (5 / 2) * Rpower PI (1 / 2)) * zeta_ext (-5)) in HR by ring.
  rewrite <- Rpower_plus in HR; replace (5 / 2 + 1 / 2) with 3 in HR by lra.
  rewrite HP3 in HR.
  assert (HPI3 : 0 < PI ^ 3) by (apply pow_lt; exact Hpi).
  apply (Rmult_eq_reg_l (- (8 / 15) * PI ^ 3));
    [ | apply Rmult_integral_contrapositive_currified; [ lra | apply Rgt_not_eq; exact HPI3 ] ].
  rewrite <- HR; field; exact Hpine.
Qed.

Corollary zeta_ext_neg5 : zeta_ext (-5) = - (1 / 252).
Proof. assert (Hh : 0 < 1 / 2) by lra; exact (zeta_neg5 Hh (Gam_half_Rpower Hh)). Qed.

Print Assumptions zeta_ext_neg5.

(* ================================================================= *)
(*  END ZetaNeg5.v.  ζ(−5) = −1/252.                                  *)
(* ================================================================= *)
