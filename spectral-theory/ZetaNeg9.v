(* ================================================================= *)
(*  ZetaNeg9.v  —  ζ(−9) = −1/132.                                    *)
(*                                                                    *)
(*  The two-sided functional equation at s=10 gives                   *)
(*    π^{−5}·Γ(5)·ζ(10) = π^{9/2}·Γ_ext(−9/2)·ζ_ext(−9).               *)
(*  With Γ(5)=24 (Gam_5), ζ(10)=π¹⁰/93555 (BaselZeta10Value), and      *)
(*  Γ_ext(−9/2)=−(32/945)·Γ(1/2) (GamH_neg_9half; prodshift(−9/2) 5 =  *)
(*  (−1/2)(−3/2)(−5/2)(−7/2)(−9/2) = −945/32), the powers of π cancel:  *)
(*    24·(π¹⁰/93555)·(−945/32)/π⁵·π^{−9/2}·/√π = 24·(−945)/(93555·32)   *)
(*      = −1/132.                                                     *)
(*  No new axioms (classical Reals only).                            *)
(* ================================================================= *)

From Stdlib Require Import Reals Rpower Lra Lia.
Require Import GammaReal GammaRecur GammaExtend XiReflection XiTwoSided
        GammaHalf BaselZeta10Value ZetaNeg3 ZetaNeg5 ZetaNeg7.
Open Scope R_scope.

Lemma Gam_5 : forall (H : 0 < 5), Gam 5 H = 24.
Proof.
  intro H; assert (H4 : 0 < 4) by lra; assert (H41 : 0 < 4 + 1) by lra.
  rewrite (Gam_arg_eq 5 (4 + 1) H H41 ltac:(ring)), (Gam_recur 4 H4 H41), (Gam_4 H4); ring.
Qed.

Lemma GamN_neg9half : forall (Hh : 0 < 1 / 2) (H : 0 < - (9 / 2) + INR 5),
  GamN (- (9 / 2)) 5 H = - (32 / 945) * Gam (1 / 2) Hh.
Proof.
  intros Hh H; unfold GamN; cbn [prodshift].
  rewrite (Gam_arg_eq (- (9 / 2) + INR 5) (1 / 2) H Hh
             ltac:(rewrite S_INR, S_INR, S_INR, S_INR, S_INR, INR_0; lra)).
  rewrite !S_INR, INR_0; field; lra.
Qed.

Lemma GamH_neg_9half : forall (Hh : 0 < 1 / 2), GamH (- (9 / 2)) = - (32 / 945) * Gam (1 / 2) Hh.
Proof.
  intro Hh; assert (H5 : 0 < - (9 / 2) + INR 5)
    by (rewrite S_INR, S_INR, S_INR, S_INR, S_INR, INR_0; lra).
  rewrite (GamH_eq_GamN (- (9 / 2)) 5 H5); apply GamN_neg9half.
Qed.

Lemma not_nonpos_int_neg9half : not_nonpos_int (- (9 / 2)).
Proof.
  intro n; destruct n as [| [| [| [| [| m]]]]].
  - rewrite INR_0; lra.
  - rewrite S_INR, INR_0; lra.
  - rewrite S_INR, S_INR, INR_0; lra.
  - rewrite S_INR, S_INR, S_INR, INR_0; lra.
  - rewrite S_INR, S_INR, S_INR, S_INR, INR_0; lra.
  - rewrite !S_INR; pose proof (pos_INR m); lra.
Qed.

Theorem zeta_neg9 : forall (Hh : 0 < 1 / 2),
  Gam (1 / 2) Hh = Rpower PI (1 / 2) -> zeta_ext (-9) = - (1 / 132).
Proof.
  intros Hh HGh.
  assert (Hs0 : 0 < 10) by lra. assert (Hs1 : (10:R) <> 1) by lra.
  assert (Hs2 : 0 < 10 / 2) by lra.
  assert (Hpi : 0 < PI) by apply PI_RGT_0.
  assert (Hpine : PI <> 0) by (apply Rgt_not_eq; exact Hpi).
  assert (H5 : 0 < 5) by lra.
  assert (Hnr : not_nonpos_int ((1 - 10) / 2))
    by (replace ((1 - 10) / 2) with (- (9 / 2)) by lra; apply not_nonpos_int_neg9half).
  pose proof (two_sided_reflection 10 Hs0 Hs1 Hs2 ltac:(lra) Hnr) as HR.
  rewrite (zeta_cont_10 Hs0 Hs1) in HR.
  rewrite (Gam_arg_eq (10 / 2) 5 Hs2 H5 ltac:(lra)), (Gam_5 H5) in HR.
  replace ((1 - 10) / 2) with (- (9 / 2)) in HR by lra.
  replace (1 - 10) with (-9) in HR by lra.
  rewrite (GamH_neg_9half Hh), HGh in HR.
  assert (HP5 : Rpower PI 5 = PI ^ 5)
    by (replace 5 with (INR 5) by (simpl; ring); apply Rpower_pow; exact Hpi).
  rewrite (Rpower_Ropp PI (10 / 2)) in HR.
  replace (10 / 2) with 5 in HR by lra; rewrite HP5 in HR.
  rewrite Ropp_involutive in HR.
  replace (Rpower PI (9 / 2) * (- (32 / 945) * Rpower PI (1 / 2)) * zeta_ext (-9))
    with (- (32 / 945) * (Rpower PI (9 / 2) * Rpower PI (1 / 2)) * zeta_ext (-9)) in HR by ring.
  rewrite <- Rpower_plus in HR; replace (9 / 2 + 1 / 2) with 5 in HR by lra.
  rewrite HP5 in HR.
  assert (HPI5 : 0 < PI ^ 5) by (apply pow_lt; exact Hpi).
  apply (Rmult_eq_reg_l (- (32 / 945) * PI ^ 5));
    [ | apply Rmult_integral_contrapositive_currified; [ lra | apply Rgt_not_eq; exact HPI5 ] ].
  rewrite <- HR; field; exact Hpine.
Qed.

Corollary zeta_ext_neg9 : zeta_ext (-9) = - (1 / 132).
Proof. assert (Hh : 0 < 1 / 2) by lra; exact (zeta_neg9 Hh (Gam_half_Rpower Hh)). Qed.

Print Assumptions zeta_ext_neg9.

(* ================================================================= *)
(*  END ZetaNeg9.v.  ζ(−9) = −1/132.                                  *)
(* ================================================================= *)
