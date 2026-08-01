(* ================================================================= *)
(*  ZetaNeg7.v  —  ζ(−7) = 1/240.                                     *)
(*                                                                    *)
(*  The two-sided functional equation at s=8 gives                    *)
(*    π^{−4}·Γ(4)·ζ(8) = π^{7/2}·Γ_ext(−7/2)·ζ_ext(−7).                *)
(*  With Γ(4)=6 (Gam_4), ζ(8)=π⁸/9450 (BaselZeta8Value), and          *)
(*  Γ_ext(−7/2)=(16/105)·Γ(1/2) (prodshift(−7/2) 4 =                   *)
(*  (−1/2)(−3/2)(−5/2)(−7/2) = 105/16), the powers of π cancel:        *)
(*    6·(π⁸/9450)·(105/16)/π⁴·π^{−7/2}·/√π = 1/240.                    *)
(*  No new axioms (classical Reals only).                            *)
(* ================================================================= *)

From Stdlib Require Import Reals Rpower Lra Lia.
Require Import GammaReal GammaRecur GammaExtend XiReflection XiTwoSided
        GammaHalf BaselZeta8Value ZetaNeg3 ZetaNeg5.
Open Scope R_scope.

Lemma Gam_4 : forall (H : 0 < 4), Gam 4 H = 6.
Proof.
  intro H; assert (H3 : 0 < 3) by lra; assert (H31 : 0 < 3 + 1) by lra.
  rewrite (Gam_arg_eq 4 (3 + 1) H H31 ltac:(ring)), (Gam_recur 3 H3 H31), (Gam_3 H3); ring.
Qed.

Lemma GamN_neg7half : forall (Hh : 0 < 1 / 2) (H : 0 < - (7 / 2) + INR 4),
  GamN (- (7 / 2)) 4 H = 16 / 105 * Gam (1 / 2) Hh.
Proof.
  intros Hh H; unfold GamN; cbn [prodshift].
  rewrite (Gam_arg_eq (- (7 / 2) + INR 4) (1 / 2) H Hh
             ltac:(rewrite S_INR, S_INR, S_INR, S_INR, INR_0; lra)).
  rewrite !S_INR, INR_0; field; lra.
Qed.

Lemma GamH_neg_7half : forall (Hh : 0 < 1 / 2), GamH (- (7 / 2)) = 16 / 105 * Gam (1 / 2) Hh.
Proof.
  intro Hh; assert (H4 : 0 < - (7 / 2) + INR 4)
    by (rewrite S_INR, S_INR, S_INR, S_INR, INR_0; lra).
  rewrite (GamH_eq_GamN (- (7 / 2)) 4 H4); apply GamN_neg7half.
Qed.

Lemma not_nonpos_int_neg7half : not_nonpos_int (- (7 / 2)).
Proof.
  intro n; destruct n as [| [| [| [| m]]]].
  - rewrite INR_0; lra.
  - rewrite S_INR, INR_0; lra.
  - rewrite S_INR, S_INR, INR_0; lra.
  - rewrite S_INR, S_INR, S_INR, INR_0; lra.
  - rewrite !S_INR; pose proof (pos_INR m); lra.
Qed.

Theorem zeta_neg7 : forall (Hh : 0 < 1 / 2),
  Gam (1 / 2) Hh = Rpower PI (1 / 2) -> zeta_ext (-7) = 1 / 240.
Proof.
  intros Hh HGh.
  assert (Hs0 : 0 < 8) by lra. assert (Hs1 : (8:R) <> 1) by lra.
  assert (Hs2 : 0 < 8 / 2) by lra.
  assert (Hpi : 0 < PI) by apply PI_RGT_0.
  assert (Hpine : PI <> 0) by (apply Rgt_not_eq; exact Hpi).
  assert (H4 : 0 < 4) by lra.
  assert (Hnr : not_nonpos_int ((1 - 8) / 2))
    by (replace ((1 - 8) / 2) with (- (7 / 2)) by lra; apply not_nonpos_int_neg7half).
  pose proof (two_sided_reflection 8 Hs0 Hs1 Hs2 ltac:(lra) Hnr) as HR.
  rewrite (zeta_cont_8 Hs0 Hs1) in HR.
  rewrite (Gam_arg_eq (8 / 2) 4 Hs2 H4 ltac:(lra)), (Gam_4 H4) in HR.
  replace ((1 - 8) / 2) with (- (7 / 2)) in HR by lra.
  replace (1 - 8) with (-7) in HR by lra.
  rewrite (GamH_neg_7half Hh), HGh in HR.
  assert (HP4 : Rpower PI 4 = PI ^ 4)
    by (replace 4 with (INR 4) by (simpl; ring); apply Rpower_pow; exact Hpi).
  rewrite (Rpower_Ropp PI (8 / 2)) in HR.
  replace (8 / 2) with 4 in HR by lra; rewrite HP4 in HR.
  rewrite Ropp_involutive in HR.
  replace (Rpower PI (7 / 2) * (16 / 105 * Rpower PI (1 / 2)) * zeta_ext (-7))
    with (16 / 105 * (Rpower PI (7 / 2) * Rpower PI (1 / 2)) * zeta_ext (-7)) in HR by ring.
  rewrite <- Rpower_plus in HR; replace (7 / 2 + 1 / 2) with 4 in HR by lra.
  rewrite HP4 in HR.
  assert (HPI4 : 0 < PI ^ 4) by (apply pow_lt; exact Hpi).
  apply (Rmult_eq_reg_l (16 / 105 * PI ^ 4));
    [ | apply Rmult_integral_contrapositive_currified; [ lra | apply Rgt_not_eq; exact HPI4 ] ].
  rewrite <- HR; field; exact Hpine.
Qed.

Corollary zeta_ext_neg7 : zeta_ext (-7) = 1 / 240.
Proof. assert (Hh : 0 < 1 / 2) by lra; exact (zeta_neg7 Hh (Gam_half_Rpower Hh)). Qed.

Print Assumptions zeta_ext_neg7.

(* ================================================================= *)
(*  END ZetaNeg7.v.  ζ(−7) = 1/240.                                   *)
(* ================================================================= *)
