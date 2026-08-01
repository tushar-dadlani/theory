(* ================================================================= *)
(*  ZetaNeg3.v  —  ζ(−3) = 1/120.                                     *)
(*                                                                    *)
(*  The two-sided functional equation at s=4 gives                    *)
(*    π^{−2}·Γ(2)·ζ(4) = π^{3/2}·Γ_ext(−3/2)·ζ_ext(−3).                *)
(*  With Γ(2)=1 (Gam_recur+Gam_1), ζ(4)=π⁴/90 (BaselZeta4Value),       *)
(*  Γ_ext(−3/2)=(4/3)·Γ(1/2) (GamH_neg_3half), and Γ(1/2)=√π           *)
(*  (GammaHalf.Gam_half_Rpower), the powers of π cancel:              *)
(*    π^{−2}·(π⁴/90)·π^{−3/2}·(3/(4√π)) = (3/4)/90 = 1/120.            *)
(*  No new axioms (classical Reals only).                            *)
(* ================================================================= *)

From Stdlib Require Import Reals Rpower Lra Lia.
Require Import GammaReal GammaRecur GammaOne GammaExtend XiReflection XiTwoSided
        GammaHalf BaselZeta4Value ZetaValues.
Open Scope R_scope.

(* --- level-independence of GamN, and GamH at any valid level --- *)

Lemma GamN_up : forall a k N HN HNk, GamN a N HN = GamN a (N + k) HNk.
Proof.
  induction k as [| k IH]; intros N HN HNk.
  - revert HNk; rewrite Nat.add_0_r; intro HNk; apply GamN_pirr.
  - assert (HNk' : 0 < a + INR (N + k))
      by (pose proof (le_INR N (N + k) ltac:(lia)); lra).
    rewrite (IH N HN HNk').
    revert HNk; replace (N + S k)%nat with (S (N + k)) by lia; intro HNk.
    apply GamN_coherent.
Qed.

Lemma GamN_indep : forall a N M HN HM, GamN a N HN = GamN a M HM.
Proof.
  intros a N M HN HM; destruct (Nat.le_ge_cases N M) as [Hle | Hge].
  - assert (HNk : 0 < a + INR (N + (M - N)))
      by (replace (N + (M - N))%nat with M by lia; exact HM).
    rewrite (GamN_up a (M - N) N HN HNk).
    revert HNk; assert (Hidx : (N + (M - N))%nat = M) by lia; rewrite Hidx;
      intro HNk; apply GamN_pirr.
  - assert (HMk : 0 < a + INR (M + (N - M)))
      by (replace (M + (N - M))%nat with N by lia; exact HN).
    rewrite (GamN_up a (N - M) M HM HMk).
    revert HMk; assert (Hidx : (M + (N - M))%nat = N) by lia; rewrite Hidx;
      intro HMk; symmetry; apply GamN_pirr.
Qed.

Lemma GamH_eq_GamN : forall a N (H : 0 < a + INR N), GamH a = GamN a N H.
Proof. intros a N H; unfold GamH; apply GamN_indep. Qed.

(* --- Γ(2) = 1  and  Γ_ext(−3/2) = (4/3)·Γ(1/2) --- *)

Lemma Gam_2 : forall (H : 0 < 2), Gam 2 H = 1.
Proof.
  intro H; assert (H1 : 0 < 1) by lra; assert (H11 : 0 < 1 + 1) by lra.
  rewrite (Gam_arg_eq 2 (1 + 1) H H11 ltac:(ring)), (Gam_recur 1 H1 H11), (Gam_1 H1); ring.
Qed.

Lemma GamN_neg3half : forall (Hh : 0 < 1 / 2) (H : 0 < - (3 / 2) + INR 2),
  GamN (- (3 / 2)) 2 H = 4 / 3 * Gam (1 / 2) Hh.
Proof.
  intros Hh H; unfold GamN; cbn [prodshift].
  rewrite (Gam_arg_eq (- (3 / 2) + INR 2) (1 / 2) H Hh
             ltac:(rewrite S_INR, S_INR, INR_0; lra)).
  rewrite !S_INR, INR_0; field; lra.
Qed.

Lemma GamH_neg_3half : forall (Hh : 0 < 1 / 2), GamH (- (3 / 2)) = 4 / 3 * Gam (1 / 2) Hh.
Proof.
  intro Hh; assert (H2 : 0 < - (3 / 2) + INR 2) by (simpl; lra).
  rewrite (GamH_eq_GamN (- (3 / 2)) 2 H2); apply GamN_neg3half.
Qed.

Lemma not_nonpos_int_neg3half : not_nonpos_int (- (3 / 2)).
Proof.
  intro n; destruct n as [| [| m]].
  - rewrite INR_0; lra.
  - rewrite S_INR, INR_0; lra.
  - rewrite !S_INR; pose proof (pos_INR m); lra.
Qed.

(* --- ζ(−3) = 1/120, given Γ(1/2)=√π --- *)

Theorem zeta_neg3 : forall (Hh : 0 < 1 / 2),
  Gam (1 / 2) Hh = Rpower PI (1 / 2) -> zeta_ext (-3) = 1 / 120.
Proof.
  intros Hh HGh.
  assert (Hs0 : 0 < 4) by lra. assert (Hs1 : (4:R) <> 1) by lra.
  assert (Hs2 : 0 < 4 / 2) by lra.
  assert (Hpi : 0 < PI) by apply PI_RGT_0.
  assert (Hpine : PI <> 0) by (apply Rgt_not_eq; exact Hpi).
  assert (H2 : 0 < 2) by lra.
  assert (Hnr : not_nonpos_int ((1 - 4) / 2))
    by (replace ((1 - 4) / 2) with (- (3 / 2)) by lra; apply not_nonpos_int_neg3half).
  pose proof (two_sided_reflection 4 Hs0 Hs1 Hs2 ltac:(lra) Hnr) as HR.
  rewrite (zeta_cont_4 Hs0 Hs1) in HR.
  rewrite (Gam_arg_eq (4 / 2) 2 Hs2 H2 ltac:(lra)), (Gam_2 H2) in HR.
  replace ((1 - 4) / 2) with (- (3 / 2)) in HR by lra.
  replace (1 - 4) with (-3) in HR by lra.
  rewrite (GamH_neg_3half Hh), HGh in HR.
  (* Rpower facts *)
  assert (HP1 : Rpower PI 1 = PI) by (apply Rpower_1; exact Hpi).
  assert (HP2 : Rpower PI 2 = PI ^ 2)
    by (replace 2 with (INR 2) by (simpl; ring); apply Rpower_pow; exact Hpi).
  rewrite (Rpower_Ropp PI (4 / 2)) in HR.
  replace (4 / 2) with 2 in HR by lra; rewrite HP2 in HR.
  rewrite Ropp_involutive in HR.
  replace (Rpower PI (3 / 2) * (4 / 3 * Rpower PI (1 / 2)) * zeta_ext (-3))
    with (4 / 3 * (Rpower PI (3 / 2) * Rpower PI (1 / 2)) * zeta_ext (-3)) in HR by ring.
  rewrite <- Rpower_plus in HR; replace (3 / 2 + 1 / 2) with 2 in HR by lra.
  rewrite HP2 in HR.
  (* HR : / PI ^ 2 * 1 * (PI ^ 4 / 90) = 4 / 3 * PI ^ 2 * zeta_ext (-3) *)
  assert (HPI2 : 0 < PI ^ 2) by (apply pow_lt; exact Hpi).
  apply (Rmult_eq_reg_l (4 / 3 * PI ^ 2));
    [ | apply Rmult_integral_contrapositive_currified; [ lra | apply Rgt_not_eq; exact HPI2 ] ].
  rewrite <- HR; field; exact Hpine.
Qed.

Corollary zeta_ext_neg3 : zeta_ext (-3) = 1 / 120.
Proof. assert (Hh : 0 < 1 / 2) by lra; exact (zeta_neg3 Hh (Gam_half_Rpower Hh)). Qed.

Print Assumptions zeta_ext_neg3.

(* ================================================================= *)
(*  END ZetaNeg3.v.  ζ(−3) = 1/120.                                   *)
(* ================================================================= *)
