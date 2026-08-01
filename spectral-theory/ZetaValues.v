(* ================================================================= *)
(*  ZetaValues.v  —  special values of the completed zeta's ζ.        *)
(*                                                                    *)
(*   ζ(2) = π²/6   (zeta_cont_2): connecting the Basel development     *)
(*                 (Ell2Basel.zeta2_value) to the completed-zeta's ζ  *)
(*                 via dzeta_eq_Zpart + the ζ-hookup.                 *)
(*                                                                    *)
(*   ζ(−1) = −1/12 (zeta_neg1): from the two-sided functional equation *)
(*                 at s=2.  The reflection forces                     *)
(*                    π^{−1}·Γ(1)·ζ(2) = π^{1/2}·Γ_ext(−1/2)·ζ_ext(−1),*)
(*                 and Γ_ext(−1/2)=−2·Γ(1/2) (GamN_FE at s=−1/2).      *)
(*                 Discharging ζ(2)=π²/6 internally and given the two  *)
(*                 classical Γ-values Γ(1)=1 and Γ(1/2)=√π, the π's   *)
(*                 cancel and ζ_ext(−1)=−1/12.                        *)
(*                 (Γ(1)=1 is provable in-system; Γ(1/2)=√π is the    *)
(*                 Gaussian integral, left classical in this dev — so  *)
(*                 both enter as hypotheses.)                          *)
(*                                                                    *)
(*   ζ(0) = −1/2 sits at the pole s=1 of the reflection (both sides    *)
(*   singular); it needs a Laurent/limit analysis, not a substitution,*)
(*   and is out of scope here.                                        *)
(*  No new axioms (classical Reals only).                            *)
(* ================================================================= *)

From Stdlib Require Import Reals Rpower Lra Lia.
Require Import Ell2Zeta Ell2Basel Ell2ZetaCont ZetaCompleted HagedornTransition
        XiTwoSided GammaReal GammaExtend MellinTail.
Open Scope R_scope.

(* --- ζ(2) = π²/6 --- *)

Lemma Un_cv_shift_S : forall (a : nat -> R) L, Un_cv a L -> Un_cv (fun n => a (S n)) L.
Proof.
  intros a L Ha eps He; destruct (Ha eps He) as [N HN]; exists N; intros n Hn; apply HN; lia.
Qed.

Theorem zeta_cont_2 : forall (Hs0 : 0 < 2) (Hs1 : (2:R) <> 1),
  zeta_cont 2 Hs0 Hs1 = PI ^ 2 / 6.
Proof.
  intros Hs0 Hs1.
  apply (UL_sequence (Zpart 2)).
  - apply (zeta_hookup 2 Hs0 Hs1); lra.
  - apply (Un_cv_ext (fun M => dzeta 2 (S M)) (Zpart 2));
      [ intro M; apply dzeta_eq_Zpart | apply Un_cv_shift_S; apply zeta2_value ].
Qed.

(* --- Γ_ext(−1/2) = −2·Γ(1/2)  (the reflected Γ-factor) --- *)

Lemma not_nonpos_int_neg_half : not_nonpos_int (- (1 / 2)).
Proof.
  intro n; destruct n as [ | m].
  - simpl; lra.
  - rewrite S_INR; pose proof (pos_INR m); lra.
Qed.

Lemma GamH_neg_half : forall (Hh : 0 < 1 / 2), GamH (- (1 / 2)) = -2 * Gam (1 / 2) Hh.
Proof.
  intro Hh.
  set (q := proj1_sig (nat_gt (- - (1 / 2)))).
  assert (Hs' : 0 < - (1 / 2) + 1) by lra.
  assert (H1 : 0 < - (1 / 2) + 1 + INR q) by (pose proof (pos_INR q); lra).
  assert (H  : 0 < - (1 / 2) + INR (S q)) by (rewrite S_INR; pose proof (pos_INR q); lra).
  pose proof (GamN_FE (- (1 / 2)) q H1 H ltac:(lra)) as HFE.
  rewrite (GamN_pos q (- (1 / 2) + 1) Hs' H1) in HFE.
  rewrite (Gam_arg_eq (- (1 / 2) + 1) (1 / 2) Hs' Hh ltac:(lra)) in HFE.
  unfold GamH; change (lvl (- (1 / 2))) with (S q).
  rewrite (GamN_pirr (- (1 / 2)) (S q) (lvl_pos (- (1 / 2))) H).
  lra.
Qed.

(* --- ζ(−1) = −1/12, given Γ(1)=1 and Γ(1/2)=√π --- *)

Theorem zeta_neg1 : forall (H1 : 0 < 1) (Hh : 0 < 1 / 2),
  Gam 1 H1 = 1 -> Gam (1 / 2) Hh = Rpower PI (1 / 2) ->
  zeta_ext (-1) = - (1 / 12).
Proof.
  intros H1 Hh HG1 HGh.
  assert (Hs0 : 0 < 2) by lra.
  assert (Hs1 : (2:R) <> 1) by lra.
  assert (Hs2 : 0 < 2 / 2) by lra.
  assert (Hpi : 0 < PI) by apply PI_RGT_0.
  assert (Hpine : PI <> 0) by (apply Rgt_not_eq; exact Hpi).
  assert (Hnr : not_nonpos_int ((1 - 2) / 2))
    by (replace ((1 - 2) / 2) with (- (1 / 2)) by lra; apply not_nonpos_int_neg_half).
  pose proof (two_sided_reflection 2 Hs0 Hs1 Hs2 ltac:(lra) Hnr) as HR.
  rewrite (zeta_cont_2 Hs0 Hs1) in HR.
  rewrite (Gam_arg_eq (2 / 2) 1 Hs2 H1 ltac:(lra)), HG1 in HR.
  replace ((1 - 2) / 2) with (- (1 / 2)) in HR by lra.
  replace (1 - 2) with (-1) in HR by lra.
  rewrite (GamH_neg_half Hh), HGh in HR.
  (* Rpower facts on PI *)
  assert (HP1 : Rpower PI 1 = PI) by (apply Rpower_1; exact Hpi).
  rewrite (Rpower_Ropp PI (2 / 2)) in HR.
  replace (2 / 2) with 1 in HR by lra; rewrite HP1 in HR.
  rewrite Ropp_involutive in HR.
  replace (Rpower PI (1 / 2) * (-2 * Rpower PI (1 / 2)) * zeta_ext (-1))
    with (-2 * (Rpower PI (1 / 2) * Rpower PI (1 / 2)) * zeta_ext (-1)) in HR by ring.
  rewrite <- Rpower_plus in HR; replace (1 / 2 + 1 / 2) with 1 in HR by lra.
  rewrite HP1 in HR.
  (* HR : / PI * 1 * (PI ^ 2 / 6) = -2 * PI * zeta_ext (-1) *)
  apply (Rmult_eq_reg_l (-2 * PI));
    [ | apply Rmult_integral_contrapositive_currified; [ lra | exact Hpine ] ].
  rewrite <- HR; field; exact Hpine.
Qed.

Print Assumptions zeta_cont_2.
Print Assumptions zeta_neg1.

(* ================================================================= *)
(*  END ZetaValues.v.  ζ(2)=π²/6 (proved); ζ(−1)=−1/12 (given the      *)
(*  classical Γ(1)=1, Γ(1/2)=√π); ζ(0)=−1/2 needs Laurent (pole).      *)
(* ================================================================= *)
