(* ================================================================= *)
(*  XiLnBound.v  —  the LOGARITHMIC form of xi's growth bound.         *)
(*                                                                    *)
(*    xi_ln_bound : 8 <= |z|  ==>  ln |xi z| <= Lxi (|z|),             *)
(*      Lxi t := ln M0 + 2 ln (t+1) + (t+1)/2 . ln ((t+1)/PI).         *)
(*                                                                    *)
(*  XiGrowthBound's header advertises an XiC_order1_bound of exactly   *)
(*  this shape, but the lemma is not in that file -- the development   *)
(*  only ever needed the MULTIPLICATIVE bound XiC_growth.  SubQuadLog  *)
(*  is about ln |H|, so the logarithm has to be taken somewhere, and   *)
(*  this is the cheapest place: XiC_growth's right-hand side is        *)
(*  literally XiM (|z|), and XiHgrow.ln4XiM_bound has already done the *)
(*  ln M0 / 2 ln u / (u/2) ln(u/PI) computation for exactly that       *)
(*  expression while proving the counting bound.                       *)
(*                                                                    *)
(*  The factor 4 costs nothing: 4 . XiM Rc = 2 + 4 u^2 Tgb u with      *)
(*  u = Rc+1, and XiM <= 4 XiM, so monotonicity of ln lands directly   *)
(*  on ln4XiM_bound's left-hand side without dividing anything.        *)
(*                                                                    *)
(*  ZEROS ARE NOT A SPECIAL CASE, but they do need a word: Coq's ln is *)
(*  0 on non-positive arguments, so at a zero of xi the claim reads    *)
(*  0 <= Lxi, which holds because M0 > 1 and (t+1)/PI > 1 for t >= 8.  *)
(*  Stating it this way keeps the bound unconditional in z.            *)
(*                                                                    *)
(*  Lxi is O(t ln t) -- comfortably o(t^2), which is all SubQuadLog    *)
(*  will ask of it.  Axiom-clean.                                      *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra.
Require Import ComplexField Cmodulus Holomorphic CDeriv
        RiemannXiEntire XiGrowthBound XiZeroCount XiHgrow.
Open Scope R_scope.

Lemma ln_zero : ln 0 = 0.
Proof.
  unfold ln. destruct (Rlt_dec 0 0) as [H | H]; [ exfalso; lra | reflexivity ].
Qed.

Definition Lxi (t : R) : R :=
  ln M0 + 2 * ln (t + 1) + (t + 1) / 2 * ln ((t + 1) / PI).

Lemma M0_gt1 : 1 < M0.
Proof. unfold M0. pose proof Kc_pos. lra. Qed.

Lemma Lxi_nonneg : forall t, 8 <= t -> 0 <= Lxi t.
Proof.
  intros t Ht. pose proof PI_RGT_0 as HPI. pose proof PI_4 as HPI4.
  unfold Lxi.
  assert (H1 : 0 <= ln M0)
    by (rewrite <- ln_1; apply ln_le_mono; [ lra | pose proof M0_gt1; lra ]).
  assert (H2 : 0 <= ln (t + 1))
    by (rewrite <- ln_1; apply ln_le_mono; lra).
  assert (H3 : 0 <= ln ((t + 1) / PI)).
  { rewrite <- ln_1. apply ln_le_mono; [ lra | ].
    apply (Rmult_le_reg_r PI); [ lra | ].
    unfold Rdiv. rewrite Rmult_assoc, Rinv_l by lra. lra. }
  nra.
Qed.

(* xi's circle bound IS XiM, and 4 XiM is what ln4XiM_bound eats *)
Lemma XiM_eq : forall t, 4 * XiM t = 2 + 4 * (t + 1) ^ 2 * Tgb (t + 1).
Proof. intro t. unfold XiM. field. Qed.

Lemma XiM_pos : forall t, 0 < XiM t.
Proof.
  intro t. unfold XiM. pose proof (Tgb_pos (t + 1)) as HT.
  pose proof (Rle_0_sqr (t + 1)) as Hsq.
  assert (0 <= (t + 1) ^ 2 * Tgb (t + 1))
    by (apply Rmult_le_pos; [ unfold Rsqr in Hsq; nra | lra ]).
  lra.
Qed.

(* the bound on the CIRCLE majorant itself -- what the disk transfer wants *)
Lemma XiM_ln_bound : forall t, 8 <= t -> ln (XiM t) <= Lxi t.
Proof.
  intros t Ht. pose proof (XiM_pos t) as HXM.
  apply Rle_trans with (ln (4 * XiM t)); [ apply ln_le_mono; lra | ].
  rewrite (XiM_eq t). unfold Lxi. apply ln4XiM_bound. lra.
Qed.

Theorem xi_ln_bound : forall z, 8 <= Cmod z ->
  ln (Cmod (XiC z)) <= Lxi (Cmod z).
Proof.
  intros z Hz. pose proof PI_RGT_0 as HPI. pose proof PI_4 as HPI4.
  pose proof (XiM_pos (Cmod z)) as HXM.
  (* the multiplicative bound, recognised as XiM *)
  assert (Hmul : Cmod (XiC z) <= XiM (Cmod z))
    by (unfold XiM; apply XiC_growth).
  destruct (Rle_lt_dec (Cmod (XiC z)) 0) as [Hle | Hpos].
  - (* xi z = 0 : Coq's ln is 0 there *)
    assert (Hz0 : Cmod (XiC z) = 0)
      by (pose proof (Cmod_nonneg (XiC z)); lra).
    rewrite Hz0, ln_zero. apply Lxi_nonneg; exact Hz.
  - apply Rle_trans with (ln (XiM (Cmod z)));
      [ apply ln_le_mono; assumption | apply XiM_ln_bound; exact Hz ].
Qed.

Print Assumptions XiM_ln_bound.
Print Assumptions xi_ln_bound.
