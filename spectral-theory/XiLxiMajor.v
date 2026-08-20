(* ================================================================= *)
(*  XiLxiMajor.v  —  Lxi is monotone and o(r^2).                       *)
(*                                                                    *)
(*    ln_scal_le : ln (a . t) <= 2 ln t          (1 <= a <= t)         *)
(*    Lxi_le     : Lxi t <= ln M0 + 4 ln t + 2 t ln t   (5 <= t)       *)
(*    Lxi_mono   : Lxi nondecreasing on [4, oo)                        *)
(*    Lsh_monoR / Lsh_subquad : the two properties Mf needs, for the   *)
(*      shifted argument 4 (max r 0 + 80).                             *)
(*                                                                    *)
(*  Lxi is NOT monotone on all of [0, oo): the term                    *)
(*  (t+1)/2 . ln((t+1)/PI) is negative below t = PI-1, so the product  *)
(*  falls before it rises.  Past t = 4 both factors are nonnegative    *)
(*  and increasing, hence so is the product -- which is why every use  *)
(*  here shifts the argument clear of the origin rather than patching  *)
(*  the small-t behaviour.                                             *)
(*                                                                    *)
(*  ln_scal_le is the only trick the size estimate needs: a constant   *)
(*  factor inside a logarithm costs a factor 2 outside, once the       *)
(*  constant has been passed by the argument.  Axiom-clean.            *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra.
Require Import RLogPower RSubQuad XiZeroCount XiHgrow XiLnBound.
Open Scope R_scope.

Lemma ln3_ge1 : 1 <= ln 3.
Proof.
  pose proof exp_le_3 as H3. pose proof (exp_pos 1) as H1.
  rewrite <- (ln_exp 1). apply ln_mono_le; lra.
Qed.

Lemma ln_ge1 : forall t, 3 <= t -> 1 <= ln t.
Proof.
  intros t Ht. apply Rle_trans with (ln 3); [ apply ln3_ge1 | ].
  apply ln_mono_le; lra.
Qed.

Lemma ln_scal_le : forall a t, 1 <= a -> a <= t -> ln (a * t) <= 2 * ln t.
Proof.
  intros a t Ha Hat.
  rewrite ln_mult by lra.
  pose proof (ln_mono_le a t ltac:(lra) Hat). lra.
Qed.

(* ----------------------------------------------------------------- *)
(*  A.  the size estimate                                              *)
(* ----------------------------------------------------------------- *)
Lemma Lxi_le : forall t, 5 <= t ->
  Lxi t <= ln M0 + 4 * ln t + 2 * (t * ln t).
Proof.
  intros t Ht. pose proof PI_RGT_0 as HPI. pose proof PI_4 as HPI4.
  pose proof PI_lb2 as HPI2.
  pose proof (ln_ge1 t ltac:(lra)) as Hlnt.
  unfold Lxi.
  (* the logarithmic term *)
  assert (H1 : ln (t + 1) <= 2 * ln t).
  { apply Rle_trans with (ln (2 * t));
      [ apply ln_mono_le; lra | apply ln_scal_le; lra ]. }
  (* the linear-times-log term *)
  assert (Hq0 : 0 <= ln ((t + 1) / PI)).
  { rewrite <- ln_1. apply ln_mono_le; [ lra | ].
    apply (Rmult_le_reg_r PI); [ lra | ].
    unfold Rdiv. rewrite Rmult_assoc, Rinv_l by lra. lra. }
  assert (Hq1 : ln ((t + 1) / PI) <= 2 * ln t).
  { apply Rle_trans with (ln (t + 1)); [ | exact H1 ].
    apply ln_mono_le.
    - apply Rdiv_lt_0_compat; lra.
    - apply (Rmult_le_reg_r PI); [ lra | ].
      unfold Rdiv. rewrite Rmult_assoc, Rinv_l by lra. nra. }
  assert (Hprod : (t + 1) / 2 * ln ((t + 1) / PI) <= t * (2 * ln t)).
  { apply Rmult_le_compat; [ lra | exact Hq0 | lra | exact Hq1 ]. }
  lra.
Qed.

(* ----------------------------------------------------------------- *)
(*  B.  monotonicity, past the dip                                     *)
(* ----------------------------------------------------------------- *)
Lemma Lxi_mono : forall a b, 4 <= a -> a <= b -> Lxi a <= Lxi b.
Proof.
  intros a b Ha Hab. pose proof PI_RGT_0 as HPI. pose proof PI_4 as HPI4.
  pose proof PI_lb2 as HPI2.
  unfold Lxi.
  assert (H1 : ln (a + 1) <= ln (b + 1)) by (apply ln_mono_le; lra).
  assert (Hqa0 : 0 <= ln ((a + 1) / PI)).
  { rewrite <- ln_1. apply ln_mono_le; [ lra | ].
    apply (Rmult_le_reg_r PI); [ lra | ].
    unfold Rdiv. rewrite Rmult_assoc, Rinv_l by lra. lra. }
  assert (Hq : ln ((a + 1) / PI) <= ln ((b + 1) / PI)).
  { apply ln_mono_le; [ apply Rdiv_lt_0_compat; lra | ].
    apply Rmult_le_compat_r; [ left; apply Rinv_0_lt_compat; lra | lra ]. }
  assert (Hprod : (a + 1) / 2 * ln ((a + 1) / PI)
                  <= (b + 1) / 2 * ln ((b + 1) / PI))
    by (apply Rmult_le_compat; [ lra | exact Hqa0 | lra | exact Hq ]).
  lra.
Qed.

(* ----------------------------------------------------------------- *)
(*  C.  the shifted form, with the two properties Mf needs             *)
(* ----------------------------------------------------------------- *)
Definition Lsh (r : R) : R := Lxi (4 * (Rmax r 0 + 80)).

Lemma Lsh_monoR : MonoR Lsh.
Proof.
  intros a b Hab. unfold Lsh.
  assert (Hm : Rmax a 0 <= Rmax b 0).
  { apply Rmax_lub; [ apply Rle_trans with b; [ exact Hab | apply Rmax_l ]
                    | apply Rmax_r ]. }
  assert (Ha0 : 0 <= Rmax a 0) by apply Rmax_r.
  apply Lxi_mono; lra.
Qed.

Lemma Lsh_subquad : SubQuad Lsh.
Proof.
  apply (SubQuad_le Lsh (fun r => ln M0 + 40 * (r * (ln r) ^ 2))).
  - apply SubQuad_plus; [ apply SubQuad_const | ].
    apply SubQuad_scal; [ lra | apply SubQuad_rln2 ].
  - exists 80. intros r Hr.
    assert (Hmax : Rmax r 0 = r) by (apply Rmax_left; lra).
    unfold Lsh. rewrite Hmax.
    pose proof (ln_ge1 r ltac:(lra)) as Hlnr.
    assert (Hle : 4 * (r + 80) <= 8 * r) by lra.
    assert (Hge : 5 <= 4 * (r + 80)) by lra.
    pose proof (Lxi_le (4 * (r + 80)) Hge) as HL.
    (* the inner logarithm *)
    assert (Hln8 : ln (4 * (r + 80)) <= 2 * ln r).
    { apply Rle_trans with (ln (8 * r));
        [ apply ln_mono_le; lra | apply ln_scal_le; lra ]. }
    assert (Hln0 : 0 <= ln (4 * (r + 80)))
      by (rewrite <- ln_1; apply ln_mono_le; lra).
    (* the product term *)
    assert (Hpr : 4 * (r + 80) * ln (4 * (r + 80)) <= 8 * r * (2 * ln r))
      by (apply Rmult_le_compat; lra).
    (* fold both into r ln^2 r *)
    assert (Hs1 : ln r <= r * (ln r) ^ 2) by nra.
    assert (Hs2 : r * ln r <= r * (ln r) ^ 2) by nra.
    lra.
Qed.

Print Assumptions Lxi_le.
Print Assumptions Lsh_subquad.
