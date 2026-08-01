(* ================================================================= *)
(*  RpowerZero.v  —  Riemann FE milestone R2a, file 1:              *)
(*  the near-0 limit of a positive real power.                       *)
(*                                                                    *)
(*  Mirror of ZetaContinuation.Rpower_neg_cv0 (which sends n^{c}→0    *)
(*  as n→∞ for c<0): here εᵃ → 0 as ε→0⁺ for a>0.  The threshold is   *)
(*  δ = ε₀^{1/a} (so δᵃ = ε₀), and Rpower is increasing in its base   *)
(*  for a positive exponent.                                         *)
(*  No new axioms (classical Reals only).                            *)
(* ================================================================= *)

From Stdlib Require Import Reals Rpower Lra.
Open Scope R_scope.

Lemma Rpower_pos' : forall x y, 0 < Rpower x y.
Proof. intros x y; unfold Rpower; apply exp_pos. Qed.

Lemma Rpower_base_lt : forall a x y, 0 < a -> 0 < x -> x < y -> Rpower x a < Rpower y a.
Proof.
  intros a x y Ha Hx Hxy; unfold Rpower; apply exp_increasing.
  apply Rmult_lt_compat_l; [ exact Ha | apply ln_increasing; [ exact Hx | exact Hxy ] ].
Qed.

Theorem Rpower_pos_cv0 : forall a, 0 < a ->
  forall e, (forall k, 0 < e k) -> Un_cv e 0 -> Un_cv (fun k => Rpower (e k) a) 0.
Proof.
  intros a Ha e He Hcv eps Heps.
  set (delta := Rpower eps (/ a)).
  destruct (Hcv delta (Rpower_pos' eps (/ a))) as [N HN]; exists N; intros k Hk.
  specialize (HN k Hk); unfold R_dist in HN; rewrite Rminus_0_r in HN.
  rewrite Rabs_right in HN by (apply Rle_ge; left; apply He).
  unfold R_dist; rewrite Rminus_0_r; rewrite Rabs_right by (apply Rle_ge; left; apply Rpower_pos').
  apply Rlt_le_trans with (Rpower delta a);
    [ apply Rpower_base_lt; [ exact Ha | apply He | exact HN ] | ].
  unfold delta; rewrite Rpower_mult.
  replace (/ a * a) with 1 by (field; apply Rgt_not_eq; exact Ha).
  rewrite (Rpower_1 eps Heps); apply Rle_refl.
Qed.

Print Assumptions Rpower_pos_cv0.

(* ================================================================= *)
(*  END RpowerZero.v  —  εᵃ → 0 as ε → 0⁺  (a > 0).                   *)
(* ================================================================= *)
