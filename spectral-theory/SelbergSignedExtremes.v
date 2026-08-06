(* ================================================================= *)
(*  SelbergSignedExtremes.v  —  the signed extremes of the error.     *)
(*                                                                    *)
(*  V = limsup Vsig, v = liminf Vsig, alpha = limsup Vrem (= limsup    *)
(*  |Vsig|).  The correct Selberg endgame works with V, v (the         *)
(*  degree-1 |.|-average cannot, see moonlit plan).  This file proves   *)
(*  the STRUCTURAL relation, always true:                              *)
(*                                                                    *)
(*    alpha_eq_max : alpha = Rmax V (- v).                             *)
(*                                                                    *)
(*  (The deeper fact V = -v = alpha, needing the signed pin            *)
(*  selberg_average_signed, is the next rung.)  Axiom-clean.           *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia Arith.
Require Import Chebyshev ChebyshevBound SelbergEndgame SelbergAverage
        SelbergAverageSigned LimSup LimInf.
Open Scope R_scope.

Lemma inv_INR_nonneg : forall n, 0 <= / INR n.
Proof.
  intros n; destruct (Nat.eq_dec n 0) as [->|Hn];
    [ simpl; rewrite Rinv_0; lra
    | apply Rlt_le, Rinv_0_lt_compat, lt_0_INR; lia ].
Qed.

(* limsup and liminf are monotone in the sequence *)
Lemma is_limsup_mono : forall u w Lu Lw,
  is_limsup u Lu -> is_limsup w Lw -> (forall n, u n <= w n) -> Lu <= Lw.
Proof.
  intros u w Lu Lw [_ Hub] [Hwa _] Hle.
  destruct (Rle_or_lt Lu Lw) as [H|H]; [ exact H | exfalso ].
  destruct (Hwa ((Lu - Lw) / 2) ltac:(lra)) as [N0 HN0].
  destruct (Hub ((Lu - Lw) / 2) ltac:(lra) N0) as [k [Hk Hgt]].
  specialize (HN0 k Hk); pose proof (Hle k); lra.
Qed.

(* Vsig and Vrem = |Vsig| are sandwiched: -Vrem <= Vsig <= Vrem *)
Lemma Vsig_le_Vrem : forall n, Vsig n <= Vrem n.
Proof.
  intros n; unfold Vsig, Vrem, Rdiv.
  apply Rmult_le_compat_r; [ apply inv_INR_nonneg | apply Rle_abs ].
Qed.

Lemma negVrem_le_Vsig : forall n, - Vrem n <= Vsig n.
Proof.
  intros n; unfold Vsig, Vrem, Rdiv.
  rewrite Ropp_mult_distr_l.
  apply Rmult_le_compat_r; [ apply inv_INR_nonneg | ].
  pose proof (Rle_abs (- Rem n)) as H; rewrite Rabs_Ropp in H; lra.
Qed.

Lemma Vrem_eq_absVsig : forall n, Vrem n = Rabs (Vsig n).
Proof.
  intros n; unfold Vrem, Vsig, Rdiv.
  rewrite Rabs_mult, (Rabs_pos_eq (/ INR n)); [ reflexivity | apply inv_INR_nonneg ].
Qed.

Section Extremes.

Variables V v alpha : R.
Hypothesis HV : is_limsup Vsig V.
Hypothesis Hv : is_liminf Vsig v.
Hypothesis Halpha : is_limsup Vrem alpha.

Lemma V_le_alpha : V <= alpha.
Proof. exact (is_limsup_mono Vsig Vrem V alpha HV Halpha Vsig_le_Vrem). Qed.

Lemma negalpha_le_v : - alpha <= v.
Proof.
  destruct Halpha as [Halpha_ub _]; destruct Hv as [_ Hv_io].
  destruct (Rle_or_lt (- alpha) v) as [H|H]; [ exact H | exfalso ].
  destruct (Halpha_ub ((- alpha - v) / 2) ltac:(lra)) as [N0 HN0].
  destruct (Hv_io ((- alpha - v) / 2) ltac:(lra) N0) as [k [Hk Hlt]].
  specialize (HN0 k Hk); pose proof (negVrem_le_Vsig k); lra.
Qed.

Lemma alpha_le_max : alpha <= Rmax V (- v).
Proof.
  destruct HV as [HV_ub _]; destruct Hv as [Hv_lb _]; destruct Halpha as [_ Halpha_io].
  destruct (Rle_or_lt alpha (Rmax V (- v))) as [H|H]; [ exact H | exfalso ].
  set (eps := (alpha - Rmax V (- v)) / 2).
  assert (Heps : 0 < eps) by (unfold eps; lra).
  destruct (HV_ub eps Heps) as [N1 HN1].
  destruct (Hv_lb eps Heps) as [N2 HN2].
  destruct (Halpha_io eps Heps (Nat.max N1 N2)) as [k [Hk Hgt]].
  specialize (HN1 k ltac:(lia)); specialize (HN2 k ltac:(lia)).
  assert (Hbound : Rabs (Vsig k) < Rmax V (- v) + eps).
  { apply Rabs_def1.
    - pose proof (Rmax_l V (- v)); lra.
    - pose proof (Rmax_r V (- v)); lra. }
  rewrite <- Vrem_eq_absVsig in Hbound.
  unfold eps in *; lra.
Qed.

Theorem alpha_eq_max : alpha = Rmax V (- v).
Proof.
  apply Rle_antisym; [ apply alpha_le_max | ].
  apply Rmax_lub; [ apply V_le_alpha | pose proof negalpha_le_v; lra ].
Qed.

End Extremes.

Print Assumptions alpha_eq_max.

(* ================================================================= *)
(*  END SelbergSignedExtremes.v  —  alpha = max(V, -v).  Next: the      *)
(*  signed pin forces V = -v = alpha (both extremes reach alpha).       *)
(* ================================================================= *)
