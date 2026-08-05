(* ================================================================= *)
(*  EulerMaclaurin.v  —  the per-step defect bound (Step 2d, v3 core).  *)
(*                                                                    *)
(*  For the refined estimate  Sum_{m<=y} (2 ln m - 2)/m = q(ln y)+C+o(1) *)
(*  (q(L)=L^2-2L), the engine is a bound on the Euler-Maclaurin defect   *)
(*      b(m) := h(m) - (Q(m) - Q(m-1)),                                 *)
(*  where Q(t)=ln^2 t - 2 ln t = q(ln t),  Q'(t)=h(t)=(2 ln t - 2)/t.    *)
(*  Two nested MVTs (Q'=h, h'=hp with hp(t)=(4-2 ln t)/t^2) give          *)
(*      b(m) = h(m) - h(xi) = hp(eta)*(m-xi),  m-1<xi<eta<m,             *)
(*  hence  |b(m)| <= |hp(eta)| <= 16 (ln m + 1)/m^2,                     *)
(*  a summable bound (Sum ln m/m^2 < oo).  Axiom-clean.                 *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia Arith.
Require Import ChebyshevBound.
Open Scope R_scope.

Definition Qfun (t : R) : R := ln t * ln t - 2 * ln t.
Definition hfun (t : R) : R := (2 * ln t - 2) / t.
Definition hp   (t : R) : R := (4 - 2 * ln t) / (t * t).

(* Q'(t) = h(t) *)
Lemma dQ : forall t, 0 < t -> derivable_pt_lim Qfun t (hfun t).
Proof.
  intros t Ht.
  assert (Hln : derivable_pt_lim ln t (/ t)) by (apply derivable_pt_lim_ln; exact Ht).
  assert (Hsq : derivable_pt_lim (fun t => ln t * ln t) t (/ t * ln t + ln t * / t))
    by (apply (derivable_pt_lim_mult ln ln t (/ t) (/ t)); exact Hln).
  assert (H2 : derivable_pt_lim (fun t => 2 * ln t) t (2 * / t))
    by (apply (derivable_pt_lim_scal ln 2 t (/ t)); exact Hln).
  assert (Hm : derivable_pt_lim Qfun t ((/ t * ln t + ln t * / t) - 2 * / t))
    by (unfold Qfun; apply derivable_pt_lim_minus; [ exact Hsq | exact H2 ]).
  replace (hfun t) with ((/ t * ln t + ln t * / t) - 2 * / t) by (unfold hfun; field; lra).
  exact Hm.
Qed.

(* h'(t) = hp(t) *)
Lemma dh : forall t, 0 < t -> derivable_pt_lim hfun t (hp t).
Proof.
  intros t Ht.
  assert (Hln : derivable_pt_lim ln t (/ t)) by (apply derivable_pt_lim_ln; exact Ht).
  assert (Hf : derivable_pt_lim (fun y => 2 * ln y - 2) t (2 * / t)).
  { replace (2 * / t) with (2 * / t - 0) by ring.
    apply derivable_pt_lim_minus;
      [ apply (derivable_pt_lim_scal ln 2 t (/ t)); exact Hln
      | apply (derivable_pt_lim_const 2 t) ]. }
  assert (Hg : derivable_pt_lim (fun y => y) t 1) by apply derivable_pt_lim_id.
  pose proof (derivable_pt_lim_div (fun y => 2 * ln y - 2) (fun y => y) t (2 * / t) 1
                Hf Hg ltac:(simpl; lra)) as Hd.
  replace (hp t) with ((2 * / t * t - 1 * (2 * ln t - 2)) / (t)²)
    by (unfold hp, Rsqr; field; lra).
  exact Hd.
Qed.

Definition bdefect (m : nat) : R :=
  hfun (INR m) - (Qfun (INR m) - Qfun (INR (m - 1))).

(* the summable per-step bound *)
Theorem b_bound : forall m, (2 <= m)%nat ->
  Rabs (bdefect m) <= 16 * (ln (INR m) + 1) / (INR m * INR m).
Proof.
  intros m Hm; unfold bdefect.
  assert (Hc1 : 1 <= INR (m - 1)) by (apply (le_INR 1); lia).
  assert (Hstep : INR m = INR (m - 1) + 1) by (rewrite <- S_INR; f_equal; lia).
  set (a := INR (m - 1)) in *; set (c := INR m) in *.
  assert (Hca : c = a + 1) by exact Hstep.
  assert (Hac : a < c) by lra.
  assert (Ha0 : 0 < a) by lra.
  (* MVT on Q over [a,c] *)
  destruct (MVT_cor2 Qfun hfun a c Hac (fun x Hx => dQ x ltac:(lra))) as [xi [HQ Hxi]].
  assert (Hca1 : c - a = 1) by lra.
  rewrite Hca1, Rmult_1_r in HQ.
  rewrite HQ.
  (* MVT on h over [xi,c] *)
  assert (Hxic : xi < c) by lra.
  destruct (MVT_cor2 hfun hp xi c Hxic (fun x Hx => dh x ltac:(lra))) as [eta [Hh Heta]].
  rewrite Hh.
  (* geometric / analytic bounds *)
  assert (Heta0 : 0 < eta) by lra.
  assert (Hee : 0 < eta * eta) by nra.
  assert (Haa : 0 < a * a) by nra.
  assert (Hcc : 0 < c * c) by nra.
  assert (Hlnc0 : 0 <= ln c) by (rewrite <- ln_1; apply ln_le; lra).
  assert (Hlne0 : 0 <= ln eta) by (rewrite <- ln_1; apply ln_le; lra).
  assert (Hlnec : ln eta <= ln c) by (apply ln_le; lra).
  assert (Hesq : a * a <= eta * eta) by nra.
  assert (Hac4 : c * c <= 4 * (a * a)) by nra.
  assert (Hcxi : 0 <= c - xi <= 1) by lra.
  (* |hp eta| <= (16 + 8 ln c)/(c*c) *)
  assert (Hhp : Rabs (hp eta) <= (16 + 8 * ln c) / (c * c)).
  { unfold hp, Rdiv; rewrite Rabs_mult, Rabs_inv, (Rabs_pos_eq (eta * eta)) by lra.
    apply Rle_trans with ((4 + 2 * ln c) * / (a * a)).
    - apply Rmult_le_compat.
      + apply Rabs_pos.
      + left; apply Rinv_0_lt_compat; exact Hee.
      + apply Rabs_le; split; lra.
      + apply Rinv_le_contravar; [ exact Haa | exact Hesq ].
    - replace ((16 + 8 * ln c) * / (c * c)) with ((4 + 2 * ln c) * (4 * / (c * c)))
        by (field; lra).
      apply Rmult_le_compat_l; [ lra | ].
      apply Rmult_le_reg_l with (a * a); [ exact Haa | ].
      rewrite Rinv_r by lra.
      apply Rmult_le_reg_l with (c * c); [ exact Hcc | ].
      rewrite Rmult_1_r.
      replace (c * c * (a * a * (4 * / (c * c)))) with (4 * (a * a)) by (field; lra).
      exact Hac4. }
  (* conclude *)
  rewrite Rabs_mult, (Rabs_pos_eq (c - xi)) by lra.
  apply Rle_trans with (Rabs (hp eta) * 1); [ apply Rmult_le_compat_l; [ apply Rabs_pos | lra ] | ].
  rewrite Rmult_1_r.
  apply Rle_trans with ((16 + 8 * ln c) / (c * c)); [ exact Hhp | ].
  unfold Rdiv; apply Rmult_le_compat_r; [ left; apply Rinv_0_lt_compat; exact Hcc | lra ].
Qed.

Print Assumptions b_bound.

(* ================================================================= *)
(*  END EulerMaclaurin.v  —  |b(m)| <= 16 (ln m + 1)/m^2.              *)
(* ================================================================= *)
