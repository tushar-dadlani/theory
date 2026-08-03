(* ================================================================= *)
(*  CDerivLine.v  —  the line-bridge: a complex derivative is_Cderiv    *)
(*  gives the real derivable_pt_lim of the components along a complex   *)
(*  line s+t*h, in the real parameter t.  This is what feeds the        *)
(*  componentwise second-order Taylor bound (order2_bound) for the      *)
(*  differentiation-under-the-sum.  Axiom-clean.                       *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra.
Require Import ComplexField Cmodulus CSeries Holomorphic.
Open Scope R_scope.

Lemma Re_RtoC_mul : forall r c, Re (Cmul (RtoC r) c) = r * Re c.
Proof. intros r c; unfold Cmul, RtoC; cbn; ring. Qed.

Lemma Im_RtoC_mul : forall r c, Im (Cmul (RtoC r) c) = r * Im c.
Proof. intros r c; unfold Cmul, RtoC; cbn; ring. Qed.

Lemma Re_Cminus : forall a b, Re (Cminus a b) = Re a - Re b.
Proof. intros a b; unfold Cminus; cbn; ring. Qed.

Lemma Im_Cminus : forall a b, Im (Cminus a b) = Im a - Im b.
Proof. intros a b; unfold Cminus; cbn; ring. Qed.

Section Line.
Variables (F : C -> C) (z h : C).

Lemma is_Cderiv_line_Re : forall d t,
  is_Cderiv F (Cadd z (Cmul (RtoC t) h)) d ->
  derivable_pt_lim (fun u => Re (F (Cadd z (Cmul (RtoC u) h)))) t (Re (Cmul d h)).
Proof.
  intros d t HF eps Heps.
  pose proof (Cmod_nonneg h) as Hh0.
  destruct (HF (eps / (Cmod h + 1)) ltac:(apply Rdiv_lt_0_compat; lra)) as [dF [HdF HF']].
  assert (Hdel : 0 < dF / (Cmod h + 1)) by (apply Rdiv_lt_0_compat; lra).
  exists (mkposreal _ Hdel).
  intros dh Hdh0 Hdh.
  set (P := Cadd z (Cmul (RtoC t) h)); set (k := Cmul (RtoC dh) h).
  assert (Hpt : Cadd z (Cmul (RtoC (t + dh)) h) = Cadd P k)
    by (unfold P, k; rewrite RtoC_add; ring).
  rewrite Hpt.
  assert (Hkmod : Cmod k = Rabs dh * Cmod h)
    by (unfold k; rewrite Cmod_mul, Cmod_RtoC; reflexivity).
  assert (Hdhpos : 0 < Rabs dh) by (apply Rabs_pos_lt; exact Hdh0).
  assert (HkF : Cmod k < dF).
  { rewrite Hkmod.
    apply Rle_lt_trans with (Rabs dh * (Cmod h + 1));
      [ apply Rmult_le_compat_l; [ apply Rabs_pos | lra ] | ].
    replace dF with (dF / (Cmod h + 1) * (Cmod h + 1)) by (field; lra).
    apply Rmult_lt_compat_r; [ lra | exact Hdh ]. }
  pose proof (HF' k HkF) as HR.
  assert (HdRe : Re (Cmul d k) = dh * Re (Cmul d h))
    by (unfold k; replace (Cmul d (Cmul (RtoC dh) h)) with (Cmul (RtoC dh) (Cmul d h)) by ring;
        apply Re_RtoC_mul).
  unfold R_dist.
  replace ((Re (F (Cadd P k)) - Re (F P)) / dh - Re (Cmul d h))
    with (Re (Cminus (Cminus (F (Cadd P k)) (F P)) (Cmul d k)) / dh)
    by (rewrite !Re_Cminus, HdRe; field; exact Hdh0).
  unfold Rdiv; rewrite Rabs_mult, Rabs_Rinv by exact Hdh0.
  apply Rle_lt_trans with (Cmod (Cminus (Cminus (F (Cadd P k)) (F P)) (Cmul d k)) * / Rabs dh).
  - apply Rmult_le_compat_r; [ apply Rlt_le; apply Rinv_0_lt_compat; exact Hdhpos | apply Cmod_Re_le ].
  - apply Rle_lt_trans with (eps / (Cmod h + 1) * Cmod k * / Rabs dh).
    + apply Rmult_le_compat_r; [ apply Rlt_le; apply Rinv_0_lt_compat; exact Hdhpos | exact HR ].
    + rewrite Hkmod.
      replace (eps / (Cmod h + 1) * (Rabs dh * Cmod h) * / Rabs dh)
        with (eps / (Cmod h + 1) * Cmod h) by (field; lra).
      apply Rmult_lt_reg_r with (Cmod h + 1); [ lra | ].
      replace (eps / (Cmod h + 1) * Cmod h * (Cmod h + 1)) with (eps * Cmod h) by (field; lra).
      nra.
Qed.

Lemma is_Cderiv_line_Im : forall d t,
  is_Cderiv F (Cadd z (Cmul (RtoC t) h)) d ->
  derivable_pt_lim (fun u => Im (F (Cadd z (Cmul (RtoC u) h)))) t (Im (Cmul d h)).
Proof.
  intros d t HF eps Heps.
  pose proof (Cmod_nonneg h) as Hh0.
  destruct (HF (eps / (Cmod h + 1)) ltac:(apply Rdiv_lt_0_compat; lra)) as [dF [HdF HF']].
  assert (Hdel : 0 < dF / (Cmod h + 1)) by (apply Rdiv_lt_0_compat; lra).
  exists (mkposreal _ Hdel).
  intros dh Hdh0 Hdh.
  set (P := Cadd z (Cmul (RtoC t) h)); set (k := Cmul (RtoC dh) h).
  assert (Hpt : Cadd z (Cmul (RtoC (t + dh)) h) = Cadd P k)
    by (unfold P, k; rewrite RtoC_add; ring).
  rewrite Hpt.
  assert (Hkmod : Cmod k = Rabs dh * Cmod h)
    by (unfold k; rewrite Cmod_mul, Cmod_RtoC; reflexivity).
  assert (Hdhpos : 0 < Rabs dh) by (apply Rabs_pos_lt; exact Hdh0).
  assert (HkF : Cmod k < dF).
  { rewrite Hkmod.
    apply Rle_lt_trans with (Rabs dh * (Cmod h + 1));
      [ apply Rmult_le_compat_l; [ apply Rabs_pos | lra ] | ].
    replace dF with (dF / (Cmod h + 1) * (Cmod h + 1)) by (field; lra).
    apply Rmult_lt_compat_r; [ lra | exact Hdh ]. }
  pose proof (HF' k HkF) as HR.
  assert (HdIm : Im (Cmul d k) = dh * Im (Cmul d h))
    by (unfold k; replace (Cmul d (Cmul (RtoC dh) h)) with (Cmul (RtoC dh) (Cmul d h)) by ring;
        apply Im_RtoC_mul).
  unfold R_dist.
  replace ((Im (F (Cadd P k)) - Im (F P)) / dh - Im (Cmul d h))
    with (Im (Cminus (Cminus (F (Cadd P k)) (F P)) (Cmul d k)) / dh)
    by (rewrite !Im_Cminus, HdIm; field; exact Hdh0).
  unfold Rdiv; rewrite Rabs_mult, Rabs_Rinv by exact Hdh0.
  apply Rle_lt_trans with (Cmod (Cminus (Cminus (F (Cadd P k)) (F P)) (Cmul d k)) * / Rabs dh).
  - apply Rmult_le_compat_r; [ apply Rlt_le; apply Rinv_0_lt_compat; exact Hdhpos | apply Cmod_Im_le ].
  - apply Rle_lt_trans with (eps / (Cmod h + 1) * Cmod k * / Rabs dh).
    + apply Rmult_le_compat_r; [ apply Rlt_le; apply Rinv_0_lt_compat; exact Hdhpos | exact HR ].
    + rewrite Hkmod.
      replace (eps / (Cmod h + 1) * (Rabs dh * Cmod h) * / Rabs dh)
        with (eps / (Cmod h + 1) * Cmod h) by (field; lra).
      apply Rmult_lt_reg_r with (Cmod h + 1); [ lra | ].
      replace (eps / (Cmod h + 1) * Cmod h * (Cmod h + 1)) with (eps * Cmod h) by (field; lra).
      nra.
Qed.

End Line.

Print Assumptions is_Cderiv_line_Re.

(* ================================================================= *)
(*  END CDerivLine.v.                                                  *)
(* ================================================================= *)
