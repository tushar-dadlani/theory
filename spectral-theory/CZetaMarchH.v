(* ================================================================= *)
(*  CZetaMarchH.v   (Phase C1: horizontal march / from-region reach)    *)
(*                                                                    *)
(*  If F is holomorphic + continuous on {Re>0} and vanishes on the      *)
(*  2-D region {Re>1}, then F vanishes on ALL of {Re>0}.               *)
(*                                                                    *)
(*  Unlike CWalk.reach (which seeds on the real ray), this marches       *)
(*  HORIZONTALLY at fixed Im from a seed disk in {Re>1} (radius from     *)
(*  the target's Re), via CScaledDisk.scaled_disk_zero (center-general). *)
(*                                                                    *)
(*  Axioms: standard classical-Reals only.                            *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import ComplexField Cmodulus Holomorphic CIdentityProp
        CScaledDisk CSeries.
Open Scope R_scope.

Section MarchH.
Variable F : C -> C.
Hypothesis HFptc : forall z, 0 < Re z -> forall e, 0 < e -> exists del, 0 < del /\
  forall z', Cmod (Cminus z' z) < del -> Cmod (Cminus (F z') (F z)) < e.
Hypothesis HFhol : forall z, 0 < Re z -> exists d, is_Cderiv F z d.
Hypothesis Hvanish : forall z, 1 < Re z -> F z = C0.

(* one horizontal step: spread the zero-disk from (x0,y) to nearby (x1,y) *)
Lemma march_step_h : forall a, 0 < a -> forall x0 x1 y,
  a <= x1 ->
  (forall z, Cmod (Cminus z (mkC x0 y)) < a / 7 -> F z = C0) ->
  Rabs (x1 - x0) < a / 14 ->
  forall z, Cmod (Cminus z (mkC x1 y)) < a / 7 -> F z = C0.
Proof.
  intros a Ha x0 x1 y Hx1 H0 Hstep z Hz.
  apply (scaled_disk_zero F HFptc HFhol (mkC x1 y) (a / 7) (a / 14)).
  - lra.
  - cbn [Re]; lra.
  - lra.
  - intros z' Hz'. apply H0.
    assert (Hgeo : Cmod (Cminus (mkC x1 y) (mkC x0 y)) = Rabs (x1 - x0)).
    { replace (Cminus (mkC x1 y) (mkC x0 y)) with (mkC (x1 - x0) 0)
        by (apply Ceq; unfold Cminus, Cadd, Copp; cbn [Re Im]; ring).
      unfold Cmod, Cnorm2; cbn [Re Im].
      replace ((x1 - x0) * (x1 - x0) + 0 * 0) with (Rsqr (x1 - x0))
        by (unfold Rsqr; ring).
      rewrite sqrt_Rsqr_abs; reflexivity. }
    assert (Htri : Cmod (Cminus z' (mkC x0 y))
                   <= Cmod (Cminus z' (mkC x1 y)) + Cmod (Cminus (mkC x1 y) (mkC x0 y))).
    { replace (Cminus z' (mkC x0 y))
        with (Cadd (Cminus z' (mkC x1 y)) (Cminus (mkC x1 y) (mkC x0 y))) by ring.
      apply Cmod_triangle. }
    rewrite Hgeo in Htri. lra.
  - exact Hz.
Qed.

(* march the i-th interpolation point from x=2 down to x=a (fixed Im=y) *)
Lemma march_to_h : forall a, 0 < a -> a <= 2 -> forall y,
  (forall z, Cmod (Cminus z (mkC 2 y)) < a / 7 -> F z = C0) ->
  forall N, (0 < N)%nat -> Rabs (a - 2) < INR N * (a / 14) ->
    forall i, (i <= N)%nat ->
      forall z, Cmod (Cminus z (mkC (2 + INR i / INR N * (a - 2)) y)) < a / 7 -> F z = C0.
Proof.
  intros a Ha Ha2 y Hbase N HN Hbnd.
  assert (HNr : 0 < INR N) by (apply lt_0_INR; lia).
  induction i as [| i IHi]; intros Hi z Hz.
  - assert (Hx0 : 2 + INR 0 / INR N * (a - 2) = 2) by (simpl; field; lra).
    rewrite Hx0 in Hz. apply Hbase; exact Hz.
  - assert (Hile : (i <= N)%nat) by lia.
    assert (Hfrac : 0 <= INR (S i) / INR N <= 1).
    { split; [ apply Rle_mult_inv_pos; [ apply pos_INR | exact HNr ] | ].
      apply (Rmult_le_reg_r (INR N)); [ exact HNr | ].
      replace (INR (S i) / INR N * INR N) with (INR (S i)) by (field; lra).
      rewrite Rmult_1_l. apply le_INR; lia. }
    apply (march_step_h a Ha (2 + INR i / INR N * (a - 2))
                        (2 + INR (S i) / INR N * (a - 2)) y).
    + nra.
    + apply (IHi Hile).
    + replace (2 + INR (S i) / INR N * (a - 2) - (2 + INR i / INR N * (a - 2)))
        with ((a - 2) * / INR N) by (rewrite S_INR; field; lra).
      rewrite Rabs_mult, (Rabs_right (/ INR N))
        by (apply Rle_ge; left; apply Rinv_0_lt_compat; exact HNr).
      apply (Rmult_lt_reg_r (INR N)); [ exact HNr | ].
      replace (Rabs (a - 2) * / INR N * INR N) with (Rabs (a - 2)) by (field; lra).
      lra.
    + exact Hz.
Qed.

Theorem region_reach : forall w, 0 < Re w -> F w = C0.
Proof.
  intros w Hw.
  destruct (Rle_lt_dec (Re w) 1) as [Hle | Hgt]; [ | apply Hvanish; exact Hgt ].
  set (a := Re w). set (y := Im w).
  assert (Ha : 0 < a) by exact Hw.
  assert (Ha1 : a <= 1) by (unfold a; exact Hle).
  assert (Ha2 : a <= 2) by lra.
  assert (Hbase : forall z, Cmod (Cminus z (mkC 2 y)) < a / 7 -> F z = C0).
  { intros z Hz. apply Hvanish.
    pose proof (Cmod_Re_le (Cminus z (mkC 2 y))) as HR.
    assert (Hre : Re (Cminus z (mkC 2 y)) = Re z - 2)
      by (unfold Cminus, Cadd, Copp; cbn [Re Im]; ring).
    rewrite Hre in HR. unfold Rabs in HR; destruct (Rcase_abs (Re z - 2)); lra. }
  assert (Hnn : 0 <= Rabs (a - 2) / (a / 14))
    by (apply Rle_mult_inv_pos; [ apply Rabs_pos | lra ]).
  destruct (exists_nat_gt _ Hnn) as [N HN].
  set (N' := S N).
  assert (HN'pos : (0 < N')%nat) by lia.
  assert (HN'r : INR N' <> 0) by (apply Rgt_not_eq, lt_0_INR; lia).
  assert (H1 : Rabs (a - 2) < INR N * (a / 14)).
  { apply (Rmult_lt_reg_r (/ (a / 14))); [ apply Rinv_0_lt_compat; lra | ].
    replace (INR N * (a / 14) * / (a / 14)) with (INR N) by (field; lra).
    replace (Rabs (a - 2) * / (a / 14)) with (Rabs (a - 2) / (a / 14))
      by (unfold Rdiv; reflexivity).
    exact HN. }
  assert (Hbound : Rabs (a - 2) < INR N' * (a / 14)).
  { apply Rlt_le_trans with (INR N * (a / 14)); [ exact H1 | ].
    unfold N'; rewrite S_INR. pose proof (pos_INR N). nra. }
  pose proof (march_to_h a Ha Ha2 y Hbase N' HN'pos Hbound N' (le_n N')) as Hend.
  apply Hend.
  replace (2 + INR N' / INR N' * (a - 2)) with a by (field; exact HN'r).
  replace (mkC a y) with w by (apply Ceq; unfold a, y; cbn [Re Im]; reflexivity).
  replace (Cminus w w) with C0 by ring.
  rewrite (proj2 (Cmod0 C0) eq_refl). lra.
Qed.

End MarchH.

Print Assumptions region_reach.
