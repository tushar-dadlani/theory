(* ================================================================= *)
(*  CClampCont.v  (identity-theorem plan, FE chain brick 2 — clamp)    *)
(*                                                                    *)
(*  The radial clamp clampw is 2-Lipschitz:                            *)
(*     |clampw w1 - clampw w2| <= 2 |w1 - w2|,                          *)
(*  hence continuous.  Four branch cases (both inside / mixed / both    *)
(*  outside); the outside pieces use                                   *)
(*     w1/|w1| - w2/|w2| = w1(1/|w1| - 1/|w2|) + (w1 - w2)/|w2|         *)
(*  and rho <= |w| for outside points.  Combined with                  *)
(*  CFEChainCont.PhiN_ptcont this gives PhiN global continuity.        *)
(*                                                                    *)
(*  Axioms: standard classical-Reals only.                            *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import ComplexField Cmodulus CWindingOffCenter CCauchyAnalytic.
Open Scope R_scope.

(* complex scalar reassociations (componentwise; ring rejects RtoC atoms) *)
Lemma cscale_sub : forall (r : R) (w : C),
  Cminus w (Cmul (RtoC r) w) = Cmul (RtoC (1 - r)) w.
Proof. intros; apply Ceq; simpl; ring. Qed.

Lemma cscale_diff2 : forall (r1 r2 : R) (w1 w2 : C),
  Cminus (Cmul (RtoC r1) w1) (Cmul (RtoC r2) w2)
  = Cadd (Cmul (RtoC (r1 - r2)) w1) (Cmul (RtoC r2) (Cminus w1 w2)).
Proof. intros; apply Ceq; simpl; ring. Qed.

(* the outside-outside term-1 identity, as pure real algebra *)
Lemma clamp_term1_eq : forall rho a b : R, 0 < a -> 0 < b -> 0 <= rho ->
  Rabs (rho / a - rho / b) * a = rho / b * Rabs (a - b).
Proof.
  intros rho a b Ha Hb Hr.
  replace (rho / a - rho / b) with (- (rho / (a * b)) * (a - b)) by (field; lra).
  rewrite Rabs_mult, Rabs_Ropp, (Rabs_pos_eq (rho / (a * b)))
    by (apply Rle_mult_inv_pos; [ lra | apply Rmult_lt_0_compat; lra ]).
  rewrite Rmult_assoc, (Rmult_comm (Rabs (a - b)) a), <- Rmult_assoc.
  replace (rho / (a * b) * a) with (rho / b) by (field; lra).
  reflexivity.
Qed.

(* | |w1| - |w2| | <= |w1 - w2| *)
Lemma abs_Cmod_diff : forall w1 w2, Rabs (Cmod w1 - Cmod w2) <= Cmod (Cminus w1 w2).
Proof.
  intros w1 w2. apply Rabs_le. split.
  - assert (Cmod w2 - Cmod w1 <= Cmod (Cminus w2 w1)) by apply Cmod_rev_triangle.
    replace (Cmod (Cminus w2 w1)) with (Cmod (Cminus w1 w2)) in H
      by (rewrite <- Cmod_opp; f_equal; ring). lra.
  - pose proof (Cmod_rev_triangle w1 w2). lra.
Qed.

Lemma clampw_lipschitz : forall Rr w0 w1 w2, 0 < Rr ->
  Cmod (Cminus (clampw Rr w0 w1) (clampw Rr w0 w2)) <= 2 * Cmod (Cminus w1 w2).
Proof.
  intros Rr w0 w1 w2 HR.
  assert (Hrh : 0 < rho Rr w0)
    by (unfold rho; pose proof (Cmod_nonneg w0); lra).
  pose proof (Cmod_nonneg (Cminus w1 w2)) as Hd0.
  unfold clampw.
  destruct (Rle_dec (Cmod w1) (rho Rr w0)) as [H1 | H1];
  destruct (Rle_dec (Cmod w2) (rho Rr w0)) as [H2 | H2].
  - (* both inside *) lra.
  - (* w1 in, w2 out *)
    apply Rnot_le_lt in H2. assert (Hw2 : 0 < Cmod w2) by lra.
    assert (Hr2 : rho Rr w0 / Cmod w2 <= 1).
    { apply (Rmult_le_reg_r (Cmod w2)); [ exact Hw2 | ].
      unfold Rdiv; rewrite Rmult_assoc; rewrite Rinv_l by lra; lra. }
    replace (Cminus w1 (Cmul (RtoC (rho Rr w0 / Cmod w2)) w2))
      with (Cadd (Cminus w1 w2) (Cminus w2 (Cmul (RtoC (rho Rr w0 / Cmod w2)) w2)))
      by ring.
    eapply Rle_trans; [ apply Cmod_triangle | ].
    rewrite cscale_sub, Cmod_mul, Cmod_RtoC.
    rewrite (Rabs_right (1 - rho Rr w0 / Cmod w2)) by lra.
    (* Cmod(w1-w2) + (1 - rho/|w2|)|w2| <= 2 Cmod(w1-w2) *)
    assert (Hpd : (1 - rho Rr w0 / Cmod w2) * Cmod w2 = Cmod w2 - rho Rr w0)
      by (field; lra).
    rewrite Hpd.
    assert (Hle : Cmod w2 - rho Rr w0 <= Cmod (Cminus w1 w2)).
    { apply Rle_trans with (Rabs (Cmod w2 - Cmod w1)).
      - pose proof (Rle_abs (Cmod w2 - Cmod w1)); lra.
      - replace (Cmod w2 - Cmod w1) with (- (Cmod w1 - Cmod w2)) by ring.
        rewrite Rabs_Ropp. apply abs_Cmod_diff. }
    lra.
  - (* w1 out, w2 in *)
    apply Rnot_le_lt in H1. assert (Hw1 : 0 < Cmod w1) by lra.
    assert (Hr1 : rho Rr w0 / Cmod w1 <= 1).
    { apply (Rmult_le_reg_r (Cmod w1)); [ exact Hw1 | ].
      unfold Rdiv; rewrite Rmult_assoc; rewrite Rinv_l by lra; lra. }
    replace (Cminus (Cmul (RtoC (rho Rr w0 / Cmod w1)) w1) w2)
      with (Copp (Cadd (Cminus w2 w1) (Cminus w1 (Cmul (RtoC (rho Rr w0 / Cmod w1)) w1))))
      by ring.
    rewrite Cmod_opp.
    eapply Rle_trans; [ apply Cmod_triangle | ].
    rewrite cscale_sub, Cmod_mul, Cmod_RtoC.
    rewrite (Rabs_right (1 - rho Rr w0 / Cmod w1)) by lra.
    assert (Hpd : (1 - rho Rr w0 / Cmod w1) * Cmod w1 = Cmod w1 - rho Rr w0)
      by (field; lra).
    rewrite Hpd.
    assert (Hle : Cmod w1 - rho Rr w0 <= Cmod (Cminus w2 w1)).
    { apply Rle_trans with (Rabs (Cmod w1 - Cmod w2)).
      - pose proof (Rle_abs (Cmod w1 - Cmod w2)); lra.
      - eapply Rle_trans; [ apply abs_Cmod_diff | ].
        apply Req_le; rewrite <- Cmod_opp; f_equal; ring. }
    assert (Hsym : Cmod (Cminus w2 w1) = Cmod (Cminus w1 w2))
      by (rewrite <- Cmod_opp; f_equal; ring).
    lra.
  - (* both out *)
    apply Rnot_le_lt in H1. apply Rnot_le_lt in H2.
    assert (Hw1 : 0 < Cmod w1) by lra. assert (Hw2 : 0 < Cmod w2) by lra.
    rewrite cscale_diff2.
    eapply Rle_trans; [ apply Cmod_triangle | ].
    rewrite Cmod_mul, Cmod_RtoC, Cmod_mul, Cmod_RtoC.
    rewrite (Rabs_right (rho Rr w0 / Cmod w2)) by
      (apply Rle_ge; apply Rle_mult_inv_pos; lra).
    (* term2 = (rho/|w2|) |w1-w2| <= |w1-w2| *)
    assert (Hterm2 : rho Rr w0 / Cmod w2 * Cmod (Cminus w1 w2) <= Cmod (Cminus w1 w2)).
    { rewrite <- (Rmult_1_l (Cmod (Cminus w1 w2))) at 2.
      apply Rmult_le_compat_r; [ exact Hd0 | ].
      apply (Rmult_le_reg_r (Cmod w2)); [ exact Hw2 | ].
      unfold Rdiv; rewrite Rmult_assoc, Rinv_l by lra; lra. }
    (* term1 = |rho/|w1| - rho/|w2|| |w1| <= |w1-w2| *)
    assert (Hterm1 : Rabs (rho Rr w0 / Cmod w1 - rho Rr w0 / Cmod w2) * Cmod w1
                     <= Cmod (Cminus w1 w2)).
    { rewrite (clamp_term1_eq (rho Rr w0) (Cmod w1) (Cmod w2) Hw1 Hw2 (Rlt_le _ _ Hrh)).
      apply Rle_trans with (1 * Cmod (Cminus w1 w2)); [ | lra ].
      apply Rmult_le_compat.
      - apply Rle_mult_inv_pos; lra.
      - apply Rabs_pos.
      - apply (Rmult_le_reg_r (Cmod w2)); [ exact Hw2 | ].
        unfold Rdiv; rewrite Rmult_assoc; rewrite Rinv_l by lra; lra.
      - apply abs_Cmod_diff. }
    lra.
Qed.

(* pointwise continuity, in exactly the shape PhiN_ptcont's hypothesis wants *)
Lemma clampw_ptcont : forall Rr w0, 0 < Rr ->
  forall w2 e, 0 < e -> exists del, 0 < del /\
    forall w, Cmod (Cminus w w2) < del ->
      Cmod (Cminus (clampw Rr w0 w) (clampw Rr w0 w2)) < e.
Proof.
  intros Rr w0 HR w2 e He.
  exists (e / 2); split; [ lra | ].
  intros w Hw.
  eapply Rle_lt_trans; [ apply (clampw_lipschitz Rr w0 w w2 HR) | ].
  lra.
Qed.

Print Assumptions clampw_lipschitz.
Print Assumptions clampw_ptcont.
