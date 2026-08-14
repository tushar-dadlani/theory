(* ================================================================= *)
(*  CWalk.v  (identity-theorem plan, FE chain brick 5 — the walk)       *)
(*                                                                    *)
(*  Propagate the zero-set of F (holomorphic on {Re>0}, continuous,     *)
(*  vanishing on the positive ray) across the whole half-plane by a      *)
(*  finite vertical walk: from the seed disk at a real point            *)
(*  (real_disk_zero) step upward, each step spreading the zero-disk via  *)
(*  scaled_disk_zero.  Conclusion: F w = 0 for every Re w > 0.          *)
(*                                                                    *)
(*  Axioms: standard classical-Reals only.                            *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import ComplexField Cmodulus Holomorphic CIdentityProp
        CScaledDisk CRealDisk.
Open Scope R_scope.

Section Walk.
Variable F : C -> C.
Hypothesis HFptc : forall z, 0 < Re z -> forall e, 0 < e -> exists del, 0 < del /\
  forall z', Cmod (Cminus z' z) < del -> Cmod (Cminus (F z') (F z)) < e.
Hypothesis HFhol : forall z, 0 < Re z -> exists d, is_Cderiv F z d.

(* one vertical step: spread the zero-disk from (a,y0) to a nearby (a,y1) *)
Lemma walk_step : forall a, 0 < a -> forall y0 y1,
  (forall z, Cmod (Cminus z (mkC a y0)) < a / 7 -> F z = C0) ->
  Rabs (y1 - y0) < a / 14 ->
  forall z, Cmod (Cminus z (mkC a y1)) < a / 7 -> F z = C0.
Proof.
  intros a Ha y0 y1 H0 Hstep z Hz.
  apply (scaled_disk_zero F HFptc HFhol (mkC a y1) (a / 7) (a / 14)).
  - lra.
  - cbn [Re]; lra.
  - lra.
  - intros z' Hz'. apply H0.
    assert (Hgeo : Cmod (Cminus (mkC a y1) (mkC a y0)) = Rabs (y1 - y0)).
    { replace (Cminus (mkC a y1) (mkC a y0)) with (mkC 0 (y1 - y0))
        by (apply Ceq; unfold Cminus, Cadd, Copp; cbn [Re Im]; ring).
      unfold Cmod, Cnorm2; cbn [Re Im].
      replace (0 * 0 + (y1 - y0) * (y1 - y0)) with (Rsqr (y1 - y0))
        by (unfold Rsqr; ring).
      rewrite sqrt_Rsqr_abs; reflexivity. }
    assert (Htri : Cmod (Cminus z' (mkC a y0))
                   <= Cmod (Cminus z' (mkC a y1)) + Cmod (Cminus (mkC a y1) (mkC a y0))).
    { replace (Cminus z' (mkC a y0))
        with (Cadd (Cminus z' (mkC a y1)) (Cminus (mkC a y1) (mkC a y0))) by ring.
      apply Cmod_triangle. }
    rewrite Hgeo in Htri. lra.
  - exact Hz.
Qed.

(* the walk to the i-th interpolation point of the segment [0, ytarget] *)
Lemma walk_to : forall a, 0 < a ->
  (forall z, Cmod (Cminus z (mkC a 0)) < a / 7 -> F z = C0) ->
  forall (N : nat), (0 < N)%nat -> forall ytarget, Rabs ytarget < INR N * (a / 14) ->
    forall i, (i <= N)%nat ->
      forall z, Cmod (Cminus z (mkC a (INR i / INR N * ytarget))) < a / 7 -> F z = C0.
Proof.
  intros a Ha Hbase N HN ytarget Hyt.
  assert (HNr : 0 < INR N) by (apply lt_0_INR; lia).
  induction i as [| i IHi]; intros Hi z Hz.
  - assert (Hy0 : INR 0 / INR N * ytarget = 0) by (simpl; unfold Rdiv; ring).
    rewrite Hy0 in Hz. apply Hbase; exact Hz.
  - assert (Hile : (i <= N)%nat) by lia.
    apply (walk_step a Ha (INR i / INR N * ytarget) (INR (S i) / INR N * ytarget)
             (IHi Hile)); [ | exact Hz ].
    replace (INR (S i) / INR N * ytarget - INR i / INR N * ytarget)
      with (ytarget * / INR N) by (rewrite S_INR; field; lra).
    rewrite Rabs_mult, (Rabs_right (/ INR N))
      by (apply Rle_ge; left; apply Rinv_0_lt_compat; exact HNr).
    apply (Rmult_lt_reg_r (INR N)); [ exact HNr | ].
    replace (Rabs ytarget * / INR N * INR N) with (Rabs ytarget) by (field; lra).
    lra.
Qed.

Theorem reach : (forall s, 0 < s -> F (mkC s 0) = C0) ->
  forall w, 0 < Re w -> F w = C0.
Proof.
  intros Hray w Hw.
  set (a := Re w).
  assert (Ha : 0 < a) by (unfold a; exact Hw).
  assert (Hbase : forall z, Cmod (Cminus z (mkC a 0)) < a / 7 -> F z = C0).
  { apply (real_disk_zero F HFptc HFhol a Ha).
    intros s Hs. apply Hray.
    destruct (Rabs_def2 (s - a) (a / 2) Hs) as [Hlt Hgt]. lra. }
  assert (Hnn : 0 <= Rabs (Im w) / (a / 14))
    by (apply Rle_mult_inv_pos; [ apply Rabs_pos | lra ]).
  destruct (exists_nat_gt _ Hnn) as [N HN].
  set (N' := S N).
  assert (HN'pos : (0 < N')%nat) by lia.
  assert (HN'r : INR N' <> 0) by (apply Rgt_not_eq, lt_0_INR; lia).
  assert (H1 : Rabs (Im w) < INR N * (a / 14)).
  { apply (Rmult_lt_reg_r (/ (a / 14))); [ apply Rinv_0_lt_compat; lra | ].
    replace (INR N * (a / 14) * / (a / 14)) with (INR N) by (field; lra).
    replace (Rabs (Im w) * / (a / 14)) with (Rabs (Im w) / (a / 14))
      by (unfold Rdiv; reflexivity).
    exact HN. }
  assert (Hbound : Rabs (Im w) < INR N' * (a / 14)).
  { apply Rlt_le_trans with (INR N * (a / 14)); [ exact H1 | ].
    unfold N'; rewrite S_INR. pose proof (pos_INR N). nra. }
  pose proof (walk_to a Ha Hbase N' HN'pos (Im w) Hbound N' (le_n N')) as Hend.
  apply Hend.
  replace (INR N' / INR N' * Im w) with (Im w) by (field; exact HN'r).
  replace (mkC a (Im w)) with w by (apply Ceq; unfold a; cbn [Re Im]; reflexivity).
  replace (Cminus w w) with C0 by ring.
  rewrite (proj2 (Cmod0 C0) eq_refl). lra.
Qed.

End Walk.

Print Assumptions reach.
