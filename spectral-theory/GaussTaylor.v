(* ================================================================= *)
(*  GaussTaylor.v  —  Leibniz-gap Phase 2 (analytic core): the         *)
(*  Taylor remainder bound for cos, the key that avoids Heine.        *)
(*                                                                    *)
(*  The bounded parameter-Leibniz for ∫_{−A}^A e^{−πx²}cos(2πxξ) needs  *)
(*  the pointwise difference-quotient error to carry a factor t² (so   *)
(*  a t² factors out of the integral, leaving O(|t|) → 0).  That is    *)
(*  exactly the second-order Taylor remainder of cos:                 *)
(*                                                                    *)
(*    cos_taylor_bound : |cos(a+h) − cos a + h·sin a| ≤ h²,            *)
(*                                                                    *)
(*  proved from the mean value theorem (MVT_cor1) plus the 1-Lipschitz *)
(*  bound of sin (|sin u − sin v| ≤ |u − v|, itself MVT + |cos| ≤ 1).  *)
(*  No general 2-D uniform-continuity (Heine) is needed — the explicit *)
(*  quadratic bound suffices.  No new axioms (classical Reals only).   *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  sin is 1-Lipschitz.                                              *)
(* ----------------------------------------------------------------- *)

Lemma sin_lipschitz : forall u v, Rabs (sin u - sin v) <= Rabs (u - v).
Proof.
  intros u v.
  pose (pr := fun x => exist (fun l => derivable_pt_lim sin x l) (cos x)
                         (derivable_pt_lim_sin x) : derivable_pt sin x).
  destruct (Rtotal_order v u) as [Hlt | [Heq | Hgt]].
  - destruct (MVT_cor1 sin v u pr Hlt) as [c [Hc _]].
    assert (Hd : derive_pt sin c (pr c) = cos c) by reflexivity.
    rewrite Hd in Hc; rewrite Hc, Rabs_mult.
    apply Rle_trans with (1 * Rabs (u - v)); [ | rewrite Rmult_1_l; apply Rle_refl ].
    apply Rmult_le_compat_r; [ apply Rabs_pos | ].
    unfold Rabs; destruct (Rcase_abs (cos c)); pose proof (COS_bound c) as [? ?]; lra.
  - rewrite Heq; replace (sin u - sin u) with 0 by ring; replace (u - u) with 0 by ring;
      rewrite Rabs_R0; apply Rle_refl.
  - destruct (MVT_cor1 sin u v pr Hgt) as [c [Hc _]].
    assert (Hd : derive_pt sin c (pr c) = cos c) by reflexivity.
    rewrite Hd in Hc.
    rewrite (Rabs_minus_sym (sin u) (sin v)), (Rabs_minus_sym u v), Hc, Rabs_mult.
    apply Rle_trans with (1 * Rabs (v - u)); [ | rewrite Rmult_1_l; apply Rle_refl ].
    apply Rmult_le_compat_r; [ apply Rabs_pos | ].
    unfold Rabs; destruct (Rcase_abs (cos c)); pose proof (COS_bound c) as [? ?]; lra.
Qed.

(* ----------------------------------------------------------------- *)
(*  Second-order Taylor remainder of cos.                            *)
(* ----------------------------------------------------------------- *)

Lemma deriv_lin : forall (b : R) x, derivable_pt_lim (fun z => z * b) x b.
Proof.
  intros b x.
  pose proof (derivable_pt_lim_mult (fun z => z) (fct_cte b) x 1 0
                (derivable_pt_lim_id x) (derivable_pt_lim_const b x)) as Hm.
  cbv beta in Hm.
  match type of Hm with derivable_pt_lim _ _ ?V => replace V with b in Hm by (unfold fct_cte; ring) end.
  exact Hm.
Qed.

Lemma cos_taylor_bound : forall a h, Rabs (cos (a + h) - cos a + h * sin a) <= h ^ 2.
Proof.
  intros a h.
  pose (r := fun s => cos (a + s) - cos a + s * sin a).
  assert (Hr' : forall s, derivable_pt_lim r s (- sin (a + s) + sin a)).
  { intro s; unfold r.
    apply (derivable_pt_lim_plus (fun z => cos (a + z) - cos a) (fun z => z * sin a)
             s (- sin (a + s)) (sin a)).
    - replace (- sin (a + s)) with (- sin (a + s) - 0) by ring.
      apply derivable_pt_lim_minus; [ | apply derivable_pt_lim_const ].
      replace (- sin (a + s)) with (- sin (a + s) * 1) by ring.
      apply (derivable_pt_lim_comp (fun z => a + z) cos s 1 (- sin (a + s))).
      + replace 1 with (0 + 1) by ring; apply derivable_pt_lim_plus;
          [ apply derivable_pt_lim_const | apply derivable_pt_lim_id ].
      + apply derivable_pt_lim_cos.
    - exact (deriv_lin (sin a) s). }
  pose (pr := fun s => exist (fun l => derivable_pt_lim r s l) (- sin (a + s) + sin a)
                         (Hr' s) : derivable_pt r s).
  assert (Hr0 : r 0 = 0) by (unfold r; replace (a + 0) with a by ring; ring).
  assert (Hhh : Rabs h * Rabs h = h ^ 2) by (rewrite <- Rabs_mult, Rabs_pos_eq by nra; ring).
  change (Rabs (r h) <= h ^ 2).
  destruct (Rtotal_order h 0) as [Hlt | [Heq | Hgt]].
  - destruct (MVT_cor1 r h 0 pr Hlt) as [c [Hc [Hc1 Hc2]]].
    assert (Hd : derive_pt r c (pr c) = - sin (a + c) + sin a) by reflexivity.
    rewrite Hd, Hr0 in Hc.
    assert (Hrh : r h = (sin a - sin (a + c)) * h) by nra.
    rewrite Hrh, Rabs_mult, <- Hhh.
    apply Rmult_le_compat_r; [ apply Rabs_pos | ].
    apply Rle_trans with (Rabs (a - (a + c))); [ apply sin_lipschitz | ].
    replace (a - (a + c)) with (- c) by ring; rewrite Rabs_Ropp.
    unfold Rabs; destruct (Rcase_abs c); destruct (Rcase_abs h); lra.
  - subst h; rewrite Hr0, Rabs_R0; simpl; lra.
  - destruct (MVT_cor1 r 0 h pr Hgt) as [c [Hc [Hc1 Hc2]]].
    assert (Hd : derive_pt r c (pr c) = - sin (a + c) + sin a) by reflexivity.
    rewrite Hd, Hr0 in Hc.
    assert (Hrh : r h = (sin a - sin (a + c)) * h) by nra.
    rewrite Hrh, Rabs_mult, <- Hhh.
    apply Rmult_le_compat_r; [ apply Rabs_pos | ].
    apply Rle_trans with (Rabs (a - (a + c))); [ apply sin_lipschitz | ].
    replace (a - (a + c)) with (- c) by ring; rewrite Rabs_Ropp.
    unfold Rabs; destruct (Rcase_abs c); destruct (Rcase_abs h); lra.
Qed.

Print Assumptions sin_lipschitz.
Print Assumptions cos_taylor_bound.

(* ================================================================= *)
(*  END GaussTaylor.v (Phase 2 analytic core)                       *)
(*  |cos(a+h) − cos a + h sin a| ≤ h².  This is the pointwise engine    *)
(*  of the bounded parameter-Leibniz: with a = 2πxξ, h = 2πxt it gives  *)
(*  |diff-quotient error(x)| ≤ e^{−πx²}(2πx)²·t², whose integral is      *)
(*  O(|t|) → 0 — no Heine required.  Next: assemble leibniz_bounded.    *)
(* ================================================================= *)
