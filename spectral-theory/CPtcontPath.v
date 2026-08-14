(* ================================================================= *)
(*  CPtcontPath.v  (identity-theorem plan, FE chain brick 5 — cont)     *)
(*                                                                    *)
(*  Pointwise continuity along a path => Ccont of the composition:      *)
(*  if F : C -> C is (Cmod eps-delta) continuous at every point gam u   *)
(*  of a continuous path gam, then u |-> F (gam u) is Ccont.  This is    *)
(*  what lets us build CcontC of a clamped scaled function whose         *)
(*  argument stays in {Re>0} from the pointwise continuity of a          *)
(*  MEROMORPHIC F (e.g. FE_diff), sidestepping the false global CcontC.  *)
(*                                                                    *)
(*  Axioms: standard classical-Reals only.                            *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra.
Require Import ComplexField Cmodulus CIntegral2 CContBounded.
Open Scope R_scope.

Lemma Rabs_Re_le_Cmod : forall c, Rabs (Re c) <= Cmod c.
Proof.
  intro c. unfold Cmod, Cnorm2.
  rewrite <- (sqrt_Rsqr_abs (Re c)).
  apply sqrt_le_1_alt. unfold Rsqr.
  pose proof (Rle_0_sqr (Im c)) as H. unfold Rsqr in H. nra.
Qed.

Lemma Rabs_Im_le_Cmod : forall c, Rabs (Im c) <= Cmod c.
Proof.
  intro c. unfold Cmod, Cnorm2.
  rewrite <- (sqrt_Rsqr_abs (Im c)).
  apply sqrt_le_1_alt. unfold Rsqr.
  pose proof (Rle_0_sqr (Re c)) as H. unfold Rsqr in H. nra.
Qed.

(* continuity_pt <-> eps-delta *)
Lemma contpt_epsdel : forall (f : R -> R) x, continuity_pt f x ->
  forall eps, 0 < eps -> exists del, 0 < del /\
    forall y, Rabs (y - x) < del -> Rabs (f y - f x) < eps.
Proof.
  intros f x H eps Heps.
  unfold continuity_pt, continue_in, limit1_in, limit_in in H. simpl in H.
  destruct (H eps Heps) as [alp [Halp Hb]].
  exists (alp / 2). split; [ lra | ]. intros y Hy.
  destruct (Req_dec y x) as [Hyx | Hyx].
  - subst y. replace (f x - f x) with 0 by ring. rewrite Rabs_R0. exact Heps.
  - apply Hb. split.
    + unfold D_x, no_cond. split; [ exact I | exact (not_eq_sym Hyx) ].
    + unfold Rdist. lra.
Qed.

Lemma epsdel_contpt : forall (f : R -> R) x,
  (forall eps, 0 < eps -> exists del, 0 < del /\
     forall y, Rabs (y - x) < del -> Rabs (f y - f x) < eps) ->
  continuity_pt f x.
Proof.
  intros f x H.
  unfold continuity_pt, continue_in, limit1_in, limit_in. simpl.
  intros eps Heps. destruct (H eps Heps) as [del [Hdel Hb]].
  exists del. split; [ exact Hdel | ]. intros x0 [_ Hdist].
  unfold Rdist in *. apply Hb. exact Hdist.
Qed.

Lemma Ccont_Cmod_cont : forall (h : R -> C) x, Ccont h ->
  forall del, 0 < del -> exists alp, 0 < alp /\
    forall y, Rabs (y - x) < alp -> Cmod (Cminus (h y) (h x)) < del.
Proof.
  intros h x [HRe HIm] del Hdel.
  destruct (contpt_epsdel (fun u => Re (h u)) x (HRe x) (del / 2) ltac:(lra))
    as [a1 [Ha1 Hb1]].
  destruct (contpt_epsdel (fun u => Im (h u)) x (HIm x) (del / 2) ltac:(lra))
    as [a2 [Ha2 Hb2]].
  exists (Rmin a1 a2). split; [ apply Rmin_glb_lt; assumption | ].
  intros y Hy.
  eapply Rle_lt_trans; [ apply Cmod_le_ReIm | ].
  replace (Re (Cminus (h y) (h x))) with (Re (h y) - Re (h x))
    by (unfold Cminus, Copp; cbn [Re Im]; ring).
  replace (Im (Cminus (h y) (h x))) with (Im (h y) - Im (h x))
    by (unfold Cminus, Copp; cbn [Re Im]; ring).
  assert (Rabs (Re (h y) - Re (h x)) < del / 2)
    by (apply Hb1; eapply Rlt_le_trans; [ exact Hy | apply Rmin_l ]).
  assert (Rabs (Im (h y) - Im (h x)) < del / 2)
    by (apply Hb2; eapply Rlt_le_trans; [ exact Hy | apply Rmin_r ]).
  lra.
Qed.

Theorem ptcont_path : forall (F : C -> C) (gam : R -> C),
  Ccont gam ->
  (forall u eps, 0 < eps -> exists del, 0 < del /\
     forall z', Cmod (Cminus z' (gam u)) < del -> Cmod (Cminus (F z') (F (gam u))) < eps) ->
  Ccont (fun u => F (gam u)).
Proof.
  intros F gam Hgam HF. split; intro x; apply epsdel_contpt; intros eps Heps.
  - destruct (HF x eps Heps) as [delF [HdelF HbF]].
    destruct (Ccont_Cmod_cont gam x Hgam delF HdelF) as [alp [Halp Hg]].
    exists alp. split; [ exact Halp | ]. intros y Hy.
    eapply Rle_lt_trans.
    + replace (Re (F (gam y)) - Re (F (gam x)))
        with (Re (Cminus (F (gam y)) (F (gam x))))
        by (unfold Cminus, Copp; cbn [Re Im]; ring).
      apply Rabs_Re_le_Cmod.
    + apply HbF. apply Hg. exact Hy.
  - destruct (HF x eps Heps) as [delF [HdelF HbF]].
    destruct (Ccont_Cmod_cont gam x Hgam delF HdelF) as [alp [Halp Hg]].
    exists alp. split; [ exact Halp | ]. intros y Hy.
    eapply Rle_lt_trans.
    + replace (Im (F (gam y)) - Im (F (gam x)))
        with (Im (Cminus (F (gam y)) (F (gam x))))
        by (unfold Cminus, Copp; cbn [Re Im]; ring).
      apply Rabs_Im_le_Cmod.
    + apply HbF. apply Hg. exact Hy.
Qed.

Print Assumptions ptcont_path.
