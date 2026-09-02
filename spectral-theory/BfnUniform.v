(* ================================================================= *)
(*  BfnUniform.v  --  the UNIFORM delta on a compact piece of the      *)
(*  line Re s = 1.                                                     *)
(*                                                                    *)
(*      exists del > 0, forall s,                                      *)
(*        |Re s - 1| < del -> |Im s| <= Rb -> BfnT s <> C0             *)
(*                                                                    *)
(*  Newman's contour enters Re z < 0, so g must be holomorphic on an   *)
(*  OPEN neighbourhood of the compact segment {Re z = 0, |z| <= R}.    *)
(*  NewmanGExt gives non-vanishing pointwise ON the line; this file    *)
(*  turns that into one delta valid along the whole segment.           *)
(*                                                                    *)
(*  Method: exactly CUnifCont's -- a "good box radius" at each height  *)
(*  t, defined as the lub of the set of radii that work, then the      *)
(*  discs of half that radius form an open cover of the compact        *)
(*  [-Rb, Rb], and compact_P3 extracts a finite subcover whose minimum *)
(*  half-radius is the uniform delta.  (CUnifCont does the same for    *)
(*  Fp o arc over [0, 2*PI]; its trailer calls that 2D uniform          *)
(*  continuity.)                                                                                                            *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia Rtopology List Classical.
Require Import ComplexField Cmodulus Holomorphic CDeriv CHoloCalculus
        CContBounded CZeta ZetaFn CZetaRegular CZetaRegular2 CZetaRegular6
        ZetaPoleCancel ZetaPoleCancel2 NewmanGExt.
Open Scope R_scope.

Section Uniform.

Variable Rb : R.
Hypothesis HRb : 0 < Rb.

(* radii z that certify non-vanishing on the box of half-width z at height t *)
Definition Nbox (t z : R) : Prop :=
  (0 < z <= 1) /\
  (forall s : C, Rabs (Im s - t) < z -> Rabs (Re s - 1) < z -> BfnT s <> C0).

Lemma Nbox_bound : forall t, bound (Nbox t).
Proof. intro t; exists 1; intros z Hz; apply (proj2 (proj1 Hz)). Qed.

Lemma Nbox_ne : forall t, exists z, Nbox t z.
Proof.
  intro t.
  assert (Hre : (0 : R) < Re (mkC 1 t)) by (cbn; lra).
  assert (Hne : BfnT (mkC 1 t) <> C0)
    by (apply BfnT_ne0_re_ge1; cbn; lra).
  destruct (BfnT_holo (mkC 1 t) Hre) as [d Hd].
  destruct (Cderiv_nonzero_nbhd BfnT (mkC 1 t) d Hd Hne) as [del [Hdel Hnb]].
  exists (Rmin (del / 2) 1). split.
  - split; [ apply Rmin_pos; lra | apply Rmin_r ].
  - intros s Him Hre'.
    pose proof (Rmin_l (del / 2) 1) as Hm1.
    replace s with (Cadd (mkC 1 t) (Cminus s (mkC 1 t)))
      by (apply Ceq; cbn; ring).
    apply Hnb.
    eapply Rle_lt_trans; [ apply Cmod_le_ReIm | ].
    cbn [Re Im Cminus]. lra.
Qed.

Definition deln (t : R) : R :=
  proj1_sig (completeness (Nbox t) (Nbox_bound t) (Nbox_ne t)).
Lemma deln_lub : forall t, is_lub (Nbox t) (deln t).
Proof.
  intro t; exact (proj2_sig (completeness (Nbox t) (Nbox_bound t) (Nbox_ne t))).
Qed.
Lemma deln_pos : forall t, 0 < deln t.
Proof.
  intro t; destruct (Nbox_ne t) as [z Hz].
  apply Rlt_le_trans with z;
    [ apply (proj1 (proj1 Hz)) | apply (proj1 (deln_lub t)); exact Hz ].
Qed.
Lemma halfdeln_pos : forall t, 0 < deln t / 2.
Proof. intro t; pose proof (deln_pos t); lra. Qed.
Definition posdeln (t : R) : posreal := mkposreal (deln t / 2) (halfdeln_pos t).

Lemma Nbox_down : forall t z z', Nbox t z -> 0 < z' -> z' <= z -> Nbox t z'.
Proof.
  intros t z z' [[Hz1 Hz2] Hbox] Hz'1 Hz'2;
    split; [ split; [ exact Hz'1 | lra ] | ].
  intros s Him Hre; apply Hbox; lra.
Qed.

Lemma Nbox_half : forall t, Nbox t (deln t / 2).
Proof.
  intro t; destruct (deln_lub t) as [Hub Hlub].
  destruct (classic (exists z, Nbox t z /\ deln t / 2 < z)) as [ [z [Hz Hzlt]] | Hno ].
  - apply (Nbox_down t z (deln t / 2) Hz (halfdeln_pos t)); lra.
  - exfalso; assert (Hub2 : is_upper_bound (Nbox t) (deln t / 2)).
    { intros x Hx; destruct (Rle_dec x (deln t / 2)) as [Hle | Hgt];
        [ exact Hle | exfalso; apply Hno; exists x; split; [ exact Hx | lra ] ]. }
    pose proof (Hlub _ Hub2); pose proof (deln_pos t); lra.
Qed.

(* the open cover of [-Rb, Rb] by discs of radius deln/2 *)
Definition nfam (ts t : R) : Prop := (- Rb <= ts <= Rb) /\ disc ts (posdeln ts) t.
Lemma nfam_cond : forall ts, (exists t, nfam ts t) -> (- Rb <= ts <= Rb).
Proof. intros ts [t [Hts _]]; exact Hts. Qed.
Definition nffam : family := mkfamily (fun ts => - Rb <= ts <= Rb) nfam nfam_cond.

Lemma nffam_cover_open : covering_open_set (fun t => - Rb <= t <= Rb) nffam.
Proof.
  split.
  - intros th Hth; exists th; split; [ exact Hth | ].
    unfold disc; replace (th - th) with 0 by ring; rewrite Rabs_R0;
      apply (cond_pos (posdeln th)).
  - intro ts; simpl; destruct (classic (- Rb <= ts <= Rb)) as [Hin | Hout].
    + apply open_set_P6 with (disc ts (posdeln ts)); [ apply disc_P1 | ].
      unfold eq_Dom, included, nfam; split; intros t Ht;
        [ split; [ exact Hin | exact Ht ] | exact (proj2 Ht) ].
    + apply open_set_P6 with (fun _ : R => False); [ apply open_set_P4 | ].
      unfold eq_Dom, included, nfam; split; intros t Ht;
        [ contradiction | exact (Hout (proj1 Ht)) ].
Qed.

Theorem BfnT_ne0_unif : exists del, 0 < del /\
  forall s : C, Rabs (Re s - 1) < del -> Rabs (Im s) <= Rb -> BfnT s <> C0.
Proof.
  destruct (compact_P3 (- Rb) Rb nffam nffam_cover_open) as [D [Hcov Hfin]].
  unfold family_finite, domain_finite in Hfin; destruct Hfin as [l Hl].
  set (del := fold_right (fun ts a => Rmin (deln ts / 2) a) 1 l).
  assert (Hdpos : 0 < del).
  { unfold del; clear; induction l as [ | ts l' IH ]; simpl;
      [ lra | apply Rmin_pos; [ apply halfdeln_pos | exact IH ] ]. }
  assert (Hdle : forall ts, In ts l -> del <= deln ts / 2).
  { unfold del; intros ts Hts; clear -Hts;
    induction l as [ | t0 l' IH ]; simpl in *;
      [ contradiction
      | destruct Hts as [ -> | Hin ];
        [ apply Rmin_l | eapply Rle_trans; [ apply Rmin_r | apply IH; exact Hin ] ] ]. }
  exists del; split; [ exact Hdpos | ].
  intros s Hre Him.
  assert (Ht : - Rb <= Im s <= Rb).
  { unfold Rabs in Him; destruct (Rcase_abs (Im s)); lra. }
  destruct (Hcov (Im s) Ht) as [ts Hts]; simpl in Hts.
  destruct Hts as [[Hts_in Hts_disc] Hts_D].
  assert (Hin_l : In ts l)
    by (apply (proj1 (Hl ts)); split; [ exact Hts_in | exact Hts_D ]).
  assert (Hdts := Hdle ts Hin_l).
  destruct (Nbox_half ts) as [_ Hbox].
  apply Hbox.
  - unfold disc in Hts_disc; simpl in Hts_disc; exact Hts_disc.
  - eapply Rlt_le_trans; [ exact Hre | exact Hdts ].
Qed.

End Uniform.

(* ================================================================= *)
(*  What Newman's contour actually consumes: gext is holomorphic on a  *)
(*  full OPEN neighbourhood of the compact segment {Re z = 0,          *)
(*  |Im z| <= Rb} -- so the contour may be pushed to Re z = -del.      *)
(* ================================================================= *)

Theorem gext_holo_strip : forall Rb, 0 < Rb ->
  exists del, 0 < del /\
    forall z : C, Rabs (Re z) < del -> Rabs (Im z) <= Rb ->
      exists d, is_Cderiv gext z d.
Proof.
  intros Rb HRb.
  destruct (BfnT_ne0_unif Rb HRb) as [del [Hdel Hne]].
  exists (Rmin del 1). split; [ apply Rmin_glb_lt; lra | ].
  intros z Hre Him.
  pose proof (Rmin_l del 1) as Hm1. pose proof (Rmin_r del 1) as Hm2.
  assert (HreZ : Rabs (Re z) < 1) by lra.
  assert (Hpos : 0 < Re (Cadd z C1)).
  { cbn. unfold Rabs in HreZ; destruct (Rcase_abs (Re z)); lra. }
  apply gext_holo; [ exact Hpos | ].
  apply Hne.
  - cbn. replace (Re z + 1 - 1) with (Re z) by ring. lra.
  - cbn. replace (Im z + 0) with (Im z) by ring. exact Him.
Qed.

Print Assumptions BfnT_ne0_unif.
Print Assumptions gext_holo_strip.
