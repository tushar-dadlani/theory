(* ================================================================= *)
(*  CStripBound.v  --  a pointwise-continuous function is bounded on   *)
(*  a thin strip around a compact piece of the imaginary axis:         *)
(*                                                                    *)
(*    exists del M, 0 < del /\                                         *)
(*      forall s, |Re s| < del -> |Im s| <= Rb -> Cmod (F s) <= M      *)
(*                                                                    *)
(*  Pointwise continuity alone gives a radius at each point; this      *)
(*  turns it into ONE radius along the whole segment {Re z = 0,        *)
(*  |Im z| <= Rb}, by the compactness template of CUnifCont /          *)
(*  BfnUniform: the "good box radius" at height t is the lub of the    *)
(*  radii that work (canonical, so choice-free), the discs of half     *)
(*  that radius cover the compact [-Rb, Rb], and compact_P3 extracts   *)
(*  a finite subcover whose minimum half-radius is the uniform del.    *)
(*                                                                    *)
(*  The bound itself comes from Ccont_bounded on the segment, since    *)
(*  t |-> F (mkC 0 t) is a continuous path.                            *)
(*                                                                    *)
(*  Newman's contour needs this for the CHORD, where the estimate is   *)
(*  |g| <= M and the truncation depth is only chosen afterwards -- so  *)
(*  M must not depend on it.                                          *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia Rtopology List Classical.
Require Import ComplexField Cmodulus CIntegral2 CSegInt CContBounded.
Open Scope R_scope.

Lemma Ccont_vert : forall F : C -> C, CcontC F -> Ccont (fun u => F (mkC 0 u)).
Proof.
  intros F Fcc; apply Fcc; split; intro x.
  - apply continuity_pt_const; intros a b; reflexivity.
  - change (continuity_pt (fun u : R => u) x).
    apply derivable_continuous_pt, derivable_pt_id.
Qed.

Section StripBound.

Variable F : C -> C.
Hypothesis Fptc : forall (z : C) (eps : R), 0 < eps -> exists del, 0 < del /\
  forall w, Cmod (Cminus w z) < del -> Cmod (Cminus (F w) (F z)) < eps.

Variable Rb : R.
Hypothesis HRb : 0 < Rb.

Variable M0 : R.
Hypothesis HM0 : forall u, - Rb <= u <= Rb -> Cmod (F (mkC 0 u)) <= M0.

(* radii that certify the bound M0 + 1 on the box of half-width z at height t *)
Definition Sbox (t z : R) : Prop :=
  (0 < z <= 1) /\
  (Rabs t <= Rb ->
   forall s : C, Rabs (Im s - t) < z -> Rabs (Re s) < z -> Cmod (F s) <= M0 + 1).

Lemma Sbox_bound : forall t, bound (Sbox t).
Proof. intro t; exists 1; intros z Hz; apply (proj2 (proj1 Hz)). Qed.

Lemma Sbox_ne : forall t, exists z, Sbox t z.
Proof.
  intro t.
  destruct (Fptc (mkC 0 t) 1 ltac:(lra)) as [d [Hd Hc]].
  exists (Rmin (d / 2) 1); split.
  - split; [ apply Rmin_pos; lra | apply Rmin_r ].
  - intros Ht s Him Hre.
    pose proof (Rmin_l (d / 2) 1) as Hm1.
    assert (Hs : Cmod (Cminus s (mkC 0 t)) < d).
    { eapply Rle_lt_trans; [ apply Cmod_le_ReIm | ].
      cbn [Re Im Cminus]. replace (Re s - 0) with (Re s) by ring. lra. }
    assert (Hcs := Hc s Hs).
    assert (Hbase : Cmod (F (mkC 0 t)) <= M0).
    { apply HM0; unfold Rabs in Ht; destruct (Rcase_abs t); lra. }
    replace (F s) with (Cadd (F (mkC 0 t)) (Cminus (F s) (F (mkC 0 t)))) by ring.
    eapply Rle_trans; [ apply Cmod_triangle | ]; lra.
Qed.

Definition dels (t : R) : R :=
  proj1_sig (completeness (Sbox t) (Sbox_bound t) (Sbox_ne t)).
Lemma dels_lub : forall t, is_lub (Sbox t) (dels t).
Proof.
  intro t; exact (proj2_sig (completeness (Sbox t) (Sbox_bound t) (Sbox_ne t))).
Qed.
Lemma dels_pos : forall t, 0 < dels t.
Proof.
  intro t; destruct (Sbox_ne t) as [z Hz].
  apply Rlt_le_trans with z;
    [ apply (proj1 (proj1 Hz)) | apply (proj1 (dels_lub t)); exact Hz ].
Qed.
Lemma halfdels_pos : forall t, 0 < dels t / 2.
Proof. intro t; pose proof (dels_pos t); lra. Qed.
Definition posdels (t : R) : posreal := mkposreal (dels t / 2) (halfdels_pos t).

Lemma Sbox_down : forall t z z', Sbox t z -> 0 < z' -> z' <= z -> Sbox t z'.
Proof.
  intros t z z' [[Hz1 Hz2] Hbox] Hz'1 Hz'2;
    split; [ split; [ exact Hz'1 | lra ] | ].
  intros Ht s Him Hre; apply Hbox; solve [ exact Ht | lra ].
Qed.

Lemma Sbox_half : forall t, Sbox t (dels t / 2).
Proof.
  intro t; destruct (dels_lub t) as [Hub Hlub].
  destruct (classic (exists z, Sbox t z /\ dels t / 2 < z)) as [ [z [Hz Hzlt]] | Hno ].
  - apply (Sbox_down t z (dels t / 2) Hz (halfdels_pos t)); lra.
  - exfalso; assert (Hub2 : is_upper_bound (Sbox t) (dels t / 2)).
    { intros x Hx; destruct (Rle_dec x (dels t / 2)) as [Hle | Hgt];
        [ exact Hle | exfalso; apply Hno; exists x; split; [ exact Hx | lra ] ]. }
    pose proof (Hlub _ Hub2); pose proof (dels_pos t); lra.
Qed.

Definition sfam (ts t : R) : Prop := (- Rb <= ts <= Rb) /\ disc ts (posdels ts) t.
Lemma sfam_cond : forall ts, (exists t, sfam ts t) -> (- Rb <= ts <= Rb).
Proof. intros ts [t [Hts _]]; exact Hts. Qed.
Definition sffam : family := mkfamily (fun ts => - Rb <= ts <= Rb) sfam sfam_cond.

Lemma sffam_cover_open : covering_open_set (fun t => - Rb <= t <= Rb) sffam.
Proof.
  split.
  - intros th Hth; exists th; split; [ exact Hth | ].
    unfold disc; replace (th - th) with 0 by ring; rewrite Rabs_R0;
      apply (cond_pos (posdels th)).
  - intro ts; simpl; destruct (classic (- Rb <= ts <= Rb)) as [Hin | Hout].
    + apply open_set_P6 with (disc ts (posdels ts)); [ apply disc_P1 | ].
      unfold eq_Dom, included, sfam; split; intros t Ht;
        [ split; [ exact Hin | exact Ht ] | exact (proj2 Ht) ].
    + apply open_set_P6 with (fun _ : R => False); [ apply open_set_P4 | ].
      unfold eq_Dom, included, sfam; split; intros t Ht;
        [ contradiction | exact (Hout (proj1 Ht)) ].
Qed.

Theorem strip_bounded_aux : exists del, 0 < del /\
  forall s : C, Rabs (Re s) < del -> Rabs (Im s) <= Rb -> Cmod (F s) <= M0 + 1.
Proof.
  destruct (compact_P3 (- Rb) Rb sffam sffam_cover_open) as [D [Hcov Hfin]].
  unfold family_finite, domain_finite in Hfin; destruct Hfin as [l Hl].
  set (del := fold_right (fun ts a => Rmin (dels ts / 2) a) 1 l).
  assert (Hdpos : 0 < del).
  { unfold del; clear; induction l as [ | ts l' IH ]; simpl;
      [ lra | apply Rmin_pos; [ apply halfdels_pos | exact IH ] ]. }
  assert (Hdle : forall ts, In ts l -> del <= dels ts / 2).
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
  destruct (Sbox_half ts) as [_ Hbox].
  apply Hbox.
  - unfold Rabs; destruct (Rcase_abs ts); lra.
  - unfold disc in Hts_disc; simpl in Hts_disc; exact Hts_disc.
  - eapply Rlt_le_trans; [ exact Hre | exact Hdts ].
Qed.

End StripBound.

(* ---- the packaged form: no base-point bound to supply ---- *)
Theorem strip_bounded : forall (F : C -> C),
  (forall (z : C) (eps : R), 0 < eps -> exists del, 0 < del /\
     forall w, Cmod (Cminus w z) < del -> Cmod (Cminus (F w) (F z)) < eps) ->
  CcontC F -> forall Rb, 0 < Rb ->
  exists del M, 0 < del /\
    forall s : C, Rabs (Re s) < del -> Rabs (Im s) <= Rb -> Cmod (F s) <= M.
Proof.
  intros F Fptc Fcc Rb HRb.
  destruct (Ccont_bounded (fun u => F (mkC 0 u)) (Ccont_vert F Fcc)
              (- Rb) Rb ltac:(lra)) as [M0 HM0].
  destruct (strip_bounded_aux F Fptc Rb HRb M0 HM0) as [del [Hdel Hb]].
  exists del, (M0 + 1); split; [ exact Hdel | exact Hb ].
Qed.

Print Assumptions strip_bounded.

(* ================================================================= *)
(*  END CStripBound.v -- one radius, one bound, along the whole        *)
(*  compact segment of the imaginary axis.                             *)
(* ================================================================= *)
