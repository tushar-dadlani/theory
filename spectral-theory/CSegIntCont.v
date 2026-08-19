(* ================================================================= *)
(*  CSegIntCont.v  —  disk-cofactor bridge, the LINCHPIN:               *)
(*  the parametrized segment integral is continuous in its endpoint.    *)
(*                                                                    *)
(*    seg_int_endpoint_cont : CcontC f ->                               *)
(*      CcontC (fun b => seg_int f Hf a b)                             *)
(*                                                                    *)
(*  This is the piece the whole log/primitive tower silently needs to   *)
(*  go disk-local: the disk logarithm G = seg_int(g_cut) C0 must be     *)
(*  path-continuous (CcontC) to feed the mean value.  Nothing in the    *)
(*  repo provided continuity of a Riemann integral w.r.t. a parameter.  *)
(*                                                                    *)
(*  Built in four parts:                                               *)
(*   A. Cmodcont_CcontC : pointwise Cmod-continuity ==> CcontC          *)
(*      (extracted from CHoloCcontC.holo_CcontC's core).               *)
(*   B. seg_f_unif : a 2D Heine for the SEGMENT sweep -- uniform        *)
(*      continuity of f along seg a b v, uniform in v, as b -> b0       *)
(*      (mirrors CUnifCont.arc_Fp_unif's compact_P3 covering argument). *)
(*   C. seg_int_cmod_cont : Cmod-continuity of seg_int in the endpoint  *)
(*      (Cintf_ML on the difference + seg_f_unif + boundedness).        *)
(*   D. assemble A + C.                                                 *)
(*  Axiom-clean.                                                        *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia List Rtopology Classical FunctionalExtensionality.
Require Import ComplexField Cmodulus CIntegral2 CPathIntegral CSegInt
        CGoursatML CGoursatLin CLeibniz CSeries CDerivConst CHoloCcontC PerronEdge.
Open Scope R_scope.

Lemma Ccont_sub_loc : forall f g, Ccont f -> Ccont g -> Ccont (fun u => Cminus (f u) (g u)).
Proof.
  intros f g [Hf1 Hf2] [Hg1 Hg2]; split; cbv beta.
  - replace (fun u => Re (Cminus (f u) (g u))) with (fun u => Re (f u) - Re (g u))
      by (apply functional_extensionality; intro u; symmetry; apply ReCm).
    apply continuity_minus; assumption.
  - replace (fun u => Im (Cminus (f u) (g u))) with (fun u => Im (f u) - Im (g u))
      by (apply functional_extensionality; intro u; symmetry; apply ImCm).
    apply continuity_minus; assumption.
Qed.

Lemma Cmod_Cminus_sym : forall a b, Cmod (Cminus a b) = Cmod (Cminus b a).
Proof.
  intros a b; replace (Cminus b a) with (Copp (Cminus a b)) by ring;
    rewrite Cmod_opp; reflexivity.
Qed.

(* ---- Part A: pointwise Cmod-continuity implies CcontC ---- *)
Theorem Cmodcont_CcontC : forall F : C -> C,
  (forall z eps, 0 < eps -> exists del, 0 < del /\
     forall w, Cmod (Cminus w z) < del -> Cmod (Cminus (F w) (F z)) < eps) ->
  CcontC F.
Proof.
  intros F HFcm g Hg. destruct Hg as [HgRe HgIm].
  assert (comp : forall (proj : C -> R),
            (forall w, Rabs (proj w) <= Cmod w) ->
            (forall x y, proj (Cminus x y) = proj x - proj y) ->
            continuity (fun u => proj (F (g u)))).
  { intros proj Hproj Hpmin u0.
    unfold continuity_pt, continue_in, limit1_in.
    cbn [dist R_met]. unfold R_dist. cbv beta. intros eps Heps.
    destruct (HFcm (g u0) eps Heps) as [eta [Heta HF]].
    assert (Heta2 : 0 < eta / 2) by lra.
    destruct (HgRe u0 (eta / 2) Heta2) as [a1 [Ha1 HRe]].
    destruct (HgIm u0 (eta / 2) Heta2) as [a2 [Ha2 HIm]].
    cbn [dist R_met] in HRe, HIm. unfold R_dist in HRe, HIm. cbv beta in HRe, HIm.
    exists (Rmin a1 a2). split; [ apply Rmin_pos; assumption | ].
    intros x [Hdx Hxd].
    assert (Hx1 : Rabs (x - u0) < a1) by (eapply Rlt_le_trans; [ exact Hxd | apply Rmin_l ]).
    assert (Hx2 : Rabs (x - u0) < a2) by (eapply Rlt_le_trans; [ exact Hxd | apply Rmin_r ]).
    specialize (HRe x (conj Hdx Hx1)). specialize (HIm x (conj Hdx Hx2)).
    assert (Hcm : Cmod (Cminus (g x) (g u0)) < eta).
    { eapply Rle_lt_trans; [ apply Cmod_le_ReIm | ].
      rewrite ReCm, ImCm.
      apply Rlt_le_trans with (eta / 2 + eta / 2); [ | lra ].
      apply Rplus_lt_compat; assumption. }
    specialize (HF (g x) Hcm).
    change (dist R_met (proj (F (g x))) (proj (F (g u0))) < eps)
      with (Rabs (proj (F (g x)) - proj (F (g u0))) < eps).
    rewrite <- Hpmin.
    eapply Rle_lt_trans; [ apply Hproj | exact HF ]. }
  split; [ apply (comp Re Cmod_Re_le ReCm) | apply (comp Im Cmod_Im_le ImCm) ].
Qed.

(* ---- Part B: 2D Heine for the segment sweep (mirrors arc_Fp_unif) ---- *)

(* joint continuity of the sweep point seg a b v in (v, b) *)
Lemma seg_joint_cont : forall (a b0 : C) vs eps', 0 < eps' -> exists beta, 0 < beta /\
  forall v b, Rabs (v - vs) < beta -> Cmod (Cminus b b0) < beta ->
    Cmod (Cminus (seg a b v) (seg a b0 vs)) < eps'.
Proof.
  intros a b0 vs eps' Heps'.
  set (K := Rabs vs + 1 + Cmod (Cminus b0 a) + 1).
  assert (HK : 0 < K)
    by (unfold K; pose proof (Rabs_pos vs); pose proof (Cmod_nonneg (Cminus b0 a)); lra).
  exists (Rmin 1 (eps' / K)); split;
    [ apply Rmin_pos; [ lra | apply Rdiv_lt_0_compat; lra ] | ].
  intros v b Hv Hb.
  assert (Hv1 : Rabs (v - vs) < 1) by (eapply Rlt_le_trans; [ exact Hv | apply Rmin_l ]).
  assert (HvK : Rabs (v - vs) < eps' / K) by (eapply Rlt_le_trans; [ exact Hv | apply Rmin_r ]).
  assert (HbK : Cmod (Cminus b b0) < eps' / K) by (eapply Rlt_le_trans; [ exact Hb | apply Rmin_r ]).
  assert (HvB : Rabs v < Rabs vs + 1).
  { pose proof (Rabs_triang (v - vs) vs) as Ht. replace (v - vs + vs) with v in Ht by ring. lra. }
  assert (Heq : Cminus (seg a b v) (seg a b0 vs)
              = Cadd (Cmul (RtoC v) (Cminus b b0)) (Cmul (RtoC (v - vs)) (Cminus b0 a)))
    by (unfold seg, Cminus, Cadd, Cmul, RtoC; apply Ceq; cbn; ring).
  rewrite Heq.
  eapply Rle_lt_trans; [ apply Cmod_triangle | ].
  rewrite !Cmod_mul, !Cmod_RtoC.
  pose proof (Cmod_nonneg (Cminus b b0)) as Hbb.
  pose proof (Cmod_nonneg (Cminus b0 a)) as Hba.
  pose proof (Rabs_pos v) as Hav. pose proof (Rabs_pos (v - vs)) as Havs.
  apply Rle_lt_trans with ((Rabs vs + 1) * (eps' / K) + (eps' / K) * Cmod (Cminus b0 a)).
  - apply Rplus_le_compat; apply Rmult_le_compat; try assumption; lra.
  - replace ((Rabs vs + 1) * (eps' / K) + (eps' / K) * Cmod (Cminus b0 a))
       with ((eps' / K) * ((Rabs vs + 1) + Cmod (Cminus b0 a))) by ring.
    apply Rlt_le_trans with ((eps' / K) * K).
    + apply Rmult_lt_compat_l; [ apply Rdiv_lt_0_compat; lra | unfold K; lra ].
    + apply Req_le; field; lra.
Qed.

Section SegCover.
Variable f : C -> C.
Hypothesis Hfcont : forall w eps0, 0 < eps0 -> exists del, 0 < del /\
  forall w', Cmod (Cminus w' w) < del -> Cmod (Cminus (f w') (f w)) < eps0.
Variables (a b0 : C) (eps : R).
Hypothesis Heps : 0 < eps.

Definition SEbox (vs z : R) : Prop :=
  (0 < z <= 1) /\
  (forall v b, Rabs (v - vs) < z -> Cmod (Cminus b b0) < z ->
     Cmod (Cminus (f (seg a b v)) (f (seg a b0 vs))) < eps / 2).

Lemma SEbox_bound : forall vs, bound (SEbox vs).
Proof. intro vs; exists 1; intros z Hz; apply (proj2 (proj1 Hz)). Qed.

Lemma SEbox_ne : forall vs, exists z, SEbox vs z.
Proof.
  intro vs.
  destruct (Hfcont (seg a b0 vs) (eps / 2) ltac:(lra)) as [eta [Heta Hc]].
  destruct (seg_joint_cont a b0 vs eta Heta) as [beta [Hbeta Hj]].
  exists (Rmin beta 1); split.
  - split; [ apply Rmin_pos; lra | apply Rmin_r ].
  - intros v b Hv Hb; apply Hc; apply Hj;
      (eapply Rlt_le_trans; [ eassumption | apply Rmin_l ]).
Qed.

Definition sdelc (vs : R) : R :=
  proj1_sig (completeness (SEbox vs) (SEbox_bound vs) (SEbox_ne vs)).
Lemma sdelc_lub : forall vs, is_lub (SEbox vs) (sdelc vs).
Proof. intro vs; exact (proj2_sig (completeness (SEbox vs) (SEbox_bound vs) (SEbox_ne vs))). Qed.
Lemma sdelc_pos : forall vs, 0 < sdelc vs.
Proof.
  intro vs; destruct (SEbox_ne vs) as [z Hz].
  apply Rlt_le_trans with z; [ apply (proj1 (proj1 Hz)) | apply (proj1 (sdelc_lub vs)); exact Hz ].
Qed.
Lemma halfsdelc_pos : forall vs, 0 < sdelc vs / 2.
Proof. intro vs; pose proof (sdelc_pos vs); lra. Qed.
Definition posdelc (vs : R) : posreal := mkposreal (sdelc vs / 2) (halfsdelc_pos vs).

Lemma SEbox_down : forall vs z z', SEbox vs z -> 0 < z' -> z' <= z -> SEbox vs z'.
Proof.
  intros vs z z' [[Hz1 Hz2] Hbox] Hz'1 Hz'2; split; [ split; [ exact Hz'1 | lra ] | ].
  intros v b Hv Hb; apply Hbox; lra.
Qed.

Lemma SEbox_half : forall vs, SEbox vs (sdelc vs / 2).
Proof.
  intro vs; destruct (sdelc_lub vs) as [Hub Hlub].
  destruct (classic (exists z, SEbox vs z /\ sdelc vs / 2 < z)) as [ [z [Hz Hzlt]] | Hno ].
  - apply (SEbox_down vs z (sdelc vs / 2) Hz (halfsdelc_pos vs)); lra.
  - exfalso; assert (Hub2 : is_upper_bound (SEbox vs) (sdelc vs / 2)).
    { intros x Hx; destruct (Rle_dec x (sdelc vs / 2)) as [Hle | Hgt];
        [ exact Hle | exfalso; apply Hno; exists x; split; [ exact Hx | lra ] ]. }
    pose proof (Hlub _ Hub2); pose proof (sdelc_pos vs); lra.
Qed.

Definition sgfam (vs t : R) : Prop := (0 <= vs <= 1) /\ disc vs (posdelc vs) t.
Lemma sgfam_cond : forall vs, (exists t, sgfam vs t) -> (0 <= vs <= 1).
Proof. intros vs [t [Hvs _]]; exact Hvs. Qed.
Definition sffam : family := mkfamily (fun vs => 0 <= vs <= 1) sgfam sgfam_cond.

Lemma sffam_cover_open : covering_open_set (fun t => 0 <= t <= 1) sffam.
Proof.
  split.
  - intros th Hth; exists th; split; [ exact Hth | ].
    unfold disc; replace (th - th) with 0 by ring; rewrite Rabs_R0; apply (cond_pos (posdelc th)).
  - intro vs; simpl; destruct (classic (0 <= vs <= 1)) as [Hin | Hout].
    + apply open_set_P6 with (disc vs (posdelc vs)); [ apply disc_P1 | ].
      unfold eq_Dom, included, sgfam; split; intros t Ht;
        [ split; [ exact Hin | exact Ht ] | exact (proj2 Ht) ].
    + apply open_set_P6 with (fun _ : R => False); [ apply open_set_P4 | ].
      unfold eq_Dom, included, sgfam; split; intros t Ht;
        [ contradiction | exact (Hout (proj1 Ht)) ].
Qed.

Theorem seg_f_unif : exists del, 0 < del /\
  forall v b, 0 <= v <= 1 -> Cmod (Cminus b b0) < del ->
    Cmod (Cminus (f (seg a b v)) (f (seg a b0 v))) < eps.
Proof.
  destruct (compact_P3 0 1 sffam sffam_cover_open) as [D [Hcov Hfin]].
  unfold family_finite, domain_finite in Hfin; destruct Hfin as [l Hl].
  set (del := fold_right (fun vs acc => Rmin (sdelc vs / 2) acc) 1 l).
  assert (Hdpos : 0 < del).
  { unfold del; clear; induction l as [ | vs l' IH ]; simpl;
      [ lra | apply Rmin_pos; [ apply halfsdelc_pos | exact IH ] ]. }
  assert (Hdle : forall vs, In vs l -> del <= sdelc vs / 2).
  { unfold del; intros vs Hvs; clear -Hvs; induction l as [ | v0 l' IH ]; simpl in *;
      [ contradiction
      | destruct Hvs as [ -> | Hin ];
        [ apply Rmin_l | eapply Rle_trans; [ apply Rmin_r | apply IH; exact Hin ] ] ]. }
  exists del; split; [ exact Hdpos | ]; intros v b Hv Hb.
  destruct (Hcov v Hv) as [vs Hvs]; simpl in Hvs.
  destruct Hvs as [[Hvs_in Hvs_disc] Hvs_D].
  assert (Hin_l : In vs l) by (apply (proj1 (Hl vs)); split; [ exact Hvs_in | exact Hvs_D ]).
  assert (Hdvs := Hdle vs Hin_l).
  unfold disc in Hvs_disc; simpl in Hvs_disc.
  destruct (SEbox_half vs) as [_ Hbox].
  apply Rle_lt_trans with (Cmod (Cminus (f (seg a b v)) (f (seg a b0 vs)))
                         + Cmod (Cminus (f (seg a b0 vs)) (f (seg a b0 v)))).
  - replace (Cminus (f (seg a b v)) (f (seg a b0 v)))
       with (Cadd (Cminus (f (seg a b v)) (f (seg a b0 vs)))
                  (Cminus (f (seg a b0 vs)) (f (seg a b0 v)))) by ring;
      apply Cmod_triangle.
  - replace eps with (eps / 2 + eps / 2) by field; apply Rplus_lt_compat.
    + apply Hbox; [ exact Hvs_disc | eapply Rlt_le_trans; [ exact Hb | exact Hdvs ] ].
    + rewrite Cmod_Cminus_sym; apply Hbox;
        [ exact Hvs_disc
        | replace (Cminus b0 b0) with C0 by ring;
          rewrite (proj2 (Cmod0 C0) eq_refl); apply halfsdelc_pos ].
Qed.

End SegCover.

(* ---- Part C: Cmod-continuity of seg_int in the endpoint ---- *)
Lemma seg_int_cmod_cont : forall f (Hf : CcontC f) a,
  (forall z eps0, 0 < eps0 -> exists del, 0 < del /\
     forall w, Cmod (Cminus w z) < del -> Cmod (Cminus (f w) (f z)) < eps0) ->
  forall b0 eps, 0 < eps -> exists del, 0 < del /\
    forall b, Cmod (Cminus b b0) < del ->
      Cmod (Cminus (seg_int f Hf a b) (seg_int f Hf a b0)) < eps.
Proof.
  intros f Hf a Hfcm b0 eps Heps.
  assert (Hsegcont : Ccont (fun v => seg a b0 v))
    by (apply (Ccont_seg_comp a b0 (fun u => u)); intro x;
        apply derivable_continuous_pt; apply derivable_pt_id).
  assert (Hfsegcont : Ccont (fun v => f (seg a b0 v))) by (apply Hf; exact Hsegcont).
  destruct (continuity_ab_maj (fun v => Cmod (f (seg a b0 v))) 0 1 ltac:(lra)
             (fun c _ => Ccont_Cmod _ Hfsegcont c)) as [vmax [Hmaj Hvmax]].
  set (M2 := Cmod (f (seg a b0 vmax))).
  set (K1 := Cmod (Cminus b0 a) + 1).
  assert (HK1 : 0 < K1) by (unfold K1; pose proof (Cmod_nonneg (Cminus b0 a)); lra).
  assert (HM2 : 0 <= M2) by (unfold M2; apply Cmod_nonneg).
  destruct (seg_f_unif f Hfcm a b0 (eps / (8 * K1)) ltac:(apply Rdiv_lt_0_compat; lra))
    as [del1 [Hdel1 Hunif]].
  set (del := Rmin (Rmin del1 1) (eps / (8 * (M2 + 1)))).
  assert (Hdelpos : 0 < del)
    by (unfold del; repeat apply Rmin_pos; try lra; apply Rdiv_lt_0_compat; lra).
  exists del; split; [ exact Hdelpos | ]; intros b Hb.
  pose (gb := fun v => Cmul (f (seg a b v)) (Cminus b a)).
  pose (gb0 := fun v => Cmul (f (seg a b0 v)) (Cminus b0 a)).
  pose (diff := fun v => Cminus (gb v) (gb0 v)).
  assert (Hgb : Ccont gb) by exact (seg_ig_cont f Hf a b).
  assert (Hgb0 : Ccont gb0) by exact (seg_ig_cont f Hf a b0).
  assert (Hdiff : Ccont diff) by (unfold diff; apply Ccont_sub_loc; assumption).
  assert (Hlin : Cminus (seg_int f Hf a b) (seg_int f Hf a b0) = Cintf diff Hdiff 0 1).
  { assert (E1 : seg_int f Hf a b = Cintf gb Hgb 0 1)
      by (unfold seg_int; apply (Cintf_ext _ gb _ Hgb 0 1); intro u; unfold gb, seg'; reflexivity).
    assert (E0 : seg_int f Hf a b0 = Cintf gb0 Hgb0 0 1)
      by (unfold seg_int; apply (Cintf_ext _ gb0 _ Hgb0 0 1); intro u; unfold gb0, seg'; reflexivity).
    rewrite E1, E0.
    assert (Hsum : Ccont (fun v => Cadd (diff v) (gb0 v))) by (apply Ccont_add; assumption).
    assert (Hgbeq : Cintf gb Hgb 0 1 = Cadd (Cintf diff Hdiff 0 1) (Cintf gb0 Hgb0 0 1)).
    { rewrite <- (Cintf_add diff gb0 Hdiff Hgb0 Hsum 0 1 ltac:(lra)).
      apply (Cintf_ext gb (fun v => Cadd (diff v) (gb0 v)) Hgb Hsum 0 1).
      intro v; unfold diff; ring. }
    rewrite Hgbeq; ring. }
  rewrite Hlin.
  apply Rle_lt_trans with (2 * (eps / 4) * (1 - 0)).
  - apply (Cintf_ML diff Hdiff 0 1 (eps / 4) ltac:(lra)).
    intros v Hv.
    assert (Hdeq : diff v = Cadd (Cmul (Cminus (f (seg a b v)) (f (seg a b0 v))) (Cminus b a))
                                 (Cmul (f (seg a b0 v)) (Cminus b b0)))
      by (unfold diff, gb, gb0, Cmul, Cminus, Cadd; apply Ceq; cbn; ring).
    rewrite Hdeq.
    eapply Rle_trans; [ apply Cmod_triangle | ]. rewrite !Cmod_mul.
    assert (Hb1 : Cmod (Cminus b b0) <= 1)
      by (apply Rlt_le; eapply Rlt_le_trans; [ exact Hb | unfold del; eapply Rle_trans;
          [ apply Rmin_l | apply Rmin_r ] ]).
    assert (HbaK1 : Cmod (Cminus b a) <= K1).
    { replace (Cminus b a) with (Cadd (Cminus b b0) (Cminus b0 a)) by ring.
      eapply Rle_trans; [ apply Cmod_triangle | ]. unfold K1; lra. }
    assert (HT1 : Cmod (Cminus (f (seg a b v)) (f (seg a b0 v))) * Cmod (Cminus b a) <= eps / 8).
    { assert (Hu1 : Cmod (Cminus (f (seg a b v)) (f (seg a b0 v))) < eps / (8 * K1)).
      { apply Hunif; [ exact Hv | eapply Rlt_le_trans; [ exact Hb | unfold del;
          eapply Rle_trans; [ apply Rmin_l | apply Rmin_l ] ] ]. }
      apply Rle_trans with (eps / (8 * K1) * K1);
        [ apply Rmult_le_compat;
          [ apply Cmod_nonneg | apply Cmod_nonneg | apply Rlt_le; exact Hu1 | exact HbaK1 ]
        | apply Req_le; field; lra ]. }
    assert (HT2 : Cmod (f (seg a b0 v)) * Cmod (Cminus b b0) <= eps / 8).
    { assert (Hfb0v : Cmod (f (seg a b0 v)) <= M2) by (unfold M2; apply Hmaj; exact Hv).
      assert (Hbdel : Cmod (Cminus b b0) <= eps / (8 * (M2 + 1)))
        by (apply Rlt_le; eapply Rlt_le_trans; [ exact Hb | unfold del; apply Rmin_r ]).
      apply Rle_trans with (M2 * (eps / (8 * (M2 + 1)))).
      - apply Rmult_le_compat;
          [ apply Cmod_nonneg | apply Cmod_nonneg | exact Hfb0v | exact Hbdel ].
      - apply Rle_trans with ((M2 + 1) * (eps / (8 * (M2 + 1))));
          [ apply Rmult_le_compat_r; [ apply Rlt_le; apply Rdiv_lt_0_compat; lra | lra ]
          | apply Req_le; field; lra ]. }
    lra.
  - pose proof PI_RGT_0; lra.
Qed.

(* ---- Part D: assemble ---- *)
Theorem seg_int_endpoint_cont : forall f (Hf : CcontC f) a,
  (forall z eps0, 0 < eps0 -> exists del, 0 < del /\
     forall w, Cmod (Cminus w z) < del -> Cmod (Cminus (f w) (f z)) < eps0) ->
  CcontC (fun b => seg_int f Hf a b).
Proof.
  intros f Hf a Hfcm. apply Cmodcont_CcontC. intros b0 eps Heps.
  exact (seg_int_cmod_cont f Hf a Hfcm b0 eps Heps).
Qed.

Print Assumptions seg_int_endpoint_cont.
