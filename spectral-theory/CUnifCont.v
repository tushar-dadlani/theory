(* ================================================================= *)
(*  CUnifCont.v  —  Milestone C, brick C2d Block A: the 2D uniform      *)
(*  continuity of Fp∘arc, uniform in θ over the compact [0,2π].          *)
(*                                                                    *)
(*  This discharges the Harc_uc hypothesis of CCauchyFormula.  Proof by  *)
(*  a finite open cover of [0,2π] (compact_P3), mirroring Rtopology's    *)
(*  Heine: the cover radius at each θ* is the lub of "good box radii",   *)
(*  which is choice-free (canonical), keeping the four-axiom budget.     *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia Rtopology List Classical.
Require Import ComplexField Cmodulus CSeries CPathIntegral CIntegral2 CSegInt
        Holomorphic CCauchyFormula.
Open Scope R_scope.

Lemma Cmod_Cminus_sym : forall a b, Cmod (Cminus a b) = Cmod (Cminus b a).
Proof. intros a b; unfold Cmod, Cnorm2, Cminus; cbn; f_equal; ring. Qed.

(* ---- Lipschitz bounds for sin and cos (|f'| <= 1) ---- *)
Lemma deriv_lip1 : forall (f f' : R -> R),
  (forall c, derivable_pt_lim f c (f' c)) ->
  (forall c, Rabs (f' c) <= 1) ->
  forall x y, Rabs (f x - f y) <= Rabs (x - y).
Proof.
  intros f f' Hd Hb x y.
  destruct (Rtotal_order x y) as [Hlt | [Heq | Hgt]].
  - destruct (MVT_cor2 f f' x y Hlt (fun c _ => Hd c)) as [c [Hc _]].
    rewrite Rabs_minus_sym, Hc, Rabs_mult, (Rabs_minus_sym y x).
    apply Rle_trans with (1 * Rabs (x - y));
      [ apply Rmult_le_compat_r; [ apply Rabs_pos | apply Hb ] | lra ].
  - subst; replace (f y - f y) with 0 by ring; replace (y - y) with 0 by ring;
      rewrite Rabs_R0; apply Rle_refl.
  - destruct (MVT_cor2 f f' y x Hgt (fun c _ => Hd c)) as [c [Hc _]].
    rewrite Hc, Rabs_mult.
    apply Rle_trans with (1 * Rabs (x - y));
      [ apply Rmult_le_compat_r; [ apply Rabs_pos | apply Hb ] | lra ].
Qed.

Lemma cos_lip : forall x y, Rabs (cos x - cos y) <= Rabs (x - y).
Proof.
  apply (deriv_lip1 cos (fun c => - sin c)).
  - intro c; apply derivable_pt_lim_cos.
  - intro c; rewrite Rabs_Ropp; apply Rabs_le; pose proof (SIN_bound c); lra.
Qed.

Lemma sin_lip : forall x y, Rabs (sin x - sin y) <= Rabs (x - y).
Proof.
  apply (deriv_lip1 sin cos).
  - intro c; apply derivable_pt_lim_sin.
  - intro c; apply Rabs_le; pose proof (COS_bound c); lra.
Qed.

(* ---- arc is jointly continuous in (ρ,θ) ---- *)
Lemma arc_joint_cont : forall r0 t0 eps, 0 < eps -> exists b, 0 < b /\
  forall rho t, Rabs (rho - r0) < b -> Rabs (t - t0) < b ->
    Cmod (Cminus (arc rho t) (arc r0 t0)) < eps.
Proof.
  intros r0 t0 eps Heps.
  exists (eps / (2 * (1 + Rabs r0))).
  assert (Hpos : 0 < 2 * (1 + Rabs r0)) by (pose proof (Rabs_pos r0); lra).
  split; [ apply Rdiv_lt_0_compat; lra | ].
  intros rho t Hr Ht.
  set (b := eps / (2 * (1 + Rabs r0))) in *.
  eapply Rle_lt_trans; [ apply Cmod_le_sum | ].
  unfold arc, Cminus; cbn [Re Im].
  (* |ρcos t − r0 cos t0| + |ρ sin t − r0 sin t0| < eps *)
  assert (Hb1 : Rabs (rho * cos t - r0 * cos t0) <= Rabs (rho - r0) + Rabs r0 * Rabs (t - t0)).
  { replace (rho * cos t - r0 * cos t0)
       with ((rho - r0) * cos t + r0 * (cos t - cos t0)) by ring.
    eapply Rle_trans; [ apply Rabs_triang | ].
    apply Rplus_le_compat.
    - rewrite Rabs_mult; rewrite <- (Rmult_1_r (Rabs (rho - r0))) at 2.
      apply Rmult_le_compat_l; [ apply Rabs_pos | apply Rabs_le; pose proof (COS_bound t); lra ].
    - rewrite Rabs_mult; apply Rmult_le_compat_l; [ apply Rabs_pos | apply cos_lip ]. }
  assert (Hb2 : Rabs (rho * sin t - r0 * sin t0) <= Rabs (rho - r0) + Rabs r0 * Rabs (t - t0)).
  { replace (rho * sin t - r0 * sin t0)
       with ((rho - r0) * sin t + r0 * (sin t - sin t0)) by ring.
    eapply Rle_trans; [ apply Rabs_triang | ].
    apply Rplus_le_compat.
    - rewrite Rabs_mult; rewrite <- (Rmult_1_r (Rabs (rho - r0))) at 2.
      apply Rmult_le_compat_l; [ apply Rabs_pos | apply Rabs_le; pose proof (SIN_bound t); lra ].
    - rewrite Rabs_mult; apply Rmult_le_compat_l; [ apply Rabs_pos | apply sin_lip ]. }
  pose proof (Rabs_pos r0).
  apply Rle_lt_trans with (2 * (Rabs (rho - r0) + Rabs r0 * Rabs (t - t0))); [ lra | ].
  (* both |ρ−r0|,|t−t0| < b, and 2*(b + |r0|*b) = 2*(1+|r0|)*b <= 2*(2+|r0|)*b = eps *)
  apply Rlt_le_trans with (2 * (b + Rabs r0 * b)).
  - apply Rmult_lt_compat_l; [ lra | ].
    apply Rplus_lt_le_compat; [ exact Hr | ].
    apply Rmult_le_compat_l; [ exact H | left; exact Ht ].
  - unfold b; apply Req_le; field; lra.
Qed.

(* ================================================================= *)
(*  The finite-open-cover argument (mirrors Rtopology.Heine): the cover  *)
(*  radius at θ* is the lub of "good box radii" (choice-free), so a       *)
(*  finite subcover of [0,2π] yields a uniform δ = min over the list.     *)
(* ================================================================= *)

Section Cover.
Variable Fp : C -> C.
Hypothesis Hpcont : forall w eps, 0 < eps -> exists del, 0 < del /\
  forall w', Cmod (Cminus w' w) < del -> Cmod (Cminus (Fp w') (Fp w)) < eps.
Variables r0 eps : R.
Hypothesis Heps : 0 < eps.

(* a "good box radius" at center ts: within it, Fp∘arc stays eps/2-close to Fp(arc r0 ts) *)
Definition Ebox (ts z : R) : Prop :=
  (0 < z <= 2 * PI) /\
  (forall t rho, Rabs (t - ts) < z -> Rabs (rho - r0) < z ->
     Cmod (Cminus (Fp (arc rho t)) (Fp (arc r0 ts))) < eps / 2).

Lemma Ebox_bound : forall ts, bound (Ebox ts).
Proof. intro ts; exists (2 * PI); intros z Hz; apply (proj2 (proj1 Hz)). Qed.

Lemma Ebox_ne : forall ts, exists z, Ebox ts z.
Proof.
  intro ts.
  destruct (Hpcont (arc r0 ts) (eps / 2) ltac:(lra)) as [eta [Heta Hc]].
  destruct (arc_joint_cont r0 ts eta Heta) as [beta [Hbeta Hj]].
  exists (Rmin beta (2 * PI)); split.
  - split; [ apply Rmin_pos; [ exact Hbeta | apply Rmult_lt_0_compat; [ lra | apply PI_RGT_0 ] ]
          | apply Rmin_r ].
  - intros t rho Ht Hr; apply (Hc (arc rho t)); apply Hj.
    + eapply Rlt_le_trans; [ exact Hr | apply Rmin_l ].
    + eapply Rlt_le_trans; [ exact Ht | apply Rmin_l ].
Qed.

Definition delc (ts : R) : R :=
  proj1_sig (completeness (Ebox ts) (Ebox_bound ts) (Ebox_ne ts)).
Lemma delc_lub : forall ts, is_lub (Ebox ts) (delc ts).
Proof. intro ts; exact (proj2_sig (completeness (Ebox ts) (Ebox_bound ts) (Ebox_ne ts))). Qed.
Lemma delc_pos : forall ts, 0 < delc ts.
Proof.
  intro ts; destruct (Ebox_ne ts) as [z Hz].
  apply Rlt_le_trans with z; [ apply (proj1 (proj1 Hz)) | apply (proj1 (delc_lub ts)); exact Hz ].
Qed.
Lemma halfdelc_pos : forall ts, 0 < delc ts / 2.
Proof. intro ts; pose proof (delc_pos ts); lra. Qed.
Definition posdelc (ts : R) : posreal := mkposreal (delc ts / 2) (halfdelc_pos ts).

Lemma Ebox_down : forall ts z z', Ebox ts z -> 0 < z' -> z' <= z -> Ebox ts z'.
Proof.
  intros ts z z' [[Hz1 Hz2] Hbox] Hz'1 Hz'2; split; [ split; [ exact Hz'1 | lra ] | ].
  intros t rho Ht Hr; apply Hbox; lra.
Qed.

Lemma Ebox_half : forall ts, Ebox ts (delc ts / 2).
Proof.
  intro ts; destruct (delc_lub ts) as [Hub Hlub].
  destruct (classic (exists z, Ebox ts z /\ delc ts / 2 < z)) as [ [z [Hz Hzlt]] | Hno ].
  - apply (Ebox_down ts z (delc ts / 2) Hz (halfdelc_pos ts)); lra.
  - exfalso; assert (Hub2 : is_upper_bound (Ebox ts) (delc ts / 2)).
    { intros x Hx; destruct (Rle_dec x (delc ts / 2)) as [Hle | Hgt];
        [ exact Hle | exfalso; apply Hno; exists x; split; [ exact Hx | lra ] ]. }
    pose proof (Hlub _ Hub2); pose proof (delc_pos ts); lra.
Qed.

(* the open cover of [0,2π] by discs of radius delc/2 *)
Definition gfam (ts t : R) : Prop := (0 <= ts <= 2 * PI) /\ disc ts (posdelc ts) t.
Lemma gfam_cond : forall ts, (exists t, gfam ts t) -> (0 <= ts <= 2 * PI).
Proof. intros ts [t [Hts _]]; exact Hts. Qed.
Definition ffam : family := mkfamily (fun ts => 0 <= ts <= 2 * PI) gfam gfam_cond.

Lemma ffam_cover_open : covering_open_set (fun t => 0 <= t <= 2 * PI) ffam.
Proof.
  split.
  - intros th Hth; exists th; split; [ exact Hth | ].
    unfold disc; replace (th - th) with 0 by ring; rewrite Rabs_R0; apply (cond_pos (posdelc th)).
  - intro ts; simpl; destruct (classic (0 <= ts <= 2 * PI)) as [Hin | Hout].
    + apply open_set_P6 with (disc ts (posdelc ts)); [ apply disc_P1 | ].
      unfold eq_Dom, included, gfam; split; intros t Ht;
        [ split; [ exact Hin | exact Ht ] | exact (proj2 Ht) ].
    + apply open_set_P6 with (fun _ : R => False); [ apply open_set_P4 | ].
      unfold eq_Dom, included, gfam; split; intros t Ht;
        [ contradiction | exact (Hout (proj1 Ht)) ].
Qed.

Theorem arc_Fp_unif : exists del, 0 < del /\
  forall rho t, 0 <= t <= 2 * PI -> Rabs (rho - r0) < del ->
    Cmod (Cminus (Fp (arc rho t)) (Fp (arc r0 t))) < eps.
Proof.
  destruct (compact_P3 0 (2 * PI) ffam ffam_cover_open) as [D [Hcov Hfin]].
  unfold family_finite, domain_finite in Hfin; destruct Hfin as [l Hl].
  set (del := fold_right (fun ts a => Rmin (delc ts / 2) a) (2 * PI) l).
  assert (Hdpos : 0 < del).
  { unfold del; clear; induction l as [ | ts l' IH ]; simpl;
      [ apply Rmult_lt_0_compat; [ lra | apply PI_RGT_0 ]
      | apply Rmin_pos; [ apply halfdelc_pos | exact IH ] ]. }
  assert (Hdle : forall ts, In ts l -> del <= delc ts / 2).
  { unfold del; intros ts Hts; clear -Hts; induction l as [ | t0 l' IH ]; simpl in *;
      [ contradiction
      | destruct Hts as [ -> | Hin ];
        [ apply Rmin_l | eapply Rle_trans; [ apply Rmin_r | apply IH; exact Hin ] ] ]. }
  exists del; split; [ exact Hdpos | ]; intros rho t Ht Hr.
  destruct (Hcov t Ht) as [ts Hts]; simpl in Hts.
  destruct Hts as [[Hts_in Hts_disc] Hts_D].
  assert (Hin_l : In ts l) by (apply (proj1 (Hl ts)); split; [ exact Hts_in | exact Hts_D ]).
  assert (Hdts := Hdle ts Hin_l).
  unfold disc in Hts_disc; simpl in Hts_disc.
  destruct (Ebox_half ts) as [_ Hbox].
  apply Rle_lt_trans with (Cmod (Cminus (Fp (arc rho t)) (Fp (arc r0 ts)))
                         + Cmod (Cminus (Fp (arc r0 ts)) (Fp (arc r0 t)))).
  - replace (Cminus (Fp (arc rho t)) (Fp (arc r0 t)))
       with (Cadd (Cminus (Fp (arc rho t)) (Fp (arc r0 ts)))
                  (Cminus (Fp (arc r0 ts)) (Fp (arc r0 t)))) by ring;
      apply Cmod_triangle.
  - replace eps with (eps / 2 + eps / 2) by field; apply Rplus_lt_compat.
    + apply Hbox; [ exact Hts_disc | eapply Rlt_le_trans; [ exact Hr | exact Hdts ] ].
    + rewrite Cmod_Cminus_sym; apply Hbox;
        [ exact Hts_disc
        | replace (r0 - r0) with 0 by ring; rewrite Rabs_R0; apply halfdelc_pos ].
Qed.

End Cover.

(* ---- wrapper: Cauchy's formula with "Fp continuous" instead of Harc_uc ---- *)
Theorem cauchy_formula_full : forall (F Fp : C -> C),
  CcontC F -> CcontC Fp -> (forall z, is_Cderiv F z (Fp z)) ->
  (forall w eps, 0 < eps -> exists del, 0 < del /\
     forall w', Cmod (Cminus w' w) < del -> Cmod (Cminus (Fp w') (Fp w)) < eps) ->
  forall (R : R), 0 < R ->
  forall (Hpf : Ccont (fun u => Cmul (Cmul (F (arc R u)) (Cinv (arc R u))) (arc' R u))),
  pathint (arc R) (arc' R) (fun z => Cmul (F z) (Cinv z)) Hpf 0 (2 * PI)
  = Cmul (mkC 0 (2 * PI)) (F C0).
Proof.
  intros F Fp HF HFp HFhol Hpcont R HR Hpf.
  exact (cauchy_integral_formula F Fp HF HFp HFhol
           (fun r0 eps Heps => arc_Fp_unif Fp Hpcont r0 eps Heps) R HR Hpf).
Qed.

Print Assumptions cauchy_formula_full.

(* ================================================================= *)
(*  END CUnifCont.v  —  2D uniform continuity of Fp∘arc + Cauchy full.   *)
(* ================================================================= *)
