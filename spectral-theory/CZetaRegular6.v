(* ================================================================= *)
(*  CZetaRegular6.v   (Phase B2, part 5: BfnT total + holomorphic)     *)
(*                                                                    *)
(*  BfnT : C -> C  is the total regular part  (z-1)*zetaC z  (= 1 at 1).*)
(*  It is holomorphic on ALL of {Re>0}:                               *)
(*    - off z=1: BfnT z = (z-1)*zF z  (BfnT_eq), a product of holo;     *)
(*    - at z=1: is_Cderiv BfnT C1 (RtoC ellsum), because                *)
(*        BfnT(1+h) - BfnT(1) = h * G(1+h)  and  G -> ellsum (G_limit). *)
(*                                                                    *)
(*  Axioms: standard classical-Reals only.                            *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import ComplexField Cmodulus Holomorphic CDeriv CHoloCalculus
        CexpFull CPower CSeries CSeriesLin CZeta ZetaFn CZetaTerm
        CZetaRegular CZetaRegular2 CZetaRegular5.
Open Scope R_scope.

(* proj1_sig of gtermC_cv is independent of the proof arguments *)
Lemma gtermC_proj_irrel : forall s Ha Hb Hc Hd,
  proj1_sig (gtermC_cv s Ha Hb) = proj1_sig (gtermC_cv s Hc Hd).
Proof.
  intros s Ha Hb Hc Hd.
  apply (CUn_cv_unique (Cpsum (gtermC s)));
    [ exact (proj2_sig (gtermC_cv s Ha Hb)) | exact (proj2_sig (gtermC_cv s Hc Hd)) ].
Qed.

(* the regular sum off the pole equals (s-1) times the gterm sum *)
Lemma Bsum_off1 : forall s (H : 0 < Re s) (H1 : Cminus C1 s <> C0),
  Bsum s H = Cmul (Cminus s C1) (proj1_sig (gtermC_cv s H H1)).
Proof.
  intros s H H1.
  apply (CUn_cv_unique (Cpsum (bterm s))).
  - exact (Bsum_series s H).
  - apply (Cseries_cv_ext (fun n => Cmul (Cminus s C1) (gtermC s n))).
    + intro n. symmetry; apply bterm_eq; exact H1.
    + apply Cseries_cv_cscal. exact (proj2_sig (gtermC_cv s H H1)).
Qed.

(* ----------------------------------------------------------------- *)
(*  the total wrapper                                                 *)
(* ----------------------------------------------------------------- *)
Definition BsumT (s : C) : C :=
  match Rlt_dec 0 (Re s) with
  | left H => Bsum s H
  | right _ => C0
  end.

Definition BfnT (s : C) : C := Cadd C1 (BsumT s).

Lemma BfnT_at1 : BfnT C1 = C1.
Proof.
  unfold BfnT, BsumT. destruct (Rlt_dec 0 (Re C1)) as [H | H].
  - unfold Bsum.
    assert (HB : proj1_sig (bterm_cv C1 H) = C0).
    { apply (CUn_cv_unique (Cpsum (bterm C1))).
      - exact (proj2_sig (bterm_cv C1 H)).
      - unfold Cseries_cv, CUn_cv. intros eps Heps. exists 0%nat. intros n _.
        assert (HC : Cpsum (bterm C1) n = C0).
        { induction n as [| k IH]; [ apply bterm_at1 | ].
          simpl Cpsum. rewrite IH, bterm_at1.
          apply Ceq; unfold Cadd, C0; cbn [Re Im]; ring. }
        rewrite HC.
        assert (Hcm : Cmod (Cminus C0 C0) = 0)
          by (apply (proj2 (Cmod0 _)); apply Ceq; unfold Cminus, Cadd, Copp, C0; cbn [Re Im]; ring).
        rewrite Hcm; exact Heps. }
    rewrite HB. apply Ceq; unfold Cadd, C0, C1; cbn [Re Im]; ring.
  - exfalso; apply H; unfold C1; cbn [Re]; lra.
Qed.

(* off the pole:  BfnT s = (s-1) * zF s *)
Lemma BfnT_eq : forall s (H : 0 < Re s) (Hne : Cminus C1 s <> C0),
  BfnT s = Cmul (Cminus s C1) (zF s).
Proof.
  intros s H Hne.
  assert (Hne' : Cminus s C1 <> C0).
  { intro Hc. apply Hne. apply Ceq;
      [ apply (f_equal Re) in Hc | apply (f_equal Im) in Hc ];
      unfold Cminus, Cadd, Copp, C0 in *; cbn [Re Im] in *; lra. }
  rewrite (zF_eq s H Hne). unfold zetaC.
  unfold BfnT, BsumT. destruct (Rlt_dec 0 (Re s)) as [H' | H']; [ | exfalso; lra ].
  rewrite (Bsum_off1 s H' Hne), (gtermC_proj_irrel s H' Hne H Hne).
  field. exact Hne'.
Qed.

(* ----------------------------------------------------------------- *)
(*  holomorphy at z = 1  (from G_limit)                               *)
(* ----------------------------------------------------------------- *)
Lemma BfnT_deriv1 : is_Cderiv BfnT C1 (RtoC ellsum).
Proof.
  unfold is_Cderiv. intros eps Heps.
  destruct (G_limit eps Heps) as [del [Hdel Hg]].
  exists (Rmin del 1); split; [ apply Rmin_pos; lra | ].
  intros h Hh.
  destruct (Ceq_dec h C0) as [Hh0 | Hh0].
  - (* h = 0 *)
    subst h.
    assert (He : Cminus (Cminus (BfnT (Cadd C1 C0)) (BfnT C1)) (Cmul (RtoC ellsum) C0) = C0).
    { replace (Cadd C1 C0) with C1 by ring.
      apply Ceq; unfold Cminus, Cadd, Copp, Cmul, C0; cbn [Re Im]; ring. }
    rewrite He.
    assert (Hcm : Cmod C0 = 0) by (apply (proj2 (Cmod0 _)); reflexivity).
    rewrite Hcm, Rmult_0_r. apply Rle_refl.
  - (* h <> 0 *)
    assert (HsRe : 0 < Re (Cadd C1 h)).
    { assert (Hlt1 : Cmod h < 1) by (eapply Rlt_le_trans; [ exact Hh | apply Rmin_r ]).
      pose proof (Cmod_Re_le h) as HR. unfold Cadd, C1; cbn [Re].
      unfold Rabs in HR; destruct (Rcase_abs (Re h)); lra. }
    assert (Hsne : Cminus C1 (Cadd C1 h) <> C0).
    { intro Hc. apply Hh0. apply Ceq;
        [ apply (f_equal Re) in Hc | apply (f_equal Im) in Hc ];
        unfold Cminus, Cadd, Copp, C0, C1 in *; cbn [Re Im] in *; lra. }
    (* BfnT(1+h) - BfnT(1) = h * G(1+h) *)
    assert (Hval : Cminus (BfnT (Cadd C1 h)) (BfnT C1)
                 = Cmul h (proj1_sig (gtermC_cv (Cadd C1 h) HsRe Hsne))).
    { rewrite BfnT_at1. unfold BfnT, BsumT.
      destruct (Rlt_dec 0 (Re (Cadd C1 h))) as [H' | H']; [ | exfalso; lra ].
      rewrite (Bsum_off1 (Cadd C1 h) H' Hsne).
      rewrite (gtermC_proj_irrel (Cadd C1 h) H' Hsne HsRe Hsne).
      replace (Cminus (Cadd C1 h) C1) with h by ring.
      apply Ceq; unfold Cminus, Cadd, Copp, Cmul, C1; cbn [Re Im]; ring. }
    rewrite Hval.
    replace (Cminus (Cmul h (proj1_sig (gtermC_cv (Cadd C1 h) HsRe Hsne)))
                    (Cmul (RtoC ellsum) h))
       with (Cmul h (Cminus (proj1_sig (gtermC_cv (Cadd C1 h) HsRe Hsne)) (RtoC ellsum)))
       by ring.
    rewrite Cmod_mul, Rmult_comm.
    apply Rmult_le_compat_r; [ apply Cmod_nonneg | ].
    apply Rlt_le. apply (Hg (Cadd C1 h) HsRe Hsne).
    replace (Cminus (Cadd C1 h) C1) with h by ring.
    eapply Rlt_le_trans; [ exact Hh | apply Rmin_l ].
Qed.

Print Assumptions BfnT_deriv1.

(* ----------------------------------------------------------------- *)
(*  holomorphy off z = 1  (BfnT = (w-1) zF w there)                   *)
(* ----------------------------------------------------------------- *)
Lemma is_Cderiv_congr_local : forall F G z d r, 0 < r ->
  (forall w, Cmod (Cminus w z) < r -> F w = G w) ->
  is_Cderiv G z d -> is_Cderiv F z d.
Proof.
  intros F G z d r Hr Hagree HG eps Heps.
  destruct (HG eps Heps) as [del [Hdel Hb]].
  exists (Rmin del r); split; [ apply Rmin_pos; assumption | ].
  intros h Hh.
  assert (Hhd : Cmod h < del) by (eapply Rlt_le_trans; [ exact Hh | apply Rmin_l ]).
  assert (Hhr : Cmod h < r) by (eapply Rlt_le_trans; [ exact Hh | apply Rmin_r ]).
  rewrite (Hagree (Cadd z h)), (Hagree z).
  - apply Hb; exact Hhd.
  - replace (Cminus z z) with C0 by ring.
    assert (Cmod C0 = 0) by (apply (proj2 (Cmod0 _)); reflexivity). lra.
  - replace (Cminus (Cadd z h) z) with h by ring. exact Hhr.
Qed.

Lemma BfnT_holo_off1 : forall z, 0 < Re z -> Cminus C1 z <> C0 ->
  exists d, is_Cderiv BfnT z d.
Proof.
  intros z Hz Hne.
  destruct (zF_holo z (conj Hz Hne)) as [dz Hdz].
  assert (HzC1 : Cminus z C1 <> C0).
  { intro Hc. apply Hne. apply Ceq;
      [ apply (f_equal Re) in Hc | apply (f_equal Im) in Hc ];
      unfold Cminus, Cadd, Copp, C0 in *; cbn [Re Im] in *; lra. }
  assert (HzC1pos : 0 < Cmod (Cminus z C1)).
  { pose proof (Cmod_nonneg (Cminus z C1)).
    assert (Cmod (Cminus z C1) <> 0)
      by (intro Hc; apply HzC1; apply (proj1 (Cmod0 _)); exact Hc). lra. }
  set (r := Rmin (Re z / 2) (Cmod (Cminus z C1))).
  assert (Hr0 : 0 < r) by (apply Rmin_pos; lra).
  eexists.
  apply (is_Cderiv_congr_local BfnT (fun w => Cmul (Cminus w C1) (zF w)) z _ r Hr0).
  - intros w Hw.
    assert (HwRe : 0 < Re w).
    { assert (r <= Re z / 2) by apply Rmin_l.
      pose proof (Cmod_Re_le (Cminus w z)) as HR.
      assert (Hre : Re (Cminus w z) = Re w - Re z)
        by (unfold Cminus, Cadd, Copp; cbn [Re Im]; ring).
      rewrite Hre in HR. unfold Rabs in HR; destruct (Rcase_abs (Re w - Re z)); lra. }
    assert (HwC1 : Cminus C1 w <> C0).
    { intro Hc.
      assert (Hw1 : w = C1)
        by (apply Ceq; [ apply (f_equal Re) in Hc | apply (f_equal Im) in Hc ];
            unfold Cminus, Cadd, Copp, C0, C1 in *; cbn [Re Im] in *; lra).
      subst w.
      assert (Heq : Cmod (Cminus C1 z) = Cmod (Cminus z C1))
        by (replace (Cminus C1 z) with (Copp (Cminus z C1)) by ring; apply Cmod_opp).
      assert (r <= Cmod (Cminus z C1)) by apply Rmin_r.
      rewrite Heq in Hw. lra. }
    apply (BfnT_eq w HwRe HwC1).
  - apply (Cderiv_mul (fun w => Cminus w C1) zF z (Cminus C1 C0) dz).
    + apply (Cderiv_minus (fun w => w) (fun _ => C1));
        [ apply Cderiv_id | apply Cderiv_const ].
    + exact Hdz.
Qed.

(* ----------------------------------------------------------------- *)
(*  BfnT is holomorphic on ALL of {Re > 0}                           *)
(* ----------------------------------------------------------------- *)
Theorem BfnT_holo : forall z, 0 < Re z -> exists d, is_Cderiv BfnT z d.
Proof.
  intros z Hz.
  destruct (Ceq_dec (Cminus C1 z) C0) as [Hpole | Hpole].
  - assert (Hz1 : z = C1)
      by (apply Ceq; [ apply (f_equal Re) in Hpole | apply (f_equal Im) in Hpole ];
          unfold Cminus, Cadd, Copp, C0, C1 in *; cbn [Re Im] in *; lra).
    subst z. exists (RtoC ellsum). exact BfnT_deriv1.
  - apply (BfnT_holo_off1 z Hz Hpole).
Qed.

Print Assumptions BfnT_holo.
