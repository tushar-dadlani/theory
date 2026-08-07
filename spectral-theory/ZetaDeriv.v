(* ================================================================= *)
(*  ZetaDeriv.v  —  Milestone B, brick B8: zeta' as a total function,   *)
(*  and zeta'' (its derivative), both in clean is_Cderiv form.          *)
(*                                                                    *)
(*  zDF s = -1/(s-1)^2 + Sum dgtermC(s,n)  is the derivative of zF from   *)
(*  zetaC_holo, packaged total (like zF).  We prove                     *)
(*    zF_deriv  : is_Cderiv zF  z (zDF z)   (zeta'  = zDF)               *)
(*    zDF_deriv : is_Cderiv zDF z (zD2 z)   (zeta'' exists)              *)
(*  by the head + analytic-sum split (head_deriv/sum_deriv and          *)
(*  head_deriv2/sum_deriv2).                                            *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import ComplexField Cmodulus CDeriv Holomorphic CHoloCalculus
        CSeries CSeriesLin CZetaTerm CZetaDeriv2 CZetaDeriv3 CZetaDeriv4
        CZeta CZetaHolo CZetaHolo2 ZetaFn.
Open Scope R_scope.

Definition Dhead (s : C) : C := Cmul C1 (Copp (Cinv (Cmul (Cminus s C1) (Cminus s C1)))).
Definition Dhead2 (s : C) : C :=
  Cmul (Cadd C1 C1) (Cinv (Cmul (Cminus s C1) (Cmul (Cminus s C1) (Cminus s C1)))).

(* the second derivative of the pole term: d/dw [-1/(w-1)^2] = 2/(w-1)^3 *)
Lemma head_deriv2 : forall z, Cminus z C1 <> C0 -> is_Cderiv (fun w => Dhead w) z (Dhead2 z).
Proof.
  intros z Hz; unfold Dhead.
  eapply is_Cderiv_eq.
  - apply Cderiv_cscal; apply Cderiv_opp; apply Cderiv_invc.
    + apply Cderiv_mul; apply Cderiv_minus; solve [ apply Cderiv_id | apply Cderiv_const ].
    + cbv beta; apply Cmul_ne0; exact Hz.
  - unfold Dhead2; field; exact Hz.
Qed.

(* zeta' as a total function *)
Definition zDF (s : C) : C :=
  match Rlt_dec 0 (Re s) with
  | left h0 => match Ceq_dec2 (Cminus C1 s) C0 with
               | left _ => C0
               | right h1 => Cadd (Dhead s) (proj1_sig (dgtermC_cv s h0 h1))
               end
  | right _ => C0
  end.

Lemma dgtermC_cv_irrel : forall s H0 H1 H0' H1',
  proj1_sig (dgtermC_cv s H0 H1) = proj1_sig (dgtermC_cv s H0' H1').
Proof.
  intros s H0 H1 H0' H1'; apply (CUn_cv_unique (Cpsum (dgtermC s)));
    [ exact (proj2_sig (dgtermC_cv s H0 H1)) | exact (proj2_sig (dgtermC_cv s H0' H1')) ].
Qed.

Lemma zDF_eq : forall s (H0 : 0 < Re s) (H1 : Cminus C1 s <> C0),
  zDF s = Cadd (Dhead s) (proj1_sig (dgtermC_cv s H0 H1)).
Proof.
  intros s H0 H1; unfold zDF.
  destruct (Rlt_dec 0 (Re s)) as [h0 | h0]; [ | exfalso; lra ].
  destruct (Ceq_dec2 (Cminus C1 s) C0) as [Hc | h1];
    [ exfalso; apply H1; exact Hc | rewrite (dgtermC_cv_irrel s h0 h1 H0 H1); reflexivity ].
Qed.

(* the second derivative value zeta''(z) *)
Definition zD2 (s : C) (H0 : 0 < Re s) (H1 : Cminus C1 s <> C0) : C :=
  Cadd (Dhead2 s) (proj1_sig (d2gtermC_cv s H0 H1)).

(* ---- a local helper: the small-h neighborhood keeps z+h in the domain ---- *)
Lemma nbhd_domain : forall z h (H0 : 0 < Re z) (H1 : Cminus C1 z <> C0),
  Cmod h < Re z -> Cmod h < Cmod (Cminus C1 z) ->
  0 < Re (Cadd z h) /\ Cminus C1 (Cadd z h) <> C0.
Proof.
  intros z h H0 H1 HhRe Hhc; split.
  - unfold Cadd; cbn [Re]; pose proof (Cmod_Re_le h) as HR.
    assert (Rabs (Re h) < Re z) by lra; apply Rabs_def2 in H; lra.
  - intro Hc.
    assert (H' : Cminus C1 z = h)
      by (replace (Cminus C1 z) with (Cadd (Cminus C1 (Cadd z h)) h) by ring; rewrite Hc; ring).
    rewrite H' in Hhc; lra.
Qed.

(* ================================================================= *)
(*  zeta' = zDF : the derivative of zF is zDF                          *)
(* ================================================================= *)
Theorem zF_deriv : forall z, inDom z -> is_Cderiv zF z (zDF z).
Proof.
  intros z [H0 H1].
  assert (H1' : Cminus z C1 <> C0)
    by (intro Hc; apply H1; replace (Cminus C1 z) with (Copp (Cminus z C1)) by ring;
        rewrite Hc; unfold Copp, C0; apply Ceq; cbn; ring).
  rewrite (zDF_eq z H0 H1); intros eps Heps.
  destruct (head_deriv z H1' (eps / 2) ltac:(lra)) as [delh [Hdelh Hhead]].
  destruct (sum_deriv z H0 H1 (eps / 2) ltac:(lra)) as [dels [Hdels Hsum]].
  assert (Hcm : 0 < Cmod (Cminus C1 z)) by (apply Cmod_pos_ne0; exact H1).
  set (del := Rmin delh (Rmin dels (Rmin (Re z) (Cmod (Cminus C1 z))))).
  assert (Hr : 0 < del)
    by (unfold del; repeat apply Rmin_glb_lt; assumption).
  exists del; split; [ exact Hr | ].
  intros h Hh.
  assert (Hhh : Cmod h < delh) by (eapply Rlt_le_trans; [ exact Hh | unfold del; apply Rmin_l ]).
  assert (Hhs : Cmod h < dels)
    by (eapply Rlt_le_trans; [ exact Hh | unfold del; eapply Rle_trans; [ apply Rmin_r | apply Rmin_l ] ]).
  assert (HhRe : Cmod h < Re z)
    by (eapply Rlt_le_trans; [ exact Hh | unfold del; eapply Rle_trans;
          [ apply Rmin_r | eapply Rle_trans; [ apply Rmin_r | apply Rmin_l ] ] ]).
  assert (Hhc : Cmod h < Cmod (Cminus C1 z))
    by (eapply Rlt_le_trans; [ exact Hh | unfold del; eapply Rle_trans;
          [ apply Rmin_r | eapply Rle_trans; [ apply Rmin_r | apply Rmin_r ] ] ]).
  destruct (nbhd_domain z h H0 H1 HhRe Hhc) as [K0 K1].
  rewrite (zF_eq (Cadd z h) K0 K1), (zF_eq z H0 H1); unfold zetaC.
  set (A1 := Cinv (Cminus (Cadd z h) C1)); set (A2 := Cinv (Cminus z C1)).
  set (B1 := proj1_sig (gtermC_cv (Cadd z h) K0 K1)); set (B2 := proj1_sig (gtermC_cv z H0 H1)).
  set (Ds := proj1_sig (dgtermC_cv z H0 H1)).
  replace (Cminus (Cminus (Cadd A1 B1) (Cadd A2 B2)) (Cmul (Cadd (Dhead z) Ds) h))
    with (Cadd (Cminus (Cminus A1 A2) (Cmul (Dhead z) h)) (Cminus (Cminus B1 B2) (Cmul Ds h)))
    by ring.
  eapply Rle_trans; [ apply Cmod_triangle | ].
  replace (eps * Cmod h) with (eps / 2 * Cmod h + eps / 2 * Cmod h) by field.
  apply Rplus_le_compat.
  - exact (Hhead h Hhh).
  - apply (Hsum h B1 B2 Hhs); [ exact (proj2_sig (gtermC_cv (Cadd z h) K0 K1))
                              | exact (proj2_sig (gtermC_cv z H0 H1)) ].
Qed.

(* ================================================================= *)
(*  zeta'' : the derivative of zDF is zD2                              *)
(* ================================================================= *)
Theorem zDF_deriv : forall z (H0 : 0 < Re z) (H1 : Cminus C1 z <> C0),
  is_Cderiv zDF z (zD2 z H0 H1).
Proof.
  intros z H0 H1.
  assert (H1' : Cminus z C1 <> C0)
    by (intro Hc; apply H1; replace (Cminus C1 z) with (Copp (Cminus z C1)) by ring;
        rewrite Hc; unfold Copp, C0; apply Ceq; cbn; ring).
  unfold zD2; intros eps Heps.
  destruct (head_deriv2 z H1' (eps / 2) ltac:(lra)) as [delh [Hdelh Hhead]].
  destruct (sum_deriv2 z H0 H1 (eps / 2) ltac:(lra)) as [dels [Hdels Hsum]].
  assert (Hcm : 0 < Cmod (Cminus C1 z)) by (apply Cmod_pos_ne0; exact H1).
  set (del := Rmin delh (Rmin dels (Rmin (Re z) (Cmod (Cminus C1 z))))).
  assert (Hr : 0 < del) by (unfold del; repeat apply Rmin_glb_lt; assumption).
  exists del; split; [ exact Hr | ].
  intros h Hh.
  assert (Hhh : Cmod h < delh) by (eapply Rlt_le_trans; [ exact Hh | unfold del; apply Rmin_l ]).
  assert (Hhs : Cmod h < dels)
    by (eapply Rlt_le_trans; [ exact Hh | unfold del; eapply Rle_trans; [ apply Rmin_r | apply Rmin_l ] ]).
  assert (HhRe : Cmod h < Re z)
    by (eapply Rlt_le_trans; [ exact Hh | unfold del; eapply Rle_trans;
          [ apply Rmin_r | eapply Rle_trans; [ apply Rmin_r | apply Rmin_l ] ] ]).
  assert (Hhc : Cmod h < Cmod (Cminus C1 z))
    by (eapply Rlt_le_trans; [ exact Hh | unfold del; eapply Rle_trans;
          [ apply Rmin_r | eapply Rle_trans; [ apply Rmin_r | apply Rmin_r ] ] ]).
  destruct (nbhd_domain z h H0 H1 HhRe Hhc) as [K0 K1].
  rewrite (zDF_eq (Cadd z h) K0 K1), (zDF_eq z H0 H1).
  set (B1 := proj1_sig (dgtermC_cv (Cadd z h) K0 K1)); set (B2 := proj1_sig (dgtermC_cv z H0 H1)).
  set (Ds := proj1_sig (d2gtermC_cv z H0 H1)).
  replace (Cminus (Cminus (Cadd (Dhead (Cadd z h)) B1) (Cadd (Dhead z) B2))
                  (Cmul (Cadd (Dhead2 z) Ds) h))
    with (Cadd (Cminus (Cminus (Dhead (Cadd z h)) (Dhead z)) (Cmul (Dhead2 z) h))
               (Cminus (Cminus B1 B2) (Cmul Ds h)))
    by ring.
  eapply Rle_trans; [ apply Cmod_triangle | ].
  replace (eps * Cmod h) with (eps / 2 * Cmod h + eps / 2 * Cmod h) by field.
  apply Rplus_le_compat.
  - exact (Hhead h Hhh).
  - apply (Hsum h B1 B2 Hhs); [ exact (proj2_sig (dgtermC_cv (Cadd z h) K0 K1))
                              | exact (proj2_sig (dgtermC_cv z H0 H1)) ].
Qed.

Print Assumptions zF_deriv.
Print Assumptions zDF_deriv.

(* ================================================================= *)
(*  END ZetaDeriv.v  —  zeta' (zDF) and zeta'' (zD2) as is_Cderiv.       *)
(* ================================================================= *)
