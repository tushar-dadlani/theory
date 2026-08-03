(* ================================================================= *)
(*  CDeriv.v  —  extra complex-derivative rules: extensionality, the   *)
(*  reciprocal rule 1/z, and the general product rule.                 *)
(*                                                                    *)
(*  These extend Holomorphic.v (which had only const/id/±/affine) to   *)
(*  what the holomorphy of the Euler–Maclaurin zeta needs.  Axiom-clean.*)
(* ================================================================= *)

From Stdlib Require Import Reals Lra FunctionalExtensionality.
Require Import ComplexField Cmodulus Holomorphic.
Open Scope R_scope.

Lemma is_Cderiv_ext : forall F G z d,
  (forall w, F w = G w) -> is_Cderiv F z d -> is_Cderiv G z d.
Proof.
  intros F G z d Heq HF.
  assert (HFG : F = G) by (apply functional_extensionality; exact Heq).
  rewrite <- HFG; exact HF.
Qed.

Lemma Cmod_C1 : Cmod C1 = 1.
Proof.
  unfold Cmod, Cnorm2, C1; cbn; replace (1 * 1 + 0 * 0) with 1 by ring; apply sqrt_1.
Qed.

Lemma Cmod_pos_ne0 : forall c, c <> C0 -> 0 < Cmod c.
Proof.
  intros c Hc; destruct (Cmod_nonneg c) as [H | H]; [ exact H | ].
  exfalso; apply Hc; apply (proj1 (Cmod0 c)); symmetry; exact H.
Qed.

Lemma Cmod_inv : forall c, c <> C0 -> Cmod (Cinv c) = / Cmod c.
Proof.
  intros c Hc.
  assert (Hcm : Cmod c <> 0) by (apply Rgt_not_eq; apply Cmod_pos_ne0; exact Hc).
  apply (Rmult_eq_reg_r (Cmod c)); [ | exact Hcm ].
  rewrite <- Cmod_mul, Cinv_l by exact Hc.
  rewrite Cmod_C1, Rinv_l by exact Hcm; reflexivity.
Qed.

Lemma Cmul_ne0 : forall a b, a <> C0 -> b <> C0 -> Cmul a b <> C0.
Proof.
  intros a b Ha Hb H.
  assert (Hm : Cmod (Cmul a b) = 0) by (rewrite H; apply (proj2 (Cmod0 C0)); reflexivity).
  rewrite Cmod_mul in Hm.
  pose proof (Cmod_pos_ne0 a Ha); pose proof (Cmod_pos_ne0 b Hb); nra.
Qed.

(* the reciprocal rule  d/dz (1/z) = -1/z^2 *)
Lemma Cderiv_inv : forall z, z <> C0 -> is_Cderiv Cinv z (Copp (Cinv (Cmul z z))).
Proof.
  intros z Hz eps Heps.
  assert (Hzm : 0 < Cmod z) by (apply Cmod_pos_ne0; exact Hz).
  assert (Hz3 : 0 < Cmod z ^ 3) by (apply pow_lt; exact Hzm).
  set (del := Rmin (Cmod z / 2) (eps * Cmod z ^ 3 / 2)).
  assert (Hd : 0 < del).
  { unfold del; apply Rmin_glb_lt; [ lra | ].
    apply Rmult_lt_0_compat; [ apply Rmult_lt_0_compat; [ exact Heps | exact Hz3 ] | lra ]. }
  exists del; split; [ exact Hd | ].
  intros h Hh.
  assert (Hhz : Cmod h < Cmod z / 2)
    by (eapply Rlt_le_trans; [ exact Hh | apply Rmin_l ]).
  assert (Hhe : Cmod h < eps * Cmod z ^ 3 / 2)
    by (eapply Rlt_le_trans; [ exact Hh | apply Rmin_r ]).
  (* z+h is nonzero, with modulus > Cmod z / 2 *)
  assert (Hzhlow : Cmod z / 2 < Cmod (Cadd z h)).
  { pose proof (Cmod_triangle (Cadd z h) (Copp h)) as HT.
    replace (Cadd (Cadd z h) (Copp h)) with z in HT by ring.
    rewrite Cmod_opp in HT; lra. }
  assert (Hzh : Cadd z h <> C0)
    by (intro Hc; rewrite Hc in Hzhlow; rewrite (proj2 (Cmod0 C0)) in Hzhlow by reflexivity; lra).
  assert (Hprod : Cmul (Cadd z h) (Cmul z z) <> C0)
    by (apply Cmul_ne0; [ exact Hzh | apply Cmul_ne0; exact Hz ]).
  (* the o(h) remainder equals h^2 / ((z+h) z^2) *)
  assert (Hrem : Cminus (Cminus (Cinv (Cadd z h)) (Cinv z)) (Cmul (Copp (Cinv (Cmul z z))) h)
               = Cmul (Cmul h h) (Cinv (Cmul (Cadd z h) (Cmul z z)))).
  { field; split; [ exact Hz | exact Hzh ]. }
  rewrite Hrem, Cmod_mul, Cmod_mul, Cmod_inv by exact Hprod.
  rewrite Cmod_mul, Cmod_mul.
  (* Cmod h * Cmod h * / (Cmod(z+h) * (Cmod z * Cmod z)) <= eps * Cmod h *)
  assert (Hden : 0 < Cmod (Cadd z h) * (Cmod z * Cmod z))
    by (apply Rmult_lt_0_compat;
        [ apply Rlt_trans with (Cmod z / 2); [ lra | exact Hzhlow ]
        | apply Rmult_lt_0_compat; exact Hzm ]).
  assert (Hzhpos : 0 < Cmod (Cadd z h))
    by (apply Rlt_trans with (Cmod z / 2); [ lra | exact Hzhlow ]).
  apply Rmult_le_reg_r with (Cmod (Cadd z h) * (Cmod z * Cmod z)); [ exact Hden | ].
  replace (Cmod h * Cmod h * / (Cmod (Cadd z h) * (Cmod z * Cmod z))
           * (Cmod (Cadd z h) * (Cmod z * Cmod z)))
    with (Cmod h * Cmod h)
    by (field; split; apply Rgt_not_eq; [ exact Hzm | exact Hzhpos ]).
  replace (Cmod z ^ 3) with (Cmod z * Cmod z * Cmod z) in Hhe by ring.
  apply Rle_trans with (Cmod h * (eps * (Cmod z * Cmod z * Cmod z) / 2)).
  - apply Rmult_le_compat_l; [ apply Cmod_nonneg | apply Rlt_le; exact Hhe ].
  - replace (eps * Cmod h * (Cmod (Cadd z h) * (Cmod z * Cmod z)))
      with (Cmod h * (eps * Cmod (Cadd z h) * (Cmod z * Cmod z))) by ring.
    apply Rmult_le_compat_l; [ apply Cmod_nonneg | ].
    replace (eps * (Cmod z * Cmod z * Cmod z) / 2)
      with (eps * (Cmod z * Cmod z) * (Cmod z / 2)) by field.
    replace (eps * Cmod (Cadd z h) * (Cmod z * Cmod z))
      with (eps * (Cmod z * Cmod z) * Cmod (Cadd z h)) by ring.
    apply Rmult_le_compat_l;
      [ apply Rmult_le_pos;
          [ apply Rlt_le; exact Heps | apply Rmult_le_pos; apply Cmod_nonneg ]
      | apply Rlt_le; exact Hzhlow ].
Qed.

(* the general product rule *)
Lemma Cderiv_mul : forall F G z dF dG,
  is_Cderiv F z dF -> is_Cderiv G z dG ->
  is_Cderiv (fun w => Cmul (F w) (G w)) z (Cadd (Cmul dF (G z)) (Cmul (F z) dG)).
Proof.
  intros F G z dF dG HF HG eps Heps.
  set (MG := Cmod (G z)); set (MF := Cmod (F z)); set (DF := Cmod dF); set (DG := Cmod dG).
  assert (HMG : 0 <= MG) by apply Cmod_nonneg.
  assert (HMF : 0 <= MF) by apply Cmod_nonneg.
  assert (HDF : 0 <= DF) by apply Cmod_nonneg.
  assert (HDG : 0 <= DG) by apply Cmod_nonneg.
  set (e1 := Rmin 1 (eps / (3 * (MG + 1)))).
  set (e2 := Rmin 1 (eps / (3 * (MF + 1)))).
  assert (He1 : 0 < e1) by (apply Rmin_glb_lt; [ lra | apply Rdiv_lt_0_compat; lra ]).
  assert (He2 : 0 < e2) by (apply Rmin_glb_lt; [ lra | apply Rdiv_lt_0_compat; lra ]).
  destruct (HF e1 He1) as [d1 [Hd1 HF']].
  destruct (HG e2 He2) as [d2 [Hd2 HG']].
  set (del := Rmin (Rmin d1 d2) (eps / (3 * ((DF + 1) * (DG + 1))))).
  assert (Hpp : 0 < (DF + 1) * (DG + 1)) by (apply Rmult_lt_0_compat; lra).
  assert (Hd : 0 < del)
    by (apply Rmin_glb_lt; [ apply Rmin_glb_lt; assumption | apply Rdiv_lt_0_compat; lra ]).
  exists del; split; [ exact Hd | ].
  intros h Hh.
  set (mh := Cmod h); assert (Hmh : 0 <= mh) by apply Cmod_nonneg.
  assert (Hh1 : mh < d1)
    by (eapply Rlt_le_trans; [ exact Hh | eapply Rle_trans; [ apply Rmin_l | apply Rmin_l ] ]).
  assert (Hh2 : mh < d2)
    by (eapply Rlt_le_trans; [ exact Hh | eapply Rle_trans; [ apply Rmin_l | apply Rmin_r ] ]).
  assert (Hh3 : mh < eps / (3 * ((DF + 1) * (DG + 1))))
    by (eapply Rlt_le_trans; [ exact Hh | apply Rmin_r ]).
  pose proof (HF' h Hh1) as HRF; pose proof (HG' h Hh2) as HRG.
  fold mh in HRF, HRG.
  (* bounds on the increments *)
  assert (HDFmod : Cmod (Cminus (F (Cadd z h)) (F z)) <= (DF + 1) * mh).
  { replace (Cminus (F (Cadd z h)) (F z))
      with (Cadd (Cmul dF h) (Cminus (Cminus (F (Cadd z h)) (F z)) (Cmul dF h))) by ring.
    eapply Rle_trans; [ apply Cmod_triangle | ]; rewrite Cmod_mul; fold DF mh.
    apply Rle_trans with (DF * mh + e1 * mh); [ apply Rplus_le_compat_l; exact HRF | ].
    pose proof (Rmin_l 1 (eps / (3 * (MG + 1)))) as Hle1; fold e1 in Hle1; nra. }
  assert (HDGmod : Cmod (Cminus (G (Cadd z h)) (G z)) <= (DG + 1) * mh).
  { replace (Cminus (G (Cadd z h)) (G z))
      with (Cadd (Cmul dG h) (Cminus (Cminus (G (Cadd z h)) (G z)) (Cmul dG h))) by ring.
    eapply Rle_trans; [ apply Cmod_triangle | ]; rewrite Cmod_mul; fold DG mh.
    apply Rle_trans with (DG * mh + e2 * mh); [ apply Rplus_le_compat_l; exact HRG | ].
    pose proof (Rmin_l 1 (eps / (3 * (MF + 1)))) as Hle2; fold e2 in Hle2; nra. }
  (* the three eps/3 bounds *)
  assert (Hb1 : e1 * MG <= eps / 3).
  { apply Rle_trans with (e1 * (MG + 1)); [ apply Rmult_le_compat_l; [ apply Rlt_le; exact He1 | lra ] | ].
    apply Rle_trans with (eps / (3 * (MG + 1)) * (MG + 1));
      [ apply Rmult_le_compat_r; [ lra | apply Rmin_r ] | right; field; lra ]. }
  assert (Hb2 : MF * e2 <= eps / 3).
  { apply Rle_trans with ((MF + 1) * e2); [ apply Rmult_le_compat_r; [ apply Rlt_le; exact He2 | lra ] | ].
    apply Rle_trans with ((MF + 1) * (eps / (3 * (MF + 1))));
      [ apply Rmult_le_compat_l; [ lra | apply Rmin_r ] | right; field; lra ]. }
  assert (Hb3 : (DF + 1) * (DG + 1) * mh <= eps / 3).
  { apply Rle_trans with ((DF + 1) * (DG + 1) * (eps / (3 * ((DF + 1) * (DG + 1)))));
      [ apply Rmult_le_compat_l; [ apply Rlt_le; exact Hpp | apply Rlt_le; exact Hh3 ]
      | right; field; lra ]. }
  (* rewrite the remainder and bound by triangle *)
  replace (Cminus (Cminus (Cmul (F (Cadd z h)) (G (Cadd z h))) (Cmul (F z) (G z)))
                  (Cmul (Cadd (Cmul dF (G z)) (Cmul (F z) dG)) h))
    with (Cadd (Cadd (Cmul (Cminus (Cminus (F (Cadd z h)) (F z)) (Cmul dF h)) (G z))
                     (Cmul (F z) (Cminus (Cminus (G (Cadd z h)) (G z)) (Cmul dG h))))
               (Cmul (Cminus (F (Cadd z h)) (F z)) (Cminus (G (Cadd z h)) (G z))))
    by ring.
  eapply Rle_trans; [ apply Cmod_triangle | ].
  eapply Rle_trans; [ apply Rplus_le_compat_r; apply Cmod_triangle | ].
  rewrite !Cmod_mul; fold MG MF mh.
  apply Rle_trans with (e1 * mh * MG + MF * (e2 * mh) + (DF + 1) * mh * ((DG + 1) * mh)).
  - apply Rplus_le_compat.
    + apply Rplus_le_compat.
      * apply Rmult_le_compat_r; [ exact HMG | exact HRF ].
      * apply Rmult_le_compat_l; [ exact HMF | exact HRG ].
    + apply Rmult_le_compat; [ apply Cmod_nonneg | apply Cmod_nonneg | exact HDFmod | exact HDGmod ].
  - nra.
Qed.

Print Assumptions Cderiv_inv.
Print Assumptions Cderiv_mul.

(* ================================================================= *)
(*  END CDeriv.v (part 2).                                            *)
(* ================================================================= *)
