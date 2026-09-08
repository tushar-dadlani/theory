(* ================================================================= *)
(*  CLLineNonzero.v  --  L(1+it, chi) <> 0 for t <> 0.                *)
(*                                                                    *)
(*  The Dirichlet-L analogue of ZetaLineNonzero.zetaC_line_nonzero,    *)
(*  i.e. of the zero-free line equivalent to PNT.                      *)
(*                                                                    *)
(*  Assume L(1+i t0, chi) = 0 and put sigma = 1 + e with e small.      *)
(*  CTwistEuler341.tfo_L gives                                         *)
(*                                                                    *)
(*    1 <= |L(sig,chi_0)|^3 |L(sig+i t0,chi)|^4 |L(sig+2i t0,chi^2)|   *)
(*                                                                    *)
(*  while                                                             *)
(*                                                                    *)
(*    |L(sig,chi_0)|       <= 2/(sig-1)    [L_mod_le_zeta and          *)
(*                                          zeta_cont_pole]            *)
(*    |L(sig+i t0,chi)|    <= C (sig-1)    [LFun_holo at the zero]     *)
(*    |L(sig+2i t0,chi^2)| <= M            [LFun_holo, bounded]        *)
(*                                                                    *)
(*  so 1 <= 8 C^4 M (sig-1), which fails for small e.                  *)
(*                                                                    *)
(*  HYPOTHESIS ON chi^2.  The third factor is bounded via holomorphy of *)
(*  L(.,chi^2) on Re s > 0, which needs chi^2 NON-PRINCIPAL.  When     *)
(*  chi^2 = chi_0 -- chi quadratic -- that factor has a pole at        *)
(*  sigma = 1 and this argument does not apply.  That is the same      *)
(*  degenerate case that blocks L(1,chi) <> 0 for real characters:     *)
(*  both failures are chi^2 = chi_0.                                   *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia ZArith Znumtheory List.
Require Import ComplexField Cmodulus CSeries CDeriv Holomorphic RootsOfUnity
        ZmodOrder DirichletModP Ell2Zeta Ell2ZetaCont ZetaLineNonzero
        CharModulus CTwistedCoeff CLSeries CCharSumBound CLContinue
        CLHolo1 CLHolo3 CTwistEuler341 CLLineTools.
Import ListNotations.
Open Scope R_scope.

(* the 3-4-1 endgame at a single sigma *)
Lemma tfo_bound_pt : forall Fv Gv Hv Cc Mm sg,
  1 < sg -> 0 <= Fv -> 0 <= Gv -> 0 <= Hv -> 0 <= Cc -> 0 <= Mm ->
  Fv <= 2 / (sg - 1) -> Gv <= Cc * (sg - 1) -> Hv <= Mm ->
  1 <= Fv ^ 3 * Gv ^ 4 * Hv ->
  1 <= 8 * Cc ^ 4 * Mm * (sg - 1).
Proof.
  intros Fv Gv Hv Cc Mm sg Hs HF0 HG0 HH0 HC0 HM0 HFb HGb HHb Htfo.
  assert (He : 0 < sg - 1) by lra.
  assert (HF3 : Fv ^ 3 <= (2 / (sg - 1)) ^ 3) by (apply pow_incr; split; assumption).
  assert (HG4 : Gv ^ 4 <= (Cc * (sg - 1)) ^ 4) by (apply pow_incr; split; assumption).
  assert (HF30 : 0 <= Fv ^ 3) by (apply pow_le; exact HF0).
  assert (HG40 : 0 <= Gv ^ 4) by (apply pow_le; exact HG0).
  assert (HGe : 0 <= (Cc * (sg - 1)) ^ 4) by (apply pow_le; nra).
  assert (Hchain : Fv ^ 3 * Gv ^ 4 * Hv
                   <= (2 / (sg - 1)) ^ 3 * (Cc * (sg - 1)) ^ 4 * Mm).
  { apply Rmult_le_compat; [ nra | exact HH0 | | exact HHb ].
    apply Rmult_le_compat; assumption. }
  assert (Hval : (2 / (sg - 1)) ^ 3 * (Cc * (sg - 1)) ^ 4 * Mm
                 = 8 * Cc ^ 4 * Mm * (sg - 1)) by (field; lra).
  lra.
Qed.

(* ================================================================= *)
Theorem LFun_line_nonzero : forall p g A B
  (Hp : prime (Z.of_nat p)) (Hg : (1 <= g <= p - 1)%nat)
  (Hord : ord p g = (p - 1)%nat)
  (HA : (0 < A < p - 1)%nat) (HB : (0 < B < p - 1)%nat),
  (forall n, dchar p g (2 * A) n = dchar p g B n) ->
  forall t,
  LFun p g A Hp Hg Hord HA (mkC 1 t) <> C0.
Proof.
  intros p g A B Hp Hg Hord HA HB HBeq t Hzero.
  assert (Hre1 : 0 < Re (mkC 1 t)) by (cbn [Re]; lra).
  assert (Hre2 : 0 < Re (mkC 1 (2 * t))) by (cbn [Re]; lra).
  destruct (LFun_holo p g A Hp Hg Hord HA (mkC 1 t) Hre1) as [D1 HD1].
  destruct (HD1 1 Rlt_0_1) as [del1 [Hdel1 Hb1]].
  destruct (LFun_holo p g B Hp Hg Hord HB (mkC 1 (2 * t)) Hre2) as [D2 HD2].
  destruct (HD2 1 Rlt_0_1) as [del2 [Hdel2 Hb2]].
  set (Z2 := LFun p g B Hp Hg Hord HB (mkC 1 (2 * t))) in *.
  set (Cc := Cmod D1 + 1).
  set (Mm := Cmod Z2 + (Cmod D2 + 1)).
  assert (HCc : 0 <= Cc) by (unfold Cc; pose proof (Cmod_nonneg D1); lra).
  assert (HMm : 0 <= Mm)
    by (unfold Mm; pose proof (Cmod_nonneg Z2); pose proof (Cmod_nonneg D2); lra).
  assert (HCM : 0 <= 8 * Cc ^ 4 * Mm)
    by (apply Rmult_le_pos;
        [ apply Rmult_le_pos; [ lra | apply pow_le; exact HCc ] | exact HMm ]).
  set (K := 8 * Cc ^ 4 * Mm + 1).
  assert (HK : 0 < K) by (unfold K; lra).
  set (e := Rmin (Rmin (Rmin (del1 / 2) (del2 / 2)) 1) (/ (2 * K))).
  assert (He0 : 0 < e).
  { unfold e. apply Rmin_pos; [ apply Rmin_pos; [ apply Rmin_pos; lra | lra ] | ].
    apply Rinv_0_lt_compat; lra. }
  assert (He1 : e <= 1)
    by (eapply Rle_trans;
        [ eapply Rle_trans; [ apply Rmin_l | apply Rmin_r ] | apply Rle_refl ]).
  assert (HeK : e <= / (2 * K)) by apply Rmin_r.
  assert (Hed1 : e < del1).
  { eapply Rle_lt_trans;
      [ eapply Rle_trans;
          [ eapply Rle_trans; [ apply Rmin_l | apply Rmin_l ] | apply Rmin_l ] | lra ]. }
  assert (Hed2 : e < del2).
  { eapply Rle_lt_trans;
      [ eapply Rle_trans;
          [ eapply Rle_trans; [ apply Rmin_l | apply Rmin_l ] | apply Rmin_r ] | lra ]. }
  set (sg := 1 + e).
  set (h := mkC e 0).
  assert (Hhmod : Cmod h = e).
  { unfold h; change (mkC e 0) with (RtoC e).
    rewrite Cmod_RtoC, Rabs_pos_eq; [ reflexivity | lra ]. }
  assert (Hsg1 : 1 < sg) by (unfold sg; lra).
  assert (Hsg2 : sg <= 2) by (unfold sg; lra).
  assert (Hsgm1 : sg - 1 = e) by (unfold sg; ring).
  assert (Ha0 : 0 < sg) by lra.
  assert (Ha1 : sg <> 1) by lra.
  assert (Hgt0 : 1 < Re (mkC sg 0)) by (cbn [Re]; lra).
  assert (Hgt1 : 0 < Re (mkC sg t)) by (cbn [Re]; lra).
  assert (Hgt2 : 0 < Re (mkC sg (2 * t))) by (cbn [Re]; lra).
  (* the three values *)
  set (L0 := LC p g 0 Hg Hord (mkC sg 0) Hgt0).
  set (L1 := LFun p g A Hp Hg Hord HA (mkC sg t)).
  set (L2 := LFun p g B Hp Hg Hord HB (mkC sg (2 * t))).
  assert (HL0 : Cseries_cv (Lterm p g 0 (mkC sg 0)) L0) by apply L_is_series.
  assert (HL1 : Cseries_cv (Lterm p g A (mkC sg t)) L1)
    by (apply LFun_series; exact Hgt1).
  assert (HL2 : Cseries_cv (Lterm p g (2 * A) (mkC sg (2 * t))) L2).
  { assert (E : forall k, Lterm p g (2 * A) (mkC sg (2 * t)) k
                          = Lterm p g B (mkC sg (2 * t)) k)
      by (intro k; unfold Lterm, Gchi; rewrite HBeq; reflexivity).
    intros eps Heps.
    destruct (LFun_series p g B Hp Hg Hord HB (mkC sg (2 * t)) Hgt2 eps Heps)
      as [N HN].
    exists N. intros n Hn. rewrite (Cpsum_ext _ _ n E). apply HN; exact Hn. }
  pose proof (tfo_L p g A sg t Hp Hg Hord Hsg1 L0 L1 L2 HL0 HL1 HL2) as Htfo.
  (* bound 1: the pole factor *)
  assert (HF : Cmod L0 <= 2 / (sg - 1)).
  { eapply Rle_trans;
      [ exact (L_mod_le_zeta p g 0 (mkC sg 0) L0 Hg Hord Ha0 Ha1 Hgt0 HL0)
      | exact (zeta_cont_pole sg Ha0 Ha1 Hsg1 Hsg2) ]. }
  (* bound 2: the assumed zero *)
  assert (Heq1 : mkC sg t = Cadd (mkC 1 t) h)
    by (unfold sg, h, Cadd; apply Ceq; cbn [Re Im]; ring).
  assert (Hhd1 : Cmod h < del1) by (rewrite Hhmod; exact Hed1).
  pose proof (Hb1 h Hhd1) as Hbb1. rewrite Rmult_1_l, Hhmod in Hbb1.
  rewrite Hzero in Hbb1.
  assert (HG : Cmod L1 <= Cc * (sg - 1)).
  { unfold L1. rewrite Heq1.
    set (X := LFun p g A Hp Hg Hord HA (Cadd (mkC 1 t) h)) in *.
    set (Y := LFun p g A Hp Hg Hord HA (mkC 1 t)) in *.
    replace X with (Cadd (Cminus (Cminus X Y) (Cmul D1 h))
                         (Cadd Y (Cmul D1 h))) by ring.
    rewrite Hzero.
    eapply Rle_trans; [ apply Cmod_triangle | ].
    replace (Cadd C0 (Cmul D1 h)) with (Cmul D1 h) by ring.
    rewrite Cmod_mul, Hhmod, Hsgm1.
    unfold Cc. lra. }
  (* bound 3: boundedness at 1 + 2 i t *)
  assert (Heq2 : mkC sg (2 * t) = Cadd (mkC 1 (2 * t)) h)
    by (unfold sg, h, Cadd; apply Ceq; cbn [Re Im]; ring).
  assert (Hhd2 : Cmod h < del2) by (rewrite Hhmod; exact Hed2).
  pose proof (Hb2 h Hhd2) as Hbb2. rewrite Rmult_1_l, Hhmod in Hbb2.
  assert (HH : Cmod L2 <= Mm).
  { unfold L2. rewrite Heq2.
    set (X := LFun p g B Hp Hg Hord HB (Cadd (mkC 1 (2 * t)) h)) in *.
    replace X with (Cadd (Cadd (Cminus (Cminus X Z2) (Cmul D2 h)) Z2)
                         (Cmul D2 h)) by ring.
    eapply Rle_trans; [ apply Cmod_triangle | ].
    eapply Rle_trans; [ apply Rplus_le_compat_r, Cmod_triangle | ].
    rewrite Cmod_mul, Hhmod.
    pose proof (Cmod_nonneg D2) as HD20.
    assert (Hde : Cmod D2 * e <= Cmod D2).
    { rewrite <- (Rmult_1_r (Cmod D2)) at 2.
      apply Rmult_le_compat_l; [ exact HD20 | exact He1 ]. }
    unfold Mm. lra. }
  (* contradiction *)
  assert (HF0 : 0 <= Cmod L0) by apply Cmod_nonneg.
  assert (HG0 : 0 <= Cmod L1) by apply Cmod_nonneg.
  assert (HH0 : 0 <= Cmod L2) by apply Cmod_nonneg.
  pose proof (tfo_bound_pt (Cmod L0) (Cmod L1) (Cmod L2) Cc Mm sg
                Hsg1 HF0 HG0 HH0 HCc HMm HF HG HH Htfo) as Hfin.
  rewrite Hsgm1 in Hfin.
  assert (Hsmall : 8 * Cc ^ 4 * Mm * e < 1).
  { assert (Hb : 8 * Cc ^ 4 * Mm <= K) by (unfold K; lra).
    apply Rle_lt_trans with (K * / (2 * K)).
    - apply Rmult_le_compat; [ exact HCM | lra | exact Hb | exact HeK ].
    - replace (K * / (2 * K)) with (/ 2) by (field; lra). lra. }
  lra.
Qed.

(* the hypothesis on chi^2, discharged by index reduction *)
Corollary LFun_line_nonzero_mod : forall p g A
  (Hp : prime (Z.of_nat p)) (Hg : (1 <= g <= p - 1)%nat)
  (Hord : ord p g = (p - 1)%nat) (HA : (0 < A < p - 1)%nat)
  (HB : (0 < (2 * A) mod (p - 1) < p - 1)%nat),
  forall t,
  LFun p g A Hp Hg Hord HA (mkC 1 t) <> C0.
Proof.
  intros p g A Hp Hg Hord HA HB t.
  apply (LFun_line_nonzero p g A ((2 * A) mod (p - 1)) Hp Hg Hord HA HB).
  intro n. apply dchar_index_mod. lia.
Qed.

(* ================================================================= *)
(*  L(1,chi) <> 0 FOR COMPLEX chi                                     *)
(*                                                                    *)
(*  t <> 0 is never used above.  For zeta it is essential -- zeta has  *)
(*  a pole at s = 1, so at t = 0 the pole factor and the zero          *)
(*  factor would be the same point.  A NON-PRINCIPAL L has no pole     *)
(*  there, so the argument runs unchanged at t = 0 and delivers the    *)
(*  value at s = 1.                                                    *)
(*                                                                    *)
(*  The side condition chi^2 non-principal is exactly: chi is not     *)
(*  real, since chi = conj chi iff chi^2 = chi_0.  So this is the      *)
(*  classical easy half of L(1,chi) <> 0 -- obtained straight from     *)
(*  3-4-1, without the usual conjugate-pair argument.                  *)
(* ================================================================= *)

Corollary LFun_one_nonzero : forall p g A
  (Hp : prime (Z.of_nat p)) (Hg : (1 <= g <= p - 1)%nat)
  (Hord : ord p g = (p - 1)%nat) (HA : (0 < A < p - 1)%nat)
  (HB : (0 < (2 * A) mod (p - 1) < p - 1)%nat),
  LFun p g A Hp Hg Hord HA (mkC 1 0) <> C0.
Proof.
  intros p g A Hp Hg Hord HA HB.
  apply (LFun_line_nonzero_mod p g A Hp Hg Hord HA HB 0).
Qed.

Print Assumptions LFun_line_nonzero.
Print Assumptions LFun_one_nonzero.

(* ================================================================= *)
(*  END CLLineNonzero.v                                               *)
(* ================================================================= *)
