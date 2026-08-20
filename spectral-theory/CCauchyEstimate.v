(* ================================================================= *)
(*  CCauchyEstimate.v  —  Cauchy estimates OFF THE CENTRE.             *)
(*                                                                    *)
(*    disk_value_bound : |G| <= M on the circle |z| = Rr               *)
(*        ==>  |G w| <= 4 M        for  |w| <= Rr/2                    *)
(*    disk_deriv_bound : same hypothesis                               *)
(*        ==>  |G' w| <= 8 M / Rr  for  |w| <= Rr/2                    *)
(*                                                                    *)
(*  CCentreBound.centre_bound is this argument at w = C0.  Moving off  *)
(*  the centre changes exactly one thing: the Cauchy kernel is bounded *)
(*  by 1/(Rr - |w|) rather than 1/Rr, and on the half-disk that is at  *)
(*  most 2/Rr.  cauchy_interior_dom is ALREADY stated for a general    *)
(*  interior point, so nothing has to be reproved -- only the ML       *)
(*  estimate is recomputed.                                            *)
(*                                                                    *)
(*  WHY BOTH.  These are the two ways to cash in a bound on a circle:  *)
(*   * the VALUE bound stands in for the maximum-modulus principle,    *)
(*     which this development does not have -- it is how an estimate   *)
(*     established on a zero-avoiding circle is carried inward, across *)
(*     the zeros, where the estimate itself is unavailable;            *)
(*   * the DERIVATIVE bound converts smallness of a function into      *)
(*     smallness of its derivative, which is what turns a uniform      *)
(*     tail estimate on an infinite product into control of the        *)
(*     product's logarithmic derivative.                               *)
(*                                                                    *)
(*  The constant 2 is Cintf_ML's Re/Im split, not the sharp maximum    *)
(*  principle (which would give 1).  Harmless in both uses.            *)
(*  Axiom-clean.                                                       *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra FunctionalExtensionality.
Require Import ComplexField Cmodulus Holomorphic CDeriv CIntegral2 CSegInt
        CPathIntegral CSeries PerronRemovable RootsOfUnity CCauchyAnalytic
        CRemovableExtDom CCauchyDeriv CZeroListFactor CCentreBound.
Open Scope R_scope.

Lemma Cpow_two : forall x : C, Cpow x 2 = Cmul x x.
Proof. intro x; cbn; ring. Qed.

Section Estimate.

Variable G : C -> C.
Variable Rr M : R.
Variable w : C.
Hypothesis HR : 0 < Rr.
Hypothesis Hptc : ptcont G.
Hypothesis Hbd : forall u, Cmod (G (arc Rr u)) <= M.
Hypothesis Hw : Cmod w <= Rr / 2.

Lemma HGc : CcontC G.
Proof. apply ptcont_CcontC; exact Hptc. Qed.

Lemma HwR : Cmod w < Rr.
Proof. lra. Qed.

(* the circle keeps its distance from w *)
Lemma Hgap : forall u, Rr / 2 <= Cmod (Cminus (arc Rr u) w).
Proof.
  intro u.
  pose proof (Cmod_diff_le (arc Rr u) w) as Ht.
  pose proof (Rle_abs (Cmod (arc Rr u) - Cmod w)) as Ha.
  rewrite (Cmod_arc Rr u ltac:(lra)) in *. lra.
Qed.

Lemma Harcne : forall u, Cminus (arc Rr u) w <> C0.
Proof.
  intros u Hc. pose proof (Hgap u) as H.
  rewrite Hc, (proj2 (Cmod0 C0) eq_refl) in H. lra.
Qed.

(* ----------------------------------------------------------------- *)
(*  A.  the VALUE bound                                                *)
(* ----------------------------------------------------------------- *)
Theorem disk_value_bound :
  (forall z, Cmod z < Rr + 1 -> exists d, is_Cderiv G z d) ->
  Cmod (G w) <= 4 * M.
Proof.
  intro Hhol.
  pose proof PI_RGT_0 as HPI. pose proof HwR as HwR'.
  destruct (Hhol w ltac:(lra)) as [dw Hdw].
  assert (Hpc : Ccont (fun u => Cmul (Cmul (G (arc Rr u))
                                  (Cinv (Cminus (arc Rr u) w))) (arc' Rr u))).
  { assert (Hfe : (fun u => Cmul (Cmul (G (arc Rr u))
                             (Cinv (Cminus (arc Rr u) w))) (arc' Rr u))
                  = Kwn G Rr 1 w)
      by (apply functional_extensionality; intro u; unfold Kwn;
          rewrite Cpow_one; reflexivity).
    rewrite Hfe. exact (Kwn_cont G Rr 1 HGc w Harcne). }
  pose proof (cauchy_interior_dom G Rr w dw HR HwR' Hdw Hptc
                (fun z Hz (_ : z <> w) => Hhol z Hz) Hpc) as Hcauchy.
  assert (Hml : forall u, 0 <= u <= 2 * PI ->
      Cmod (Cmul ((fun z => Cmul (G z) (Cinv (Cminus z w))) (arc Rr u)) (arc' Rr u))
      <= 2 * M).
  { intros u _. cbv beta.
    pose proof (Hgap u) as Hg. pose proof (Hbd u) as Hb.
    pose proof (Cmod_nonneg (G (arc Rr u))) as Hg0.
    rewrite !Cmod_mul, (Cmod_inv (Cminus (arc Rr u) w) (Harcne u)),
            (Cmod_arc' Rr u ltac:(lra)).
    assert (Hinv : / Cmod (Cminus (arc Rr u) w) <= 2 / Rr).
    { apply Rle_trans with (/ (Rr / 2)); [ apply Rinv_le_contravar; lra | ].
      apply Req_le. field. lra. }
    assert (Hstep : Cmod (G (arc Rr u)) * / Cmod (Cminus (arc Rr u) w) * Rr
                    <= M * (2 / Rr) * Rr).
    { apply Rmult_le_compat_r; [ lra | ].
      apply Rmult_le_compat; [ exact Hg0 | | exact Hb | exact Hinv ].
      left; apply Rinv_0_lt_compat; lra. }
    replace (M * (2 / Rr) * Rr) with (2 * M) in Hstep by (field; lra).
    exact Hstep. }
  pose proof (pathint_ML (arc Rr) (arc' Rr)
                (fun z => Cmul (G z) (Cinv (Cminus z w))) Hpc 0 (2 * PI) (2 * M)
                ltac:(lra) Hml) as HML.
  rewrite Hcauchy, Cmod_mul, Cmod_2PIi in HML.
  apply (Rmult_le_reg_l (2 * PI)); [ lra | ].
  replace (2 * PI * (4 * M)) with (2 * (2 * M) * (2 * PI - 0)) by ring.
  exact HML.
Qed.

(* ----------------------------------------------------------------- *)
(*  B.  the DERIVATIVE bound                                           *)
(* ----------------------------------------------------------------- *)
Theorem disk_deriv_bound : forall Fd : C -> C,
  (forall z, is_Cderiv G z (Fd z)) ->
  (forall z, exists d, is_Cderiv Fd z d) ->
  CcontC Fd ->
  Cmod (Fd w) <= 8 * M / Rr.
Proof.
  intros Fd HFd HFdhol HFdcc.
  pose proof PI_RGT_0 as HPI. pose proof HwR as HwR'.
  assert (Hsqne : forall u,
            Cmul (Cminus (arc Rr u) w) (Cminus (arc Rr u) w) <> C0)
    by (intro u; apply Cmul_ne0; apply Harcne).
  assert (Hpc : Ccont (fun u => Cmul (Cmul (G (arc Rr u))
                    (Cinv (Cmul (Cminus (arc Rr u) w) (Cminus (arc Rr u) w))))
                    (arc' Rr u))).
  { assert (Hfe : (fun u => Cmul (Cmul (G (arc Rr u))
                    (Cinv (Cmul (Cminus (arc Rr u) w) (Cminus (arc Rr u) w))))
                    (arc' Rr u))
                  = Kwn G Rr 2 w)
      by (apply functional_extensionality; intro u; unfold Kwn;
          rewrite Cpow_two; reflexivity).
    rewrite Hfe. exact (Kwn_cont G Rr 2 HGc w Harcne). }
  pose proof (cauchy_deriv G Fd HFd HFdhol HGc HFdcc Rr w HR HwR' Hpc) as Hcauchy.
  assert (Hml : forall u, 0 <= u <= 2 * PI ->
      Cmod (Cmul ((fun z => Cmul (G z)
                     (Cinv (Cmul (Cminus z w) (Cminus z w)))) (arc Rr u))
                 (arc' Rr u))
      <= 4 * M / Rr).
  { intros u _. cbv beta.
    pose proof (Hgap u) as Hg. pose proof (Hbd u) as Hb.
    pose proof (Cmod_nonneg (G (arc Rr u))) as Hg0.
    rewrite !Cmod_mul, (Cmod_inv _ (Hsqne u)), Cmod_mul,
            (Cmod_arc' Rr u ltac:(lra)).
    assert (Hinv : / (Cmod (Cminus (arc Rr u) w) * Cmod (Cminus (arc Rr u) w))
                   <= 4 / (Rr * Rr)).
    { apply Rle_trans with (/ (Rr / 2 * (Rr / 2)));
        [ apply Rinv_le_contravar; [ nra | nra ] | apply Req_le; field; lra ]. }
    assert (Hstep : Cmod (G (arc Rr u))
                    * / (Cmod (Cminus (arc Rr u) w) * Cmod (Cminus (arc Rr u) w))
                    * Rr
                    <= M * (4 / (Rr * Rr)) * Rr).
    { apply Rmult_le_compat_r; [ lra | ].
      apply Rmult_le_compat; [ exact Hg0 | | exact Hb | exact Hinv ].
      left; apply Rinv_0_lt_compat; nra. }
    replace (M * (4 / (Rr * Rr)) * Rr) with (4 * M / Rr) in Hstep
      by (field; lra).
    exact Hstep. }
  pose proof (pathint_ML (arc Rr) (arc' Rr)
                (fun z => Cmul (G z) (Cinv (Cmul (Cminus z w) (Cminus z w))))
                Hpc 0 (2 * PI) (4 * M / Rr) ltac:(lra) Hml) as HML.
  rewrite Hcauchy, Cmod_mul, Cmod_2PIi in HML.
  apply (Rmult_le_reg_l (2 * PI)); [ lra | ].
  replace (2 * PI * (8 * M / Rr)) with (2 * (4 * M / Rr) * (2 * PI - 0))
    by (field; lra).
  exact HML.
Qed.

End Estimate.

Print Assumptions disk_value_bound.
Print Assumptions disk_deriv_bound.
