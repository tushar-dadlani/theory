(* ================================================================= *)
(*  NewmanML.v  --  the pointwise modulus estimates of brick E6,       *)
(*  restated for the HONEST transform.                                *)
(*                                                                    *)
(*  NewmanArc.right_arc_bound and NewmanLeft.left_arc_bound prove the  *)
(*  4B/R^2 cancellation for LaplaceFull's gfull/LT, which are built on *)
(*  Cintf and so are unavailable at Newman's step function.  The       *)
(*  cancellation itself is f-agnostic, so it is stated here once, for  *)
(*  ANY w obeying the tail bound, and covers BOTH signs of Re z at     *)
(*  once via Rabs -- including Re z = 0, where the kernel vanishes on  *)
(*  the circle and the estimate is trivial.  That last case is what    *)
(*  lets the arc be split at Re z = 0 with a closed parameter interval *)
(*  on each side.                                                     *)
(*                                                                    *)
(*  Also: the LTN tail bound for Re z < 0 (LTN_tail assumed 0 < Re z   *)
(*  only through exp_int_AB_scaled; NewmanLeft.exp_int_AB_ne removes   *)
(*  that), the gext - LTN bound on the right (LTN_gN_bound + gN_eq_    *)
(*  gext), and the chord's ML lemma.                                  *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia Arith.
Require Import ComplexField Cmodulus CDeriv CIntegral2 CSegInt CPathIntegral
        CExpKernel CNewmanKernel CContBounded
        Chebyshev ChebyshevBound ChebyshevPsiR PsiRIntegrable TintCoV
        CIntegralD LaplaceFull NewmanLeft NewmanGLeft NewmanNearAxis
        NewmanTransform NewmanTail NewmanGN NewmanGExt.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  The cancellation on the circle, for either sign of Re z.           *)
(* ----------------------------------------------------------------- *)

Lemma kern_bound : forall (w z : C) (B T Rr : R),
  0 <= B -> 0 < Rr -> Cnorm2 z = Rr * Rr ->
  (Re z <> 0 -> Cmod w <= 2 * B * exp (- (Re z * T)) / Rabs (Re z)) ->
  Cmod (Cmul (Cmul w (cexpzt z T)) (newman_kernel Rr z)) <= 4 * B / (Rr * Rr).
Proof.
  intros w z B T Rr HB HR Hcirc Hbd.
  assert (HRR : 0 < Rr * Rr) by nra.
  rewrite !Cmod_mul, (Cmod_cexpzt z T), (Cmod_newman_kernel Rr z HR Hcirc).
  destruct (Req_dec (Re z) 0) as [Hz0 | Hne].
  - rewrite Hz0, Rabs_R0.
    replace (2 * 0 / (Rr * Rr)) with 0 by (field; lra).
    rewrite Rmult_0_r.
    unfold Rdiv; apply Rmult_le_pos; [ lra | left; apply Rinv_0_lt_compat; lra ].
  - assert (Hxa : 0 < Rabs (Re z)) by (apply Rabs_pos_lt; exact Hne).
    assert (Hex : 0 < exp (Re z * T)) by apply exp_pos.
    eapply Rle_trans.
    + apply Rmult_le_compat_r.
      * unfold Rdiv; apply Rmult_le_pos;
          [ lra | left; apply Rinv_0_lt_compat; lra ].
      * apply Rmult_le_compat_r; [ left; exact Hex | apply Hbd; exact Hne ].
    + rewrite exp_Ropp; apply Req_le; field; repeat split; lra.
Qed.

(* ----------------------------------------------------------------- *)
(*  The near-axis control (gleft_nearaxis, re-associated).             *)
(* ----------------------------------------------------------------- *)

Lemma kern_nearaxis : forall (w z : C) (delta M T Rr : R),
  0 <= delta -> 0 <= T -> Re z <= 0 -> Rabs (Re z) <= delta -> Cmod w <= M ->
  0 < Rr -> Cnorm2 z = Rr * Rr ->
  Cmod (Cmul (Cmul w (cexpzt z T)) (newman_kernel Rr z))
  <= 2 * M * delta / (Rr * Rr).
Proof.
  intros w z delta M T Rr Hd HT Hz Hzd HM HR Hcirc.
  replace (Cmul (Cmul w (cexpzt z T)) (newman_kernel Rr z))
    with (Cmul w (Cmul (cexpzt z T) (newman_kernel Rr z))) by ring.
  apply (gleft_nearaxis w z delta M T Rr Hd HT Hz Hzd HM HR Hcirc).
Qed.

(* ----------------------------------------------------------------- *)
(*  The LTN tail bound with Re z of either sign.                       *)
(* ----------------------------------------------------------------- *)

Theorem LTN_tail_ne : forall z a b Ha Hab, Re z <> 0 ->
  Cmod (LTN z a b Ha Hab)
  <= 2 * ((Kup + 1) * (exp (- (Re z * a)) - exp (- (Re z * b))) / Re z).
Proof.
  intros z a b Ha Hab Hz.
  assert (prU : Riemann_integrable (fun t => (Kup + 1) * exp (- (Re z * t))) a b)
    by (apply continuity_implies_RiemannInt;
        [ exact Hab | intros u _; apply Bexp_cont ]).
  assert (prL : Riemann_integrable (fun t => (- (Kup + 1)) * exp (- (Re z * t))) a b)
    by (apply continuity_implies_RiemannInt;
        [ exact Hab | intros u _; apply Bexp_cont ]).
  assert (HU : RiemannInt prU
               = (Kup + 1) * (exp (- (Re z * a)) - exp (- (Re z * b))) / Re z)
    by (apply exp_int_AB_ne; assumption).
  assert (HL : RiemannInt prL
               = (- (Kup + 1)) * (exp (- (Re z * a)) - exp (- (Re z * b))) / Re z)
    by (apply exp_int_AB_ne; assumption).
  assert (Hpt : forall u, a < u < b ->
            Cmod (lintN z u) <= (Kup + 1) * exp (- (Re z * u))).
  { intros u Hu.
    assert (Hu0 : 0 <= u) by lra.
    pose proof (Cmod_lintN z u) as HM.
    replace (- Re z * u) with (- (Re z * u)) in HM by ring.
    pose proof (nf_bound u Hu0) as HB.
    pose proof (exp_pos (- (Re z * u))) as Hep.
    rewrite HM; nra. }
  assert (HReU : RiemannInt (lintN_Re_int z a b Ha Hab) <= RiemannInt prU).
  { apply (RiemannInt_P19 _ prU Hab); intros x Hx.
    pose proof (Hpt x Hx) as H; pose proof (Rabs_Re_le4 (lintN z x)) as HR.
    unfold Rabs in HR; destruct (Rcase_abs (Re (lintN z x))); lra. }
  assert (HReL : RiemannInt prL <= RiemannInt (lintN_Re_int z a b Ha Hab)).
  { apply (RiemannInt_P19 prL _ Hab); intros x Hx.
    pose proof (Hpt x Hx) as H; pose proof (Rabs_Re_le4 (lintN z x)) as HR.
    unfold Rabs in HR; destruct (Rcase_abs (Re (lintN z x))); lra. }
  assert (HImU : RiemannInt (lintN_Im_int z a b Ha Hab) <= RiemannInt prU).
  { apply (RiemannInt_P19 _ prU Hab); intros x Hx.
    pose proof (Hpt x Hx) as H; pose proof (Rabs_Im_le4 (lintN z x)) as HR.
    unfold Rabs in HR; destruct (Rcase_abs (Im (lintN z x))); lra. }
  assert (HImL : RiemannInt prL <= RiemannInt (lintN_Im_int z a b Ha Hab)).
  { apply (RiemannInt_P19 prL _ Hab); intros x Hx.
    pose proof (Hpt x Hx) as H; pose proof (Rabs_Im_le4 (lintN z x)) as HR.
    unfold Rabs in HR; destruct (Rcase_abs (Im (lintN z x))); lra. }
  eapply Rle_trans; [ apply Cmod_le_ReIm4 | ].
  unfold LTN; rewrite Re_CintfD, Im_CintfD.
  rewrite HU in HReU, HImU; rewrite HL in HReL, HImL.
  unfold Rabs;
    destruct (Rcase_abs (RiemannInt (lintN_Re_int z a b Ha Hab)));
    destruct (Rcase_abs (RiemannInt (lintN_Im_int z a b Ha Hab))); lra.
Qed.

Corollary LTN_tail_left : forall z T (H0 : 0 <= 0) (HT : 0 <= T), Re z < 0 ->
  Cmod (LTN z 0 T H0 HT)
  <= 2 * (Kup + 1) * exp (- (Re z * T)) / Rabs (Re z).
Proof.
  intros z T H0 HT Hz.
  assert (Hne : Re z <> 0) by lra.
  eapply Rle_trans; [ apply LTN_tail_ne; exact Hne | ].
  rewrite Rmult_0_r, Ropp_0, exp_0, (Rabs_left (Re z) Hz).
  pose proof (exp_pos (- (Re z * T))) as He.
  pose proof Kup_pos as HK.
  apply Rmult_le_reg_r with (- Re z); [ lra | ].
  replace (2 * ((Kup + 1) * (1 - exp (- (Re z * T))) / Re z) * - Re z)
    with (2 * (Kup + 1) * (exp (- (Re z * T)) - 1)) by (field; lra).
  replace (2 * (Kup + 1) * exp (- (Re z * T)) / - Re z * - Re z)
    with (2 * (Kup + 1) * exp (- (Re z * T))) by (field; lra).
  nra.
Qed.

(* ----------------------------------------------------------------- *)
(*  The right-hand-side bound: gext minus its truncation.              *)
(* ----------------------------------------------------------------- *)

Theorem gext_LTN_bound : forall z T (H0 : 0 <= 0) (HT : 0 <= T), 0 < Re z ->
  Cmod (Cminus (gext z) (LTN z 0 T H0 HT))
  <= 2 * (Kup + 1) * exp (- (Re z * T)) / Rabs (Re z).
Proof.
  intros z T H0 HT Hz.
  rewrite (Rabs_right (Re z)) by lra.
  rewrite Cmod_min_sym, <- (gN_eq_gext z Hz).
  assert (Heq : LTN z 0 T H0 HT = LTN z 0 T (Rle_refl 0) HT) by apply LTN_irrel.
  rewrite Heq; apply LTN_gN_bound.
Qed.

(* ----------------------------------------------------------------- *)
(*  The chord: an ML lemma and a crude kernel bound.                   *)
(* ----------------------------------------------------------------- *)

Lemma seg_ML : forall (f : C -> C) (P Q : C) (M : R)
  (Hf : Ccont (fun u => Cmul (f (seg P Q u)) (seg' P Q u))),
  (forall u, 0 <= u <= 1 -> Cmod (f (seg P Q u)) <= M) ->
  Cmod (pathint (seg P Q) (seg' P Q) f Hf 0 1) <= 2 * (M * Cmod (Cminus Q P)).
Proof.
  intros f P Q M Hf Hbd; unfold pathint.
  eapply Rle_trans.
  - apply (Cintf_ML (fun u => Cmul (f (seg P Q u)) (seg' P Q u)) Hf 0 1
             (M * Cmod (Cminus Q P))); [ lra | ].
    intros u Hu; rewrite Cmod_mul; unfold seg'.
    apply Rmult_le_compat_r; [ apply Cmod_nonneg | apply Hbd; exact Hu ].
  - apply Req_le; ring.
Qed.

Lemma Cmod_newman_kernel_le : forall Rr z, z <> C0 -> 0 < Rr ->
  Cmod (newman_kernel Rr z) <= / Cmod z + Cmod z / (Rr * Rr).
Proof.
  intros Rr z Hz HR; unfold newman_kernel.
  eapply Rle_trans; [ apply Cmod_triangle | ].
  rewrite (Cmod_inv z Hz), Cmod_mul, Cmod_RtoC, Rabs_inv,
          (Rabs_pos_eq (Rr * Rr)) by nra.
  apply Req_le; unfold Rdiv; ring.
Qed.

Print Assumptions kern_bound.
Print Assumptions LTN_tail_left.
Print Assumptions gext_LTN_bound.

(* ================================================================= *)
(*  END NewmanML.v -- every pointwise estimate E6 needs, for the       *)
(*  honest transform, with the Re z = 0 case folded in.                *)
(* ================================================================= *)
