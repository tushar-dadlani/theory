(* ================================================================= *)
(*  CBorelBound.v  —  Borel-Caratheodory, Steps 5 onward.              *)
(*                                                                    *)
(*  Step 3 gave  G''(0) = A/PI  with  A = INT G(arc Rr t) . wgt Rr t.   *)
(*  Steps 2 and 4 gave  INT wgt = 0  and  INT conj(G(arc)) . wgt = 0.   *)
(*                                                                    *)
(*  STEP 5 (A_shift).  Those two zeros let A be rewritten with a REAL   *)
(*  integrand shifted by an ARBITRARY constant M:                       *)
(*                                                                    *)
(*    A = INT (2 Re G(arc Rr t) - 2 M) . wgt Rr t dt.                   *)
(*                                                                    *)
(*  2 Re x = x + conj x supplies the first zero (the conj half), and    *)
(*  INT wgt = 0 the second (the constant).  Choosing M := Mf Rr later   *)
(*  makes the scalar factor NON-POSITIVE, which is the whole point:     *)
(*  its absolute value is then 2M - 2 Re G, whose integral the mean     *)
(*  value property pins down exactly.  Axiom-clean.                    *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra.
Require Import ComplexField Cmodulus Holomorphic CDeriv CIntegral2 CSegInt
        CPathIntegral RootsOfUnity CImproperIntegral
        CIntfLinear CConjIntegral CArcWeight CConjHalf
        PerronRemovable CUnifCont CPrimitiveDisk CMeanValueDisk
        CDerivUnique CCoeffTwo.
Open Scope R_scope.

Lemma RtoC_two_Re : forall w : C, RtoC (2 * Re w) = Cadd w (Cconj w).
Proof. intros [wr wi]. apply Ceq; cbn [Re Im RtoC Cadd Cconj]; ring. Qed.

Section BorelBound.

Variable G Gp : C -> C.
Variable Rr : R.
Hypothesis HR : 0 < Rr.
Hypothesis HGc : CcontC G.
Hypothesis HG : forall z, is_Cderiv G z (Gp z).

(* the three continuity facts the split needs *)
Definition HkerB : Ccont (fun t => Cmul (G (arc Rr t)) (wgt Rr t)) :=
  Ccont_G_wgt G Rr HR HGc.

Lemma HcjB : Ccont (fun t => Cmul (Cconj (G (arc Rr t))) (wgt Rr t)).
Proof.
  apply Ccont_mul.
  - apply Ccont_conj. exact (HGc (arc Rr) (Ccont_arc Rr)).
  - apply Ccont_wgt; exact HR.
Qed.

Lemma HconstB : forall c : C, Ccont (fun t => Cmul c (wgt Rr t)).
Proof. intro c. apply Ccont_scal. apply Ccont_wgt; exact HR. Qed.

(* ================================================================= *)
(*  STEP 5                                                             *)
(* ================================================================= *)
Theorem A_shift : forall (M : R)
  (Hsh : Ccont (fun t => Cmul (RtoC (2 * Re (G (arc Rr t)) - 2 * M)) (wgt Rr t))),
  Cintf (fun t => Cmul (RtoC (2 * Re (G (arc Rr t)) - 2 * M)) (wgt Rr t)) Hsh 0 (2 * PI)
  = Cintf (fun t => Cmul (G (arc Rr t)) (wgt Rr t)) HkerB 0 (2 * PI).
Proof.
  intros M Hsh.
  pose proof HcjB as Hcj.
  pose proof (HconstB (RtoC (- (2 * M)))) as H3.
  (* the inner sum: conj half + constant *)
  assert (Hin : Ccont (fun t => Cadd (Cmul (Cconj (G (arc Rr t))) (wgt Rr t))
                                     (Cmul (RtoC (- (2 * M))) (wgt Rr t))))
    by (apply Ccont_add; [ exact Hcj | exact H3 ]).
  assert (Hall : Ccont (fun t => Cadd (Cmul (G (arc Rr t)) (wgt Rr t))
                          (Cadd (Cmul (Cconj (G (arc Rr t))) (wgt Rr t))
                                (Cmul (RtoC (- (2 * M))) (wgt Rr t)))))
    by (apply Ccont_add; [ exact HkerB | exact Hin ]).
  (* pointwise split *)
  assert (Hpt : forall t,
    Cmul (RtoC (2 * Re (G (arc Rr t)) - 2 * M)) (wgt Rr t)
    = Cadd (Cmul (G (arc Rr t)) (wgt Rr t))
           (Cadd (Cmul (Cconj (G (arc Rr t))) (wgt Rr t))
                 (Cmul (RtoC (- (2 * M))) (wgt Rr t)))).
  { intro t.
    assert (Hs : RtoC (2 * Re (G (arc Rr t)) - 2 * M)
               = Cadd (Cadd (G (arc Rr t)) (Cconj (G (arc Rr t))))
                      (RtoC (- (2 * M)))).
    { rewrite <- RtoC_two_Re.
      destruct (G (arc Rr t)) as [gr gi].
      apply Ceq; cbn [Re Im RtoC Cadd]; ring. }
    rewrite Hs. ring. }
  rewrite (Cintf_ext _ _ Hsh Hall 0 (2 * PI) Hpt).
  rewrite (Cintf_add _ _ HkerB Hin Hall 0 (2 * PI)).
  rewrite (Cintf_add _ _ Hcj H3 Hin 0 (2 * PI)).
  (* the conjugate half is 0 (Step 4) *)
  rewrite (conj_half_zero G Gp Rr HR HGc HG Hcj).
  (* the constant term is 0 (Step 2) *)
  assert (Hwc : Ccont (wgt Rr)) by (apply Ccont_wgt; exact HR).
  rewrite (Cintf_scal (RtoC (- (2 * M))) (wgt Rr) Hwc H3 0 (2 * PI)).
  rewrite (Cintf_wgt_zero Rr Hwc HR).
  (* x + (0 + c*0) = x *)
  ring.
Qed.

(* ================================================================= *)
(*  STEP 7 -- the mean value property at the centre.                   *)
(*                                                                    *)
(*  This is what pins down INT Re G(arc Rr t) dt EXACTLY, and so turns  *)
(*  the Step 6 domination bound into something that actually decays.    *)
(*  Reuses CMeanValueDisk on a disk of radius Rr + 1 (G is entire, so   *)
(*  any radius does); the derivative's own regularity -- CcontC Gp and  *)
(*  uniform continuity along arcs -- comes from Gp being pointwise      *)
(*  continuous, which holo_ptcont gives from Gp holomorphic.           *)
(* ================================================================= *)
Hypothesis HGpptc : forall z eps, 0 < eps -> exists del, 0 < del /\
  forall z', Cmod (Cminus z' z) < del -> Cmod (Cminus (Gp z') (Gp z)) < eps.

Definition HGpc : CcontC Gp := ptcont_CcontC Gp HGpptc.

Theorem mean_value_G : forall (Hg : Ccont (fun t => G (arc Rr t))),
  Cintf (fun t => G (arc Rr t)) Hg 0 (2 * PI) = Cmul (RtoC (2 * PI)) (G C0).
Proof.
  intro Hg.
  assert (HGder : forall z, disk (Rr + 1) z -> is_Cderiv G z (Gp z))
    by (intros z _; apply HG).
  assert (HMconst : M G HGc Rr = M G HGc 0)
    by (apply (M_const_disk (Rr + 1) G Gp HGc HGpc HGder
                 (fun r0 eps He => arc_Fp_unif Gp HGpptc r0 eps He) Rr HR
                 ltac:(lra))).
  assert (HMval : M G HGc Rr = Cmul (RtoC (2 * PI)) (G C0))
    by (rewrite HMconst; apply meanval0_disk).
  rewrite <- HMval. unfold M, Fphi. apply Cintf_irrel.
Qed.

(* ================================================================= *)
(*  STEPS 6 and 8 -- THE BOREL-CARATHEODORY BOUND.                     *)
(*                                                                    *)
(*    Cmod (G''(0))  <=  (8 / Rr^2) . (Mf Rr - Re (G C0))              *)
(*                                                                    *)
(*  With M := Mf Rr the shifted integrand of Step 5 has a NON-POSITIVE *)
(*  scalar factor, so its modulus is exactly (2M - 2 Re G)/Rr^2.       *)
(*  Cintf_dom bounds the integral by twice the integral of that, and    *)
(*  Step 7 evaluates it: INT (2M - 2 Re G) = 4 PI (M - Re G(0)).       *)
(*  Dividing by PI (Step 3's constant) leaves 8/Rr^2 . (M - Re G(0)).  *)
(* ================================================================= *)
Variable Mf : R -> R.
Hypothesis HReG : forall z, Re (G z) <= Mf (Cmod z).

Theorem second_deriv_bound :
  Cmod (Cmul (RtoC (/ PI))
          (Cintf (fun t => Cmul (G (arc Rr t)) (wgt Rr t)) HkerB 0 (2 * PI)))
  <= 8 / Rr ^ 2 * (Mf Rr - Re (G C0)).
Proof.
  pose proof PI_RGT_0 as HPI.
  assert (HRne : Rr <> 0) by (apply Rgt_not_eq; exact HR).
  assert (HRsq : 0 < Rr ^ 2) by (apply pow_lt; exact HR).
  set (M := Mf Rr).
  (* on the circle the real part never exceeds M *)
  assert (HarcM : forall t, Re (G (arc Rr t)) <= M).
  { intro t. unfold M.
    assert (Hm : Cmod (arc Rr t) = Rr) by (apply Cmod_arc; lra).
    pose proof (HReG (arc Rr t)) as Hz. rewrite Hm in Hz. exact Hz. }
  (* the shifted integrand and its continuity *)
  assert (Hsc : Ccont (fun t => RtoC (2 * Re (G (arc Rr t)) - 2 * M))).
  { split; cbn [Re Im RtoC].
    - apply continuity_minus.
      + apply continuity_mult;
          [ apply continuity_const; intros x y; reflexivity
          | exact (proj1 (HGc (arc Rr) (Ccont_arc Rr))) ].
      + apply continuity_const; intros x y; reflexivity.
    - apply continuity_const; intros x y; reflexivity. }
  assert (Hsh : Ccont (fun t => Cmul (RtoC (2 * Re (G (arc Rr t)) - 2 * M)) (wgt Rr t)))
    by (apply Ccont_mul; [ exact Hsc | apply Ccont_wgt; exact HR ]).
  (* the dominating real function, in RInt_lin2 shape *)
  set (c1 := 2 * M / Rr ^ 2). set (c2 := - (2 / Rr ^ 2)).
  set (h1 := fun _ : R => 1). set (h2 := fun u : R => Re (G (arc Rr u))).
  assert (Hgc : continuity (fun x => c1 * h1 x + c2 * h2 x)).
  { apply continuity_plus; apply continuity_mult;
      try (apply continuity_const; intros x y; reflexivity).
    unfold h2. exact (proj1 (HGc (arc Rr) (Ccont_arc Rr))). }
  pose (prg := cont_RI _ Hgc 0 (2 * PI)).
  (* STEP 6: domination *)
  assert (Hdom : forall t, 0 <= t <= 2 * PI ->
    Cmod (Cmul (RtoC (2 * Re (G (arc Rr t)) - 2 * M)) (wgt Rr t))
    <= c1 * h1 t + c2 * h2 t).
  { intros t _. rewrite Cmod_mul, Cmod_RtoC, (Cmod_wgt Rr t HR).
    rewrite Rabs_left1 by (pose proof (HarcM t); lra).
    unfold c1, c2, h1, h2. apply Req_le. field. exact HRne. }
  pose proof (Cintf_dom _ Hsh _ 0 (2 * PI) prg ltac:(lra) Hdom) as Hbd.
  rewrite (A_shift M Hsh) in Hbd.
  (* STEP 7 evaluates the dominating integral *)
  pose (Hg := HGc (arc Rr) (Ccont_arc Rr)).
  assert (HmeanRe : RiemannInt (cont_RI _ (proj1 Hg) 0 (2 * PI))
                    = 2 * PI * Re (G C0)).
  { assert (Hm := mean_value_G Hg).
    apply (f_equal Re) in Hm. rewrite Re_Cintf in Hm.
    rewrite Hm, Re_Cmul. cbn [Re Im RtoC]. ring. }
  assert (Hone : RiemannInt (RiemannInt_P14 0 (2 * PI) 1) = 2 * PI)
    by (rewrite RiemannInt_P15; ring).
  assert (Hgint : RiemannInt prg
                  = c1 * RiemannInt (RiemannInt_P14 0 (2 * PI) 1)
                    + c2 * RiemannInt (cont_RI _ (proj1 Hg) 0 (2 * PI)))
    by (apply (RInt_lin2 c1 c2 h1 h2 0 (2 * PI)
                 (RiemannInt_P14 0 (2 * PI) 1) (cont_RI _ (proj1 Hg) 0 (2 * PI)) prg)).
  rewrite Hone, HmeanRe in Hgint.
  rewrite Hgint in Hbd.
  (* STEP 8: divide by PI *)
  rewrite Cmod_mul, Cmod_RtoC, (Rabs_right (/ PI)) by (left; apply Rinv_0_lt_compat; lra).
  apply (Rmult_le_reg_l PI); [ lra | ].
  replace (PI * (/ PI * Cmod (Cintf (fun t => Cmul (G (arc Rr t)) (wgt Rr t)) HkerB 0 (2 * PI))))
    with (Cmod (Cintf (fun t => Cmul (G (arc Rr t)) (wgt Rr t)) HkerB 0 (2 * PI)))
    by (field; lra).
  eapply Rle_trans; [ exact Hbd | ].
  unfold c1, c2, M. apply Req_le. field. lra.
Qed.

End BorelBound.

Print Assumptions A_shift.
Print Assumptions second_deriv_bound.

(* ================================================================= *)
(*  STEP 9 -- the limit Rr -> oo kills the second derivative at 0.     *)
(*                                                                    *)
(*  The Step 8 bound holds for EVERY radius, and Mf Rr = o(Rr^2) while *)
(*  Re (G C0) is a constant, so the right-hand side can be driven      *)
(*  below any eps.  Hence Cmod (G''(0)) = 0.                           *)
(*                                                                    *)
(*  The radius is chosen by the same Rmax-threshold pattern already    *)
(*  used in COrderOne.order_one_step: big enough for the o(r^2)        *)
(*  hypothesis to bite, and big enough that r^2 >= r absorbs the       *)
(*  constant Re (G C0).                                                *)
(* ================================================================= *)
Theorem second_deriv_zero : forall (G Gp : C -> C) (Mf : R -> R) (d : C),
  CcontC G ->
  (forall z eps, 0 < eps -> exists del, 0 < del /\
     forall z', Cmod (Cminus z' z) < del -> Cmod (Cminus (G z') (G z)) < eps) ->
  (forall z, is_Cderiv G z (Gp z)) ->
  (forall z eps, 0 < eps -> exists del, 0 < del /\
     forall z', Cmod (Cminus z' z) < del -> Cmod (Cminus (Gp z') (Gp z)) < eps) ->
  (forall z, Re (G z) <= Mf (Cmod z)) ->
  (forall eps, 0 < eps -> exists R0, 0 < R0 /\
     forall r, R0 <= r -> Mf r <= eps * r ^ 2) ->
  is_Cderiv Gp C0 d ->
  d = C0.
Proof.
  intros G Gp Mf d HGc HGptc HG HGpptc HReG Hsub Hd.
  set (K := Re (G C0)).
  (* the Step 8 bound, transported onto the fixed derivative value d *)
  assert (Hbound : forall Rr, 0 < Rr -> Cmod d <= 8 / Rr ^ 2 * (Mf Rr - K)).
  { intros Rr HR.
    assert (Hval : d = Cmul (RtoC (/ PI))
                       (Cintf (fun t => Cmul (G (arc Rr t)) (wgt Rr t))
                          (HkerB G Rr HR HGc) 0 (2 * PI))).
    { apply (is_Cderiv_unique Gp C0 d _ Hd).
      exact (second_deriv_circle G Gp Rr HR HGptc HG (HkerB G Rr HR HGc)). }
    rewrite Hval.
    exact (second_deriv_bound G Gp Rr HR HGc HG HGpptc Mf HReG). }
  (* drive the bound below every eps *)
  assert (Hsmall : forall eps, 0 < eps -> Cmod d <= eps).
  { intros eps Heps.
    destruct (Hsub (eps / 16) ltac:(lra)) as [R0 [HR0 HR0b]].
    set (Rr := Rmax (Rmax R0 1) (16 * Rabs K / eps + 1)).
    assert (HK : - K <= Rabs K)
      by (rewrite <- Rabs_Ropp; apply Rle_abs).
    assert (HKpos : 0 <= Rabs K) by apply Rabs_pos.
    assert (Hr0 : R0 <= Rr)
      by (unfold Rr; apply Rle_trans with (Rmax R0 1);
          [ apply Rmax_l | apply Rmax_l ]).
    assert (Hr1 : 1 <= Rr)
      by (unfold Rr; apply Rle_trans with (Rmax R0 1);
          [ apply Rmax_r | apply Rmax_l ]).
    assert (Hr2 : 16 * Rabs K / eps + 1 <= Rr) by (unfold Rr; apply Rmax_r).
    assert (HRpos : 0 < Rr) by lra.
    assert (Hsq : Rr <= Rr ^ 2) by nra.
    (* the o(r^2) hypothesis bites *)
    assert (HMf : Mf Rr <= eps / 16 * Rr ^ 2) by (apply HR0b; exact Hr0).
    (* and r^2 >= r absorbs the constant K *)
    assert (HKabs : - K <= eps / 16 * Rr ^ 2).
    { apply Rle_trans with (Rabs K); [ exact HK | ].
      apply (Rmult_le_reg_l (16 / eps)); [ apply Rdiv_lt_0_compat; lra | ].
      replace (16 / eps * (eps / 16 * Rr ^ 2)) with (Rr ^ 2) by (field; lra).
      replace (16 / eps * Rabs K) with (16 * Rabs K / eps) by (field; lra).
      lra. }
    assert (Hnum : Mf Rr - K <= eps / 8 * Rr ^ 2) by lra.
    apply Rle_trans with (8 / Rr ^ 2 * (Mf Rr - K)); [ apply Hbound; exact HRpos | ].
    assert (HRsq : 0 < Rr ^ 2) by nra.
    apply Rle_trans with (8 / Rr ^ 2 * (eps / 8 * Rr ^ 2)).
    - apply Rmult_le_compat_l; [ | exact Hnum ].
      apply Rle_mult_inv_pos; lra.
    - apply Req_le. field. lra. }
  (* a nonnegative real below every eps is 0 *)
  assert (Hzero : Cmod d = 0).
  { destruct (Cmod_nonneg d) as [Hlt | Heq]; [ | symmetry; exact Heq ].
    exfalso. pose proof (Hsmall (Cmod d / 2) ltac:(lra)). lra. }
  apply (proj1 (Cmod0 d)). exact Hzero.
Qed.

Print Assumptions second_deriv_zero.
Print Assumptions mean_value_G.
