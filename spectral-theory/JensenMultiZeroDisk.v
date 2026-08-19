(* ================================================================= *)
(*  JensenMultiZeroDisk.v  —  Hadamard keystone, brick 4 on a DISK.     *)
(*                                                                    *)
(*  jensen_multi_zero (JensenMultiZero.v) demands the cofactor G be     *)
(*  ENTIRE and zero-free.  The cofactor that actually shows up in       *)
(*  n(r) = O(r) is  G_R = xi / P_R  (P_R the finite product over the    *)
(*  zeros inside |z| < R): it is zero-free only on a DISK, never on all *)
(*  of C.  ZeroFreeMVPDisk.zero_free_MVP_disk was built precisely to    *)
(*  supply the base case under disk hypotheses; this file re-plumbs the *)
(*  zero-peeling induction on top of it, so that bridge becomes         *)
(*  load-bearing.                                                      *)
(*                                                                    *)
(*    jensen_multi_zero_D : G holomorphic and zero-free on Cmod z < R2, *)
(*    Jensen circle radius 0 < Rr < R2, zeros l all with |rho| < Rr =>  *)
(*      INT_0^{2PI} ln|prodfac l . G| (Rr e^{it}) dt                    *)
(*        = 2 PI . (#l . ln Rr + ln|G(0)|).                            *)
(*                                                                    *)
(*  The peeling step is UNCHANGED from the entire case (it only touches *)
(*  the factors (z - rho)); everything reusable -- prodfac,             *)
(*  arc_minus_ne0, prodfac_arc_ccont, prodfac_arc_ne0, ln_cmod_int,     *)
(*  cmod_pos, Ccont_sub -- is imported from JensenMultiZero rather than *)
(*  re-derived.  Two things change:                                    *)
(*    * the base case calls zero_free_MVP_disk (which needs NO HcontG   *)
(*      -- the gcut machinery builds that continuity internally), so    *)
(*      the disk version has one FEWER hypothesis than the entire one;  *)
(*    * G o arc is continuous by holo_ccont_path_dom, the domain-       *)
(*      restricted twin of CHoloCcontC.holo_CcontC (whose proof uses    *)
(*      global holomorphy in exactly one place).                       *)
(*  Axiom-clean.                                                        *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra List FunctionalExtensionality.
Require Import ComplexField Cmodulus Holomorphic CPathIntegral CSegInt
        CIntegral2 CDerivConst CSeries CDeriv CHoloCalculus CHoloCcontC
        JensenZeroFactor JensenZeroFactorC ZeroFreeMVP JensenMultiZero
        ZeroFreeMVPDisk.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  A.  holo_CcontC, domain-restricted.                               *)
(*                                                                    *)
(*  CHoloCcontC.holo_CcontC proves F o g continuous for every          *)
(*  continuous path g, from holomorphy of F EVERYWHERE.  Holomorphy is *)
(*  used at exactly one point of that proof -- at g u0 -- so it is     *)
(*  enough that the path stays inside a set D on which F is            *)
(*  holomorphic.  (is_Cderiv_cont gives honest pointwise continuity at *)
(*  each point of D with no constraint on where the nearby z' land, so *)
(*  no delta has to be shrunk to keep inside D.)                       *)
(* ----------------------------------------------------------------- *)
Lemma holo_ccont_path_dom : forall (F : C -> C) (D : C -> Prop) (g : R -> C),
  (forall z, D z -> exists d, is_Cderiv F z d) ->
  (forall u, D (g u)) -> Ccont g -> Ccont (fun u => F (g u)).
Proof.
  intros F D g Hhol HD Hg. destruct Hg as [HgRe HgIm].
  assert (comp : forall (proj : C -> R),
            (forall w, Rabs (proj w) <= Cmod w) ->
            (forall x y, proj (Cminus x y) = proj x - proj y) ->
            continuity (fun u => proj (F (g u)))).
  { intros proj Hproj Hpmin u0.
    unfold continuity_pt, continue_in, limit1_in.
    cbn [dist R_met]. unfold R_dist. cbv beta. intros eps Heps.
    destruct (Hhol (g u0) (HD u0)) as [d Hd].
    destruct (is_Cderiv_cont F (g u0) d Hd eps Heps) as [eta [Heta HF]].
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
    specialize (HF (Cminus (g x) (g u0)) Hcm).
    replace (Cadd (g u0) (Cminus (g x) (g u0))) with (g x) in HF by ring.
    change (dist R_met (proj (F (g x))) (proj (F (g u0))) < eps)
      with (Rabs (proj (F (g x)) - proj (F (g u0))) < eps).
    rewrite <- Hpmin.
    eapply Rle_lt_trans; [ apply Hproj | exact HF ]. }
  split; [ apply (comp Re Cmod_Re_le ReCm) | apply (comp Im Cmod_Im_le ImCm) ].
Qed.

(* the instance we need: the Jensen circle sits strictly inside the disk *)
Lemma holo_arc_ccont_disk : forall (G : C -> C) (R2 Rr : R),
  0 < Rr -> Rr < R2 ->
  (forall z, Cmod z < R2 -> exists d, is_Cderiv G z d) ->
  Ccont (fun t => G (arc Rr t)).
Proof.
  intros G R2 Rr HR HRR2 Hhol.
  apply (holo_ccont_path_dom G (fun z => Cmod z < R2) (arc Rr) Hhol).
  - intro u. rewrite (Cmod_arc Rr u (Rlt_le 0 Rr HR)). exact HRR2.
  - apply Ccont_arc.
Qed.

(* ----------------------------------------------------------------- *)
(*  B.  Jensen's formula for finitely many zeros, DISK cofactor.      *)
(* ----------------------------------------------------------------- *)
Theorem jensen_multi_zero_D : forall (G Gp : C -> C) (R2 Rr : R)
  (HR : 0 < Rr) (HRR2 : Rr < R2)
  (HGhol : forall z, Cmod z < R2 -> is_Cderiv G z (Gp z))
  (HGphol : forall z, Cmod z < R2 -> exists d, is_Cderiv Gp z d)
  (HGne0 : forall z, Cmod z < R2 -> G z <> C0)
  (l : list C)
  (Hin : forall rho, In rho l -> Cmod rho < Rr)
  (pr : Riemann_integrable
          (fun t => ln (Cmod (Cmul (prodfac l (arc Rr t)) (G (arc Rr t))))) 0 (2 * PI)),
  RiemannInt pr = 2 * PI * (INR (length l) * ln Rr + ln (Cmod (G C0))).
Proof.
  intros G Gp R2 Rr HR HRR2 HGhol HGphol HGne0.
  assert (HR2 : 0 < R2) by lra.
  assert (HGex : forall z, Cmod z < R2 -> exists d, is_Cderiv G z d)
    by (intros z Hz; exists (Gp z); apply HGhol; exact Hz).
  assert (Harcin : forall t, Cmod (arc Rr t) < R2)
    by (intro t; rewrite (Cmod_arc Rr t (Rlt_le 0 Rr HR)); exact HRR2).
  assert (HC0in : Cmod C0 < R2)
    by (rewrite (proj2 (Cmod0 C0) eq_refl); exact HR2).
  assert (HGarc : Ccont (fun t => G (arc Rr t)))
    by (apply (holo_arc_ccont_disk G R2 Rr HR HRR2 HGex)).
  assert (Hab : (0:R) <= 2 * PI) by (pose proof PI_RGT_0; lra).
  induction l as [| rho l' IH]; intros Hin pr.
  - (* base: F = G, on the DISK *)
    pose (prG := ln_cmod_int (fun t => G (arc Rr t)) HGarc
                   (fun t => HGne0 (arc Rr t) (Harcin t))).
    assert (Hpt0 : forall x, 0 < x < 2 * PI ->
               ln (Cmod (Cmul (prodfac nil (arc Rr x)) (G (arc Rr x)))) = ln (Cmod (G (arc Rr x))))
      by (intros x _; simpl prodfac;
          replace (Cmul C1 (G (arc Rr x))) with (G (arc Rr x)) by ring; reflexivity).
    assert (Hsplit : RiemannInt pr = RiemannInt prG)
      by (apply RiemannInt_P18; [ exact Hab | exact Hpt0 ]).
    rewrite Hsplit, (zero_free_MVP_disk G Gp R2 Rr HR HRR2 HGhol HGphol HGne0 prG).
    simpl length. replace (INR 0) with 0 by reflexivity. ring.
  - (* step: peel the complex zero rho -- identical to the entire case *)
    assert (Hinl' : forall r, In r l' -> Cmod r < Rr) by (intros r Hr; apply Hin; right; exact Hr).
    assert (Hrho : Cmod rho < Rr) by (apply Hin; left; reflexivity).
    pose (prfac := ln_cmod_int (fun t => Cminus (arc Rr t) rho)
                     (Ccont_sub _ _ (Ccont_arc Rr) (Ccont_const rho))
                     (fun t => arc_minus_ne0 Rr rho t HR Hrho)).
    pose (prrest := ln_cmod_int (fun t => Cmul (prodfac l' (arc Rr t)) (G (arc Rr t)))
                      (Ccont_mul _ _ (prodfac_arc_ccont Rr l') HGarc)
                      (fun t => Cmul_ne0 _ _ (prodfac_arc_ne0 Rr l' HR Hinl' t)
                                  (HGne0 (arc Rr t) (Harcin t)))).
    assert (Hpt : forall t,
               ln (Cmod (Cmul (prodfac (rho :: l') (arc Rr t)) (G (arc Rr t))))
               = ln (Cmod (Cminus (arc Rr t) rho))
                 + ln (Cmod (Cmul (prodfac l' (arc Rr t)) (G (arc Rr t))))).
    { intro t. simpl prodfac.
      set (A := Cminus (arc Rr t) rho). set (B := prodfac l' (arc Rr t)). set (C := G (arc Rr t)).
      assert (HAp : 0 < Cmod A) by (apply cmod_pos; apply arc_minus_ne0; assumption).
      assert (HBCp : 0 < Cmod (Cmul B C))
        by (apply cmod_pos; apply Cmul_ne0;
            [ apply prodfac_arc_ne0; assumption | apply HGne0; apply Harcin ]).
      replace (Cmod (Cmul (Cmul A B) C)) with (Cmod A * Cmod (Cmul B C))
        by (rewrite !Cmod_mul; ring).
      apply ln_mult; assumption. }
    pose (prsum := RiemannInt_P10 1 prfac prrest).
    assert (Hext : forall x, 0 < x < 2 * PI ->
               ln (Cmod (Cmul (prodfac (rho :: l') (arc Rr x)) (G (arc Rr x))))
               = ln (Cmod (Cminus (arc Rr x) rho))
                 + 1 * ln (Cmod (Cmul (prodfac l' (arc Rr x)) (G (arc Rr x)))))
      by (intros x _; rewrite Hpt; ring).
    assert (Hsplit : RiemannInt pr = RiemannInt prsum)
      by (apply RiemannInt_P18; [ exact Hab | exact Hext ]).
    assert (H13 : RiemannInt prsum = RiemannInt prfac + 1 * RiemannInt prrest)
      by apply RiemannInt_P13.
    rewrite Hsplit, H13.
    rewrite (jensen_zero_factor_C Rr rho HR Hrho prfac).
    rewrite (IH Hinl' prrest).
    simpl length. rewrite S_INR. ring.
Qed.

Print Assumptions jensen_multi_zero_D.
