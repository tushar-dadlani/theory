(* ================================================================= *)
(*  JensenMultiZero.v  —  Hadamard keystone, brick 4 (step 4b):         *)
(*  Jensen's formula for an entire function with FINITELY MANY zeros.   *)
(*                                                                    *)
(*  For F(z) = (prod_{rho in l} (z - rho)) . G(z), G entire zero-free,  *)
(*  all |rho| < Rr:                                                    *)
(*                                                                    *)
(*    (1/2PI) INT_0^{2PI} ln|F(Rr e^{it})| dt                          *)
(*        = ln|G(0)| + (#l) . ln Rr = ln|F(0)| + sum_rho ln(Rr/|rho|). *)
(*                                                                    *)
(*  Proved by induction on the zero list l, peeling one complex zero   *)
(*  per step (JensenZeroFactorC.jensen_zero_factor_C) down to the       *)
(*  zero-free base (ZeroFreeMVP.zero_free_MVP).  The `pr` integrability *)
(*  hypotheses that pervade the Jensen lemmas are here DISCHARGED by    *)
(*  ln_cmod_int (continuity of ln|.| of a non-vanishing path).         *)
(*                                                                    *)
(*  This is the finite-zero Hadamard/Jensen count; the last step of    *)
(*  n(r)=O(r) is to bound the RHS by the order-1 growth of xi.          *)
(*  Axiom-clean.                                                        *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra List FunctionalExtensionality.
Require Import ComplexField Cmodulus Holomorphic CPathIntegral CSegInt
        CIntegral2 CDerivConst CSeries CDeriv PerronEdge CHoloCcontC
        JensenZeroFactor JensenZeroFactorC ZeroFreeMVP.
Open Scope R_scope.

(* --- integrability of ln|h| for a continuous non-vanishing path --- *)
Lemma cmod_pos : forall x, x <> C0 -> 0 < Cmod x.
Proof.
  intros x Hx. destruct (Cmod_nonneg x) as [H | H]; [ exact H | ].
  exfalso; apply Hx; apply (proj1 (Cmod0 x)); symmetry; exact H.
Qed.

Lemma ln_cmod_int : forall (h : R -> C),
  Ccont h -> (forall t, h t <> C0) ->
  Riemann_integrable (fun t => ln (Cmod (h t))) 0 (2 * PI).
Proof.
  intros h Hc Hne. apply continuity_implies_RiemannInt.
  - pose proof PI_RGT_0; lra.
  - intros t _. apply (continuity_pt_comp (fun s => Cmod (h s)) ln).
    + apply Ccont_Cmod; exact Hc.
    + apply derivable_continuous_pt. exists (/ Cmod (h t)).
      apply derivable_pt_lim_ln. apply cmod_pos; apply Hne.
Qed.

(* --- Ccont of a difference, and the product function --- *)
Lemma Ccont_sub : forall f g, Ccont f -> Ccont g -> Ccont (fun u => Cminus (f u) (g u)).
Proof.
  intros f g [Hf1 Hf2] [Hg1 Hg2]; split; cbv beta.
  - replace (fun u => Re (Cminus (f u) (g u))) with (fun u => Re (f u) - Re (g u))
      by (apply functional_extensionality; intro u; symmetry; apply ReCm).
    apply continuity_minus; assumption.
  - replace (fun u => Im (Cminus (f u) (g u))) with (fun u => Im (f u) - Im (g u))
      by (apply functional_extensionality; intro u; symmetry; apply ImCm).
    apply continuity_minus; assumption.
Qed.

Fixpoint prodfac (l : list C) (z : C) : C :=
  match l with
  | nil => C1
  | rho :: l' => Cmul (Cminus z rho) (prodfac l' z)
  end.

Lemma arc_minus_ne0 : forall Rr rho t, 0 < Rr -> Cmod rho < Rr -> Cminus (arc Rr t) rho <> C0.
Proof.
  intros Rr rho t HR Hlt Hc.
  assert (Harc : arc Rr t = rho)
    by (replace (arc Rr t) with (Cadd (Cminus (arc Rr t) rho) rho) by ring; rewrite Hc; ring).
  assert (Hm : Cmod (arc Rr t) = Rr) by (apply Cmod_arc; lra).
  rewrite Harc in Hm. lra.
Qed.

Lemma prodfac_arc_ccont : forall Rr l, Ccont (fun t => prodfac l (arc Rr t)).
Proof.
  intros Rr l; induction l as [| rho l' IH]; simpl.
  - apply Ccont_const.
  - apply Ccont_mul; [ apply Ccont_sub; [ apply Ccont_arc | apply Ccont_const ] | exact IH ].
Qed.

Lemma prodfac_arc_ne0 : forall Rr l, 0 < Rr ->
  (forall rho, In rho l -> Cmod rho < Rr) ->
  forall t, prodfac l (arc Rr t) <> C0.
Proof.
  intros Rr l HR; induction l as [| rho l' IH]; intros Hin t; simpl.
  - exact C1_neq_C0.
  - apply Cmul_ne0.
    + apply arc_minus_ne0; [ exact HR | apply Hin; left; reflexivity ].
    + apply IH; intros r Hr; apply Hin; right; exact Hr.
Qed.

(* --- Jensen's formula for finitely many complex zeros --- *)
Theorem jensen_multi_zero : forall (G Gp : C -> C) (Rr : R)
  (HGhol : forall z, is_Cderiv G z (Gp z))
  (HGphol : forall z, exists d, is_Cderiv Gp z d)
  (HGne0 : forall z, G z <> C0)
  (HcontG : CcontC (fun w => Cmul (Gp w) (Cinv (G w))))
  (HR : 0 < Rr) (l : list C)
  (Hin : forall rho, In rho l -> Cmod rho < Rr)
  (pr : Riemann_integrable
          (fun t => ln (Cmod (Cmul (prodfac l (arc Rr t)) (G (arc Rr t))))) 0 (2 * PI)),
  RiemannInt pr = 2 * PI * (INR (length l) * ln Rr + ln (Cmod (G C0))).
Proof.
  intros G Gp Rr HGhol HGphol HGne0 HcontG HR.
  assert (HGex : forall z, exists d, is_Cderiv G z d)
    by (intro z; exists (Gp z); apply HGhol).
  assert (HGarc : Ccont (fun t => G (arc Rr t)))
    by (apply (holo_CcontC G HGex (arc Rr)); apply Ccont_arc).
  assert (Hab : (0:R) <= 2 * PI) by (pose proof PI_RGT_0; lra).
  induction l as [| rho l' IH]; intros Hin pr.
  - (* base: F = G *)
    pose (prG := ln_cmod_int (fun t => G (arc Rr t)) HGarc (fun t => HGne0 (arc Rr t))).
    assert (Hpt0 : forall x, 0 < x < 2 * PI ->
               ln (Cmod (Cmul (prodfac nil (arc Rr x)) (G (arc Rr x)))) = ln (Cmod (G (arc Rr x))))
      by (intros x _; simpl prodfac;
          replace (Cmul C1 (G (arc Rr x))) with (G (arc Rr x)) by ring; reflexivity).
    assert (Hsplit : RiemannInt pr = RiemannInt prG)
      by (apply RiemannInt_P18; [ exact Hab | exact Hpt0 ]).
    rewrite Hsplit, (zero_free_MVP G Gp Rr HGhol HGphol HGne0 HcontG HR prG).
    simpl length. replace (INR 0) with 0 by reflexivity. ring.
  - (* step: peel the complex zero rho *)
    assert (Hinl' : forall r, In r l' -> Cmod r < Rr) by (intros r Hr; apply Hin; right; exact Hr).
    assert (Hrho : Cmod rho < Rr) by (apply Hin; left; reflexivity).
    pose (prfac := ln_cmod_int (fun t => Cminus (arc Rr t) rho)
                     (Ccont_sub _ _ (Ccont_arc Rr) (Ccont_const rho))
                     (fun t => arc_minus_ne0 Rr rho t HR Hrho)).
    pose (prrest := ln_cmod_int (fun t => Cmul (prodfac l' (arc Rr t)) (G (arc Rr t)))
                      (Ccont_mul _ _ (prodfac_arc_ccont Rr l') HGarc)
                      (fun t => Cmul_ne0 _ _ (prodfac_arc_ne0 Rr l' HR Hinl' t) (HGne0 (arc Rr t)))).
    assert (Hpt : forall t,
               ln (Cmod (Cmul (prodfac (rho :: l') (arc Rr t)) (G (arc Rr t))))
               = ln (Cmod (Cminus (arc Rr t) rho))
                 + ln (Cmod (Cmul (prodfac l' (arc Rr t)) (G (arc Rr t))))).
    { intro t. simpl prodfac.
      set (A := Cminus (arc Rr t) rho). set (B := prodfac l' (arc Rr t)). set (C := G (arc Rr t)).
      assert (HAp : 0 < Cmod A) by (apply cmod_pos; apply arc_minus_ne0; assumption).
      assert (HBCp : 0 < Cmod (Cmul B C))
        by (apply cmod_pos; apply Cmul_ne0;
            [ apply prodfac_arc_ne0; assumption | apply HGne0 ]).
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

Print Assumptions jensen_multi_zero.
