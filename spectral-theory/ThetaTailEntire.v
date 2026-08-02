(* ================================================================= *)
(*  ThetaTailEntire.v  —  the complex θ-tail integral TC and its       *)
(*  holomorphy.                                                        *)
(*                                                                    *)
(*  wkerC z u := Ψ(clamp u) · (clamp u)^{z/2−1}  is the complexified   *)
(*  Mellin kernel.  Its modulus is the real kernel wker(Re z), so the  *)
(*  real tail dominates it and CImp_abs makes TC well-defined.  This   *)
(*  file (part 1) builds the kernel, its modulus formula, and the      *)
(*  component-continuity needed downstream.  Axiom-clean.             *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra FunctionalExtensionality.
Require Import ComplexField Cmodulus CexpFull EulerFormula
        RiemannPsi MellinElem MellinTail ImproperCv1 CImproperIntegral.
Open Scope R_scope.

Definition wkerC (z : C) (u : R) : C :=
  Cmul (RtoC (Psi (clamp u))) (Cpw (clamp u) (Cminus (Cmul z (RtoC (/ 2))) C1)).

(* --- modulus of the complex kernel = the real kernel at Re z --- *)

Lemma Cmod_wkerC : forall z u, Cmod (wkerC z u) = wker (Re z) u.
Proof.
  intros z u; unfold wkerC.
  rewrite Cmod_mul, Cmod_RtoC, Cpw_mod.
  rewrite (Rabs_right (Psi (clamp u))) by (apply Rle_ge, Psi_nonneg).
  assert (HRe : Re (Cminus (Cmul z (RtoC (/ 2))) C1) = Re z / 2 - 1)
    by (unfold Cminus, Cadd, Cmul, Copp, RtoC, C1; simpl; lra).
  rewrite HRe; unfold wker; ring.
Qed.

(* --- continuity building blocks --- *)

Lemma continuity_ext : forall f g, (forall x, f x = g x) -> continuity f -> continuity g.
Proof.
  intros f g H Hf; assert (Heq : f = g) by (apply functional_extensionality; exact H).
  rewrite <- Heq; exact Hf.
Qed.

Definition cont_exp : continuity exp := derivable_continuous exp derivable_exp.

Lemma cont_lnclamp : continuity (fun u => ln (clamp u)).
Proof.
  intro u; apply (continuity_pt_comp clamp ln u).
  - apply cont_clamp.
  - apply derivable_continuous_pt; exists (/ clamp u); apply derivable_pt_lim_ln; apply clamp_pos.
Qed.

Lemma cont_Psi_clamp : continuity (fun u => Psi (clamp u)).
Proof.
  apply (continuity_ext (wker 2)).
  - intro u; unfold wker.
    replace (2 / 2 - 1) with 0 by field. unfold Rpower.
    rewrite Rmult_0_l, exp_0; ring.
  - apply cont_wker.
Qed.

(* --- the "both real components continuous" predicate and its algebra --- *)

Definition Ccont (k : R -> C) : Prop :=
  continuity (fun u => Re (k u)) /\ continuity (fun u => Im (k u)).

Lemma Ccont_const : forall c, Ccont (fun _ => c).
Proof. intro c; split; apply continuity_const; red; intros; reflexivity. Qed.

Lemma Ccont_RtoC : forall h, continuity h -> Ccont (fun u => RtoC (h u)).
Proof.
  intros h Hh; split.
  - apply (continuity_ext h); [ intro u; reflexivity | exact Hh ].
  - apply (continuity_ext (fun _ => 0));
      [ intro u; reflexivity | apply continuity_const; red; intros; reflexivity ].
Qed.

Lemma Ccont_mul : forall a b, Ccont a -> Ccont b -> Ccont (fun u => Cmul (a u) (b u)).
Proof.
  intros a b [Har Hai] [Hbr Hbi]; split.
  - apply (continuity_ext (fun u => Re (a u) * Re (b u) - Im (a u) * Im (b u))).
    + intro u; unfold Cmul; simpl; ring.
    + exact (continuity_minus _ _ (continuity_mult _ _ Har Hbr)
                                  (continuity_mult _ _ Hai Hbi)).
  - apply (continuity_ext (fun u => Re (a u) * Im (b u) + Im (a u) * Re (b u))).
    + intro u; unfold Cmul; simpl; ring.
    + exact (continuity_plus _ _ (continuity_mult _ _ Har Hbi)
                                 (continuity_mult _ _ Hai Hbr)).
Qed.

Lemma Ccont_Cexpf : forall g, Ccont g -> Ccont (fun u => Cexpf (g u)).
Proof.
  intros g [Hgr Hgi]; split.
  - apply (continuity_ext (fun u => exp (Re (g u)) * cos (Im (g u)))).
    + intro u; unfold Cexpf, Cexp, Cmul, RtoC; simpl; ring.
    + exact (continuity_mult _ _ (continuity_comp _ exp Hgr cont_exp)
                                 (continuity_comp _ cos Hgi continuity_cos)).
  - apply (continuity_ext (fun u => exp (Re (g u)) * sin (Im (g u)))).
    + intro u; unfold Cexpf, Cexp, Cmul, RtoC; simpl; ring.
    + exact (continuity_mult _ _ (continuity_comp _ exp Hgr cont_exp)
                                 (continuity_comp _ sin Hgi continuity_sin)).
Qed.

Lemma Ccont_wkerC : forall z, Ccont (wkerC z).
Proof.
  intro z; unfold wkerC.
  apply Ccont_mul.
  - apply Ccont_RtoC, cont_Psi_clamp.
  - unfold Cpw. apply Ccont_Cexpf. apply Ccont_mul.
    + apply Ccont_const.
    + apply Ccont_RtoC, cont_lnclamp.
Qed.

Definition cont_wkerC_re (z : C) : continuity (fun u => Re (wkerC z u)) := proj1 (Ccont_wkerC z).
Definition cont_wkerC_im (z : C) : continuity (fun u => Im (wkerC z u)) := proj2 (Ccont_wkerC z).

(* ================================================================= *)
(*  The complex tail integral TC z = ∫₁^∞ wkerC z.                     *)
(* ================================================================= *)

(* uniqueness of the improper-integral value (equal integrands) *)
Lemma improper_unique : forall f Hf g Hg I1 I2,
  (forall x, 1 <= x -> f x = g x) ->
  ImproperCv1 f Hf I1 -> ImproperCv1 g Hg I2 -> I1 = I2.
Proof.
  intros f Hf g Hg I1 I2 Heq HF HG.
  assert (HG1 : ImproperCv1 g Hg I1) by (apply (improper_ext f g Hf Hg I1 Heq HF)).
  set (b := fun n => 1 + INR n).
  assert (Hb1 : forall k, 1 <= b k) by (intro k; unfold b; pose proof (pos_INR k); lra).
  assert (Hbinf : cv_infty b) by apply cv_infty_1_INR.
  apply (UL_sequence (fun k => pint1 g Hg (b k)) I1 I2);
    [ apply HG1; assumption | apply HG; assumption ].
Qed.

(* the improper integral of the zero function is 0 *)
Lemma improper_zero : forall Hf, ImproperCv1 (fct_cte 0) Hf 0.
Proof.
  intros Hf b Hb1 Hbinf.
  apply (Un_cv_ext (fun _ => 0)).
  - intro k; unfold pint1.
    rewrite (RiemannInt_P5 (Hf 1 (b k)) (RiemannInt_P14 1 (b k) 0)).
    rewrite (RiemannInt_P15 (RiemannInt_P14 1 (b k) 0)); ring.
  - apply Un_cv_const.
Qed.

(* the complex kernel is real at real argument *)
Lemma wkerC_real : forall s u, wkerC (RtoC s) u = RtoC (wker s u).
Proof.
  intros s u; unfold wkerC.
  assert (HW : Cminus (Cmul (RtoC s) (RtoC (/ 2))) C1 = RtoC (s / 2 - 1))
    by (unfold Cminus, Cadd, Cmul, Copp, RtoC, C1; apply Ceq; simpl; lra).
  rewrite HW, Cpw_RtoC, <- RtoC_mul. unfold wker. f_equal; ring.
Qed.

Definition TC_sig (z : C) :
  { I : C | CImp (wkerC z) (cont_RI _ (cont_wkerC_re z)) (cont_RI _ (cont_wkerC_im z)) I } :=
  CImp_abs (wkerC z) (wker (Re z)) (wker_int (Re z)) (T (Re z))
    (cont_wkerC_re z) (cont_wkerC_im z)
    (fun x _ => Req_le _ _ (Cmod_wkerC z x)) (T_spec (Re z)).

Definition TC (z : C) : C := proj1_sig (TC_sig z).

Lemma TC_spec : forall z,
  CImp (wkerC z) (cont_RI _ (cont_wkerC_re z)) (cont_RI _ (cont_wkerC_im z)) (TC z).
Proof. intro z; exact (proj2_sig (TC_sig z)). Qed.

(* TC extends the real tail integral T *)
Lemma TC_agree : forall s, TC (RtoC s) = RtoC (T s).
Proof.
  intro s; destruct (TC_spec (RtoC s)) as [HRe HIm]; apply Ceq; simpl.
  - apply (improper_unique (fun u => Re (wkerC (RtoC s) u))
             (cont_RI _ (cont_wkerC_re (RtoC s))) (wker s) (wker_int s)
             (Re (TC (RtoC s))) (T s));
      [ intros x _; rewrite wkerC_real; reflexivity | exact HRe | exact (T_spec s) ].
  - apply (improper_unique (fun u => Im (wkerC (RtoC s) u))
             (cont_RI _ (cont_wkerC_im (RtoC s))) (fct_cte 0)
             (fun a b => RiemannInt_P14 a b 0) (Im (TC (RtoC s))) 0);
      [ intros x _; rewrite wkerC_real; reflexivity | exact HIm
      | apply improper_zero ].
Qed.

Print Assumptions Cmod_wkerC.
Print Assumptions Ccont_wkerC.
Print Assumptions TC_agree.

(* ================================================================= *)
(*  END ThetaTailEntire.v (part 2).                                   *)
(* ================================================================= *)
