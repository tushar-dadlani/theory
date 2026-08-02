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

(* ================================================================= *)
(*  Group 1: convergence of the ln-weighted tail ∫ (ln u)^k · wker s.  *)
(* ================================================================= *)

Lemma ln_clamp_nonneg : forall u, 0 <= ln (clamp u).
Proof.
  intro u; pose proof (clamp_ge1 u) as H1.
  rewrite <- ln_1; destruct (Rle_lt_or_eq_dec 1 (clamp u) H1) as [Hlt | Heq].
  - left; apply ln_increasing; [ lra | exact Hlt ].
  - rewrite <- Heq; apply Rle_refl.
Qed.

Lemma ln_clamp_le : forall u, ln (clamp u) <= clamp u.
Proof.
  intro u; pose proof (clamp_pos u) as Hp.
  destruct (Req_dec (ln (clamp u)) 0) as [H0 | Hne].
  - rewrite H0; left; exact Hp.
  - pose proof (exp_ineq1 (ln (clamp u)) Hne) as Hi.
    rewrite exp_ln in Hi by exact Hp; lra.
Qed.

Lemma cont_pow : forall g k, continuity g -> continuity (fun u => (g u) ^ k).
Proof.
  intros g k Hg; induction k as [| k IH].
  - apply (continuity_ext (fun _ => 1));
      [ intro u; reflexivity | apply continuity_const; red; intros; reflexivity ].
  - apply (continuity_ext (fun u => g u * (g u) ^ k));
      [ intro u; reflexivity | exact (continuity_mult _ _ Hg IH) ].
Qed.

Lemma cont_lnk_wker : forall s k, continuity (fun u => (ln (clamp u)) ^ k * wker s u).
Proof.
  intros s k; apply (continuity_mult (fun u => (ln (clamp u)) ^ k) (wker s)).
  - apply cont_pow, cont_lnclamp.
  - apply cont_wker.
Qed.

Lemma lnk_wker_le : forall s k u, 1 <= u ->
  (ln (clamp u)) ^ k * wker s u <= wker (s + 2 * INR k) u.
Proof.
  intros s k u Hu.
  assert (Hpow : (ln (clamp u)) ^ k <= (clamp u) ^ k)
    by (apply pow_incr; split; [ apply ln_clamp_nonneg | apply ln_clamp_le ]).
  apply Rle_trans with ((clamp u) ^ k * wker s u).
  - apply Rmult_le_compat_r; [ apply wker_nonneg | exact Hpow ].
  - unfold wker.
    rewrite <- Rpower_pow by apply clamp_pos.
    rewrite <- Rmult_assoc, <- Rpower_plus.
    replace (INR k + (s / 2 - 1)) with ((s + 2 * INR k) / 2 - 1) by field.
    reflexivity.
Qed.

Lemma lnk_wker_conv : forall s k,
  { I | ImproperCv1 (fun u => (ln (clamp u)) ^ k * wker s u)
          (cont_RI _ (cont_lnk_wker s k)) I }.
Proof.
  intros s k; apply improper_bounded_cv.
  - intros x _; apply Rmult_le_pos;
      [ apply pow_le; apply ln_clamp_nonneg | apply wker_nonneg ].
  - exists (T (s + 2 * INR k)); intros A HA.
    apply Rle_trans with (pint1 (wker (s + 2 * INR k)) (wker_int (s + 2 * INR k)) A).
    + unfold pint1; apply RiemannInt_P19;
        [ exact HA | intros x Hx; apply lnk_wker_le; lra ].
    + apply pint1_le_improper;
        [ apply T_spec | intros x _; apply wker_nonneg | exact HA ].
Qed.

(* ================================================================= *)
(*  Group 2: the derivative integrand dkerC and its integral dTC.      *)
(* ================================================================= *)

Definition dkerC (z : C) (u : R) : C := Cmul (RtoC (ln (clamp u) / 2)) (wkerC z u).

Lemma Cmod_dkerC : forall z u, Cmod (dkerC z u) = ln (clamp u) / 2 * wker (Re z) u.
Proof.
  intros z u; unfold dkerC.
  rewrite Cmod_mul, Cmod_RtoC, Cmod_wkerC.
  rewrite (Rabs_right (ln (clamp u) / 2)); [ reflexivity | ].
  apply Rle_ge; unfold Rdiv; apply Rmult_le_pos; [ apply ln_clamp_nonneg | lra ].
Qed.

Lemma Ccont_dkerC : forall z, Ccont (dkerC z).
Proof.
  intro z; unfold dkerC; apply Ccont_mul; [ | apply Ccont_wkerC ].
  apply Ccont_RtoC.
  apply (continuity_mult (fun u => ln (clamp u)) (fun _ => / 2));
    [ apply cont_lnclamp | apply continuity_const; red; intros; reflexivity ].
Qed.

Definition cont_dkerC_re (z : C) : continuity (fun u => Re (dkerC z u)) := proj1 (Ccont_dkerC z).
Definition cont_dkerC_im (z : C) : continuity (fun u => Im (dkerC z u)) := proj2 (Ccont_dkerC z).

Definition dTC_dom (z : C) (u : R) : R := ln (clamp u) / 2 * wker (Re z) u.

Lemma cont_dTC_dom : forall z, continuity (dTC_dom z).
Proof.
  intro z; unfold dTC_dom.
  apply (continuity_mult (fun u => ln (clamp u) / 2) (wker (Re z))); [ | apply cont_wker ].
  apply (continuity_mult (fun u => ln (clamp u)) (fun _ => / 2));
    [ apply cont_lnclamp | apply continuity_const; red; intros; reflexivity ].
Qed.

Lemma dTC_dom_conv : forall z,
  { I | ImproperCv1 (dTC_dom z) (cont_RI _ (cont_dTC_dom z)) I }.
Proof.
  intro z; destruct (lnk_wker_conv (Re z) 1) as [I1 HI1].
  exists (/ 2 * I1).
  apply (improper_ext (fun u => / 2 * ((ln (clamp u)) ^ 1 * wker (Re z) u)) (dTC_dom z)
           (fun a b => RI_scal (fun u => (ln (clamp u)) ^ 1 * wker (Re z) u) (/ 2) a b
                          (cont_RI _ (cont_lnk_wker (Re z) 1) a b))
           (cont_RI _ (cont_dTC_dom z)) (/ 2 * I1)).
  - intros x _; unfold dTC_dom; rewrite pow_1; field.
  - apply (improper_scal (fun u => (ln (clamp u)) ^ 1 * wker (Re z) u) (/ 2)
             (cont_RI _ (cont_lnk_wker (Re z) 1)) _ I1 HI1).
Qed.

Definition dTC_sig (z : C) :
  { I : C | CImp (dkerC z) (cont_RI _ (cont_dkerC_re z)) (cont_RI _ (cont_dkerC_im z)) I } :=
  CImp_abs (dkerC z) (dTC_dom z) (cont_RI _ (cont_dTC_dom z)) (proj1_sig (dTC_dom_conv z))
    (cont_dkerC_re z) (cont_dkerC_im z)
    (fun x _ => Req_le _ _ (Cmod_dkerC z x)) (proj2_sig (dTC_dom_conv z)).

Definition dTC (z : C) : C := proj1_sig (dTC_sig z).

Lemma dTC_spec : forall z,
  CImp (dkerC z) (cont_RI _ (cont_dkerC_re z)) (cont_RI _ (cont_dkerC_im z)) (dTC z).
Proof. intro z; exact (proj2_sig (dTC_sig z)). Qed.

(* ================================================================= *)
(*  Group 3: the multiplicative-shift algebra.                         *)
(* ================================================================= *)

Definition wshift (h : C) (u : R) : C := Cmul (Cmul h (RtoC (/ 2))) (RtoC (ln (clamp u))).

Lemma wkerC_shift : forall z h u,
  wkerC (Cadd z h) u = Cmul (wkerC z u) (Cexpf (wshift h u)).
Proof.
  intros z h u; unfold wkerC, wshift.
  assert (HE : Cminus (Cmul (Cadd z h) (RtoC (/ 2))) C1
             = Cadd (Cminus (Cmul z (RtoC (/ 2))) C1) (Cmul h (RtoC (/ 2)))) by ring.
  rewrite HE, Cpw_split. unfold Cpw. ring.
Qed.

Lemma Cmod_wshift : forall h u, Cmod (wshift h u) = Cmod h * (ln (clamp u) / 2).
Proof.
  intros h u; unfold wshift.
  rewrite !Cmod_mul, !Cmod_RtoC.
  rewrite (Rabs_right (/ 2)) by lra.
  rewrite (Rabs_right (ln (clamp u))) by (apply Rle_ge, ln_clamp_nonneg).
  field.
Qed.

Definition remC (z h : C) (u : R) : C :=
  Cminus (Cminus (wkerC (Cadd z h) u) (wkerC z u)) (Cmul h (dkerC z u)).

Lemma remC_eq : forall z h u,
  remC z h u = Cmul (wkerC z u) (Cminus (Cminus (Cexpf (wshift h u)) C1) (wshift h u)).
Proof.
  intros z h u; unfold remC, dkerC.
  rewrite wkerC_shift.
  assert (Hlin : Cmul h (Cmul (RtoC (ln (clamp u) / 2)) (wkerC z u))
               = Cmul (wkerC z u) (wshift h u)).
  { unfold wshift.
    replace (RtoC (ln (clamp u) / 2)) with (Cmul (RtoC (/ 2)) (RtoC (ln (clamp u))))
      by (rewrite <- RtoC_mul; f_equal; field).
    ring. }
  rewrite Hlin. ring.
Qed.

Print Assumptions Cmod_wkerC.
Print Assumptions TC_agree.
Print Assumptions lnk_wker_conv.
Print Assumptions dTC_spec.
Print Assumptions remC_eq.

(* ================================================================= *)
(*  END ThetaTailEntire.v (part 4).                                   *)
(* ================================================================= *)
