(* ================================================================= *)
(*  CImproperIntegral.v  —  toward the complex improper integral.     *)
(*  Generic real ImproperCv1 helper: value monotonicity.  Axiom-clean.*)
(* ================================================================= *)

From Stdlib Require Import Reals Lra FunctionalExtensionality.
Require Import ComplexField Cmodulus ImproperCv1.
Open Scope R_scope.

(* scalar multiple preserves Riemann-integrability *)
Lemma RI_scal : forall g l a b, Riemann_integrable g a b ->
  Riemann_integrable (fun x => l * g x) a b.
Proof.
  intros g l a b Hg.
  assert (Heq : (fun x => l * g x) = (fun x => fct_cte 0 x + l * g x))
    by (apply functional_extensionality; intro x; unfold fct_cte; ring).
  rewrite Heq. apply RiemannInt_P10; [ apply RiemannInt_P14 | exact Hg ].
Qed.

(* value monotonicity: f <= g on [1,∞) ⇒ ∫₁^∞ f <= ∫₁^∞ g *)
Lemma improper_mono : forall f g Hf Hg If Ig,
  (forall x, 1 <= x -> f x <= g x) ->
  ImproperCv1 f Hf If -> ImproperCv1 g Hg Ig -> If <= Ig.
Proof.
  intros f g Hf Hg If Ig Hle HF HG.
  set (b := fun n => 1 + INR n).
  assert (Hb1 : forall k, 1 <= b k) by (intro k; unfold b; pose proof (pos_INR k); lra).
  assert (Hbinf : cv_infty b) by apply cv_infty_1_INR.
  apply Rle_cv_lim with (Un := fun k => pint1 f Hf (b k)) (Vn := fun k => pint1 g Hg (b k)).
  - intro k; unfold pint1; apply RiemannInt_P19; [ apply Hb1 | intros x Hx; apply Hle; lra ].
  - apply HF; assumption.
  - apply HG; assumption.
Qed.

(* scalar out of a finite Riemann integral on [1,A] *)
Lemma RiemannInt_scal1 : forall g l A (prg : Riemann_integrable g 1 A)
    (prlg : Riemann_integrable (fun x => l * g x) 1 A),
  1 <= A -> RiemannInt prlg = l * RiemannInt prg.
Proof.
  intros g l A prg prlg HA.
  pose (pr0 := RiemannInt_P14 1 A 0).
  pose (pr3 := RiemannInt_P10 l pr0 prg).
  assert (Hpt : forall x, 1 < x < A -> l * g x = fct_cte 0 x + l * g x)
    by (intros x _; unfold fct_cte; ring).
  rewrite (RiemannInt_P18 prlg pr3 HA Hpt).
  rewrite (RiemannInt_P13 pr0 prg pr3).
  rewrite (RiemannInt_P15 pr0). ring.
Qed.

(* scalar multiple of an improper integral *)
Lemma improper_scal : forall g l Hg Hlg Ig,
  ImproperCv1 g Hg Ig -> ImproperCv1 (fun x => l * g x) Hlg (l * Ig).
Proof.
  intros g l Hg Hlg Ig HG b Hb1 Hbinf.
  apply (Un_cv_ext (fun k => l * pint1 g Hg (b k))).
  - intro k. unfold pint1. symmetry. apply RiemannInt_scal1. apply Hb1.
  - apply (CV_mult (fun _ => l) (fun k => pint1 g Hg (b k)) l Ig);
      [ apply Un_cv_const | apply HG; assumption ].
Qed.

(* value of a nonnegative improper integral is nonnegative *)
Lemma improper_nonneg : forall f Hf I,
  (forall x, 1 <= x -> 0 <= f x) -> ImproperCv1 f Hf I -> 0 <= I.
Proof.
  intros f Hf I Hpos HF.
  set (b := fun n => 1 + INR n).
  assert (Hb1 : forall k, 1 <= b k) by (intro k; unfold b; pose proof (pos_INR k); lra).
  assert (Hbinf : cv_infty b) by apply cv_infty_1_INR.
  apply Rle_cv_lim with (Un := fun _ : nat => 0) (Vn := fun k => pint1 f Hf (b k)).
  - intro k; unfold pint1.
    apply Rle_trans with (RiemannInt (RiemannInt_P14 1 (b k) 0)).
    + rewrite RiemannInt_P15; lra.
    + apply RiemannInt_P19; [ apply Hb1 | intros x Hx; unfold fct_cte; apply Hpos; lra ].
  - apply Un_cv_const.
  - apply HF; assumption.
Qed.

(* ================================================================= *)
(*  The complex improper integral over [1,∞): (∫Re) + i(∫Im).         *)
(* ================================================================= *)

Definition CImp (f : R -> C)
  (Hre : forall a b, Riemann_integrable (fun u => Re (f u)) a b)
  (Him : forall a b, Riemann_integrable (fun u => Im (f u)) a b)
  (I : C) : Prop :=
  ImproperCv1 (fun u => Re (f u)) Hre (Re I) /\
  ImproperCv1 (fun u => Im (f u)) Him (Im I).

(* the triangle inequality |∫f| ≤ ∫|f| for the complex improper integral *)
Lemma CImp_triangle : forall f Hre Him I Hmod J,
  CImp f Hre Him I ->
  ImproperCv1 (fun u => Cmod (f u)) Hmod J ->
  Cmod I <= J.
Proof.
  intros f Hre Him I Hmod J [HRe HIm] HJ.
  (* J >= 0 *)
  assert (HJnn : 0 <= J)
    by (apply (improper_nonneg (fun u => Cmod (f u)) Hmod J);
        [ intros x _; apply Cmod_nonneg | exact HJ ]).
  (* witnesses for  φ(u) = Re I·Re(f u) + Im I·Im(f u)  and  Cmod I·Cmod(f u) *)
  pose (HaRe := fun a b => RI_scal (fun u => Re (f u)) (Re I) a b (Hre a b)).
  pose (Hphi := fun a b => RiemannInt_P10 (Im I) (HaRe a b) (Him a b)).
  pose (HcJ  := fun a b => RI_scal (fun u => Cmod (f u)) (Cmod I) a b (Hmod a b)).
  (* ∫ φ = Cnorm2 I *)
  assert (Hphival : ImproperCv1
            (fun u => Re I * Re (f u) + Im I * Im (f u)) Hphi
            (Re I * Re I + Im I * Im I)).
  { apply (improper_linear (fun u => Re I * Re (f u)) (fun u => Im (f u)) (Im I)
             HaRe Him Hphi (Re I * Re I) (Im I)).
    - apply (improper_scal (fun u => Re (f u)) (Re I) Hre HaRe (Re I)); exact HRe.
    - exact HIm. }
  (* ∫ (Cmod I·Cmod f) = Cmod I·J *)
  assert (HcJval : ImproperCv1 (fun u => Cmod I * Cmod (f u)) HcJ (Cmod I * J))
    by (apply (improper_scal (fun u => Cmod (f u)) (Cmod I) Hmod HcJ J); exact HJ).
  (* pointwise Cauchy–Schwarz ⇒ Cnorm2 I ≤ Cmod I·J *)
  assert (Hcs : Re I * Re I + Im I * Im I <= Cmod I * J).
  { apply (improper_mono
             (fun u => Re I * Re (f u) + Im I * Im (f u))
             (fun u => Cmod I * Cmod (f u))
             Hphi HcJ _ _
             (fun x Hx => Cmod_CauchySchwarz I (f x)) Hphival HcJval). }
  (* conclude Cmod I ≤ J *)
  destruct (Rle_lt_or_eq_dec 0 (Cmod I) (Cmod_nonneg I)) as [Hpos | Hzero].
  - apply (Rmult_le_reg_l (Cmod I)); [ exact Hpos | ].
    apply Rle_trans with (Re I * Re I + Im I * Im I); [ | exact Hcs ].
    pose proof (Cmod_sqr I) as Hs; unfold Rsqr, Cnorm2 in Hs; lra.
  - rewrite <- Hzero; exact HJnn.
Qed.

(* additivity of the complex improper integral *)
Lemma CImp_add : forall f g Href Himf Hreg Himg Hrefg Himfg I J,
  CImp f Href Himf I -> CImp g Hreg Himg J ->
  CImp (fun u => Cadd (f u) (g u)) Hrefg Himfg (Cadd I J).
Proof.
  intros f g Href Himf Hreg Himg Hrefg Himfg I J [HRf HIf] [HRg HIg].
  split.
  - replace (Re (Cadd I J)) with (Re I + 1 * Re J) by (simpl; ring).
    apply (improper_ext (fun u => Re (f u) + 1 * Re (g u))
             (fun u => Re (Cadd (f u) (g u)))
             (fun a b => RiemannInt_P10 1 (Href a b) (Hreg a b)) Hrefg (Re I + 1 * Re J)).
    + intros x _; simpl; ring.
    + apply (improper_linear (fun u => Re (f u)) (fun u => Re (g u)) 1 Href Hreg
               (fun a b => RiemannInt_P10 1 (Href a b) (Hreg a b)) (Re I) (Re J) HRf HRg).
  - replace (Im (Cadd I J)) with (Im I + 1 * Im J) by (simpl; ring).
    apply (improper_ext (fun u => Im (f u) + 1 * Im (g u))
             (fun u => Im (Cadd (f u) (g u)))
             (fun a b => RiemannInt_P10 1 (Himf a b) (Himg a b)) Himfg (Im I + 1 * Im J)).
    + intros x _; simpl; ring.
    + apply (improper_linear (fun u => Im (f u)) (fun u => Im (g u)) 1 Himf Himg
               (fun a b => RiemannInt_P10 1 (Himf a b) (Himg a b)) (Im I) (Im J) HIf HIg).
Qed.

(* complex-scalar multiple of the complex improper integral *)
Lemma CImp_cscal : forall c g Hreg Himg Hre' Him' J,
  CImp g Hreg Himg J ->
  CImp (fun u => Cmul c (g u)) Hre' Him' (Cmul c J).
Proof.
  intros c g Hreg Himg Hre' Him' J [HRg HIg].
  split.
  - replace (Re (Cmul c J)) with (Re c * Re J + (- Im c) * Im J) by (simpl; ring).
    apply (improper_ext
             (fun u => Re c * Re (g u) + (- Im c) * Im (g u))
             (fun u => Re (Cmul c (g u)))
             (fun a b => RiemannInt_P10 (- Im c)
                (RI_scal (fun u => Re (g u)) (Re c) a b (Hreg a b)) (Himg a b))
             Hre' (Re c * Re J + (- Im c) * Im J)).
    + intros x _; simpl; ring.
    + apply (improper_linear (fun u => Re c * Re (g u)) (fun u => Im (g u)) (- Im c)
               (fun a b => RI_scal (fun u => Re (g u)) (Re c) a b (Hreg a b)) Himg
               (fun a b => RiemannInt_P10 (- Im c)
                  (RI_scal (fun u => Re (g u)) (Re c) a b (Hreg a b)) (Himg a b))
               (Re c * Re J) (Im J)).
      * apply (improper_scal (fun u => Re (g u)) (Re c) Hreg
                 (fun a b => RI_scal (fun u => Re (g u)) (Re c) a b (Hreg a b)) (Re J)); exact HRg.
      * exact HIg.
  - replace (Im (Cmul c J)) with (Re c * Im J + Im c * Re J) by (simpl; ring).
    apply (improper_ext
             (fun u => Re c * Im (g u) + Im c * Re (g u))
             (fun u => Im (Cmul c (g u)))
             (fun a b => RiemannInt_P10 (Im c)
                (RI_scal (fun u => Im (g u)) (Re c) a b (Himg a b)) (Hreg a b))
             Him' (Re c * Im J + Im c * Re J)).
    + intros x _; simpl; ring.
    + apply (improper_linear (fun u => Re c * Im (g u)) (fun u => Re (g u)) (Im c)
               (fun a b => RI_scal (fun u => Im (g u)) (Re c) a b (Himg a b)) Hreg
               (fun a b => RiemannInt_P10 (Im c)
                  (RI_scal (fun u => Im (g u)) (Re c) a b (Himg a b)) (Hreg a b))
               (Re c * Im J) (Re J)).
      * apply (improper_scal (fun u => Im (g u)) (Re c) Himg
                 (fun a b => RI_scal (fun u => Im (g u)) (Re c) a b (Himg a b)) (Im J)); exact HIg.
      * exact HRg.
Qed.

Print Assumptions CImp_triangle.
Print Assumptions CImp_add.
Print Assumptions CImp_cscal.
