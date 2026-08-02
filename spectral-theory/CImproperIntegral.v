(* ================================================================= *)
(*  CImproperIntegral.v  —  toward the complex improper integral.     *)
(*  Generic real ImproperCv1 helper: value monotonicity.  Axiom-clean.*)
(* ================================================================= *)

From Stdlib Require Import Reals Lra FunctionalExtensionality.
Require Import ComplexField Cmodulus ImproperCv1 MellinElem.
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

(* ================================================================= *)
(*  Absolute convergence ⇒ convergence for the complex integral.      *)
(* ================================================================= *)

(* continuity ⇒ Riemann-integrable on any interval (both orders) *)
Lemma cont_RI : forall h, continuity h -> forall x y, Riemann_integrable h x y.
Proof.
  intros h Hh x y; destruct (Rle_dec x y) as [H | H].
  - apply continuity_implies_RiemannInt; [ exact H | intros u _; apply Hh ].
  - apply RiemannInt_P1; apply continuity_implies_RiemannInt; [ lra | intros u _; apply Hh ].
Qed.

Lemma Cmod_Re : forall c, Rabs (Re c) <= Cmod c.
Proof.
  intro c; unfold Cmod; rewrite <- (sqrt_Rsqr_abs (Re c)).
  apply sqrt_le_1_alt; unfold Rsqr, Cnorm2.
  pose proof (Rle_0_sqr (Im c)); unfold Rsqr in *; lra.
Qed.

Lemma Cmod_Im : forall c, Rabs (Im c) <= Cmod c.
Proof.
  intro c; unfold Cmod; rewrite <- (sqrt_Rsqr_abs (Im c)).
  apply sqrt_le_1_alt; unfold Rsqr, Cnorm2.
  pose proof (Rle_0_sqr (Re c)); unfold Rsqr in *; lra.
Qed.

Lemma Rmax_0_eq : forall a, Rmax a 0 = (a + Rabs a) * / 2.
Proof.
  intro a; unfold Rmax, Rabs; destruct (Rle_dec a 0); destruct (Rcase_abs a); lra.
Qed.

Lemma cont_max0 : forall h, continuity h -> continuity (fun u => Rmax (h u) 0).
Proof.
  intros h Hh.
  assert (Heq : (fun u => Rmax (h u) 0) = (fun u => (h u + Rabs (h u)) * / 2))
    by (apply functional_extensionality; intro u; apply Rmax_0_eq).
  rewrite Heq.
  apply (continuity_mult (fun u => h u + Rabs (h u)) (fun _ => / 2)).
  - apply (continuity_plus h (fun u => Rabs (h u))).
    + exact Hh.
    + exact (continuity_comp h Rabs Hh Rcontinuity_abs).
  - apply continuity_const; red; intros; reflexivity.
Qed.

(* a signed continuous integrand dominated by an ImproperCv1 g is itself
   ImproperCv1 — via the positive/negative-part split. *)
Lemma abs_conv_component : forall h g Hg Ig (Hh : continuity h),
  (forall x, 1 <= x -> Rabs (h x) <= g x) ->
  ImproperCv1 g Hg Ig ->
  { I : R | ImproperCv1 h (cont_RI h Hh) I }.
Proof.
  intros h g Hg Ig Hh Hbound HG.
  assert (Hgpos : forall x, 1 <= x -> 0 <= g x)
    by (intros x Hx; apply Rle_trans with (Rabs (h x)); [ apply Rabs_pos | apply Hbound; exact Hx ]).
  pose (hp := fun u => Rmax (h u) 0).
  pose (hm := fun u => Rmax (- h u) 0).
  assert (Hchp : continuity hp) by (apply cont_max0; exact Hh).
  assert (Hchm : continuity hm) by (apply cont_max0; exact (continuity_opp h Hh)).
  assert (Hpp : forall x, 1 <= x -> 0 <= hp x) by (intros x _; apply Rmax_r).
  assert (Hmp : forall x, 1 <= x -> 0 <= hm x) by (intros x _; apply Rmax_r).
  assert (Hpg : forall x, 1 <= x -> hp x <= g x).
  { intros x Hx; unfold hp; apply Rmax_lub.
    - apply Rle_trans with (Rabs (h x)); [ apply Rle_abs | apply Hbound; exact Hx ].
    - apply Hgpos; exact Hx. }
  assert (Hmg : forall x, 1 <= x -> hm x <= g x).
  { intros x Hx; unfold hm; apply Rmax_lub.
    - apply Rle_trans with (Rabs (h x));
        [ rewrite <- (Rabs_Ropp (h x)); apply Rle_abs | apply Hbound; exact Hx ].
    - apply Hgpos; exact Hx. }
  assert (Hpbnd : exists M, forall A, 1 <= A -> pint1 hp (cont_RI hp Hchp) A <= M).
  { exists Ig; intros A HA; apply Rle_trans with (pint1 g Hg A).
    - unfold pint1; apply RiemannInt_P19; [ exact HA | intros x Hx; apply Hpg; lra ].
    - apply (pint1_le_improper g Hg Ig HG Hgpos A HA). }
  assert (Hmbnd : exists M, forall A, 1 <= A -> pint1 hm (cont_RI hm Hchm) A <= M).
  { exists Ig; intros A HA; apply Rle_trans with (pint1 g Hg A).
    - unfold pint1; apply RiemannInt_P19; [ exact HA | intros x Hx; apply Hmg; lra ].
    - apply (pint1_le_improper g Hg Ig HG Hgpos A HA). }
  destruct (improper_bounded_cv hp (cont_RI hp Hchp) Hpp Hpbnd) as [Ip HIp].
  destruct (improper_bounded_cv hm (cont_RI hm Hchm) Hmp Hmbnd) as [Im HIm].
  exists (Ip - Im).
  apply (improper_ext (fun u => hp u + (-1) * hm u) h
           (fun a b => RiemannInt_P10 (-1) (cont_RI hp Hchp a b) (cont_RI hm Hchm a b))
           (cont_RI h Hh) (Ip - Im)).
  - intros x _; unfold hp, hm, Rmax;
      destruct (Rle_dec (h x) 0); destruct (Rle_dec (- h x) 0); lra.
  - replace (Ip - Im) with (Ip + (-1) * Im) by ring.
    apply (improper_linear hp hm (-1) (cont_RI hp Hchp) (cont_RI hm Hchm)
             (fun a b => RiemannInt_P10 (-1) (cont_RI hp Hchp a b) (cont_RI hm Hchm a b))
             Ip Im HIp HIm).
Qed.

(* the complex integral of a continuous, absolutely-dominated integrand exists *)
Lemma CImp_abs : forall f g Hg Ig
    (Hre : continuity (fun u => Re (f u)))
    (Him : continuity (fun u => Im (f u))),
  (forall x, 1 <= x -> Cmod (f x) <= g x) ->
  ImproperCv1 g Hg Ig ->
  { I : C | CImp f (cont_RI _ Hre) (cont_RI _ Him) I }.
Proof.
  intros f g Hg Ig Hre Him Hbound HG.
  destruct (abs_conv_component (fun u => Re (f u)) g Hg Ig Hre
             (fun x Hx => Rle_trans _ _ _ (Cmod_Re (f x)) (Hbound x Hx)) HG) as [IR HIR].
  destruct (abs_conv_component (fun u => Im (f u)) g Hg Ig Him
             (fun x Hx => Rle_trans _ _ _ (Cmod_Im (f x)) (Hbound x Hx)) HG) as [II HII].
  exists (mkC IR II); split; [ exact HIR | exact HII ].
Qed.

Print Assumptions CImp_triangle.
Print Assumptions CImp_add.
Print Assumptions CImp_cscal.
Print Assumptions CImp_abs.
