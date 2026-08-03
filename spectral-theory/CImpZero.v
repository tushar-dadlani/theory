(* ================================================================= *)
(*  CImpZero.v  —  the COMPLEX near-0 improper integral over (0,1].     *)
(*  A port of CImproperIntegral.v from the tail toolkit ImproperCv1     *)
(*  to the near-0 toolkit ImproperCv0.  Integrability is positivity-    *)
(*  gated (∀ x y, 0<x → x≤y → RI f x y), since the integrand is         *)
(*  singular at 0; the pos/neg-part split uses RI closure               *)
(*  (RiemannInt_P16) rather than continuity.  Axiom-clean.             *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia FunctionalExtensionality.
Require Import ComplexField Cmodulus ImproperCv0 ImproperCv1 GammaContinuity
        CImproperIntegral.
Open Scope R_scope.

(* --- missing real near-0 scalars --- *)

(* scalar out of a finite Riemann integral on [e,1] *)
Lemma RiemannInt_scal01 : forall g l e (prg : Riemann_integrable g e 1)
    (prlg : Riemann_integrable (fun x => l * g x) e 1),
  e <= 1 -> RiemannInt prlg = l * RiemannInt prg.
Proof.
  intros g l e prg prlg He.
  pose (pr0 := RiemannInt_P14 e 1 0).
  pose (pr3 := RiemannInt_P10 l pr0 prg).
  assert (Hpt : forall x, e < x < 1 -> l * g x = fct_cte 0 x + l * g x)
    by (intros x _; unfold fct_cte; ring).
  rewrite (RiemannInt_P18 prlg pr3 He Hpt).
  rewrite (RiemannInt_P13 pr0 prg pr3).
  rewrite (RiemannInt_P15 pr0). ring.
Qed.

Lemma improper_scal0 : forall g l Hg Hlg Ig,
  ImproperCv0 g Hg Ig -> ImproperCv0 (fun x => l * g x) Hlg (l * Ig).
Proof.
  intros g l Hg Hlg Ig HG e He0 He1 Hecv.
  apply (Un_cv_ext (fun k => l * rint01 g Hg (e k))).
  - intro k; rewrite (rint01_val g Hg (e k) (He0 k) (He1 k)),
      (rint01_val (fun x => l * g x) Hlg (e k) (He0 k) (He1 k)).
    symmetry; apply RiemannInt_scal01; apply He1.
  - apply (CV_mult (fun _ => l) (fun k => rint01 g Hg (e k)) l Ig);
      [ apply Un_cv_const | apply HG; assumption ].
Qed.

Lemma improper_nonneg0 : forall f Hf I,
  (forall x, 0 < x -> x <= 1 -> 0 <= f x) -> ImproperCv0 f Hf I -> 0 <= I.
Proof.
  intros f Hf I Hpos HF.
  set (a := fun n => / (1 + INR n)).
  assert (Ha0 : forall k, 0 < a k)
    by (intro k; unfold a; apply Rinv_0_lt_compat; pose proof (pos_INR k); lra).
  assert (Ha1 : forall k, a k <= 1)
    by (intro k; unfold a; apply inv_le_1; pose proof (pos_INR k); lra).
  assert (Hacv : Un_cv a 0)
    by (unfold a; apply Un_cv_recip_0;
        [ intro k; pose proof (pos_INR k); lra | apply cv_infty_1_INR ]).
  apply Rle_cv_lim with (Un := fun _ => 0) (Vn := fun k => rint01 f Hf (a k)).
  - intro k; rewrite (rint01_val f Hf (a k) (Ha0 k) (Ha1 k)).
    apply Rle_trans with (RiemannInt (RiemannInt_P14 (a k) 1 0)).
    + rewrite RiemannInt_P15; pose proof (Ha1 k); lra.
    + apply RiemannInt_P19;
        [ apply Ha1 | intros x Hx; unfold fct_cte; apply Hpos; pose proof (Ha0 k); lra ].
  - apply Un_cv_const.
  - apply HF; assumption.
Qed.

Lemma improper_unique0 : forall f Hf g Hg I1 I2,
  (forall x, 0 < x -> x <= 1 -> f x = g x) ->
  ImproperCv0 f Hf I1 -> ImproperCv0 g Hg I2 -> I1 = I2.
Proof.
  intros f Hf g Hg I1 I2 Heq HF HG.
  assert (HG1 : ImproperCv0 g Hg I1) by (apply (improper_ext0 f g Hf Hg I1 Heq HF)).
  set (a := fun n => / (1 + INR n)).
  assert (Ha0 : forall k, 0 < a k)
    by (intro k; unfold a; apply Rinv_0_lt_compat; pose proof (pos_INR k); lra).
  assert (Ha1 : forall k, a k <= 1)
    by (intro k; unfold a; apply inv_le_1; pose proof (pos_INR k); lra).
  assert (Hacv : Un_cv a 0)
    by (unfold a; apply Un_cv_recip_0;
        [ intro k; pose proof (pos_INR k); lra | apply cv_infty_1_INR ]).
  apply (UL_sequence (fun k => rint01 g Hg (a k)) I1 I2);
    [ apply HG1; assumption | apply HG; assumption ].
Qed.

(* ∫_A^1 f <= I  for the improper value I (f >= 0, 0 < A <= 1). *)
Lemma rint01_le_improper : forall f Hf I, ImproperCv0 f Hf I ->
  (forall x, 0 < x -> x <= 1 -> 0 <= f x) ->
  forall A, 0 < A -> A <= 1 -> rint01 f Hf A <= I.
Proof.
  intros f Hf I HI Hpos A HA HA1.
  set (e := fun n => A * / (1 + INR n)).
  assert (He0 : forall k, 0 < e k)
    by (intro k; unfold e; apply Rmult_lt_0_compat;
        [ lra | apply Rinv_0_lt_compat; pose proof (pos_INR k); lra ]).
  assert (Hle1 : forall k, / (1 + INR k) <= 1)
    by (intro k; apply inv_le_1; pose proof (pos_INR k); lra).
  assert (HeA : forall k, e k <= A)
    by (intro k; unfold e; apply Rle_trans with (A * 1);
        [ apply Rmult_le_compat_l; [ lra | apply Hle1 ] | lra ]).
  assert (He1 : forall k, e k <= 1) by (intro k; apply Rle_trans with A; [ apply HeA | exact HA1 ]).
  assert (Hecv : Un_cv e 0).
  { replace 0 with (A * 0) by ring.
    apply (CV_mult (fun _ => A) (fun n => / (1 + INR n)) A 0);
      [ apply Un_cv_const
      | apply Un_cv_recip_0; [ intro k; pose proof (pos_INR k); lra | apply cv_infty_1_INR ] ]. }
  apply Rle_cv_lim with (Un := fun _ => rint01 f Hf A) (Vn := fun k => rint01 f Hf (e k)).
  - intro k; apply (rint01_mono f Hf Hpos (e k) A (He0 k)); [ apply HeA | exact HA1 ].
  - apply Un_cv_const.
  - apply HI; assumption.
Qed.

(* --- RI closure: Rmax(f,0) and -f are RI where f is --- *)

Lemma RI_opp : forall f x y, Riemann_integrable f x y ->
  Riemann_integrable (fun u => - f u) x y.
Proof.
  intros f x y Hf.
  assert (Heq : (fun u => - f u) = (fun u => (-1) * f u))
    by (apply functional_extensionality; intro u; ring).
  rewrite Heq; apply RI_scal; exact Hf.
Qed.

Lemma RI_max0 : forall f x y, Riemann_integrable f x y ->
  Riemann_integrable (fun u => Rmax (f u) 0) x y.
Proof.
  intros f x y Hf.
  assert (Heq : (fun u => Rmax (f u) 0) = (fun u => / 2 * (f u + 1 * Rabs (f u))))
    by (apply functional_extensionality; intro u; rewrite Rmax_0_eq; ring).
  rewrite Heq; apply RI_scal.
  apply (RiemannInt_P10 1 Hf).
  apply RiemannInt_P16; exact Hf.
Qed.

(* --- continuity on (0,∞) gives the positivity-gated integrability --- *)
Lemma cont_pos_RI : forall f, (forall t, 0 < t -> continuity_pt f t) ->
  forall x y, 0 < x -> x <= y -> Riemann_integrable f x y.
Proof.
  intros f Hf x y Hx Hxy.
  apply continuity_implies_RiemannInt; [ exact Hxy | intros t Ht; apply Hf; lra ].
Qed.

(* ================================================================= *)
(*  The complex near-0 integral over (0,1]: (∫Re) + i(∫Im).           *)
(* ================================================================= *)

Definition CImp0 (f : R -> C)
  (Hre : forall x y, 0 < x -> x <= y -> Riemann_integrable (fun u => Re (f u)) x y)
  (Him : forall x y, 0 < x -> x <= y -> Riemann_integrable (fun u => Im (f u)) x y)
  (I : C) : Prop :=
  ImproperCv0 (fun u => Re (f u)) Hre (Re I) /\
  ImproperCv0 (fun u => Im (f u)) Him (Im I).

Lemma CImp0_triangle : forall f Hre Him I Hmod J,
  CImp0 f Hre Him I ->
  ImproperCv0 (fun u => Cmod (f u)) Hmod J ->
  Cmod I <= J.
Proof.
  intros f Hre Him I Hmod J [HRe HIm] HJ.
  assert (HJnn : 0 <= J)
    by (apply (improper_nonneg0 (fun u => Cmod (f u)) Hmod J);
        [ intros x _ _; apply Cmod_nonneg | exact HJ ]).
  pose (HaRe := fun x y (Hx : 0 < x) (Hxy : x <= y) =>
                  RI_scal (fun u => Re (f u)) (Re I) x y (Hre x y Hx Hxy)).
  pose (Hphi := fun x y (Hx : 0 < x) (Hxy : x <= y) =>
                  RiemannInt_P10 (Im I) (HaRe x y Hx Hxy) (Him x y Hx Hxy)).
  pose (HcJ := fun x y (Hx : 0 < x) (Hxy : x <= y) =>
                  RI_scal (fun u => Cmod (f u)) (Cmod I) x y (Hmod x y Hx Hxy)).
  assert (Hphival : ImproperCv0 (fun u => Re I * Re (f u) + Im I * Im (f u)) Hphi
            (Re I * Re I + Im I * Im I)).
  { apply (improper_linear0 (fun u => Re I * Re (f u)) (fun u => Im (f u)) (Im I)
             HaRe Him Hphi (Re I * Re I) (Im I)).
    - apply (improper_scal0 (fun u => Re (f u)) (Re I) Hre HaRe (Re I)); exact HRe.
    - exact HIm. }
  assert (HcJval : ImproperCv0 (fun u => Cmod I * Cmod (f u)) HcJ (Cmod I * J))
    by (apply (improper_scal0 (fun u => Cmod (f u)) (Cmod I) Hmod HcJ J); exact HJ).
  assert (Hcs : Re I * Re I + Im I * Im I <= Cmod I * J).
  { apply (improper_mono0 (fun u => Re I * Re (f u) + Im I * Im (f u)) Hphi
             (fun u => Cmod I * Cmod (f u)) HcJ _ _ Hphival HcJval
             (fun x Hx Hx1 => Cmod_CauchySchwarz I (f x))). }
  destruct (Rle_lt_or_eq_dec 0 (Cmod I) (Cmod_nonneg I)) as [Hpos | Hzero].
  - apply (Rmult_le_reg_l (Cmod I)); [ exact Hpos | ].
    apply Rle_trans with (Re I * Re I + Im I * Im I); [ | exact Hcs ].
    pose proof (Cmod_sqr I) as Hs; unfold Rsqr, Cnorm2 in Hs; lra.
  - rewrite <- Hzero; exact HJnn.
Qed.

Lemma CImp0_add : forall f g Href Himf Hreg Himg Hrefg Himfg I J,
  CImp0 f Href Himf I -> CImp0 g Hreg Himg J ->
  CImp0 (fun u => Cadd (f u) (g u)) Hrefg Himfg (Cadd I J).
Proof.
  intros f g Href Himf Hreg Himg Hrefg Himfg I J [HRf HIf] [HRg HIg].
  split.
  - replace (Re (Cadd I J)) with (Re I + 1 * Re J) by (simpl; ring).
    apply (improper_ext0 (fun u => Re (f u) + 1 * Re (g u)) (fun u => Re (Cadd (f u) (g u)))
             (fun x y Hx Hxy => RiemannInt_P10 1 (Href x y Hx Hxy) (Hreg x y Hx Hxy))
             Hrefg (Re I + 1 * Re J)).
    + intros x _ _; simpl; ring.
    + apply (improper_linear0 (fun u => Re (f u)) (fun u => Re (g u)) 1 Href Hreg
               (fun x y Hx Hxy => RiemannInt_P10 1 (Href x y Hx Hxy) (Hreg x y Hx Hxy))
               (Re I) (Re J) HRf HRg).
  - replace (Im (Cadd I J)) with (Im I + 1 * Im J) by (simpl; ring).
    apply (improper_ext0 (fun u => Im (f u) + 1 * Im (g u)) (fun u => Im (Cadd (f u) (g u)))
             (fun x y Hx Hxy => RiemannInt_P10 1 (Himf x y Hx Hxy) (Himg x y Hx Hxy))
             Himfg (Im I + 1 * Im J)).
    + intros x _ _; simpl; ring.
    + apply (improper_linear0 (fun u => Im (f u)) (fun u => Im (g u)) 1 Himf Himg
               (fun x y Hx Hxy => RiemannInt_P10 1 (Himf x y Hx Hxy) (Himg x y Hx Hxy))
               (Im I) (Im J) HIf HIg).
Qed.

Lemma CImp0_cscal : forall c g Hreg Himg Hre' Him' J,
  CImp0 g Hreg Himg J ->
  CImp0 (fun u => Cmul c (g u)) Hre' Him' (Cmul c J).
Proof.
  intros c g Hreg Himg Hre' Him' J [HRg HIg].
  split.
  - replace (Re (Cmul c J)) with (Re c * Re J + (- Im c) * Im J) by (simpl; ring).
    apply (improper_ext0 (fun u => Re c * Re (g u) + (- Im c) * Im (g u))
             (fun u => Re (Cmul c (g u)))
             (fun x y Hx Hxy => RiemannInt_P10 (- Im c)
                (RI_scal (fun u => Re (g u)) (Re c) x y (Hreg x y Hx Hxy)) (Himg x y Hx Hxy))
             Hre' (Re c * Re J + (- Im c) * Im J)).
    + intros x _ _; simpl; ring.
    + apply (improper_linear0 (fun u => Re c * Re (g u)) (fun u => Im (g u)) (- Im c)
               (fun x y Hx Hxy => RI_scal (fun u => Re (g u)) (Re c) x y (Hreg x y Hx Hxy)) Himg
               (fun x y Hx Hxy => RiemannInt_P10 (- Im c)
                  (RI_scal (fun u => Re (g u)) (Re c) x y (Hreg x y Hx Hxy)) (Himg x y Hx Hxy))
               (Re c * Re J) (Im J)).
      * apply (improper_scal0 (fun u => Re (g u)) (Re c) Hreg
                 (fun x y Hx Hxy => RI_scal (fun u => Re (g u)) (Re c) x y (Hreg x y Hx Hxy)) (Re J)); exact HRg.
      * exact HIg.
  - replace (Im (Cmul c J)) with (Re c * Im J + Im c * Re J) by (simpl; ring).
    apply (improper_ext0 (fun u => Re c * Im (g u) + Im c * Re (g u))
             (fun u => Im (Cmul c (g u)))
             (fun x y Hx Hxy => RiemannInt_P10 (Im c)
                (RI_scal (fun u => Im (g u)) (Re c) x y (Himg x y Hx Hxy)) (Hreg x y Hx Hxy))
             Him' (Re c * Im J + Im c * Re J)).
    + intros x _ _; simpl; ring.
    + apply (improper_linear0 (fun u => Re c * Im (g u)) (fun u => Re (g u)) (Im c)
               (fun x y Hx Hxy => RI_scal (fun u => Im (g u)) (Re c) x y (Himg x y Hx Hxy)) Hreg
               (fun x y Hx Hxy => RiemannInt_P10 (Im c)
                  (RI_scal (fun u => Im (g u)) (Re c) x y (Himg x y Hx Hxy)) (Hreg x y Hx Hxy))
               (Re c * Im J) (Re J)).
      * apply (improper_scal0 (fun u => Im (g u)) (Re c) Himg
                 (fun x y Hx Hxy => RI_scal (fun u => Im (g u)) (Re c) x y (Himg x y Hx Hxy)) (Im J)); exact HIg.
      * exact HRg.
Qed.

Lemma CImp0_minus : forall f g Href Himf Hreg Himg Hrefg Himfg I J,
  CImp0 f Href Himf I -> CImp0 g Hreg Himg J ->
  CImp0 (fun u => Cminus (f u) (g u)) Hrefg Himfg (Cminus I J).
Proof.
  intros f g Href Himf Hreg Himg Hrefg Himfg I J [HRf HIf] [HRg HIg].
  split.
  - replace (Re (Cminus I J)) with (Re I + (-1) * Re J) by (simpl; ring).
    apply (improper_ext0 (fun u => Re (f u) + (-1) * Re (g u)) (fun u => Re (Cminus (f u) (g u)))
             (fun x y Hx Hxy => RiemannInt_P10 (-1) (Href x y Hx Hxy) (Hreg x y Hx Hxy))
             Hrefg (Re I + (-1) * Re J)).
    + intros x _ _; simpl; ring.
    + apply (improper_linear0 (fun u => Re (f u)) (fun u => Re (g u)) (-1) Href Hreg
               (fun x y Hx Hxy => RiemannInt_P10 (-1) (Href x y Hx Hxy) (Hreg x y Hx Hxy))
               (Re I) (Re J) HRf HRg).
  - replace (Im (Cminus I J)) with (Im I + (-1) * Im J) by (simpl; ring).
    apply (improper_ext0 (fun u => Im (f u) + (-1) * Im (g u)) (fun u => Im (Cminus (f u) (g u)))
             (fun x y Hx Hxy => RiemannInt_P10 (-1) (Himf x y Hx Hxy) (Himg x y Hx Hxy))
             Himfg (Im I + (-1) * Im J)).
    + intros x _ _; simpl; ring.
    + apply (improper_linear0 (fun u => Im (f u)) (fun u => Im (g u)) (-1) Himf Himg
               (fun x y Hx Hxy => RiemannInt_P10 (-1) (Himf x y Hx Hxy) (Himg x y Hx Hxy))
               (Im I) (Im J) HIf HIg).
Qed.

(* --- absolute convergence: a gated-RI signed integrand dominated by an
   ImproperCv0 g is itself ImproperCv0 (pos/neg-part split) --- *)
Lemma abs_conv_component0 : forall h g Hg Ig
    (Hh : forall x y, 0 < x -> x <= y -> Riemann_integrable h x y),
  (forall x, 0 < x -> x <= 1 -> Rabs (h x) <= g x) ->
  ImproperCv0 g Hg Ig ->
  { I : R | ImproperCv0 h Hh I }.
Proof.
  intros h g Hg Ig Hh Hbound HG.
  assert (Hgpos : forall x, 0 < x -> x <= 1 -> 0 <= g x)
    by (intros x Hx Hx1; apply Rle_trans with (Rabs (h x));
        [ apply Rabs_pos | apply Hbound; assumption ]).
  pose (hp := fun u => Rmax (h u) 0).
  pose (hm := fun u => Rmax (- h u) 0).
  pose (Hhp := fun x y (Hx : 0 < x) (Hxy : x <= y) => RI_max0 h x y (Hh x y Hx Hxy)).
  pose (Hhm := fun x y (Hx : 0 < x) (Hxy : x <= y) => RI_max0 (fun u => - h u) x y (RI_opp h x y (Hh x y Hx Hxy))).
  assert (Hpp : forall x, 0 < x -> x <= 1 -> 0 <= hp x) by (intros x _ _; apply Rmax_r).
  assert (Hmp : forall x, 0 < x -> x <= 1 -> 0 <= hm x) by (intros x _ _; apply Rmax_r).
  assert (Hpg : forall x, 0 < x -> x <= 1 -> hp x <= g x).
  { intros x Hx Hx1; unfold hp; apply Rmax_lub.
    - apply Rle_trans with (Rabs (h x)); [ apply Rle_abs | apply Hbound; assumption ].
    - apply Hgpos; assumption. }
  assert (Hmg : forall x, 0 < x -> x <= 1 -> hm x <= g x).
  { intros x Hx Hx1; unfold hm; apply Rmax_lub.
    - apply Rle_trans with (Rabs (h x));
        [ rewrite <- (Rabs_Ropp (h x)); apply Rle_abs | apply Hbound; assumption ].
    - apply Hgpos; assumption. }
  assert (Hpbnd : exists M, forall x, 0 < x -> x <= 1 -> rint01 hp Hhp x <= M).
  { exists Ig; intros A HA HA1; apply Rle_trans with (rint01 g Hg A).
    - rewrite (rint01_val hp Hhp A HA HA1), (rint01_val g Hg A HA HA1).
      apply RiemannInt_P19; [ exact HA1 | intros x Hx; apply Hpg; lra ].
    - apply (rint01_le_improper g Hg Ig HG Hgpos A HA HA1). }
  assert (Hmbnd : exists M, forall x, 0 < x -> x <= 1 -> rint01 hm Hhm x <= M).
  { exists Ig; intros A HA HA1; apply Rle_trans with (rint01 g Hg A).
    - rewrite (rint01_val hm Hhm A HA HA1), (rint01_val g Hg A HA HA1).
      apply RiemannInt_P19; [ exact HA1 | intros x Hx; apply Hmg; lra ].
    - apply (rint01_le_improper g Hg Ig HG Hgpos A HA HA1). }
  destruct (improper_bounded_cv0 hp Hhp Hpp Hpbnd) as [Ip HIp].
  destruct (improper_bounded_cv0 hm Hhm Hmp Hmbnd) as [Im HIm].
  exists (Ip - Im).
  apply (improper_ext0 (fun u => hp u + (-1) * hm u) h
           (fun x y Hx Hxy => RiemannInt_P10 (-1) (Hhp x y Hx Hxy) (Hhm x y Hx Hxy))
           Hh (Ip - Im)).
  - intros x _ _; unfold hp, hm, Rmax;
      destruct (Rle_dec (h x) 0); destruct (Rle_dec (- h x) 0); lra.
  - replace (Ip - Im) with (Ip + (-1) * Im) by ring.
    apply (improper_linear0 hp hm (-1) Hhp Hhm
             (fun x y Hx Hxy => RiemannInt_P10 (-1) (Hhp x y Hx Hxy) (Hhm x y Hx Hxy))
             Ip Im HIp HIm).
Qed.

(* the complex near-0 integral of a gated-RI, absolutely-dominated integrand *)
Lemma CImp0_abs : forall f g Hg Ig
    (Hre : forall x y, 0 < x -> x <= y -> Riemann_integrable (fun u => Re (f u)) x y)
    (Him : forall x y, 0 < x -> x <= y -> Riemann_integrable (fun u => Im (f u)) x y),
  (forall x, 0 < x -> x <= 1 -> Cmod (f x) <= g x) ->
  ImproperCv0 g Hg Ig ->
  { I : C | CImp0 f Hre Him I }.
Proof.
  intros f g Hg Ig Hre Him Hbound HG.
  destruct (abs_conv_component0 (fun u => Re (f u)) g Hg Ig Hre
             (fun x Hx Hx1 => Rle_trans _ _ _ (Cmod_Re (f x)) (Hbound x Hx Hx1)) HG) as [IR HIR].
  destruct (abs_conv_component0 (fun u => Im (f u)) g Hg Ig Him
             (fun x Hx Hx1 => Rle_trans _ _ _ (Cmod_Im (f x)) (Hbound x Hx Hx1)) HG) as [II HII].
  exists (mkC IR II); split; [ exact HIR | exact HII ].
Qed.

Print Assumptions CImp0_triangle.
Print Assumptions CImp0_abs.

(* ================================================================= *)
(*  END CImpZero.v (complex near-0 improper integral layer).          *)
(* ================================================================= *)
