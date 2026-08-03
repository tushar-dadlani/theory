(* ================================================================= *)
(*  GammaTailC.v  —  the complex Gamma tail  gtailC z = ∫₁^∞ t^{z-1}e^{-t}dt *)
(*  and its holomorphy (ENTIRE in z; e^{-t} beats every power).        *)
(*                                                                    *)
(*  A clone of ThetaTailEntire.v with the Gamma kernel                 *)
(*    gtkC z u = (clamp u)^{z-1} · exp(-clamp u)                        *)
(*  (exponent z-1 not z/2-1 ⇒ derivative factor ln(clamp u), shift +k,  *)
(*  wshift h u = h·ln(clamp u), remainder constant 3).  Axiom-clean.    *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import ComplexField Cmodulus CexpFull CexpRemainder Holomorphic
        MellinElem MellinTail GammaReal ImproperCv1 CImproperIntegral ThetaTailEntire.
Open Scope R_scope.

(* --- kernel --- *)
Definition gtkC (z : C) (u : R) : C :=
  Cmul (Cpw (clamp u) (Cminus z C1)) (RtoC (exp (- clamp u))).

Lemma Cmod_gtkC : forall z u, Cmod (gtkC z u) = gtk (Re z) 1 u.
Proof.
  intros z u; unfold gtkC, gtk.
  rewrite Cmod_mul, Cpw_mod, Cmod_RtoC.
  rewrite (Rabs_right (exp (- clamp u))) by (apply Rle_ge; apply Rlt_le; apply exp_pos).
  assert (HRe : Re (Cminus z C1) = Re z - 1) by (unfold Cminus, Cadd, Copp, C1; simpl; ring).
  rewrite HRe; replace (1 * clamp u) with (clamp u) by ring; reflexivity.
Qed.

Lemma gtkC_real : forall s u, gtkC (RtoC s) u = RtoC (gtk s 1 u).
Proof.
  intros s u; unfold gtkC, gtk.
  assert (HW : Cminus (RtoC s) C1 = RtoC (s - 1))
    by (unfold Cminus, Cadd, Copp, RtoC, C1; apply Ceq; simpl; lra).
  rewrite HW, Cpw_RtoC, <- RtoC_mul.
  f_equal; replace (1 * clamp u) with (clamp u) by ring; reflexivity.
Qed.

Lemma Ccont_gtkC : forall z, Ccont (gtkC z).
Proof.
  intro z; unfold gtkC; apply Ccont_mul.
  - unfold Cpw; apply Ccont_Cexpf; apply Ccont_mul;
      [ apply Ccont_const | apply Ccont_RtoC; apply cont_lnclamp ].
  - apply Ccont_RtoC.
    apply (continuity_ext (gtk 1 1) (fun u => exp (- clamp u)));
      [ intro u; unfold gtk; replace (1 - 1) with 0 by ring;
        rewrite Rpower_O by apply clamp_pos;
        replace (1 * clamp u) with (clamp u) by ring; ring
      | apply cont_gtk ].
Qed.

Definition cont_gtkC_re (z : C) : continuity (fun u => Re (gtkC z u)) := proj1 (Ccont_gtkC z).
Definition cont_gtkC_im (z : C) : continuity (fun u => Im (gtkC z u)) := proj2 (Ccont_gtkC z).

Definition gtailC_sig (z : C) :
  { I : C | CImp (gtkC z) (cont_RI _ (cont_gtkC_re z)) (cont_RI _ (cont_gtkC_im z)) I } :=
  CImp_abs (gtkC z) (gtk (Re z) 1) (gtk_int (Re z) 1) (gtail (Re z) 1 Rlt_0_1)
    (cont_gtkC_re z) (cont_gtkC_im z)
    (fun x _ => Req_le _ _ (Cmod_gtkC z x)) (proj2_sig (gtail_sig (Re z) 1 Rlt_0_1)).

Definition gtailC (z : C) : C := proj1_sig (gtailC_sig z).

Lemma gtailC_spec : forall z,
  CImp (gtkC z) (cont_RI _ (cont_gtkC_re z)) (cont_RI _ (cont_gtkC_im z)) (gtailC z).
Proof. intro z; exact (proj2_sig (gtailC_sig z)). Qed.

Lemma gtailC_agree : forall s, gtailC (RtoC s) = RtoC (gtail s 1 Rlt_0_1).
Proof.
  intro s; destruct (gtailC_spec (RtoC s)) as [HRe HIm]; apply Ceq; simpl.
  - apply (improper_unique (fun u => Re (gtkC (RtoC s) u))
             (cont_RI _ (cont_gtkC_re (RtoC s))) (gtk s 1) (gtk_int s 1)
             (Re (gtailC (RtoC s))) (gtail s 1 Rlt_0_1));
      [ intros x _; rewrite gtkC_real; reflexivity | exact HRe
      | exact (proj2_sig (gtail_sig s 1 Rlt_0_1)) ].
  - apply (improper_unique (fun u => Im (gtkC (RtoC s) u))
             (cont_RI _ (cont_gtkC_im (RtoC s))) (fct_cte 0)
             (fun a b => RiemannInt_P14 a b 0) (Im (gtailC (RtoC s))) 0);
      [ intros x _; rewrite gtkC_real; reflexivity | exact HIm | apply improper_zero ].
Qed.

(* --- ln-weighted tail convergence (shift +k) --- *)
Lemma cont_lnk_gtk : forall s k, continuity (fun u => (ln (clamp u)) ^ k * gtk s 1 u).
Proof.
  intros s k; apply (continuity_mult (fun u => (ln (clamp u)) ^ k) (gtk s 1)).
  - apply cont_pow, cont_lnclamp.
  - apply cont_gtk.
Qed.

Lemma lnk_gtk_le : forall s k u, 1 <= u ->
  (ln (clamp u)) ^ k * gtk s 1 u <= gtk (s + INR k) 1 u.
Proof.
  intros s k u Hu.
  assert (Hpow : (ln (clamp u)) ^ k <= (clamp u) ^ k)
    by (apply pow_incr; split; [ apply ln_clamp_nonneg | apply ln_clamp_le ]).
  apply Rle_trans with ((clamp u) ^ k * gtk s 1 u).
  - apply Rmult_le_compat_r; [ apply gtk_nonneg | exact Hpow ].
  - unfold gtk.
    rewrite <- Rpower_pow by apply clamp_pos.
    rewrite <- Rmult_assoc, <- Rpower_plus.
    replace (INR k + (s - 1)) with (s + INR k - 1) by ring.
    reflexivity.
Qed.

Lemma lnk_gtk_conv : forall s k,
  { I | ImproperCv1 (fun u => (ln (clamp u)) ^ k * gtk s 1 u) (cont_RI _ (cont_lnk_gtk s k)) I }.
Proof.
  intros s k; apply improper_bounded_cv.
  - intros x _; apply Rmult_le_pos; [ apply pow_le; apply ln_clamp_nonneg | apply gtk_nonneg ].
  - exists (gtail (s + INR k) 1 Rlt_0_1); intros A HA.
    apply Rle_trans with (pint1 (gtk (s + INR k) 1) (gtk_int (s + INR k) 1) A).
    + unfold pint1; apply RiemannInt_P19; [ exact HA | intros x Hx; apply lnk_gtk_le; lra ].
    + apply pint1_le_improper;
        [ apply (proj2_sig (gtail_sig (s + INR k) 1 Rlt_0_1))
        | intros x _; apply gtk_nonneg | exact HA ].
Qed.

(* --- derivative kernel dgtkC = ln(clamp u) · gtkC --- *)
Definition dgtkC (z : C) (u : R) : C := Cmul (RtoC (ln (clamp u))) (gtkC z u).

Lemma Cmod_dgtkC : forall z u, Cmod (dgtkC z u) = ln (clamp u) * gtk (Re z) 1 u.
Proof.
  intros z u; unfold dgtkC; rewrite Cmod_mul, Cmod_RtoC, Cmod_gtkC.
  rewrite (Rabs_right (ln (clamp u))) by (apply Rle_ge; apply ln_clamp_nonneg); reflexivity.
Qed.

Lemma Ccont_dgtkC : forall z, Ccont (dgtkC z).
Proof.
  intro z; unfold dgtkC; apply Ccont_mul;
    [ apply Ccont_RtoC; apply cont_lnclamp | apply Ccont_gtkC ].
Qed.

Definition cont_dgtkC_re (z : C) := proj1 (Ccont_dgtkC z).
Definition cont_dgtkC_im (z : C) := proj2 (Ccont_dgtkC z).

Definition dgtail_dom (z : C) (u : R) : R := ln (clamp u) * gtk (Re z) 1 u.

Lemma cont_dgtail_dom : forall z, continuity (dgtail_dom z).
Proof.
  intro z; unfold dgtail_dom;
    apply (continuity_mult (fun u => ln (clamp u)) (gtk (Re z) 1));
    [ apply cont_lnclamp | apply cont_gtk ].
Qed.

Lemma dgtail_dom_conv : forall z,
  { I | ImproperCv1 (dgtail_dom z) (cont_RI _ (cont_dgtail_dom z)) I }.
Proof.
  intro z; destruct (lnk_gtk_conv (Re z) 1) as [I1 HI1]; exists I1.
  apply (improper_ext (fun u => (ln (clamp u)) ^ 1 * gtk (Re z) 1 u) (dgtail_dom z)
           (cont_RI _ (cont_lnk_gtk (Re z) 1)) (cont_RI _ (cont_dgtail_dom z)) I1).
  - intros x _; unfold dgtail_dom; rewrite pow_1; reflexivity.
  - exact HI1.
Qed.

Definition dgtailC_sig (z : C) :
  { I : C | CImp (dgtkC z) (cont_RI _ (cont_dgtkC_re z)) (cont_RI _ (cont_dgtkC_im z)) I } :=
  CImp_abs (dgtkC z) (dgtail_dom z) (cont_RI _ (cont_dgtail_dom z)) (proj1_sig (dgtail_dom_conv z))
    (cont_dgtkC_re z) (cont_dgtkC_im z)
    (fun x _ => Req_le _ _ (Cmod_dgtkC z x)) (proj2_sig (dgtail_dom_conv z)).

Definition dgtailC (z : C) : C := proj1_sig (dgtailC_sig z).

Lemma dgtailC_spec : forall z,
  CImp (dgtkC z) (cont_RI _ (cont_dgtkC_re z)) (cont_RI _ (cont_dgtkC_im z)) (dgtailC z).
Proof. intro z; exact (proj2_sig (dgtailC_sig z)). Qed.

(* --- multiplicative shift + remainder --- *)
Definition gshift (h : C) (u : R) : C := Cmul h (RtoC (ln (clamp u))).

Lemma gtkC_shift : forall z h u, gtkC (Cadd z h) u = Cmul (gtkC z u) (Cexpf (gshift h u)).
Proof.
  intros z h u; unfold gtkC, gshift.
  assert (HE : Cminus (Cadd z h) C1 = Cadd (Cminus z C1) h) by ring.
  rewrite HE, Cpw_split. unfold Cpw. ring.
Qed.

Lemma Cmod_gshift : forall h u, Cmod (gshift h u) = Cmod h * ln (clamp u).
Proof.
  intros h u; unfold gshift; rewrite Cmod_mul, Cmod_RtoC.
  rewrite (Rabs_right (ln (clamp u))) by (apply Rle_ge; apply ln_clamp_nonneg); reflexivity.
Qed.

Definition remGtC (z h : C) (u : R) : C :=
  Cminus (Cminus (gtkC (Cadd z h) u) (gtkC z u)) (Cmul h (dgtkC z u)).

Lemma remGtC_eq : forall z h u,
  remGtC z h u = Cmul (gtkC z u) (Cminus (Cminus (Cexpf (gshift h u)) C1) (gshift h u)).
Proof.
  intros z h u; unfold remGtC, dgtkC.
  rewrite gtkC_shift.
  assert (Hlin : Cmul h (Cmul (RtoC (ln (clamp u))) (gtkC z u)) = Cmul (gtkC z u) (gshift h u))
    by (unfold gshift; ring).
  rewrite Hlin. ring.
Qed.

Lemma Cmod_remGtC_le : forall z h u, 1 <= u -> Cmod h <= 1 ->
  Cmod (remGtC z h u) <= Cmod h ^ 2 * 3 * ((ln (clamp u)) ^ 2 * gtk (Re z + 1) 1 u).
Proof.
  intros z h u Hu Hh.
  rewrite remGtC_eq, Cmod_mul, Cmod_gtkC.
  assert (HexpEq : exp (Cmod h * ln (clamp u)) = Rpower (clamp u) (Cmod h))
    by (unfold Rpower; f_equal; ring).
  assert (Hexple : Rpower (clamp u) (Cmod h) <= Rpower (clamp u) 1)
    by (apply Rle_Rpower; [ apply clamp_ge1 | exact Hh ]).
  assert (Hfold : gtk (Re z) 1 u * Rpower (clamp u) 1 = gtk (Re z + 1) 1 u).
  { unfold gtk.
    rewrite Rmult_assoc, (Rmult_comm (exp (- (1 * clamp u))) (Rpower (clamp u) 1)).
    rewrite <- Rmult_assoc, <- Rpower_plus.
    replace (Re z - 1 + 1) with (Re z + 1 - 1) by ring; reflexivity. }
  assert (Hcoef : 0 <= 3 * (Cmod h * ln (clamp u)) ^ 2).
  { apply Rmult_le_pos; [ lra | apply pow_le; apply Rmult_le_pos;
      [ apply Cmod_nonneg | apply ln_clamp_nonneg ] ]. }
  apply Rle_trans with (gtk (Re z) 1 u * (3 * (Cmod (gshift h u)) ^ 2 * exp (Cmod (gshift h u)))).
  - apply Rmult_le_compat_l; [ apply gtk_nonneg | apply Cexpf_remainder ].
  - rewrite Cmod_gshift, HexpEq.
    apply Rle_trans with
      (gtk (Re z) 1 u * (3 * (Cmod h * ln (clamp u)) ^ 2 * Rpower (clamp u) 1)).
    + apply Rmult_le_compat_l; [ apply gtk_nonneg | ].
      apply Rmult_le_compat_l; [ exact Hcoef | exact Hexple ].
    + right. rewrite <- Hfold. ring.
Qed.

(* --- assembly --- *)
Lemma Ccont_remGtC : forall z h, Ccont (remGtC z h).
Proof.
  intros z h; unfold remGtC.
  apply Ccont_minus.
  - apply Ccont_minus; apply Ccont_gtkC.
  - apply Ccont_mul; [ apply Ccont_const | apply Ccont_dgtkC ].
Qed.

Lemma cont_Cmod_remGtC : forall z h, continuity (fun u => Cmod (remGtC z h u)).
Proof.
  intros z h.
  assert (Hcn : continuity (fun u => Cnorm2 (remGtC z h u))).
  { apply (continuity_ext (fun u => Re (remGtC z h u) * Re (remGtC z h u)
                                  + Im (remGtC z h u) * Im (remGtC z h u)));
      [ intro w; reflexivity | ].
    apply continuity_plus; apply continuity_mult;
      first [ exact (proj1 (Ccont_remGtC z h)) | exact (proj2 (Ccont_remGtC z h)) ]. }
  intro u; apply (continuity_pt_comp (fun u => Cnorm2 (remGtC z h u)) sqrt u);
    [ apply Hcn | apply continuity_pt_sqrt; apply Cnorm2_nonneg ].
Qed.

Lemma cont_remGtC_dom : forall z h,
  continuity (fun u => Cmod h ^ 2 * 3 * ((ln (clamp u)) ^ 2 * gtk (Re z + 1) 1 u)).
Proof.
  intros z h.
  apply (continuity_mult (fun _ => Cmod h ^ 2 * 3)
                         (fun u => (ln (clamp u)) ^ 2 * gtk (Re z + 1) 1 u));
    [ apply continuity_const; red; intros; reflexivity | apply cont_lnk_gtk ].
Qed.

Lemma remGtC_dom_conv : forall z h,
  ImproperCv1 (fun u => Cmod h ^ 2 * 3 * ((ln (clamp u)) ^ 2 * gtk (Re z + 1) 1 u))
    (cont_RI _ (cont_remGtC_dom z h))
    (Cmod h ^ 2 * 3 * proj1_sig (lnk_gtk_conv (Re z + 1) 2)).
Proof.
  intros z h.
  apply (improper_scal (fun u => (ln (clamp u)) ^ 2 * gtk (Re z + 1) 1 u) (Cmod h ^ 2 * 3)
           (cont_RI _ (cont_lnk_gtk (Re z + 1) 2)) (cont_RI _ (cont_remGtC_dom z h))
           (proj1_sig (lnk_gtk_conv (Re z + 1) 2)) (proj2_sig (lnk_gtk_conv (Re z + 1) 2))).
Qed.

Lemma remGtC_CImp : forall z h,
  CImp (remGtC z h) (cont_RI _ (proj1 (Ccont_remGtC z h))) (cont_RI _ (proj2 (Ccont_remGtC z h)))
    (Cminus (Cminus (gtailC (Cadd z h)) (gtailC z)) (Cmul h (dgtailC z))).
Proof.
  intros z h; unfold remGtC.
  apply (CImp_minus
           (fun u => Cminus (gtkC (Cadd z h) u) (gtkC z u))
           (fun u => Cmul h (dgtkC z u))
           (cont_RI _ (proj1 (Ccont_minus _ _ (Ccont_gtkC (Cadd z h)) (Ccont_gtkC z))))
           (cont_RI _ (proj2 (Ccont_minus _ _ (Ccont_gtkC (Cadd z h)) (Ccont_gtkC z))))
           (cont_RI _ (proj1 (Ccont_mul _ _ (Ccont_const h) (Ccont_dgtkC z))))
           (cont_RI _ (proj2 (Ccont_mul _ _ (Ccont_const h) (Ccont_dgtkC z))))
           (cont_RI _ (proj1 (Ccont_remGtC z h)))
           (cont_RI _ (proj2 (Ccont_remGtC z h)))
           (Cminus (gtailC (Cadd z h)) (gtailC z)) (Cmul h (dgtailC z))).
  - apply (CImp_minus (gtkC (Cadd z h)) (gtkC z)
             (cont_RI _ (cont_gtkC_re (Cadd z h))) (cont_RI _ (cont_gtkC_im (Cadd z h)))
             (cont_RI _ (cont_gtkC_re z)) (cont_RI _ (cont_gtkC_im z))
             (cont_RI _ (proj1 (Ccont_minus _ _ (Ccont_gtkC (Cadd z h)) (Ccont_gtkC z))))
             (cont_RI _ (proj2 (Ccont_minus _ _ (Ccont_gtkC (Cadd z h)) (Ccont_gtkC z))))
             (gtailC (Cadd z h)) (gtailC z));
      apply gtailC_spec.
  - apply (CImp_cscal h (dgtkC z)
             (cont_RI _ (cont_dgtkC_re z)) (cont_RI _ (cont_dgtkC_im z))
             (cont_RI _ (proj1 (Ccont_mul _ _ (Ccont_const h) (Ccont_dgtkC z))))
             (cont_RI _ (proj2 (Ccont_mul _ _ (Ccont_const h) (Ccont_dgtkC z))))
             (dgtailC z));
      apply dgtailC_spec.
Qed.

Lemma Cmod_remGtC_conv : forall z h, Cmod h <= 1 ->
  { J | ImproperCv1 (fun u => Cmod (remGtC z h u)) (cont_RI _ (cont_Cmod_remGtC z h)) J }.
Proof.
  intros z h Hh; apply improper_bounded_cv.
  - intros x _; apply Cmod_nonneg.
  - exists (Cmod h ^ 2 * 3 * proj1_sig (lnk_gtk_conv (Re z + 1) 2)); intros A HA.
    apply Rle_trans with
      (pint1 (fun u => Cmod h ^ 2 * 3 * ((ln (clamp u)) ^ 2 * gtk (Re z + 1) 1 u))
             (cont_RI _ (cont_remGtC_dom z h)) A).
    + unfold pint1; apply RiemannInt_P19;
        [ exact HA | intros x Hx; apply Cmod_remGtC_le; [ lra | exact Hh ] ].
    + apply pint1_le_improper; [ apply remGtC_dom_conv | | exact HA ].
      intros x _; apply Rmult_le_pos;
        [ apply Rmult_le_pos; [ apply pow_le; apply Cmod_nonneg | lra ]
        | apply Rmult_le_pos; [ apply pow_le; apply ln_clamp_nonneg | apply gtk_nonneg ] ].
Qed.

Lemma gtailC_deriv_bound : forall z h, Cmod h <= 1 ->
  Cmod (Cminus (Cminus (gtailC (Cadd z h)) (gtailC z)) (Cmul (dgtailC z) h))
  <= Cmod h ^ 2 * 3 * proj1_sig (lnk_gtk_conv (Re z + 1) 2).
Proof.
  intros z h Hh.
  replace (Cmul (dgtailC z) h) with (Cmul h (dgtailC z)) by ring.
  destruct (Cmod_remGtC_conv z h Hh) as [J HJ].
  apply Rle_trans with J.
  - apply (CImp_triangle _ _ _ _ _ _ (remGtC_CImp z h) HJ).
  - apply (improper_mono (fun u => Cmod (remGtC z h u))
             (fun u => Cmod h ^ 2 * 3 * ((ln (clamp u)) ^ 2 * gtk (Re z + 1) 1 u))
             (cont_RI _ (cont_Cmod_remGtC z h)) (cont_RI _ (cont_remGtC_dom z h))
             J (Cmod h ^ 2 * 3 * proj1_sig (lnk_gtk_conv (Re z + 1) 2))).
    + intros x Hx; apply Cmod_remGtC_le; [ lra | exact Hh ].
    + exact HJ.
    + exact (remGtC_dom_conv z h).
Qed.

Theorem gtailC_entire : forall z, is_Cderiv gtailC z (dgtailC z).
Proof.
  intros z eps Heps.
  assert (HL2 : 0 <= proj1_sig (lnk_gtk_conv (Re z + 1) 2)).
  { destruct (lnk_gtk_conv (Re z + 1) 2) as [L2 HL2]; simpl.
    apply (improper_nonneg (fun u => (ln (clamp u)) ^ 2 * gtk (Re z + 1) 1 u)
             (cont_RI _ (cont_lnk_gtk (Re z + 1) 2)) L2);
      [ intros x _; apply Rmult_le_pos;
          [ apply pow_le; apply ln_clamp_nonneg | apply gtk_nonneg ]
      | exact HL2 ]. }
  set (K := 3 * proj1_sig (lnk_gtk_conv (Re z + 1) 2)).
  assert (HK : 0 <= K) by (unfold K; apply Rmult_le_pos; [ lra | exact HL2 ]).
  assert (Hd : 0 < eps / (K + 1)) by (apply Rdiv_lt_0_compat; lra).
  exists (Rmin 1 (eps / (K + 1))); split.
  - unfold Rmin; destruct (Rle_dec 1 (eps / (K + 1))); lra.
  - intros h Hlt.
    assert (Hh1 : Cmod h <= 1) by (pose proof (Rmin_l 1 (eps / (K + 1))); lra).
    assert (Hlt2 : Cmod h < eps / (K + 1)) by (pose proof (Rmin_r 1 (eps / (K + 1))); lra).
    apply Rle_trans with (Cmod h ^ 2 * 3 * proj1_sig (lnk_gtk_conv (Re z + 1) 2)).
    + apply gtailC_deriv_bound; exact Hh1.
    + assert (HcK : Cmod h * (K + 1) < eps).
      { apply Rlt_le_trans with (eps / (K + 1) * (K + 1));
          [ apply Rmult_lt_compat_r; [ lra | exact Hlt2 ] | right; field; lra ]. }
      pose proof (Cmod_nonneg h) as Hcm.
      assert (Hsq : 0 <= Cmod h ^ 2) by (apply pow_le; apply Cmod_nonneg).
      unfold K in HcK. nra.
Qed.

Print Assumptions gtailC_agree.
Print Assumptions gtailC_entire.

(* ================================================================= *)
(*  END GammaTailC.v (complex Gamma tail, holomorphic + agreeing).     *)
(* ================================================================= *)
