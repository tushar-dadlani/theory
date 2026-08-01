(* ================================================================= *)
(*  ZetaZero.v  —  ζ(0) = −1/2  as the pole limit of the completed ζ. *)
(*                                                                    *)
(*  ζ(0) sits at the pole s=1 of the reflection, so it is a genuine    *)
(*  limit, not a substitution.  Writing the continued zeta as         *)
(*     ζ_ext(a) = a·J(a) · π^{a/2} · (1/2) / Γ(a/2+1)   (Gam_recur),    *)
(*  the pole of J and the pole of Γ(a/2) cancel: as a→0⁺,             *)
(*     a·J(a) → −1   (the residue of J; T is monotone in s, hence      *)
(*                    bounded near 0, so a·T(a)→0),                    *)
(*     π^{a/2} → 1,   Γ(a/2+1) → Γ(1) = 1,                             *)
(*  giving ζ_ext(a) → (−1)·1·(1/2)/1 = −1/2.                          *)
(*  The Γ-parameter limit Γ(a/2+1)→1 enters as a hypothesis here and   *)
(*  is discharged separately (GammaContinuity), matching the          *)
(*  Γ(1)/Γ(1/2) incremental pattern.                                 *)
(*  No new axioms (classical Reals only).                            *)
(* ================================================================= *)

From Stdlib Require Import Reals Rpower Lra Lia.
Require Import MellinTail RiemannPsi RiemannThetaFE GammaReal GammaRecur
        XiReflection XiTwoSided ImproperCv1 MellinElem GammaFunction.
Open Scope R_scope.

(* --- comparison of limits and of improper integrals --- *)

Lemma Un_cv_le_lim : forall a b la lb,
  (forall n, a n <= b n) -> Un_cv a la -> Un_cv b lb -> la <= lb.
Proof.
  intros a b la lb Hab Ha Hb; apply Rnot_lt_le; intro Hlt.
  destruct (Ha ((la - lb) / 2) ltac:(lra)) as [Na HNa].
  destruct (Hb ((la - lb) / 2) ltac:(lra)) as [Nb HNb].
  pose proof (HNa (max Na Nb) (Nat.le_max_l _ _)) as HA.
  pose proof (HNb (max Na Nb) (Nat.le_max_r _ _)) as HB.
  unfold R_dist in HA, HB; apply Rabs_def2 in HA; apply Rabs_def2 in HB.
  pose proof (Hab (max Na Nb)); lra.
Qed.

Lemma improper_mono : forall f Hf g Hg If Ig,
  ImproperCv1 f Hf If -> ImproperCv1 g Hg Ig ->
  (forall u, 1 <= u -> f u <= g u) -> If <= Ig.
Proof.
  intros f Hf g Hg If Ig HIf HIg Hle.
  set (A := fun k => 1 + INR k).
  assert (HA1 : forall k, 1 <= A k) by (intro k; unfold A; pose proof (pos_INR k); lra).
  assert (HAinf : cv_infty A) by (unfold A; apply cv_infty_1_INR).
  apply (Un_cv_le_lim (fun k => pint1 f Hf (A k)) (fun k => pint1 g Hg (A k)) If Ig).
  - intro k; unfold pint1; apply RiemannInt_P19; [ apply HA1 | intros x Hx; apply Hle; lra ].
  - exact (HIf A HA1 HAinf).
  - exact (HIg A HA1 HAinf).
Qed.

Lemma improper_nonneg : forall f Hf If,
  ImproperCv1 f Hf If -> (forall u, 1 <= u -> 0 <= f u) -> 0 <= If.
Proof.
  intros f Hf If HIf Hpos.
  set (A := fun k => 1 + INR k).
  assert (HA1 : forall k, 1 <= A k) by (intro k; unfold A; pose proof (pos_INR k); lra).
  assert (HAinf : cv_infty A) by (unfold A; apply cv_infty_1_INR).
  apply (Un_cv_le_lim (fun _ => 0) (fun k => pint1 f Hf (A k)) 0 If).
  - intro k; unfold pint1; apply Rle_trans with (RiemannInt (RiemannInt_P14 1 (A k) 0)).
    + rewrite (RiemannInt_P15 (RiemannInt_P14 1 (A k) 0)); ring_simplify; apply Rle_refl.
    + apply RiemannInt_P19; [ apply HA1 | intros x Hx; unfold fct_cte; apply Hpos; lra ].
  - apply Un_cv_const.
  - exact (HIf A HA1 HAinf).
Qed.

(* --- T is monotone in s and nonnegative --- *)

Lemma T_nonneg : forall s, 0 <= T s.
Proof.
  intro s; apply (improper_nonneg (wker s) (wker_int s) (T s) (T_spec s));
    intros u _; apply wker_nonneg.
Qed.

Lemma T_le : forall x y, x <= y -> T x <= T y.
Proof.
  intros x y Hxy;
    apply (improper_mono (wker x) (wker_int x) (wker y) (wker_int y) (T x) (T y)
             (T_spec x) (T_spec y)).
  intros u Hu; unfold wker; apply Rmult_le_compat_r;
    [ apply Psi_nonneg | apply Rle_Rpower; [ apply clamp_ge1 | lra ] ].
Qed.

(* --- reciprocal of a convergent sequence --- *)

Lemma Un_cv_shift0 : forall u l, Un_cv (fun k => u k - l) 0 -> Un_cv u l.
Proof.
  intros u l H eps He; destruct (H eps He) as [N HN]; exists N; intros n Hn.
  unfold R_dist in *; replace (u n - l) with (u n - l - 0) by ring; apply HN; exact Hn.
Qed.

Lemma Un_cv_inv : forall u l, Un_cv u l -> l <> 0 -> Un_cv (fun n => / u n) (/ l).
Proof.
  intros u l Hu Hl; apply (continuity_seq (fun x => / x) u l); [ | exact Hu ].
  apply (continuity_pt_inv (fun x => x) l);
    [ apply derivable_continuous_pt; apply derivable_pt_id | exact Hl ].
Qed.

(* --- rewriting ζ_ext through the Gamma recurrence --- *)

Lemma zeta_ext_recur : forall x (Hx : 0 < x) (Hx2 : 0 < x / 2) (Hx21 : 0 < x / 2 + 1),
  zeta_ext x = x * J x * Rpower PI (x / 2) * (1 / 2) / Gam (x / 2 + 1) Hx21.
Proof.
  intros x Hx Hx2 Hx21; unfold zeta_ext; rewrite (GamH_eq_pos (x / 2) Hx2).
  pose proof (Gam_recur (x / 2) Hx2 Hx21) as HR.
  pose proof (Gam_pos (x / 2) Hx2) as HGpos.
  rewrite HR; field; split; [ apply Rgt_not_eq; exact HGpos | apply Rgt_not_eq; lra ].
Qed.

(* --- ζ(0) = −1/2 (pole limit), given Γ(a/2+1) → 1 --- *)

Theorem zeta_zero : forall a (Ha0 : forall k, 0 < a k) (Ha1 : forall k, a k < 1)
  (Hcv : Un_cv a 0) (Hp : forall k, 0 < a k / 2 + 1),
  Un_cv (fun k => Gam (a k / 2 + 1) (Hp k)) 1 ->
  Un_cv (fun k => zeta_ext (a k)) (- (1 / 2)).
Proof.
  intros a Ha0 Ha1 Hcv Hp HGlim.
  (* a·J(a) → −1 *)
  assert (HaT0 : Un_cv (fun k => a k * T (a k)) 0).
  { apply (Un_cv_squeeze0 (fun k => a k * T (a k)) (fun k => a k * T 1)).
    - exists 0%nat; intros k _; split;
        [ apply Rmult_le_pos; [ left; apply Ha0 | apply T_nonneg ]
        | apply Rmult_le_compat_l; [ left; apply Ha0 | apply T_le; pose proof (Ha1 k); lra ] ].
    - replace 0 with (0 * T 1) by ring;
        apply (CV_mult a (fun _ => T 1) 0 (T 1)); [ exact Hcv | apply Un_cv_const ]. }
  assert (HaT0' : Un_cv (fun k => a k * T (1 - a k)) 0).
  { apply (Un_cv_squeeze0 (fun k => a k * T (1 - a k)) (fun k => a k * T 1)).
    - exists 0%nat; intros k _; split;
        [ apply Rmult_le_pos; [ left; apply Ha0 | apply T_nonneg ]
        | apply Rmult_le_compat_l; [ left; apply Ha0 | apply T_le; pose proof (Ha0 k); lra ] ].
    - replace 0 with (0 * T 1) by ring;
        apply (CV_mult a (fun _ => T 1) 0 (T 1)); [ exact Hcv | apply Un_cv_const ]. }
  assert (Haq : Un_cv (fun k => a k / (a k - 1)) 0).
  { replace 0 with (0 * / (0 - 1)) by (rewrite Rmult_0_l; reflexivity).
    apply (CV_mult a (fun k => / (a k - 1)) 0 (/ (0 - 1))); [ exact Hcv | ].
    apply (Un_cv_inv (fun k => a k - 1) (0 - 1)); [ | lra ].
    apply (CV_minus a (fun _ => 1) 0 1); [ exact Hcv | apply Un_cv_const ]. }
  assert (HP : Un_cv (fun k => a k * J (a k)) (-1)).
  { apply Un_cv_shift0.
    apply (Un_cv_ext (fun k => a k * T (a k) + a k * T (1 - a k) + a k / (a k - 1))
                     (fun k => a k * J (a k) - (-1))).
    - intro k; unfold J; pose proof (Ha0 k); pose proof (Ha1 k); field;
        split; [ intro Hc; lra | intro Hc; lra ].
    - replace 0 with (0 + 0 + 0) by ring;
        apply CV_plus; [ apply CV_plus | exact Haq ]; [ exact HaT0 | exact HaT0' ]. }
  (* π^{a/2} → 1 *)
  assert (HQ : Un_cv (fun k => Rpower PI (a k / 2)) 1).
  { replace 1 with (Rpower PI 0) by (apply Rpower_O; apply PI_RGT_0).
    apply (continuity_seq (fun x => Rpower PI x) (fun k => a k / 2) 0).
    - unfold Rpower; apply (continuity_pt_comp (fun x => x * ln PI) exp 0);
        [ apply continuity_pt_mult;
            [ apply derivable_continuous_pt; apply derivable_pt_id
            | apply continuity_pt_const; intros p q; reflexivity ]
        | apply derivable_continuous_pt; apply derivable_pt_exp ].
    - replace 0 with (0 * / 2) by ring;
        apply (CV_mult a (fun _ => / 2) 0 (/ 2)); [ exact Hcv | apply Un_cv_const ]. }
  (* 1/Γ(a/2+1) → 1 *)
  assert (HRinv : Un_cv (fun k => / Gam (a k / 2 + 1) (Hp k)) 1).
  { pose proof (Un_cv_inv (fun k => Gam (a k / 2 + 1) (Hp k)) 1 HGlim R1_neq_R0) as Hinv;
      rewrite Rinv_1 in Hinv; exact Hinv. }
  (* assemble *)
  apply (Un_cv_ext (fun k => a k * J (a k) * Rpower PI (a k / 2) * (1 / 2) / Gam (a k / 2 + 1) (Hp k))
                   (fun k => zeta_ext (a k))).
  - intro k; symmetry;
      apply (zeta_ext_recur (a k) (Ha0 k) ltac:(pose proof (Ha0 k); lra) (Hp k)).
  - replace (- (1 / 2)) with (-1 * 1 * (1 / 2) * 1) by ring.
    apply (CV_mult (fun k => a k * J (a k) * Rpower PI (a k / 2) * (1 / 2))
             (fun k => / Gam (a k / 2 + 1) (Hp k)) (-1 * 1 * (1 / 2)) 1); [ | exact HRinv ].
    apply (CV_mult (fun k => a k * J (a k) * Rpower PI (a k / 2)) (fun _ => 1 / 2)
             (-1 * 1) (1 / 2)); [ | apply Un_cv_const ].
    apply (CV_mult (fun k => a k * J (a k)) (fun k => Rpower PI (a k / 2)) (-1) 1);
      [ exact HP | exact HQ ].
Qed.

Print Assumptions zeta_zero.

(* ================================================================= *)
(*  END ZetaZero.v.  ζ_ext(a) → −1/2 as a→0⁺ (given Γ(a/2+1)→1).       *)
(* ================================================================= *)
