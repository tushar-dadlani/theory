(* ================================================================= *)
(*  CSegInt.v  —  Milestone C, brick C2a-1: the segment integral and    *)
(*  its reparametrization laws (midpoint concatenation, reversal).      *)
(*                                                                    *)
(*  seg_int f a b = ∫ over the straight segment [a,b] of f, built on     *)
(*  CPathIntegral.pathint / CIntegral2.Cintf.  The concatenation law     *)
(*  seg_int a c = seg_int a m + seg_int m c (m the midpoint) and the     *)
(*  reversal seg_int b a = − seg_int a b are the inputs the Goursat      *)
(*  bisection (C2a-2) needs.  Concatenation uses the increasing change   *)
(*  of variables CSegCoV.Cintf_cov on each half; reversal uses a         *)
(*  reflection (u ↦ 1−u) built by FTC.                                  *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia FunctionalExtensionality.
Require Import ComplexField Cmodulus CImproperIntegral ContinuousCoV CIntegral2
        CPathIntegral CSegCoV.
Open Scope R_scope.

(* ---- f : C -> C preserves continuity of paths ---- *)
Definition CcontC (f : C -> C) : Prop :=
  forall g : R -> C, Ccont g -> Ccont (fun u => f (g u)).

Lemma Ccont_RtoC : forall (g : R -> R), (forall x, continuity_pt g x) ->
  Ccont (fun v => RtoC (g v)).
Proof.
  intros g Hg; split; intro x;
    [ apply Hg | apply continuity_pt_const; intros a b; reflexivity ].
Qed.

(* a segment reparametrized by a continuous real map is a continuous path *)
Lemma Ccont_seg_comp : forall a c (g : R -> R), (forall x, continuity_pt g x) ->
  Ccont (fun v => seg a c (g v)).
Proof.
  intros a c g Hg; unfold seg.
  apply Ccont_add; [ apply Ccont_const | ].
  apply Ccont_mul; [ apply Ccont_RtoC; exact Hg | apply Ccont_const ].
Qed.

(* Cintf depends only on the integrand pointwise *)
Lemma Cintf_ext : forall f1 f2 Hf1 Hf2 a b,
  (forall u, f1 u = f2 u) -> Cintf f1 Hf1 a b = Cintf f2 Hf2 a b.
Proof.
  intros f1 f2 Hf1 Hf2 a b Heq.
  assert (Hfe : f1 = f2) by (apply functional_extensionality; exact Heq).
  revert Hf2; rewrite <- Hfe; intro Hf2; apply Cintf_irrel.
Qed.

(* ---- affine derivability helper ---- *)
Lemma dlin : forall p q t, derivable_pt_lim (fun v => p * v + q) t p.
Proof.
  intros p q t.
  assert (H : derivable_pt_lim (fun v => p * v + q) t (p * 1 + 0)).
  { apply (derivable_pt_lim_plus (fun v => p * v) (fun v => q) t (p * 1) 0).
    - apply (derivable_pt_lim_scal id p t 1), derivable_pt_lim_id.
    - apply derivable_pt_lim_const. }
  replace (p * 1 + 0) with p in H by ring; exact H.
Qed.

(* ---- the segment integrand is continuous for a CcontC f ---- *)
Lemma seg_ig_cont : forall f (Hf : CcontC f) a b,
  Ccont (fun u => Cmul (f (seg a b u)) (seg' a b u)).
Proof.
  intros f Hf a b; apply Ccont_mul.
  - apply Hf, Ccont_seg.
  - unfold seg'; apply Ccont_const.
Qed.

Definition seg_int (f : C -> C) (Hf : CcontC f) (a b : C) : C :=
  Cintf (fun u => Cmul (f (seg a b u)) (seg' a b u)) (seg_ig_cont f Hf a b) 0 1.

Definition mid (a c : C) : C := Cmul (RtoC (/ 2)) (Cadd a c).

(* geometry of the midpoint *)
Lemma seg_half1 : forall a c v, seg a c (/ 2 * v + 0) = seg a (mid a c) v.
Proof. intros a c v; unfold seg, mid, Cadd, Cmul, RtoC, Cminus; apply Ceq; cbn; field. Qed.

Lemma seg_half2 : forall a c v, seg a c (/ 2 * v + / 2) = seg (mid a c) c v.
Proof. intros a c v; unfold seg, mid, Cadd, Cmul, RtoC, Cminus; apply Ceq; cbn; field. Qed.

Lemma scal_ma : forall a c, Cmul (RtoC (/ 2)) (Cminus c a) = Cminus (mid a c) a.
Proof. intros a c; unfold mid, Cadd, Cmul, RtoC, Cminus; apply Ceq; cbn; field. Qed.

Lemma scal_cm : forall a c, Cmul (RtoC (/ 2)) (Cminus c a) = Cminus c (mid a c).
Proof. intros a c; unfold mid, Cadd, Cmul, RtoC, Cminus; apply Ceq; cbn; field. Qed.

Section Concat.
Variables (f : C -> C) (Hf : CcontC f) (a c : C).

Let F := fun u => Cmul (f (seg a c u)) (seg' a c u).

Lemma HGhalf1 : Ccont (fun v => Cmul (RtoC (/ 2)) (F ((fun w => / 2 * w + 0) v))).
Proof.
  apply Ccont_scal; unfold F, seg'.
  apply Ccont_mul; [ apply Hf, Ccont_seg_comp | apply Ccont_const ].
  intro x; apply derivable_continuous_pt; exists (/ 2); apply dlin.
Qed.

Lemma HGhalf2 : Ccont (fun v => Cmul (RtoC (/ 2)) (F ((fun w => / 2 * w + / 2) v))).
Proof.
  apply Ccont_scal; unfold F, seg'.
  apply Ccont_mul; [ apply Hf, Ccont_seg_comp | apply Ccont_const ].
  intro x; apply derivable_continuous_pt; exists (/ 2); apply dlin.
Qed.

Theorem seg_concat :
  seg_int f Hf a c = Cadd (seg_int f Hf a (mid a c)) (seg_int f Hf (mid a c) c).
Proof.
  assert (Hcov1 : Cintf (fun v => Cmul (RtoC (/ 2)) (F ((fun w => / 2 * w + 0) v))) HGhalf1 0 1
                  = Cintf F (seg_ig_cont f Hf a c) 0 (/ 2)).
  { transitivity (Cintf F (seg_ig_cont f Hf a c)
                   ((fun w => / 2 * w + 0) 0) ((fun w => / 2 * w + 0) 1)).
    - apply (Cintf_cov F (fun w => / 2 * w + 0) (fun _ => / 2) 0 1
              (seg_ig_cont f Hf a c) HGhalf1 ltac:(lra)
              (fun t _ => dlin (/ 2) 0 t)
              (fun t _ => continuity_pt_const (fun _ => / 2) t (fun _ _ => eq_refl))
              ltac:(intros t Ht; cbv beta; lra)).
    - f_equal; cbv beta; field. }
  assert (Hcov2 : Cintf (fun v => Cmul (RtoC (/ 2)) (F ((fun w => / 2 * w + / 2) v))) HGhalf2 0 1
                  = Cintf F (seg_ig_cont f Hf a c) (/ 2) 1).
  { transitivity (Cintf F (seg_ig_cont f Hf a c)
                   ((fun w => / 2 * w + / 2) 0) ((fun w => / 2 * w + / 2) 1)).
    - apply (Cintf_cov F (fun w => / 2 * w + / 2) (fun _ => / 2) 0 1
              (seg_ig_cont f Hf a c) HGhalf2 ltac:(lra)
              (fun t _ => dlin (/ 2) (/ 2) t)
              (fun t _ => continuity_pt_const (fun _ => / 2) t (fun _ _ => eq_refl))
              ltac:(intros t Ht; cbv beta; lra)).
    - f_equal; cbv beta; field. }
  unfold seg_int; fold F.
  rewrite (Cintf_additive F (seg_ig_cont f Hf a c) 0 (/ 2) 1).
  rewrite <- Hcov1, <- Hcov2; f_equal.
  - apply Cintf_ext; intro v; cbv beta; unfold F, seg'; rewrite seg_half1.
    transitivity (Cmul (f (seg a (mid a c) v)) (Cmul (RtoC (/ 2)) (Cminus c a)));
      [ ring | rewrite scal_ma; reflexivity ].
  - apply Cintf_ext; intro v; cbv beta; unfold F, seg'; rewrite seg_half2.
    transitivity (Cmul (f (seg (mid a c) c v)) (Cmul (RtoC (/ 2)) (Cminus c a)));
      [ ring | rewrite scal_cm; reflexivity ].
Qed.

End Concat.

(* ================================================================= *)
(*  Segment reversal (reflection u ↦ 1−u, via FTC).                    *)
(* ================================================================= *)

(* the combined reflect+opp real change of variables:  ∫₀¹ −φ(1−u) = −∫₀¹ φ *)
Lemma RInt_reflect_opp : forall phi
  (pr1 : Riemann_integrable (fun u => - phi (1 - u)) 0 1)
  (pr2 : Riemann_integrable phi 0 1),
  (forall x, 0 <= x <= 1 -> continuity_pt phi x) ->
  RiemannInt pr1 = - RiemannInt pr2.
Proof.
  intros phi pr1 pr2 Hcont.
  assert (H01 : (0:R) <= 1) by lra.
  destruct (RiemannInt_P30 H01 Hcont) as [Phi HPhi].
  rewrite (FTC_antideriv phi Phi 0 1 H01 Hcont pr2 HPhi).
  assert (Hc1mu : forall x, continuity_pt (fun u => 1 - u) x)
    by (intro x; apply derivable_continuous_pt, derivable_pt_minus;
        [ apply derivable_pt_const | apply derivable_pt_id ]).
  assert (Hcont1 : forall x, 0 <= x <= 1 -> continuity_pt (fun u => - phi (1 - u)) x).
  { intros x Hx; apply continuity_pt_opp.
    apply (continuity_pt_comp (fun u => 1 - u) phi x);
      [ apply Hc1mu | apply Hcont; lra ]. }
  assert (Hanti : antiderivative (fun u => - phi (1 - u)) (fun u => Phi (1 - u)) 0 1).
  { split; [ | lra ]; intros x Hx.
    destruct HPhi as [HPd _].
    destruct (HPd (1 - x) ltac:(lra)) as [prx Hprx].
    assert (HL : derivable_pt_lim Phi (1 - x) (phi (1 - x)))
      by (destruct prx as [l Hl]; simpl in Hprx; subst; exact Hl).
    assert (Hd1 : derivable_pt_lim (fun u => 1 - u) x (- 1)).
    { replace (-1) with (0 - 1) by ring.
      apply (derivable_pt_lim_minus (fun _ => 1) (fun u => u) x 0 1);
        [ apply derivable_pt_lim_const | apply derivable_pt_lim_id ]. }
    assert (Hcomp0 : derivable_pt_lim (comp Phi (fun u => 1 - u)) x (phi (1 - x) * (- 1)))
      by (apply (derivable_pt_lim_comp (fun u => 1 - u) Phi x (- 1) (phi (1 - x)));
          [ exact Hd1 | exact HL ]).
    assert (Hcomp : derivable_pt_lim (fun u => Phi (1 - u)) x (- phi (1 - x)))
      by (replace (- phi (1 - x)) with (phi (1 - x) * (- 1)) by ring; exact Hcomp0).
    exists (exist (fun l => derivable_pt_lim (fun u => Phi (1 - u)) x l)
              (- phi (1 - x)) Hcomp); reflexivity. }
  rewrite (FTC_antideriv (fun u => - phi (1 - u)) (fun u => Phi (1 - u)) 0 1 H01 Hcont1 pr1 Hanti).
  replace (1 - 0) with 1 by ring; replace (1 - 1) with 0 by ring; ring.
Qed.

Lemma seg_reflect : forall a b u, seg b a u = seg a b (1 - u).
Proof. intros a b u; unfold seg, Cadd, Cmul, RtoC, Cminus; apply Ceq; cbn; ring. Qed.

Lemma seg_rev_pt : forall (f : C -> C) a b u,
  Cmul (f (seg b a u)) (seg' b a u)
  = Copp (Cmul (f (seg a b (1 - u))) (seg' a b (1 - u))).
Proof. intros f a b u; unfold seg'; rewrite seg_reflect; ring. Qed.

Theorem seg_reverse : forall f (Hf : CcontC f) a b,
  seg_int f Hf b a = Copp (seg_int f Hf a b).
Proof.
  intros f Hf a b; unfold seg_int.
  set (phiR := fun w => Re (Cmul (f (seg a b w)) (seg' a b w))).
  set (phiI := fun w => Im (Cmul (f (seg a b w)) (seg' a b w))).
  apply Ceq; unfold Copp; cbn [Re Im].
  - transitivity (RiemannInt (cont_RI (fun u => - phiR (1 - u))
                   ltac:(intro x; apply continuity_pt_opp;
                     apply (continuity_pt_comp (fun u => 1 - u) phiR x);
                       [ apply derivable_continuous_pt, derivable_pt_minus;
                           [ apply derivable_pt_const | apply derivable_pt_id ]
                       | apply (proj1 (seg_ig_cont f Hf a b)) ]) 0 1)).
    + apply RiemannInt_P18; [ lra | intros x Hx; cbv beta; unfold phiR;
        rewrite seg_rev_pt; unfold Copp; cbn [Re]; ring ].
    + apply (RInt_reflect_opp phiR _ (cont_RI _ (proj1 (seg_ig_cont f Hf a b)) 0 1)
              (fun x _ => proj1 (seg_ig_cont f Hf a b) x)).
  - transitivity (RiemannInt (cont_RI (fun u => - phiI (1 - u))
                   ltac:(intro x; apply continuity_pt_opp;
                     apply (continuity_pt_comp (fun u => 1 - u) phiI x);
                       [ apply derivable_continuous_pt, derivable_pt_minus;
                           [ apply derivable_pt_const | apply derivable_pt_id ]
                       | apply (proj2 (seg_ig_cont f Hf a b)) ]) 0 1)).
    + apply RiemannInt_P18; [ lra | intros x Hx; cbv beta; unfold phiI;
        rewrite seg_rev_pt; unfold Copp; cbn [Im]; ring ].
    + apply (RInt_reflect_opp phiI _ (cont_RI _ (proj2 (seg_ig_cont f Hf a b)) 0 1)
              (fun x _ => proj2 (seg_ig_cont f Hf a b) x)).
Qed.

Print Assumptions seg_concat.
Print Assumptions seg_reverse.

(* ================================================================= *)
(*  END CSegInt.v  —  segment integral + concatenation (reversal next). *)
(* ================================================================= *)
