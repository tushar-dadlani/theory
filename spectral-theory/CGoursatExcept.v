(* ================================================================= *)
(*  CGoursatExcept.v  —  Milestone C, brick C4-3: Goursat with one      *)
(*  exceptional point (removable singularity).                          *)
(*                                                                    *)
(*  h continuous everywhere but holomorphic only on U∖{p} still has       *)
(*  vanishing triangle integrals.  Foundation: a general segment split    *)
(*  seg_split_param (Chasles at an arbitrary parameter δ), generalising   *)
(*  CSegInt.seg_concat (δ=½).                                            *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia Classical.
Require Import ComplexField Cmodulus CSeries CIntegral2 CSegCoV CSegInt
        CPathIntegral CTriangle Holomorphic CHoloCalculus CGoursatML
        CGoursatConv CPrimConv.
Open Scope R_scope.

Section SplitParam.
Variables (f : C -> C) (Hf : CcontC f) (a c : C).
Let F := fun u => Cmul (f (seg a c u)) (seg' a c u).

Lemma seg_sp1 : forall delta v, seg a c (delta * v + 0) = seg a (seg a c delta) v.
Proof. intros; unfold seg, Cadd, Cmul, RtoC, Cminus; apply Ceq; cbn; ring. Qed.
Lemma seg_sp2 : forall delta v, seg a c ((1 - delta) * v + delta) = seg (seg a c delta) c v.
Proof. intros; unfold seg, Cadd, Cmul, RtoC, Cminus; apply Ceq; cbn; ring. Qed.
Lemma scal_sp1 : forall delta, Cmul (RtoC delta) (Cminus c a) = Cminus (seg a c delta) a.
Proof. intros; unfold seg, Cadd, Cmul, RtoC, Cminus; apply Ceq; cbn; ring. Qed.
Lemma scal_sp2 : forall delta, Cmul (RtoC (1 - delta)) (Cminus c a) = Cminus c (seg a c delta).
Proof. intros; unfold seg, Cadd, Cmul, RtoC, Cminus; apply Ceq; cbn; ring. Qed.

Lemma HGsp1 : forall delta,
  Ccont (fun v => Cmul (RtoC delta) (F ((fun w => delta * w + 0) v))).
Proof.
  intro delta; apply Ccont_scal; unfold F, seg'.
  apply Ccont_mul; [ apply Hf, Ccont_seg_comp | apply Ccont_const ].
  intro x; apply derivable_continuous_pt; exists delta; apply dlin.
Qed.
Lemma HGsp2 : forall delta,
  Ccont (fun v => Cmul (RtoC (1 - delta)) (F ((fun w => (1 - delta) * w + delta) v))).
Proof.
  intro delta; apply Ccont_scal; unfold F, seg'.
  apply Ccont_mul; [ apply Hf, Ccont_seg_comp | apply Ccont_const ].
  intro x; apply derivable_continuous_pt; exists (1 - delta); apply dlin.
Qed.

Theorem seg_split_param : forall delta, 0 <= delta <= 1 ->
  seg_int f Hf a c
  = Cadd (seg_int f Hf a (seg a c delta)) (seg_int f Hf (seg a c delta) c).
Proof.
  intros delta [Hd0 Hd1].
  assert (Hcov1 : Cintf (fun v => Cmul (RtoC delta) (F ((fun w => delta * w + 0) v)))
                    (HGsp1 delta) 0 1
                  = Cintf F (seg_ig_cont f Hf a c) 0 delta).
  { transitivity (Cintf F (seg_ig_cont f Hf a c)
                    ((fun w => delta * w + 0) 0) ((fun w => delta * w + 0) 1)).
    - apply (Cintf_cov F (fun w => delta * w + 0) (fun _ => delta) 0 1
              (seg_ig_cont f Hf a c) (HGsp1 delta) ltac:(lra)
              (fun t _ => dlin delta 0 t)
              (fun t _ => continuity_pt_const (fun _ => delta) t (fun _ _ => eq_refl))
              ltac:(intros t Ht; cbv beta; nra)).
    - f_equal; cbv beta; ring. }
  assert (Hcov2 : Cintf (fun v => Cmul (RtoC (1 - delta)) (F ((fun w => (1 - delta) * w + delta) v)))
                    (HGsp2 delta) 0 1
                  = Cintf F (seg_ig_cont f Hf a c) delta 1).
  { transitivity (Cintf F (seg_ig_cont f Hf a c)
                    ((fun w => (1 - delta) * w + delta) 0) ((fun w => (1 - delta) * w + delta) 1)).
    - apply (Cintf_cov F (fun w => (1 - delta) * w + delta) (fun _ => 1 - delta) 0 1
              (seg_ig_cont f Hf a c) (HGsp2 delta) ltac:(lra)
              (fun t _ => dlin (1 - delta) delta t)
              (fun t _ => continuity_pt_const (fun _ => 1 - delta) t (fun _ _ => eq_refl))
              ltac:(intros t Ht; cbv beta; nra)).
    - f_equal; cbv beta; ring. }
  unfold seg_int; fold F.
  rewrite (Cintf_additive F (seg_ig_cont f Hf a c) 0 delta 1).
  rewrite <- Hcov1, <- Hcov2; f_equal.
  - apply Cintf_ext; intro v; cbv beta; unfold F, seg'; rewrite seg_sp1.
    transitivity (Cmul (f (seg a (seg a c delta) v)) (Cmul (RtoC delta) (Cminus c a)));
      [ ring | rewrite scal_sp1; reflexivity ].
  - apply Cintf_ext; intro v; cbv beta; unfold F, seg'; rewrite seg_sp2.
    transitivity (Cmul (f (seg (seg a c delta) c v)) (Cmul (RtoC (1 - delta)) (Cminus c a)));
      [ ring | rewrite scal_sp2; reflexivity ].
Qed.

End SplitParam.

(* ---- cut the corner at p: p_a = seg p a δ, p_b = seg p b δ ---- *)
Lemma tri_corner_split : forall f (Hf : CcontC f) p a b delta, 0 <= delta <= 1 ->
  tri_int f Hf p a b
  = Cadd (tri_int f Hf p (seg p a delta) (seg p b delta))
    (Cadd (tri_int f Hf (seg p a delta) a b)
          (tri_int f Hf (seg p a delta) b (seg p b delta))).
Proof.
  intros f Hf p a b delta H; unfold tri_int.
  rewrite (seg_split_param f Hf p a delta H).
  rewrite (seg_reverse f Hf p b), (seg_split_param f Hf p b delta H).
  rewrite (seg_reverse f Hf p (seg p b delta)).
  rewrite (seg_reverse f Hf (seg p a delta) b).
  rewrite (seg_reverse f Hf (seg p a delta) (seg p b delta)).
  rewrite (seg_reverse f Hf (seg p b delta) b).
  ring.
Qed.

Print Assumptions tri_corner_split.

(* ================================================================= *)
(*  END (stage 2) — corner-cut identity.  ML shrink at p follows.       *)
(* ================================================================= *)
