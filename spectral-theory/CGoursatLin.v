(* ================================================================= *)
(*  CGoursatLin.v  —  Milestone C, brick C2a-3b: integrand linearity.   *)
(*                                                                    *)
(*  Cintf_add / seg_int_add / tri_int_add : the finite C-valued integral *)
(*  (and hence the segment and triangle integrals) is additive in the    *)
(*  integrand.  This lets Goursat split a holomorphic h = (affine part)  *)
(*  + (remainder): tri_int(h) = tri_int(affine) + tri_int(remainder),     *)
(*  the first term 0 (CGoursatFTC), the second small (the ML bound).     *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import ComplexField Cmodulus CImproperIntegral CIntegral2
        CPathIntegral CSegInt CTriangle.
Open Scope R_scope.

(* ---- real integral additivity (P10 + P13, bridging the "1*" shape) ---- *)
Lemma RInt_plus : forall g1 g2 a b
  (pr1 : Riemann_integrable g1 a b) (pr2 : Riemann_integrable g2 a b)
  (pr : Riemann_integrable (fun x => g1 x + g2 x) a b),
  a <= b -> RiemannInt pr = RiemannInt pr1 + RiemannInt pr2.
Proof.
  intros g1 g2 a b pr1 pr2 pr Hab.
  pose (pr3 := RiemannInt_P10 1 pr1 pr2).
  rewrite (RiemannInt_P18 pr pr3 Hab ltac:(intros x Hx; cbv beta; ring)).
  rewrite (RiemannInt_P13 pr1 pr2 pr3); ring.
Qed.

(* ---- Cintf is additive in the integrand (needs a <= b) ---- *)
Lemma Cintf_add : forall f1 f2 Hf1 Hf2 Hfg a b, a <= b ->
  Cintf (fun u => Cadd (f1 u) (f2 u)) Hfg a b
  = Cadd (Cintf f1 Hf1 a b) (Cintf f2 Hf2 a b).
Proof.
  intros f1 f2 Hf1 Hf2 Hfg a b Hab; apply Ceq; unfold Cadd; cbn [Re Im].
  - exact (RInt_plus (fun u => Re (f1 u)) (fun u => Re (f2 u)) a b
             (cont_RI _ (proj1 Hf1) a b) (cont_RI _ (proj1 Hf2) a b)
             (cont_RI _ (proj1 Hfg) a b) Hab).
  - exact (RInt_plus (fun u => Im (f1 u)) (fun u => Im (f2 u)) a b
             (cont_RI _ (proj2 Hf1) a b) (cont_RI _ (proj2 Hf2) a b)
             (cont_RI _ (proj2 Hfg) a b) Hab).
Qed.

(* ---- CcontC is closed under pointwise Cadd ---- *)
Lemma CcontC_add : forall f g, CcontC f -> CcontC g ->
  CcontC (fun z => Cadd (f z) (g z)).
Proof.
  intros f g Hf Hg gam Hgam; apply Ccont_add; [ apply Hf | apply Hg ]; exact Hgam.
Qed.

(* ---- segment integral additivity ---- *)
Lemma seg_int_add : forall f g (Hf : CcontC f) (Hg : CcontC g)
  (Hfg : CcontC (fun z => Cadd (f z) (g z))) a b,
  seg_int (fun z => Cadd (f z) (g z)) Hfg a b
  = Cadd (seg_int f Hf a b) (seg_int g Hg a b).
Proof.
  intros f g Hf Hg Hfg a b.
  transitivity (Cintf (fun u => Cadd (Cmul (f (seg a b u)) (seg' a b u))
                                     (Cmul (g (seg a b u)) (seg' a b u)))
                 (Ccont_add _ _ (seg_ig_cont f Hf a b) (seg_ig_cont g Hg a b)) 0 1).
  - unfold seg_int; apply Cintf_ext; intro u; cbv beta; ring.
  - rewrite (Cintf_add (fun u => Cmul (f (seg a b u)) (seg' a b u))
              (fun u => Cmul (g (seg a b u)) (seg' a b u))
              (seg_ig_cont f Hf a b) (seg_ig_cont g Hg a b)
              (Ccont_add _ _ (seg_ig_cont f Hf a b) (seg_ig_cont g Hg a b))
              0 1 ltac:(lra)); reflexivity.
Qed.

(* ---- triangle integral additivity ---- *)
Lemma tri_int_add : forall f g (Hf : CcontC f) (Hg : CcontC g)
  (Hfg : CcontC (fun z => Cadd (f z) (g z))) v0 v1 v2,
  tri_int (fun z => Cadd (f z) (g z)) Hfg v0 v1 v2
  = Cadd (tri_int f Hf v0 v1 v2) (tri_int g Hg v0 v1 v2).
Proof.
  intros f g Hf Hg Hfg v0 v1 v2; unfold tri_int.
  rewrite (seg_int_add f g Hf Hg Hfg v0 v1),
          (seg_int_add f g Hf Hg Hfg v1 v2),
          (seg_int_add f g Hf Hg Hfg v2 v0); ring.
Qed.

Print Assumptions tri_int_add.

(* ================================================================= *)
(*  END CGoursatLin.v  —  integrand linearity (C2a-3b).                 *)
(* ================================================================= *)
