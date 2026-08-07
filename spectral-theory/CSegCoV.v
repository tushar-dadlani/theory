(* ================================================================= *)
(*  CSegCoV.v  —  Milestone C, brick C2a-1 (core): change of variables  *)
(*  for the general finite C-valued integral Cintf, and the segment      *)
(*  reparametrization laws (reversal, midpoint concatenation) that the   *)
(*  Goursat bisection combinatorics need.                               *)
(*                                                                    *)
(*  Cintf_cov : for an increasing C^1 substitution g on [a,b],           *)
(*     ∫_a^b g'(t)·G(g t) dt = ∫_{g a}^{g b} G,                          *)
(*  proved componentwise from LocalCoV.cov_local.                       *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia FunctionalExtensionality.
Require Import ComplexField Cmodulus CImproperIntegral CDerivLine
        ContinuousCoV LocalCoV CIntegral2.
Open Scope R_scope.

(* the C-valued change of variables (increasing substitution) *)
Lemma Cintf_cov : forall (G : R -> C) (g g' : R -> R) (a b : R)
  (HG : Ccont G) (HGg : Ccont (fun t => Cmul (RtoC (g' t)) (G (g t)))),
  a <= b ->
  (forall t, a <= t <= b -> derivable_pt_lim g t (g' t)) ->
  (forall t, a <= t <= b -> continuity_pt g' t) ->
  (forall t, a <= t <= b -> g a <= g t <= g b) ->
  Cintf (fun t => Cmul (RtoC (g' t)) (G (g t))) HGg a b = Cintf G HG (g a) (g b).
Proof.
  intros G g g' a b HG HGg Hab Hd Hgc Hmap.
  assert (Hgcont : forall t, a <= t <= b -> continuity_pt g t)
    by (intros t Ht; apply derivable_continuous_pt; exists (g' t); apply Hd; exact Ht).
  assert (Hgab : g a <= g b) by (destruct (Hmap b ltac:(lra)); assumption).
  assert (HcRe : forall t, a <= t <= b -> continuity_pt (fun s => Re (G (g s)) * g' s) t).
  { intros t Ht; apply continuity_pt_mult;
      [ apply (continuity_pt_comp g (fun u => Re (G u)) t);
          [ apply Hgcont; exact Ht | apply (proj1 HG) ]
      | apply Hgc; exact Ht ]. }
  assert (HcIm : forall t, a <= t <= b -> continuity_pt (fun s => Im (G (g s)) * g' s) t).
  { intros t Ht; apply continuity_pt_mult;
      [ apply (continuity_pt_comp g (fun u => Im (G u)) t);
          [ apply Hgcont; exact Ht | apply (proj2 HG) ]
      | apply Hgc; exact Ht ]. }
  set (prLRe := continuity_implies_RiemannInt Hab HcRe).
  set (prLIm := continuity_implies_RiemannInt Hab HcIm).
  apply Ceq; cbn [Re Im].
  - transitivity (RiemannInt prLRe).
    + apply RiemannInt_P18;
        [ exact Hab | intros x Hx; cbv beta; rewrite Re_RtoC_mul; ring ].
    + apply (cov_local g g' (fun u => Re (G u)) a b Hab Hd Hgc Hmap
              (fun u _ => proj1 HG u) prLRe (cont_RI (fun u => Re (G u)) (proj1 HG) (g a) (g b))).
  - transitivity (RiemannInt prLIm).
    + apply RiemannInt_P18;
        [ exact Hab | intros x Hx; cbv beta; rewrite Im_RtoC_mul; ring ].
    + apply (cov_local g g' (fun u => Im (G u)) a b Hab Hd Hgc Hmap
              (fun u _ => proj2 HG u) prLIm (cont_RI (fun u => Im (G u)) (proj2 HG) (g a) (g b))).
Qed.

Print Assumptions Cintf_cov.

(* ================================================================= *)
(*  END CSegCoV.v  —  C-valued change of variables (core of C2a-1).      *)
(* ================================================================= *)
