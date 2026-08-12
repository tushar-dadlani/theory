(* ================================================================= *)
(*  SelfDualCenter.v                                                  *)
(*                                                                    *)
(*  WHY the seam sits at Re s = 1/2: self-duality pins the centre.    *)
(*                                                                    *)
(*  A weight-w reflection  z |-> w - z  has its fixed real-part locus  *)
(*  at Re z = w/2 (wrefl_center).  The functional equation is the      *)
(*  weight-ONE reflection (FE_weight_one, from XiC_symmetric), so its  *)
(*  centre is Re = 1/2 (self_dual_center) -- exactly the coherence     *)
(*  seam where XiC is real (self_dual_is_coherence).                   *)
(*                                                                    *)
(*  The weight is 1 for a self-duality reason, not by fiat:            *)
(*    - it is the reflection of the THETA-derived functional equation  *)
(*      J s = J (1 - s)  (RiemannThetaFE.J_symmetric), whose "1" is    *)
(*      2 x (1/2), the self-dual weight of the modular transform       *)
(*      theta(1/t) = t^{1/2} theta(t)  (GaussThetaTransform,           *)
(*      GaussSelfDual: the Gaussian is its own Fourier transform);     *)
(*    - equivalently the product-formula constant prod_v |x|_v = 1     *)
(*      (ArchimedeanTower: |n|_inf = 1 / prod_p |n|_p).               *)
(*  The 1/2 of the critical line is literally the 1/2 (= sqrt) of the  *)
(*  theta transformation -- the archimedean self-dual weight.          *)
(*                                                                    *)
(*  Axiom-clean (standard classical-Reals axioms only).               *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra.
Require Import ComplexField RiemannXiEntire CoherenceSingularity RiemannThetaFE.
Open Scope R_scope.

(* weight-w reflection on C:  z |-> w - z. *)
Definition wrefl (w : R) (z : C) : C := Cminus (RtoC w) z.

Lemma Re_wrefl : forall w z, Re (wrefl w z) = w - Re z.
Proof. intros w z; unfold wrefl, Cminus, RtoC; simpl; ring. Qed.

(* the fixed real-part locus of a weight-w reflection is Re z = w/2 *)
Lemma wrefl_center : forall w z, Re (wrefl w z) = Re z <-> Re z = w / 2.
Proof. intros w z; rewrite Re_wrefl; split; intro; lra. Qed.

(* the functional equation is the WEIGHT-ONE reflection *)
Lemma FE_weight_one : forall z, XiC z = XiC (wrefl 1 z).
Proof. intro z; unfold wrefl; apply XiC_symmetric. Qed.

(* SELF-DUAL CENTRE: the weight-one reflection fixes exactly Re = 1/2 *)
Theorem self_dual_center : forall z, Re (wrefl 1 z) = Re z <-> Re z = / 2.
Proof. intro z; rewrite (wrefl_center 1 z); split; intro; lra. Qed.

(* the self-dual centre IS the coherence seam: XiC is real there *)
Theorem self_dual_is_coherence : forall z,
  Re (wrefl 1 z) = Re z -> Im (XiC z) = 0.
Proof. intros z H; apply coherence_line, self_dual_center; exact H. Qed.

(* the weight-one reflection is the theta-derived functional equation:  *)
(* J s = J (1 - s), the "1" = 2 x (1/2) from theta(1/t) = t^{1/2}theta(t) *)
Corollary theta_FE_weight_one : forall s, s <> 0 -> s <> 1 -> J s = J (1 - s).
Proof. exact J_symmetric. Qed.

(* Punchline: the critical line Re = 1/2 is the self-dual centre        *)
(* (weight/2 with weight = 1), and it coincides with the coherence      *)
(* seam.  1/2 is the archimedean self-dual weight, not an accident.     *)
Theorem critical_line_pinned : forall z,
  Re z = / 2 <-> Re (wrefl 1 z) = Re z.
Proof. intro z; symmetry; apply self_dual_center. Qed.

Print Assumptions critical_line_pinned.
Print Assumptions self_dual_is_coherence.
