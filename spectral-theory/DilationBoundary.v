(* ================================================================= *)
(*  DilationBoundary.v                                                *)
(*                                                                    *)
(*  THE CONCRETE BOUNDARY CONDITION (Package A) for the Mellin-        *)
(*  diagonal dilation representation (BerryKeatingDilation.v).         *)
(*                                                                    *)
(*  The operator lives on the multiplicative half-line R+ modulo the  *)
(*  inversion x |-> 1/x (fundamental domain [1,oo), the fixed point    *)
(*  x=1 the boundary).  The two ends x->0 and x->oo are matched by the *)
(*  theta self-duality  theta(1/t) = sqrt(t) . theta(t)               *)
(*  (GaussThetaTransform.theta_transform) -- the same sqrt (weight     *)
(*  1/2) by which SelfDualCenter pins the seam at Re = 1/2.  The        *)
(*  matched boundary functional is the completed zeta,                 *)
(*     B = Bxi t = XiC(1/2 + it) = xi(1/2 + it).                        *)
(*                                                                    *)
(*  The concrete content, all Qed (standard classical-Reals axioms):   *)
(*   - Bxi_real   : the boundary functional is REAL on the seam        *)
(*                  (unitary / self-adjoint boundary);                 *)
(*   - crit_neg_conj : inversion acts as t |-> -t = conjugation;       *)
(*   - Bxi_even   : Bxi(-t) = Bxi t -- THE x<->1/x matching, as         *)
(*                  evenness of the boundary functional;               *)
(*   - Sphase_unit: the scattering phase is 1 (unitary extension);     *)
(*   - weight_half_center : the -1/2 exponent of psi_t = x^{-1/2+it}    *)
(*                  is the theta self-dual weight (center Re=1/2);      *)
(*   - boundary_selects_zeros : the boundary spectrum is exactly the    *)
(*                  on-seam zeta zeros.                                 *)
(*                                                                    *)
(*  Still OPEN (Hilbert-Polya gap, no axiom): that this reflection      *)
(*  boundary is the ACTUAL one realizing the zeros as the spectrum of   *)
(*  a naturally-arising H, rather than inserted via zord.              *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra.
Require Import ComplexField RiemannXiEntire ZetaZeroQuadruple CoherenceSingularity
        SelfDualCenter BerryKeatingDilation.
Open Scope R_scope.

(* 1.  the boundary functional is real on the seam (unitary boundary) *)
Lemma Bxi_real : forall t, Bxi t = RtoC (xir t).
Proof. intro t; unfold Bxi; apply XiC_crit_eq. Qed.

(* 2.  inversion x |-> 1/x acts on the seam parameter as t |-> -t,     *)
(*     i.e. as conjugation of  crit t = 1/2 + it.                      *)
Lemma crit_neg_conj : forall t, crit (- t) = Cconj (crit t).
Proof. intro t; unfold crit, Cconj; apply Ceq; simpl; ring. Qed.

(* 3.  THE x<->1/x BOUNDARY MATCHING, as evenness of B: Bxi(-t)=Bxi t. *)
(*     Functional equation (XiC_conj: Schwarz) + reality on the seam.  *)
Lemma Bxi_even : forall t, Bxi (- t) = Bxi t.
Proof.
  intro t; unfold Bxi.
  rewrite crit_neg_conj, XiC_conj, XiC_crit_eq, Cconj_RtoC; reflexivity.
Qed.

(* 4.  the scattering phase of the boundary is 1 (unitary extension).  *)
Definition Sphase (t : R) : C := Cmul (Bxi (- t)) (Cinv (Bxi t)).

Lemma Sphase_unit : forall t, Bxi t <> C0 -> Sphase t = C1.
Proof.
  intros t Ht. unfold Sphase. rewrite Bxi_even.
  assert (Ccomm : forall x y, Cmul x y = Cmul y x)
    by (intros x y; unfold Cmul; apply Ceq; simpl; ring).
  rewrite Ccomm; apply Cinv_l; exact Ht.
Qed.

(* 5.  the -1/2 exponent of psi_t = x^{-1/2+it} is the theta self-dual  *)
(*     weight (the sqrt of theta(1/t)=sqrt t theta t); equivalently the *)
(*     weight-1 reflection center Re = 1/2 (SelfDualCenter).            *)
Corollary weight_half_center : forall z, Re (wrefl 1 z) = Re z <-> Re z = / 2.
Proof. exact self_dual_center. Qed.

(* 6.  the reflection-matched boundary spectrum IS the on-seam zeros.   *)
Lemma boundary_selects_zeros : forall t, spec Bxi t <-> XiC (crit t) = C0.
Proof. exact spec_Bxi_zero. Qed.

Lemma boundary_zeros_real : forall t, spec Bxi t <-> xir t = 0.
Proof. exact spec_Bxi_xir. Qed.

Print Assumptions Bxi_even.
Print Assumptions Sphase_unit.
Print Assumptions boundary_selects_zeros.
