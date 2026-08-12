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

(* ----------------------------------------------------------------- *)
(*  7.  NO ZERO OFF THE REFLECTION AXIS STRUCTURE                     *)
(*                                                                    *)
(*  The "reflection axis structure" is the Klein-4 group of XiC-      *)
(*  symmetries {id, z|->1-z (FE), z|->conj z (Schwarz), z|->1-conj z   *)
(*  (Sbar, the line reflection)}.  The fixed axis of the composite     *)
(*  line reflection Sbar is exactly Re z = 1/2 (Sbar_fixed_iff).       *)
(*                                                                    *)
(*  The non-tautological content: the two nontrivial reflections --    *)
(*  the functional-equation image 1-z and the Schwarz image conj z --  *)
(*  COINCIDE precisely on the axis (refl_collapse_iff).  Off the axis   *)
(*  they genuinely differ (offaxis_no_collapse): the zero orbit is a    *)
(*  true 4-element quadruple.  For every point Bxi samples (crit t, on  *)
(*  the axis) the orbit DEGENERATES to the mirror pair {crit t,         *)
(*  crit(-t)} -- so Bxi has NO zero whose orbit escapes the axis.       *)
(* ----------------------------------------------------------------- *)

(* the FE-reflection 1-z and the Schwarz-reflection conj z agree iff    *)
(* z is on the reflection axis Re z = 1/2 -- the orbit-collapse test.    *)
Lemma refl_collapse_iff : forall z, Cminus C1 z = Cconj z <-> Re z = / 2.
Proof.
  intro z; split.
  - intro H; apply (f_equal Re) in H; unfold Cminus, Cconj, C1 in H; simpl in H; lra.
  - intro H; unfold Cminus, Cconj, C1; apply Ceq; simpl; lra.
Qed.

(* off the axis the two reflections DIFFER: a genuine 4-fold orbit.     *)
Corollary offaxis_no_collapse : forall z, Re z <> / 2 -> Cminus C1 z <> Cconj z.
Proof. intros z H Hc; apply H, refl_collapse_iff; exact Hc. Qed.

(* on the seam the FE-image and Schwarz-image are both the mirror point  *)
(* crit(-t); the line reflection Sbar fixes crit t.  The XiC-quadruple   *)
(* {z, 1-z, conj z, 1-conj z} at z=crit t collapses to {crit t, crit(-t)}. *)
Lemma FE_crit : forall t, Cminus C1 (crit t) = crit (- t).
Proof. intro t; unfold crit, Cminus, C1; apply Ceq; simpl; lra. Qed.

Lemma Sbar_crit_fixed : forall t, Sbar (crit t) = crit t.
Proof. intro t; apply Sbar_fixed_iff; reflexivity. Qed.

(* the boundary zero set is closed under the mirror reflection t |-> -t. *)
Lemma Bxi_zero_reflect : forall t, spec Bxi t <-> spec Bxi (- t).
Proof. intro t; unfold spec; rewrite Bxi_even; tauto. Qed.

(* HEADLINE: every boundary zero sits ON the reflection axis -- its FE-  *)
(* image and Schwarz-image coincide and Sbar fixes it.  None off it.     *)
Theorem Bxi_no_offaxis_zero : forall t,
  spec Bxi t -> Sbar (crit t) = crit t /\ Cminus C1 (crit t) = Cconj (crit t).
Proof.
  intros t _; split; [ apply Sbar_crit_fixed | rewrite FE_crit; apply crit_neg_conj ].
Qed.

(* and the whole XiC zero-orbit of a boundary zero is just the mirror     *)
(* pair {crit t, crit(-t)} -- both selected by Bxi (Bxi_zero_reflect).    *)
Corollary Bxi_zero_orbit_pair : forall t,
  spec Bxi t -> XiC (crit t) = C0 /\ XiC (crit (- t)) = C0.
Proof.
  intros t Ht. pose proof (proj1 (spec_Bxi_zero t) Ht) as H0.
  split; [ exact H0 | rewrite crit_neg_conj, XiC_conj, H0, Cconj_C0; reflexivity ].
Qed.

Print Assumptions Bxi_even.
Print Assumptions Sphase_unit.
Print Assumptions boundary_selects_zeros.
Print Assumptions Bxi_no_offaxis_zero.
Print Assumptions refl_collapse_iff.
