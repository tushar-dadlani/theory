(* ================================================================= *)
(*  BerryKeatingDilation.v                                            *)
(*                                                                    *)
(*  A CANDIDATE representation of the Berry-Keating dilation          *)
(*  Hamiltonian, Mellin-diagonal, with the BOUNDARY CONDITION as an   *)
(*  explicit parametric interface.                                    *)
(*                                                                    *)
(*  The dilation H = -i(x d/dx + 1/2) has generalised eigenfunctions  *)
(*  psi_t(x) = x^{-1/2+it} with continuous spectrum t in R (the       *)
(*  critical line).  In MELLIN coordinates the dilation is            *)
(*  multiplication by t -- diagonal -- so it fits the repo's Dmul.    *)
(*  A boundary condition  B : R -> C  discretises the spectrum to     *)
(*     spec B = { t : B t = 0 }.                                       *)
(*  The Berry-Keating-Connes proposal is that the geometric boundary  *)
(*  condition equals  Bxi t = XiC(1/2 + it),  so the spectrum becomes  *)
(*  the zeta zeros.                                                    *)
(*                                                                    *)
(*  PROVED here:                                                       *)
(*   - the target bridge: with B = Bxi, spec Bxi t <-> XiC(1/2+it)=0   *)
(*     <-> xir t = 0 (the on-seam zeros);  under RH every zero is one; *)
(*   - the l^2 realisation: any boundary-selected ordinate sequence    *)
(*     zord gives the self-adjoint diagonal operator Dmul zord with    *)
(*     real point spectrum {zord n} = the eigenvalues (Dmul_eigen /    *)
(*     diag_matrix_elt) -- the same reality condition as              *)
(*     coherence_line / BK_reality.                                    *)
(*                                                                    *)
(*  NOT proved (the Hilbert-Polya gap): that the ACTUAL geometric      *)
(*  dilation boundary condition IS Bxi -- i.e. that the zeros arise    *)
(*  as eigenvalues of a naturally-defined H rather than inserted via   *)
(*  zord.  Stated as the target `hilbert_polya_target`, no axiom.      *)
(*                                                                    *)
(*  Boundary condition interface: B : R -> C is the plug-in point;     *)
(*  supply a concrete B and relate spec B to xir.                     *)
(*                                                                    *)
(*  Axioms: standard classical-Reals only.                            *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra.
Require Import ComplexField RiemannXiEntire CoherenceSingularity
        Ell2 Ell2Basis Ell2Operator Ell2Zeta GammaReal MellinKernel.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  A.  The boundary-condition interface                             *)
(* ----------------------------------------------------------------- *)

Definition Boundary := R -> C.

(* the point spectrum selected by a boundary condition B *)
Definition spec (B : Boundary) (t : R) : Prop := B t = C0.

Lemma RtoC_eq_C0 : forall r, RtoC r = C0 <-> r = 0.
Proof.
  intro r; split.
  - intro Hh; apply (f_equal Re) in Hh; unfold RtoC, C0 in Hh; simpl in Hh; exact Hh.
  - intro Hh; subst r; unfold RtoC, C0; apply Ceq; simpl; ring.
Qed.

(* ----------------------------------------------------------------- *)
(*  B.  Dilation = multiplication by t, in Mellin coordinates        *)
(* ----------------------------------------------------------------- *)

(* mellin_scale: scaling the argument by c multiplies the Mellin       *)
(* transform by the multiplicative character c^{-a}.  On the seam      *)
(* a = 1/2 + it the character is c^{-1/2}.c^{-it} (unitary weight,      *)
(* phase -t.ln c): the dilation generator is "multiplication by t".    *)
Definition dilation_character (a c : R) : R := Rpower c (- a).

Corollary dilation_is_character : forall a c (Ha : 0 < a) (Hc : 0 < c),
  mellin a c Ha Hc = dilation_character a c * Gam a Ha.
Proof. intros a c Ha Hc; unfold dilation_character; apply mellin_scale. Qed.

(* ----------------------------------------------------------------- *)
(*  C.  Target bridge:  B = XiC o crit  gives the zeta zeros          *)
(* ----------------------------------------------------------------- *)

Definition Bxi (t : R) : C := XiC (crit t).

Lemma spec_Bxi_zero : forall t, spec Bxi t <-> XiC (crit t) = C0.
Proof. intro t; unfold spec, Bxi; reflexivity. Qed.

(* the boundary-Bxi spectrum is exactly the real zeros of xir = XiC on  *)
(* the critical line. *)
Lemma spec_Bxi_xir : forall t, spec Bxi t <-> xir t = 0.
Proof. intro t; unfold spec, Bxi; rewrite XiC_crit_eq; apply RtoC_eq_C0. Qed.

Theorem dilation_spectrum_is_zeros : forall t, spec Bxi t <-> XiC (crit t) = C0.
Proof. exact spec_Bxi_zero. Qed.

(* Under RH, every zero of XiC is on the seam and its ordinate is in    *)
(* the boundary-Bxi spectrum -- the spectral realisation of RH.         *)
Corollary RH_zeros_are_Bxi_spectrum :
  RH_XiC -> forall z, XiC z = C0 -> z = crit (Im z) /\ spec Bxi (Im z).
Proof.
  intros HRH z Hz.
  pose proof (proj1 RH_zeros_reach_R HRH z Hz) as Hcrit.
  split; [ exact Hcrit | unfold spec, Bxi; rewrite <- Hcrit; exact Hz ].
Qed.

(* ----------------------------------------------------------------- *)
(*  D.  Self-adjoint l^2 realisation of a boundary-selected spectrum *)
(* ----------------------------------------------------------------- *)

Section Realization.
  Variable B : Boundary.
  Variable zord : nat -> R.                (* the boundary-selected ordinates *)
  Hypothesis Hzord : forall n, spec B (zord n).

  (* the candidate Hamiltonian: diagonal in the ordinate basis *)
  Definition Hdil : (nat -> R) -> (nat -> R) := Dmul zord.

  (* eigenvalue at mode n is zord n  (unconditional) *)
  Lemma Hdil_eigen : forall n m, Hdil (e n) m = zord n * e n m.
  Proof. intros n m; unfold Hdil; apply Dmul_eigen. Qed.

  (* the diagonal matrix element reads off the eigenvalue *)
  Lemma Hdil_matrix_elt : forall n,
    ip (Dmul zord (e n)) (e n) (Ell2_diag_e zord n) (Ell2_e n) = zord n.
  Proof. intro n; apply diag_matrix_elt. Qed.

  (* the eigenvalues are REAL ordinates satisfying the boundary condition *)
  Lemma Hdil_eigen_real : forall n, exists r : R, zord n = r.
  Proof. intro n; exists (zord n); reflexivity. Qed.

  Lemma Hdil_eigen_boundary : forall n, B (zord n) = C0.
  Proof. exact Hzord. Qed.
End Realization.

(* With B = Bxi the spectrum consists of real ordinates that are zeros   *)
(* of XiC on the critical line -- the Hilbert-Polya spectral realisation. *)
Corollary Hdil_Bxi_spectrum : forall (zord : nat -> R),
  (forall n, spec Bxi (zord n)) -> forall n, XiC (crit (zord n)) = C0.
Proof. intros zord Hz n; exact (Hz n). Qed.

(* ----------------------------------------------------------------- *)
(*  E.  The Hilbert-Polya target (stated, not proved)                *)
(* ----------------------------------------------------------------- *)

(* The open step: that the geometric dilation boundary condition IS Bxi, *)
(* i.e. there is a boundary-selected ordinate sequence enumerating the   *)
(* zeta zeros, realised as the spectrum of the dilation Dmul zord.       *)
Definition hilbert_polya_target : Prop :=
  exists zord : nat -> R,
    (forall n, spec Bxi (zord n)) /\
    (forall z, XiC z = C0 -> Re z = / 2 -> exists n, z = crit (zord n)).

Print Assumptions spec_Bxi_xir.
Print Assumptions dilation_spectrum_is_zeros.
Print Assumptions Hdil_eigen.
