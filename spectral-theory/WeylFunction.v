(* ================================================================= *)
(*  WeylFunction.v                                                    *)
(*                                                                    *)
(*  Identifying the boundary-triple WEYL FUNCTION of the dilation      *)
(*  operator and relating the self-adjoint-extension phase to the      *)
(*  boundary functional Bxi and the reflection phase Sphase.           *)
(*                                                                    *)
(*  The Weyl function is the Cayley transform of the (real) boundary    *)
(*  value on the seam:                                                 *)
(*     Wxi t = cayley (RtoC (xir t)),   xir t = Re XiC(1/2 + it),       *)
(*  a map R -> U(1) (Wxi_unit).                                        *)
(*                                                                    *)
(*  MAIN RESULT (zeros_are_Dirichlet_phase): the zeta zeros are        *)
(*  EXACTLY the ordinates where the Weyl function reaches the          *)
(*  Dirichlet extension phase u = -1 = cayley(0):                       *)
(*     spec Bxi t  <->  Wxi t = uDir.                                   *)
(*  So the self-adjoint extension carrying the zeros is the Dirichlet   *)
(*  one, u = -1 (with ext_point uDir = 0).                             *)
(*                                                                    *)
(*  SCATTERING (Smat_eq_Sphase, scattering_trivial): the scattering    *)
(*  matrix  Smat t = XiC(1-s)/XiC(s) = xi(1-s)/xi(s)  coincides with    *)
(*  the reflection phase Sphase, and equals 1 by the functional        *)
(*  equation -- the FE IS the unitarity/triviality of scattering.       *)
(*                                                                    *)
(*  STILL OPEN (Hilbert-Polya gap): that the operator whose Weyl        *)
(*  function is Wxi is the geometric Berry-Keating dilation.           *)
(*                                                                    *)
(*  Axioms: standard classical-Reals only.                            *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra.
Require Import ComplexField RiemannXiEntire CoherenceSingularity
        BerryKeatingDilation DilationBoundary SelfAdjointExtension.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  A.  The Dirichlet extension phase  u = -1 = cayley(0)             *)
(* ----------------------------------------------------------------- *)

Definition uDir : C := mkC (-1) 0.

Lemma uDir_unit : U1 uDir.
Proof. unfold U1, uDir, Cnorm2; cbn [Re Im]; ring. Qed.

Lemma uDir_ne_C1 : uDir <> C1.
Proof. intro H; apply (f_equal Re) in H; unfold uDir, C1 in H; cbn [Re] in H; lra. Qed.

(* Cayley sends the boundary value 0 to the Dirichlet phase -1.        *)
Lemma cayley_zero : cayley (RtoC 0) = uDir.
Proof.
  unfold cayley, uDir, Cdiv, Cmul, Cminus, Cadd, Cinv, Cnorm2, Ci, RtoC.
  apply Ceq; cbn [Re Im]; field; nra.
Qed.

(* the real part of cayley on the real axis, cleared of denominators.  *)
Lemma cayley_RtoC_Re : forall x, Re (cayley (RtoC x)) * (x * x + 1) = x * x - 1.
Proof.
  intro x. unfold cayley, Cdiv, Cmul, Cminus, Cadd, Cinv, Cnorm2, Ci, RtoC; cbn [Re Im].
  field; nra.
Qed.

(* cayley(RtoC x) = -1  iff  x = 0  (injectivity at the Dirichlet phase) *)
Lemma cayley_eq_uDir : forall x, cayley (RtoC x) = uDir <-> x = 0.
Proof.
  intro x; split.
  - intro H. apply (f_equal Re) in H. unfold uDir in H; cbn [Re] in H.
    pose proof (cayley_RtoC_Re x) as HR. rewrite H in HR. nra.
  - intro H; subst x; apply cayley_zero.
Qed.

(* the extension base point of the Dirichlet phase is 0.               *)
Lemma ext_point_uDir : ext_point uDir = 0.
Proof.
  unfold ext_point, icayley, uDir, Cdiv, Cmul, Cadd, Cminus, Cinv, Cnorm2, Ci, C1;
    cbn [Re Im]; field; nra.
Qed.

(* ----------------------------------------------------------------- *)
(*  B.  The Weyl function  Wxi t = cayley (RtoC (xir t))              *)
(* ----------------------------------------------------------------- *)

Definition Wxi (t : R) : C := cayley (RtoC (xir t)).

(* the Weyl function takes values on the unit circle U(1).             *)
Lemma Wxi_unit : forall t, U1 (Wxi t).
Proof. intro t; apply cayley_maps_unit. Qed.

(* MAIN: the zeta zeros are exactly where the Weyl function reaches the *)
(* Dirichlet extension phase u = -1.                                   *)
Theorem zeros_are_Dirichlet_phase : forall t, spec Bxi t <-> Wxi t = uDir.
Proof.
  intro t; split.
  - intro H. unfold Wxi. apply cayley_eq_uDir. apply (proj1 (spec_Bxi_xir t)); exact H.
  - intro H. apply (proj2 (spec_Bxi_xir t)).
    apply (proj1 (cayley_eq_uDir (xir t))). unfold Wxi in H; exact H.
Qed.

(* ----------------------------------------------------------------- *)
(*  C.  Scattering matrix = reflection phase = 1 (functional eqn)     *)
(* ----------------------------------------------------------------- *)

(* the scattering matrix  S(t) = XiC(1-s)/XiC(s),  s = 1/2 + it.        *)
Definition Smat (t : R) : C := Cdiv (XiC (Cminus C1 (crit t))) (XiC (crit t)).

(* the scattering matrix IS the reflection phase Sphase of the         *)
(* boundary functional (they are the same ratio, via FE_crit).          *)
Lemma Smat_eq_Sphase : forall t, Smat t = Sphase t.
Proof. intro t; unfold Smat, Sphase, Bxi, Cdiv; rewrite FE_crit; reflexivity. Qed.

(* and it is trivial (= 1) wherever XiC(s) <> 0 -- the functional        *)
(* equation is the unitarity / triviality of the scattering matrix.     *)
Corollary scattering_trivial : forall t, Bxi t <> C0 -> Smat t = C1.
Proof. intros t H; rewrite Smat_eq_Sphase; apply Sphase_unit; exact H. Qed.

(* Direct FE reading: Smat = XiC(s)/XiC(s) since XiC(1-s) = XiC(s).      *)
Corollary Smat_from_FE : forall t, Bxi t <> C0 ->
  Smat t = Cdiv (XiC (crit t)) (XiC (crit t)).
Proof.
  intros t H; unfold Smat. rewrite <- XiC_symmetric. reflexivity.
Qed.

Print Assumptions zeros_are_Dirichlet_phase.
Print Assumptions Smat_eq_Sphase.
Print Assumptions scattering_trivial.
