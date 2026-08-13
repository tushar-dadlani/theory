(* ================================================================= *)
(*  HilbertPolyaCapstone.v                                           *)
(*                                                                    *)
(*  CAPSTONE for the dilation / boundary-triple / Weyl chain.  A       *)
(*  single entry point that (a) packages the proven, axiom-clean       *)
(*  results of the whole chain into one theorem, (b) shows the         *)
(*  boundary-triple target refines the original dilation target, and   *)
(*  (c) surfaces the SINGLE remaining open step as one Prop.           *)
(*                                                                    *)
(*  Chain (all axiom-clean, standard classical-Reals only):            *)
(*    CoherenceSingularity -> SelfDualCenter -> BerryKeatingDilation   *)
(*    -> DilationBoundary -> SelfAdjointExtension -> WeylFunction      *)
(*    -> {WeylHerglotz, ZeroCounting} -> WeylWinding.                  *)
(*                                                                    *)
(*  WHAT IS PROVED (berry_keating_summary), unconditionally:           *)
(*   - the boundary functional is xi and is even (the x<->1/x match);  *)
(*   - it has no zero off the reflection axis;                         *)
(*   - reality of the spectral point is DERIVED from the unit phase;   *)
(*   - the Weyl function selects the zeros at the Dirichlet phase -1;  *)
(*   - the scattering matrix is trivial (the functional equation);     *)
(*   - the Weyl map is Herglotz and a bijection R <-> U(1)\{1};        *)
(*   - a sign change of xir is a half-winding of the Weyl phase        *)
(*     through the antipode -1 (zero counting = phase winding).        *)
(*                                                                    *)
(*  WHAT IS OPEN (hilbert_polya_open): only that the geometric         *)
(*  boundary phase realising XiC's zeros is the correct one.  Reality  *)
(*  of the ordinates is NO LONGER part of the gap -- it is the theorem *)
(*  SelfAdjointExtension.icayley_real.                                 *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra.
Require Import ComplexField RiemannXiEntire CoherenceSingularity SelfDualCenter
        BerryKeatingDilation DilationBoundary SelfAdjointExtension
        WeylFunction WeylHerglotz ZeroCounting WeylWinding.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  A.  The whole proven story, packaged as one theorem              *)
(* ----------------------------------------------------------------- *)

Theorem berry_keating_summary :
  (* boundary functional is xi, and even (the x<->1/x reflection match) *)
  (forall t, Bxi (- t) = Bxi t)
  (* no zero off the reflection axis structure *)
  /\ (forall t, spec Bxi t ->
        Sbar (crit t) = crit t /\ Cminus C1 (crit t) = Cconj (crit t))
  (* self-adjoint extension DERIVES a real spectral point from a unit phase *)
  /\ (forall u, U1 u -> u <> C1 -> exists r : R, icayley u = RtoC r)
  (* the Weyl function selects the zeros at the Dirichlet phase -1 *)
  /\ (forall t, spec Bxi t <-> Wxi t = uDir)
  (* the scattering matrix is trivial (the functional equation) *)
  /\ (forall t, Bxi t <> C0 -> Smat t = C1)
  (* the Weyl / Cayley map is Herglotz (upper half-plane -> disk) *)
  /\ (forall z, 0 < Im z -> Cnorm2 (cayley z) < 1)
  (* ... and a bijection R <-> U(1)\{1} *)
  /\ (forall u, U1 u -> u <> C1 ->
        cayley (RtoC (ext_point u)) = u /\
        (forall t, cayley (RtoC t) = u -> t = ext_point u))
  (* a sign change of xir is a half-winding of Wxi through the antipode -1 *)
  /\ (forall a b, a < b -> xir a < 0 -> 0 < xir b ->
        exists t, a < t < b /\ Wxi t = uDir /\ 0 < Im (Wxi a) /\ Im (Wxi b) < 0).
Proof.
  split; [ exact Bxi_even | ].
  split; [ exact Bxi_no_offaxis_zero | ].
  split; [ exact extension_spectrum_real | ].
  split; [ exact zeros_are_Dirichlet_phase | ].
  split; [ exact scattering_trivial | ].
  split; [ exact cayley_herglotz | ].
  split; [ exact phase_ordinate_bijection | ].
  exact weyl_halfwinding_up.
Qed.

(* ----------------------------------------------------------------- *)
(*  B.  The boundary-triple target refines the dilation target       *)
(* ----------------------------------------------------------------- *)

(* Any self-adjoint-extension phase sequence enumerating the on-seam    *)
(* zeros gives an ordinate sequence enumerating them: the extension     *)
(* formulation (reality derived) refines the original dilation target.  *)
Theorem extension_target_refines_dilation_target :
  hp_target_via_extension -> hilbert_polya_target.
Proof.
  intros [u [_ [_ [Hspec Hsurj]]]].
  exists (zord_of_phase u); split; [ exact Hspec | exact Hsurj ].
Qed.

(* ----------------------------------------------------------------- *)
(*  C.  The single remaining open step, as one Prop                  *)
(* ----------------------------------------------------------------- *)

(* Everything in berry_keating_summary is proved unconditionally.  The  *)
(* reality of the ordinates is a THEOREM (icayley_real), not part of    *)
(* the gap.  The only open step is that the geometric boundary phase    *)
(* realising XiC's zeros is the specific unit-phase sequence u.          *)
Definition hilbert_polya_open : Prop := hp_target_via_extension.

(* Under RH every zero sits on the seam and its ordinate is in the       *)
(* boundary-Bxi spectrum -- the RH-conditional spectral realisation.     *)
Corollary rh_conditional_realization :
  RH_XiC -> forall z, XiC z = C0 -> z = crit (Im z) /\ spec Bxi (Im z).
Proof. exact RH_zeros_are_Bxi_spectrum. Qed.

Print Assumptions berry_keating_summary.
Print Assumptions extension_target_refines_dilation_target.
