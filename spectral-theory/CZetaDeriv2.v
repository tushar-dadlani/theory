(* ================================================================= *)
(*  CZetaDeriv2.v  —  item 2b.2: explicit first/second s-derivatives    *)
(*  of the Euler–Maclaurin term gtermC, with is_Cderiv relations, and   *)
(*  the identification of the second derivative with the STRUCTURAL      *)
(*  d2gtermC (CZetaTerm2.v) whose modulus item 3b bounds.               *)
(*                                                                    *)
(*  Route: differentiate the two kernels                               *)
(*    gC s x  = x^{-s}                (power)                           *)
(*    GC s x  = x^{1-s}/(1-s)         (antiderivative)                  *)
(*  twice in s via the Cderiv calculus, matching the results to the     *)
(*  structural kernels d2k(-s) = (ln x)^2 x^{-s} and d2sGC.  Axiom-clean.*)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import ComplexField Cmodulus CexpFull CPower Holomorphic CDeriv
               CBaseDeriv CBaseDeriv2 CZetaTerm CZetaTerm2.
Open Scope R_scope.

(* ------------------------------------------------------------------ *)
(*  Power kernel gC s x = x^{-s} = Cpw x (Copp s).                      *)
(*  first s-derivative dsk = -ln x · x^{-s};  second = (ln x)^2 x^{-s}. *)
(* ------------------------------------------------------------------ *)

Definition dsk (s : C) (x : R) : C :=
  Cmul (Copp C1) (Cmul (RtoC (ln x)) (Cpw x (Copp s))).

Lemma gC_sderiv : forall s x, 0 < x ->
  is_Cderiv (fun w => Cpw x (Copp w)) s (dsk s x).
Proof.
  intros s x Hx.
  apply (is_Cderiv_ext (fun w => Cpw x (Cadd (Cmul (Copp C1) w) C0))).
  - intro w; f_equal; ring.
  - unfold dsk.
    replace (Cmul (Copp C1) (Cmul (RtoC (ln x)) (Cpw x (Copp s))))
      with (Cmul (Copp C1) (Cmul (RtoC (ln x)) (Cpw x (Cadd (Cmul (Copp C1) s) C0))))
      by (repeat f_equal; ring).
    apply Cderiv_comp_affine; apply Cpw_deriv; exact Hx.
Qed.

Lemma dsk_sderiv : forall s x, 0 < x ->
  is_Cderiv (fun w => dsk w x) s (d2k (Copp s) x).
Proof.
  intros s x Hx; unfold dsk.
  replace (d2k (Copp s) x)
    with (Cmul (Copp C1) (Cmul (RtoC (ln x)) (dsk s x))).
  2: { unfold dsk, d2k.
       replace (RtoC (ln x * ln x)) with (Cmul (RtoC (ln x)) (RtoC (ln x)))
         by (rewrite <- RtoC_mul; reflexivity).
       ring. }
  apply Cderiv_cscal; apply Cderiv_cscal; apply gC_sderiv; exact Hx.
Qed.

Print Assumptions gC_sderiv.
Print Assumptions dsk_sderiv.

(* ================================================================= *)
(*  END CZetaDeriv2.v (part 1: power kernel s-derivatives).           *)
(* ================================================================= *)
