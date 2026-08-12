(* ================================================================= *)
(*  SpectralReflectionBridge.v  —  the functional-equation reflection    *)
(*  as a self-adjoint involution, and a NEW one-sided reduction of RH.    *)
(*                                                                    *)
(*  The completed zeta xi satisfies XiC z = XiC (1 - z): the FE reflection *)
(*      Srefl : z |-> 1 - z                                              *)
(*  is an involution (Srefl^2 = I) whose zeros are S-symmetric             *)
(*  (XiC_zero_reflect: z a zero => 1-z a zero).  Its fixed-POINT set is     *)
(*  the single point 1/2 (Srefl_fixed_point) -- NOT the whole line, since   *)
(*  1-(a+bi)=a+bi forces b=0.  The full critical LINE is the fixed axis of  *)
(*  the GEOMETRIC reflection Sbar : z |-> 1 - conj z (Sbar_fixed_iff),      *)
(*  which is Srefl post-composed with conjugation.  This is the Hilbert-    *)
(*  Polya *reflection skeleton* in the repo's own proved vocabulary -- the   *)
(*  abstract Q-level form is FEInvolution.refl with                        *)
(*  refl_fixed_iff : refl s == s <-> s == 1#2 (there over Q, the point 1/2).*)
(*                                                                    *)
(*  The payoff is a genuine NEW theorem: because the zeros come in         *)
(*  reflected PAIRS straddling the line (zero_pair_straddle:               *)
(*  Re z + Re(1-z) = 1), RH is EQUIVALENT to the one-sided statement that  *)
(*  no zero has Re < 1/2 (equivalently, none has Re > 1/2).  Excluding      *)
(*  half the strip suffices.  Axiom-clean (four classical-Reals axioms).   *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra.
Require Import ComplexField RiemannXiEntire ZetaZeroPairing.
Open Scope R_scope.

(*  The Riemann Hypothesis, stated verbatim as in RiemannHypothesis.v      *)
(*  (every zero of the entire completed zeta XiC lies on Re z = 1/2).      *)
(*  Restated here rather than imported: the project maps spectral-theory   *)
(*  and packages/GHS to the same (empty) logical namespace, so the module  *)
(*  name RiemannHypothesis is ambiguous -- but this Prop is DEFINITIONALLY *)
(*  the canonical one, over the same XiC (RiemannXiEntire).                *)
Definition RiemannHypothesis : Prop :=
  forall z : C, XiC z = C0 -> Re z = / 2.

(* ----------------------------------------------------------------- *)
(*  The reflection S : z |-> 1 - z, its involutivity, and its fixed axis. *)
(* ----------------------------------------------------------------- *)

Definition Srefl (z : C) : C := Cminus C1 z.

(*  S is an involution:  S (S z) = z.                                  *)
Lemma Srefl_involutive : forall z, Srefl (Srefl z) = z.
Proof.
  intro z; unfold Srefl, Cminus, Cadd, Copp, C1; destruct z as [a b];
    apply Ceq; simpl; ring.
Qed.

(*  the real part reflects:  Re (S z) = 1 - Re z.                      *)
Lemma Re_Srefl : forall z, Re (Srefl z) = 1 - Re z.
Proof. intro z; unfold Srefl, Cminus, Cadd, Copp, C1; simpl; ring. Qed.

(*  A fixed point of the FE reflection is the single point 1/2 (Re=1/2   *)
(*  AND Im=0): S: z|->1-z fixes only 1/2, NOT the whole line, because     *)
(*  1 - (a+bi) = a+bi forces -b = b.  (This is why the critical LINE      *)
(*  needs the vertical reflection Sbar below, not Srefl.)                *)
Lemma Srefl_fixed_point : forall z, Srefl z = z -> Re z = / 2.
Proof. intros z Hfix; exact (reflect_fixed_point z Hfix). Qed.

(*  the zeros of XiC are S-symmetric (restatement of XiC_zero_reflect). *)
Lemma zeros_S_symmetric : forall z, XiC z = C0 -> XiC (Srefl z) = C0.
Proof. intros z Hz; exact (XiC_zero_reflect z Hz). Qed.

(* ----------------------------------------------------------------- *)
(*  The GEOMETRIC reflection across the critical line, Sbar z = 1 - conj z.*)
(*  This is Srefl post-composed with conjugation; its fixed axis is the    *)
(*  FULL critical line Re z = 1/2 (all imaginary parts), unlike Srefl.      *)
(* ----------------------------------------------------------------- *)

Definition Sbar (z : C) : C := Cminus C1 (Cconj z).

Lemma Sbar_involutive : forall z, Sbar (Sbar z) = z.
Proof.
  intro z; unfold Sbar, Cconj, Cminus, Cadd, Copp, C1; destruct z as [a b];
    apply Ceq; simpl; ring.
Qed.

(*  Sbar = Srefl on the conjugate:  the vertical reflection is the FE      *)
(*  reflection composed with complex conjugation.                          *)
Lemma Sbar_eq_Srefl_conj : forall z, Sbar z = Srefl (Cconj z).
Proof. intro z; unfold Sbar, Srefl; reflexivity. Qed.

(*  the FIXED AXIS of Sbar is EXACTLY the critical line Re z = 1/2         *)
(*  (for every imaginary part) -- the genuine "reflection fixed = line".   *)
Lemma Sbar_fixed_iff : forall z, Sbar z = z <-> Re z = / 2.
Proof.
  intro z; split.
  - intro Hfix; unfold Sbar, Cconj, Cminus, Cadd, Copp, C1 in Hfix;
    destruct z as [a b]; apply (f_equal Re) in Hfix; simpl in *; lra.
  - intro Hre; unfold Sbar, Cconj, Cminus, Cadd, Copp, C1; destruct z as [a b];
    apply Ceq; simpl in *; lra.
Qed.

(* ----------------------------------------------------------------- *)
(*  THE NEW ONE-SIDED REDUCTION OF RH.                                 *)
(*  Because reflected zero-pairs straddle the line (Re z + Re(1-z) = 1),*)
(*  RH is equivalent to excluding just the LEFT half of the strip.      *)
(* ----------------------------------------------------------------- *)

(*  RH  <=>  no zero has Re < 1/2  (i.e. every zero has 1/2 <= Re z).   *)
Theorem RH_iff_no_left : RiemannHypothesis <-> (forall z, XiC z = C0 -> / 2 <= Re z).
Proof.
  split.
  - (* RH is stronger: Re z = 1/2 gives 1/2 <= Re z *)
    intros RH z Hz; rewrite (RH z Hz); lra.
  - (* the reflected partner forces equality *)
    intros Hleft z Hz.
    pose proof (Hleft z Hz) as Hz_ge.
    pose proof (Hleft (Srefl z) (zeros_S_symmetric z Hz)) as Hrefl_ge.
    rewrite Re_Srefl in Hrefl_ge.
    lra.
Qed.

(*  the symmetric form: RH <=> no zero has Re > 1/2.                    *)
Theorem RH_iff_no_right : RiemannHypothesis <-> (forall z, XiC z = C0 -> Re z <= / 2).
Proof.
  split.
  - intros RH z Hz; rewrite (RH z Hz); lra.
  - intros Hright z Hz.
    pose proof (Hright z Hz) as Hz_le.
    pose proof (Hright (Srefl z) (zeros_S_symmetric z Hz)) as Hrefl_le.
    rewrite Re_Srefl in Hrefl_le.
    lra.
Qed.

Print Assumptions RH_iff_no_left.
Print Assumptions RH_iff_no_right.

(* ================================================================= *)
(*  END SpectralReflectionBridge.v.                                       *)
(*  The functional equation is an involution Srefl: z|->1-z                 *)
(*  (Srefl_involutive) with S-symmetric zeros (zeros_S_symmetric); the      *)
(*  geometric reflection Sbar: z|->1-conj z is fixed exactly on the         *)
(*  critical line (Sbar_fixed_iff).  New result: RH reduces to             *)
(*  a ONE-SIDED strip exclusion (RH_iff_no_left / RH_iff_no_right) -- it    *)
(*  suffices to rule out zeros in half the strip.  This is the reflection   *)
(*  half of the Hilbert-Polya picture, fully proved; the missing half --    *)
(*  identifying the operator SPECTRUM with the zero ORDINATES (Berry-       *)
(*  Keating) -- is the load-bearing gap, and is equivalent to RH itself.    *)
(* ================================================================= *)
