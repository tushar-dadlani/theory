(* ================================================================= *)
(*  CLSeries.v  --  the Dirichlet L-series L(s,chi) = sum chi(n)n^-s. *)
(*                                                                    *)
(*  There is no L-function anywhere in this repo: DirichletLEuler     *)
(*  stops at finite identities in a formal variable and its header    *)
(*  concedes that assembling the infinite product "stays prose".      *)
(*  This is the analytic object.                                      *)
(*                                                                    *)
(*  Convergence on Re s > 1 is nearly free: |chi| <= 1 (CharModulus)  *)
(*  makes the p-series a majorant, and CSeries.Cseries_abs_cv is      *)
(*  already fully generic in the coefficient sequence.                *)
(*                                                                    *)
(*  DESIGN NOTE.  LC is built from a sigma type and therefore depends  *)
(*  on the PROOF TERM Hgt: LC ... H and LC ... H' are not             *)
(*  definitionally equal.  Downstream theorems are therefore stated    *)
(*  against an arbitrary Lval with Cseries_cv Lterm Lval as a          *)
(*  hypothesis, with LC appearing only in corollaries; L_unique        *)
(*  reconciles the two.                                               *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia ZArith Znumtheory.
Require Import ComplexField Cmodulus CexpFull CPowBase CSeries CZetaTerm
        Ell2Zeta ZmodOrder DirichletModP CharModulus CTwistedCoeff.
Open Scope R_scope.

Section LS.

Variable p g a : nat.
Hypothesis Hp : prime (Z.of_nat p).
Hypothesis Hg : (1 <= g <= p - 1)%nat.
Hypothesis Hord : ord p g = (p - 1)%nat.

Variable s : C.
Hypothesis Hgt : 1 < Re s.

Definition Lterm (n : nat) : C := Gchi p g a s (S n).

Lemma Lterm_bound : forall n, Cmod (Lterm n) <= Rpower (INR (S n)) (- Re s).
Proof.
  intro n. unfold Lterm.
  pose proof (Gchi_mod_le p g a Hg Hord s (S n)) as H.
  unfold z in H. cbn [Nat.eqb] in H. exact H.
Qed.

Definition LC_ex : { L | Cseries_cv Lterm L } :=
  Cseries_abs_cv Lterm (fun n => Rpower (INR (S n)) (- Re s))
                 Lterm_bound (pseries_cv (Re s) Hgt).

Definition LC : C := proj1_sig LC_ex.

Lemma L_is_series : Cseries_cv Lterm LC.
Proof. exact (proj2_sig LC_ex). Qed.

Lemma L_unique : forall L, Cseries_cv Lterm L -> L = LC.
Proof.
  intros L HL. apply (CUn_cv_unique (Cpsum Lterm)); [ exact HL | exact L_is_series ].
Qed.

End LS.

Print Assumptions LC.
Print Assumptions L_is_series.

(* ================================================================= *)
(*  END CLSeries.v                                                    *)
(* ================================================================= *)
