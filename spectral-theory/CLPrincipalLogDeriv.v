(* ================================================================= *)
(*  CLPrincipalLogDeriv.v  --  the log-derivative identity for chi_0. *)
(*                                                                    *)
(*    Phi(s,chi_0) * (1 - p^{-s}) zeta(s) = sum chi_0(n) ln n n^{-s}  *)
(*                                                                    *)
(*  CLLogDeriv covers every NON-principal character, because it is     *)
(*  phrased through CLHolo1.LFun, which is gated on 0 < A < p-1.  The  *)
(*  principal character needs its own statement -- but not its own     *)
(*  proof: CVonMangoldtLChi's section places NO constraint on A, so    *)
(*  phi_L_eq already applies at A = 0.  All that is missing is the     *)
(*  L-side hypothesis Cseries_cv (Lterm p g 0 s) L, and CLPrincipal    *)
(*  supplies exactly that value in the Cls (seq 1 N) convention.       *)
(*  So this file is one reindexing plus one application.               *)
(*                                                                    *)
(*  pchi0_val records the other half of the picture: Phi(s,chi_0) is   *)
(*  the ordinary von Mangoldt series with the p-part DELETED.  That is *)
(*  what will make it diverge as s -> 1+ (the deleted part is          *)
(*  ln p * p^{-s}/(1 - p^{-s}), bounded, while the full series is not).*)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia List ZArith Znumtheory.
Require Import ComplexField Cmodulus CexpFull CSeries CListSum CDirichlet
        CZetaTerm CZeta RootsOfUnity ZmodOrder DirichletModP CTwistedCoeff
        VonMangoldtGlobal CVonMangoldtSeries CVonMangoldtZeta
        CVonMangoldtChi CVonMangoldtLChi CLSeries CLPrincipal CLLogDeriv.
Import ListNotations.
Open Scope R_scope.

Section P0.

Variable p g : nat.
Hypothesis Hp : prime (Z.of_nat p).
Hypothesis Hg : (1 <= g <= p - 1)%nat.
Hypothesis Hord : ord p g = (p - 1)%nat.
Variable s : C.
Hypothesis Hs : 1 < Re s.

Lemma Hp2 : (2 <= p)%nat.
Proof. pose proof (prime_ge_2 _ Hp); lia. Qed.

(* the principal L-series, as a Cseries_cv *)
Lemma L0_series : forall (H0 : 0 < Re s) (H1 : Cminus C1 s <> C0),
  Cseries_cv (Lterm p g 0 s)
             (Cmul (Cminus C1 (Cpw (INR p) (Copp s))) (zetaC s H0 H1)).
Proof.
  intros H0 H1. unfold Cseries_cv.
  apply (CUn_cv_ext (fun N => Cls (seq 1 (S N))
           (fun n => Cmul (dchar p g 0 n) (bterm s n)))).
  - intro N. symmetry. apply Cpsum_shift_eq_Cls.
  - apply (CUn_cv_shift (fun N => Cls (seq 1 N)
             (fun n => Cmul (dchar p g 0 n) (bterm s n)))).
    apply (L0_eq_zeta_factor p g Hp2 s Hs H0 H1).
Qed.

(* ---- THE identity for the principal character ---- *)
Theorem phi_L0_eq : forall (H0 : 0 < Re s) (H1 : Cminus C1 s <> C0),
  CUn_cv (fun N => Cls (seq 1 N)
            (fun n => Cmul (RtoC (ln (INR n))) (Gchi p g 0 s n)))
         (Cmul (Phichi p g 0 Hg Hord s Hs)
               (Cmul (Cminus C1 (Cpw (INR p) (Copp s))) (zetaC s H0 H1))).
Proof.
  intros H0 H1.
  apply (phi_L_eq p g 0 Hp Hg Hord s Hs).
  apply L0_series.
Qed.

(* ---- Phi(s,chi_0) is the von Mangoldt series with the p-part deleted ---- *)
Lemma pchi0_val : forall n,
  pchi p g 0 s n = (if (S n mod p =? 0)%nat then C0 else pterm s n).
Proof.
  intro n. unfold pchi, pterm, Lterm, Gchi, cterm, gC.
  rewrite dchar0_val. destruct (S n mod p =? 0)%nat; ring.
Qed.

End P0.

Print Assumptions phi_L0_eq.
Print Assumptions pchi0_val.

(* ================================================================= *)
(*  END CLPrincipalLogDeriv.v                                         *)
(* ================================================================= *)
