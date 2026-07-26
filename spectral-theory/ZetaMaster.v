(* ================================================================= *)
(*  ZetaMaster.v                                                     *)
(*                                                                    *)
(*  MASTER UMBRELLA for the whole ζ(2) / analytic-ζ arc.             *)
(*                                                                    *)
(*  A single conjunction `zeta_arc` bundling the headline results of  *)
(*  the ζ(2) thread — a curated index (each conjunct is exactly the   *)
(*  corresponding standalone theorem, assembled by a positional       *)
(*  `conj` term).  Five movements:                                    *)
(*                                                                    *)
(*    I.   ζ(2) = Σ 1/n² CONVERGES              (ZetaConverge)        *)
(*    II.  finite reciprocal-square sums ≤ ζ(2) (RecipSquareBound)    *)
(*    III. EULER PRODUCT ∏(1−p⁻²)⁻¹ → ζ(2)      (EulerProductZeta)   *)
(*    IV.  the PRIMORIAL Euler tower → ζ(2)      (PrimorialZeta)      *)
(*    V.   ANALYTIC ζ²: ∑ τ(n)/n² → ζ(2)²       (ZetaSquareAnalytic) *)
(*                                                                    *)
(*  This whole arc is over the classical `Reals` axioms and is        *)
(*  deliberately QUARANTINED: `Print Assumptions zeta_arc` reports    *)
(*  the classical-ℝ trio (sig_forall_dec, sig_not_dec,               *)
(*  functional_extensionality_dep), NOT "Closed under the global      *)
(*  context".  ζ(2)'s value π²/6 is out of scope — everything is      *)
(*  stated relative to the limit `proj1_sig zeta2_converges`.         *)
(* ================================================================= *)

From Stdlib Require Import Reals QArith Qreals ZArith Znumtheory List.
Import ListNotations.
Require Import ZetaConverge RecipSquareBound EulerProductR EulerProductZeta
        EulerProductZetaBound PrimorialZeta PrimorialEuler ZetaSquareAnalytic.
Open Scope R_scope.

Theorem zeta_arc :
  (* ---- I. ζ(2) = Σ 1/n² converges ---- *)
  Un_cv zpart (proj1_sig zeta2_converges) /\
  (* ---- II. finite reciprocal-square sums ≤ ζ(2) ---- *)
  (forall L : list nat, NoDup L -> (forall m, In m L -> (1 <= m)%nat) ->
      Rlsum (map rr L) <= proj1_sig zeta2_converges) /\
  (* ---- III. Euler product ∏(1−p⁻²)⁻¹ → ζ(2) ---- *)
  Un_cv (fun N => Zfactor (map (fun p => (/ (IZR p) ^ 2)%R) (primes_upto (S N))))
        (proj1_sig zeta2_converges) /\
  (forall ps : list Z, Forall prime ps -> NoDup ps ->
      Zfactor (map (fun p => (/ (IZR p) ^ 2)%R) ps) <= proj1_sig zeta2_converges) /\
  (* ---- IV. the primorial Euler tower → ζ(2) ---- *)
  (forall P : nat -> R, (forall i, INR i + 2 <= P i) ->
      (forall n, EP P n <= proj1_sig zeta2_converges) ->
      (forall N, exists n, zpart N <= EP P n) ->
      Un_cv (EP P) (proj1_sig zeta2_converges)) /\
  (* ---- V. analytic ζ²: ∑ τ(n)/n² → ζ(2)² ---- *)
  Un_cv Spart (Lz * Lz) /\
  (forall N, Spart N = Dpart N) /\
  Un_cv Dpart (Lz * Lz).
Proof.
  exact (conj (proj2_sig zeta2_converges)
         (conj recip_sq_nodup_bound
         (conj euler_product_zeta2
         (conj euler_factor_le_zeta
         (conj tower_is_zeta2
         (conj zeta_two_sq_hyperbola
         (conj Spart_eq_Dpart
               zeta_two_sq_tau))))))).
Qed.

Print Assumptions zeta_arc.

(* ================================================================= *)
(*  END ZetaMaster.v                                                 *)
(*  One umbrella (`zeta_arc`) for the ζ(2)/analytic-ζ thread:         *)
(*  convergence + reciprocal-square bound + Euler product + primorial *)
(*  tower + analytic ζ².  Over the quarantined classical Reals        *)
(*  axioms (NOT axiom-free), relative to the limit ζ(2).             *)
(* ================================================================= *)
