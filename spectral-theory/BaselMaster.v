(* ================================================================= *)
(*  BaselMaster.v                                                    *)
(*                                                                    *)
(*  THE MASTER UMBRELLA for the whole Basel arc — a single           *)
(*  conjunction bundling the four milestones of ζ(2) = π²/6, from     *)
(*  the elementary Cauchy cotangent squeeze:                          *)
(*                                                                    *)
(*    (M1) cot²x < 1/x² < 1+cot²x on (0,π/2)      (BaselTrig)         *)
(*    (M2) sin((2m+1)θ) = sin^(2m+1)θ·Pcot(cot²θ)  (BaselCotPoly)      *)
(*    (M3) Σ cot²(kπ/(2m+1)) = m(2m−1)/3           (BaselVieta)        *)
(*    (M4) proj1_sig zeta2_converges = π²/6        (BaselZeta)        *)
(*                                                                    *)
(*  `Print Assumptions basel_arc` reports the quarantined classical-  *)
(*  ℝ axioms only (π is archimedean, so π²/6 is inherently classical, *)
(*  not axiom-free).  No `Admitted`, no custom axioms.               *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia List.
Require Import BaselCotPoly BaselVieta BaselZeta ZetaConverge.
Require BaselTrig.
Local Open Scope R_scope.

Theorem basel_arc :
  (* (M1) the cotangent squeeze on (0, π/2) *)
  (forall x, 0 < x -> x < PI / 2 ->
     BaselTrig.Rcot x ^ 2 < / x ^ 2 /\ / x ^ 2 < 1 + BaselTrig.Rcot x ^ 2) /\
  (* (M2) sin((2m+1)θ) as sin^(2m+1)θ times a polynomial in cot²θ *)
  (forall m θ, sin θ <> 0 ->
     sin (INR (2 * m + 1) * θ) = sin θ ^ (2 * m + 1) * Pcot m (Rcot θ ^ 2)) /\
  (* (M3) the cotangent-square sum, via Vieta *)
  (forall m, (1 <= m)%nat ->
     sum_f_R0 (fun k => Rcot (INR (S k) * PI / INR (2 * m + 1)) ^ 2) (m - 1)
     = INR m * (2 * INR m - 1) / 3) /\
  (* (M4) the Basel value: the whole ζ(2) arc converges to π²/6 *)
  proj1_sig zeta2_converges = PI ^ 2 / 6.
Proof.
  exact (conj BaselTrig.cot_sq_bounds
         (conj sin_eq_sinpow_Pcot
         (conj cot_sq_sum basel))).
Qed.

Print Assumptions basel_arc.

(* ================================================================= *)
(*  END BaselMaster.v.  ζ(2) = π²/6, the four-milestone Cauchy        *)
(*  cotangent-squeeze arc, in one theorem.                           *)
(* ================================================================= *)
