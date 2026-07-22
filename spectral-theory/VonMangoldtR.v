(* ================================================================= *)
(*  VonMangoldtR.v                                                    *)
(*                                                                    *)
(*  The analytic VON MANGOLDT connection (archimedean, over R): the    *)
(*  LOGARITHMIC DERIVATIVE of the Euler factor, whose per-prime value   *)
(*  generates the von Mangoldt Dirichlet series.                       *)
(*                                                                    *)
(*  VonMangoldt.v proved (over Q) the arithmetic identity              *)
(*  Lambda = mu * log.  Here is its analytic face: for the Euler        *)
(*  factor  Z_p(s) = 1/(1 - p^{-s}),                                    *)
(*                                                                    *)
(*     d/ds log Z_p(s) = - log p . fug/(1-fug),   fug = p^{-s}          *)
(*                                                                    *)
(*  so  - d/ds log Z_p = log p . fug/(1-fug) = sum_{k>=1} Lambda(p^k)   *)
(*  p^{-ks}  (since Lambda(p^k) = log p).  Summed over primes this is   *)
(*  the classical  -zeta'/zeta(s) = sum_n Lambda(n) n^{-s}.             *)
(*                                                                    *)
(*  Built from LadderDerivR.euler_factor_energy_deriv by composing with *)
(*  the derivative of ln.  Uses the classical Reals axioms             *)
(*  (quarantined); the Q core stays Closed under the global context.    *)
(* ================================================================= *)

Require Import LadderDerivR.
From Stdlib Require Import Reals Lra.
Open Scope R_scope.

(* the genuine logarithmic derivative of the Euler factor 1/(1-p^{-s}):  *)
(*   d/ds log Z_p = - log p . fug/(1-fug),                               *)
(* so minus it is  log p . fug/(1-fug) = sum_{k>=1} Lambda(p^k) p^{-ks}. *)
Theorem vonmangoldt_logderiv : forall p s, 1 < p -> 0 < s ->
  derivable_pt_lim (fun s => ln (1 / (1 - fugacity p s))) s
    (- ln p * (fugacity p s / (1 - fugacity p s))).
Proof.
  intros p s Hp Hs.
  assert (Hpos : 0 < fugacity p s) by (unfold fugacity; apply exp_pos).
  assert (Hlnp : 0 < ln p) by (rewrite <- ln_1; apply ln_increasing; lra).
  assert (Hlt : fugacity p s < 1).
  { unfold fugacity; rewrite <- exp_0; apply exp_increasing; nra. }
  assert (Hne : (1 - fugacity p s) <> 0) by lra.
  assert (HZpos : 0 < 1 / (1 - fugacity p s))
    by (apply Rdiv_lt_0_compat; lra).
  (* Z' from LadderDerivR, then compose with ln *)
  pose proof (euler_factor_energy_deriv p s (ltac:(lra) : fugacity p s <> 1)) as HZ'.
  pose proof (derivable_pt_lim_comp (fun s => 1 / (1 - fugacity p s)) ln s
                (- ln p * (fugacity p s / (1 - fugacity p s) ^ 2))
                (/ (1 / (1 - fugacity p s)))
                HZ' (derivable_pt_lim_ln _ HZpos)) as Hc.
  replace (- ln p * (fugacity p s / (1 - fugacity p s)))
     with (/ (1 / (1 - fugacity p s))
           * (- ln p * (fugacity p s / (1 - fugacity p s) ^ 2)))
     by (field; exact Hne).
  exact Hc.
Qed.

Print Assumptions vonmangoldt_logderiv.

(* ================================================================= *)
(*  END VonMangoldtR.v                                                *)
(*  The logarithmic derivative of the Euler factor generates the von   *)
(*  Mangoldt Dirichlet series per prime; summed over primes it is       *)
(*  -zeta'/zeta = sum_n Lambda(n) n^{-s}.  Uses the classical Reals      *)
(*  axioms (quarantined); the Q core stays Closed under the global      *)
(*  context.                                                           *)
(* ================================================================= *)
