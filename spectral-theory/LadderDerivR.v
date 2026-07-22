(* ================================================================= *)
(*  LadderDerivR.v                                                    *)
(*                                                                    *)
(*  THE LADDER-DERIVATIVE PAYOFF (archimedean analytic layer, over R): *)
(*  the number operator  N = x d/dx  and the primon ENERGY log p,      *)
(*  as GENUINE derivatives (Ranalysis), completing LadderOps.v.        *)
(*                                                                    *)
(*  LadderOps.v proved, over Q, the FORMAL / termwise facts:           *)
(*    MD          : x * D(x^k) = N(x^k)      (N = x d/dx, per monomial) *)
(*    deriv_number: x * dsum = nsum          (x d/dx of a partial sum)  *)
(*  Here those become ANALYTIC derivatives of the partition-function   *)
(*  limit  Z(x) = 1/(1 - x)  (EulerFactorR.geom_limit):                *)
(*                                                                    *)
(*    Zinf_deriv     : d/dx (1/(1-x)) = 1/(1-x)^2                       *)
(*    number_operator: x . d/dx Z = x/(1-x)^2  (mean-occupation gen.fn) *)
(*                                                                    *)
(*  And the ENERGY: differentiating the fugacity x = p^{-s} w.r.t. s    *)
(*  brings DOWN the single-particle energy log p,                      *)
(*                                                                    *)
(*    fugacity_deriv          : d/ds p^{-s} = - log p . p^{-s}          *)
(*    euler_factor_energy_deriv: d/ds (1/(1-p^{-s}))                    *)
(*                               = - log p . p^{-s}/(1-p^{-s})^2        *)
(*                                                                    *)
(*  so differentiating the Euler factor pulls out - log p (= the        *)
(*  primon energy).  Uses the classical Reals axioms (quarantined,      *)
(*  like EulerFactorR.v / LandauerBound.v); the Q core stays pure.      *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra.
Open Scope R_scope.

(* ================================================================= *)
(*  1.  d/dx OF THE PARTITION-FUNCTION LIMIT  Z(x) = 1/(1-x)         *)
(* ================================================================= *)

Theorem Zinf_deriv : forall x, x <> 1 ->
  derivable_pt_lim (fun y => 1 / (1 - y)) x (1 / (1 - x) ^ 2).
Proof.
  intros x Hx.
  assert (Hne : 1 - x <> 0) by (intro H; apply Hx; lra).
  assert (Hg : derivable_pt_lim (fun y => 1 - y) x (0 - 1)).
  { apply (derivable_pt_lim_minus (fct_cte 1) id x 0 1).
    - apply derivable_pt_lim_const.
    - apply derivable_pt_lim_id. }
  pose proof (derivable_pt_lim_div (fct_cte 1) (fun y => 1 - y) x 0 (0 - 1)
                (derivable_pt_lim_const 1 x) Hg Hne) as Hd.
  replace (1 / (1 - x) ^ 2)
     with ((0 * (1 - x) - (0 - 1) * 1) / Rsqr (1 - x))
     by (unfold Rsqr; field; exact Hne).
  exact Hd.
Qed.

(* the NUMBER operator N = x . d/dx applied to Z gives the mean-        *)
(* occupation generating function  x/(1-x)^2  -- the analytic form of   *)
(* LadderOps.deriv_number (x * dsum = nsum = sum_k k x^k).             *)
Theorem number_operator : forall x, x * (1 / (1 - x) ^ 2) = x / (1 - x) ^ 2.
Proof. intro x; unfold Rdiv; ring. Qed.

(* ================================================================= *)
(*  2.  THE ENERGY: DIFFERENTIATING THE FUGACITY BRINGS DOWN log p   *)
(* ================================================================= *)

(* the primon-gas fugacity of mode p at inverse-temperature s:          *)
(*   fugacity p s = p^{-s} = exp(-s log p)                              *)
Definition fugacity (p s : R) : R := exp (- s * ln p).

(* d/ds p^{-s} = - log p . p^{-s}: the derivative pulls out the         *)
(* single-particle energy log p (with a minus sign).                    *)
Theorem fugacity_deriv : forall p s,
  derivable_pt_lim (fun s => fugacity p s) s (- ln p * fugacity p s).
Proof.
  intros p s; unfold fugacity.
  assert (Hf : derivable_pt_lim (fun s => - s) s (-1)).
  { apply (derivable_pt_lim_opp id s 1); apply derivable_pt_lim_id. }
  assert (Hg : derivable_pt_lim (fun s => - s * ln p) s (- ln p)).
  { replace (- ln p) with (-1 * ln p) by ring.
    apply (derivable_pt_lim_scal_right (fun s => - s) s (-1) (ln p) Hf). }
  pose proof (derivable_pt_lim_comp (fun s => - s * ln p) exp s (- ln p)
                (exp (- s * ln p)) Hg (derivable_pt_lim_exp (- s * ln p))) as Hc.
  replace (- ln p * exp (- s * ln p)) with (exp (- s * ln p) * (- ln p)) by ring.
  exact Hc.
Qed.

(* d/ds of the Euler factor 1/(1 - p^{-s}): the chain rule composes      *)
(* Zinf_deriv (in the fugacity) with fugacity_deriv, so differentiating  *)
(* the Euler factor w.r.t. s brings down - log p (the primon energy).    *)
Theorem euler_factor_energy_deriv : forall p s, fugacity p s <> 1 ->
  derivable_pt_lim (fun s => 1 / (1 - fugacity p s)) s
    (- ln p * (fugacity p s / (1 - fugacity p s) ^ 2)).
Proof.
  intros p s Hfug.
  pose proof (derivable_pt_lim_comp (fun s => fugacity p s) (fun y => 1 / (1 - y))
                s (- ln p * fugacity p s) (1 / (1 - fugacity p s) ^ 2)
                (fugacity_deriv p s) (Zinf_deriv (fugacity p s) Hfug)) as Hc.
  replace (- ln p * (fugacity p s / (1 - fugacity p s) ^ 2))
     with (1 / (1 - fugacity p s) ^ 2 * (- ln p * fugacity p s))
     by (unfold Rdiv; ring).
  exact Hc.
Qed.

(* ----------------------------------------------------------------- *)
(*  MASTER THEOREM — the analytic ladder payoff (uses Reals axioms)   *)
(* ----------------------------------------------------------------- *)

Theorem ladder_deriv :
  (* d/dx of the partition-function limit *)
  (forall x, x <> 1 ->
     derivable_pt_lim (fun y => 1 / (1 - y)) x (1 / (1 - x) ^ 2))
  (* the number operator N = x d/dx = the mean-occupation generating fn *)
  /\ (forall x, x * (1 / (1 - x) ^ 2) = x / (1 - x) ^ 2)
  (* differentiating the fugacity brings down the energy log p *)
  /\ (forall p s,
       derivable_pt_lim (fun s => fugacity p s) s (- ln p * fugacity p s))
  (* differentiating the Euler factor brings down log p *)
  /\ (forall p s, fugacity p s <> 1 ->
       derivable_pt_lim (fun s => 1 / (1 - fugacity p s)) s
         (- ln p * (fugacity p s / (1 - fugacity p s) ^ 2))).
Proof.
  split; [ exact Zinf_deriv | ].
  split; [ exact number_operator | ].
  split; [ exact fugacity_deriv | exact euler_factor_energy_deriv ].
Qed.

Print Assumptions ladder_deriv.

(* ================================================================= *)
(*  END LadderDerivR.v                                                *)
(*  The analytic ladder payoff: N = x d/dx as a genuine derivative     *)
(*  (x/(1-x)^2), and differentiating the Euler factor brings down the   *)
(*  primon energy log p.  Uses the classical Reals axioms (quarantined);*)
(*  the Q core (LadderOps, PrimonGas, ...) stays Closed under the       *)
(*  global context.                                                    *)
(* ================================================================= *)
