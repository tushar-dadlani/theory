(* ================================================================= *)
(*  GaussDeriv.v  —  Leibniz-gap Phase 0: the exact-tail foundation.   *)
(*                                                                    *)
(*  The whole "differentiation under the improper integral" plan       *)
(*  avoids dominated convergence because the derivative integrand       *)
(*  2πx·e^{−πx²} has an ELEMENTARY antiderivative, −e^{−πx²} = −exp_pi. *)
(*  This file establishes exactly that:                               *)
(*                                                                    *)
(*    dexp_pi        : d/dx e^{−πx²} = −2πx · e^{−πx²};                 *)
(*    gauss_deriv_ftc: ∫_A^B 2πx·e^{−πx²} dx = e^{−πA²} − e^{−πB²}      *)
(*                     (exact, via FTC on the antiderivative −exp_pi).  *)
(*                                                                    *)
(*  Letting B→∞ gives the exact, ξ-INDEPENDENT tail e^{−πA²} that       *)
(*  makes the later uniform-convergence (CVU) estimates elementary,     *)
(*  with no measure theory.  No new axioms (classical Reals only).     *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import ContinuousCoV GaussSubst GaussPiValue.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  d/dx e^{−πx²} = −2πx · e^{−πx²}.                                 *)
(* ----------------------------------------------------------------- *)

Lemma dexp_pi : forall x, derivable_pt_lim exp_pi x (- (2 * PI * x) * exp_pi x).
Proof.
  intro x; unfold exp_pi.
  assert (Hin : derivable_pt_lim (fun z => - (PI * z ^ 2)) x (- (2 * PI * x))).
  { assert (Hp : derivable_pt_lim (fun z => PI * z ^ 2) x (2 * PI * x)).
    { pose proof (derivable_pt_lim_scal (fun z => z ^ 2) PI x
                    (INR 2 * x ^ Init.Nat.pred 2) (derivable_pt_lim_pow x 2)) as Hs.
      replace (2 * PI * x) with (PI * (INR 2 * x ^ Init.Nat.pred 2)) by (simpl; ring).
      exact Hs. }
    exact (derivable_pt_lim_opp (fun z => PI * z ^ 2) x (2 * PI * x) Hp). }
  pose proof (derivable_pt_lim_comp (fun z => - (PI * z ^ 2)) exp x
                (- (2 * PI * x)) (exp (- (PI * x ^ 2))) Hin
                (derivable_pt_lim_exp (- (PI * x ^ 2)))) as Hc.
  cbv beta in Hc.
  match type of Hc with
  | derivable_pt_lim _ _ ?V => replace V with (- (2 * PI * x) * exp (- (PI * x ^ 2))) in Hc by ring
  end.
  exact Hc.
Qed.

(* ----------------------------------------------------------------- *)
(*  The derivative integrand is continuous.                          *)
(* ----------------------------------------------------------------- *)

Lemma cont_deriv_integrand : continuity (fun x => 2 * PI * x * exp_pi x).
Proof.
  intro x; apply continuity_pt_mult; [ | apply cont_exp_pi ].
  apply (continuity_pt_scal (fun y => y) (2 * PI) x); apply cont_id.
Qed.

(* ----------------------------------------------------------------- *)
(*  The EXACT tail:  ∫_A^B 2πx·e^{−πx²} = e^{−πA²} − e^{−πB²}.         *)
(* ----------------------------------------------------------------- *)

Lemma gauss_deriv_ftc : forall A B
  (pr : Riemann_integrable (fun x => 2 * PI * x * exp_pi x) A B),
  A <= B -> RiemannInt pr = exp_pi A - exp_pi B.
Proof.
  intros A B pr Hab.
  assert (Hanti : antiderivative (fun x => 2 * PI * x * exp_pi x) (fun x => - exp_pi x) A B).
  { split; [ | exact Hab ]. intros t Ht.
    assert (Hd : derivable_pt_lim (fun x => - exp_pi x) t (2 * PI * t * exp_pi t)).
    { pose proof (derivable_pt_lim_opp exp_pi t (- (2 * PI * t) * exp_pi t) (dexp_pi t)) as Ho.
      replace (2 * PI * t * exp_pi t) with (- (- (2 * PI * t) * exp_pi t)) by ring.
      exact Ho. }
    exists (exist _ (2 * PI * t * exp_pi t) Hd); reflexivity. }
  rewrite (FTC_antideriv (fun x => 2 * PI * x * exp_pi x) (fun x => - exp_pi x) A B Hab
             (fun x _ => cont_deriv_integrand x) pr Hanti); ring.
Qed.

Print Assumptions dexp_pi.
Print Assumptions gauss_deriv_ftc.

(* ================================================================= *)
(*  END GaussDeriv.v                                                 *)
(*  d/dx e^{−πx²} = −2πx e^{−πx²} and the exact tail                    *)
(*  ∫_A^B 2πx e^{−πx²} = e^{−πA²} − e^{−πB²}.  These feed Phase 1        *)
(*  (Cauchy improper integral) and the ξ-independent CVU bound          *)
(*  |tail| ≤ e^{−πA²} that drives the whole Leibniz argument.          *)
(* ================================================================= *)
