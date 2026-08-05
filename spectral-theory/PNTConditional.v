(* ================================================================= *)
(*  PNTConditional.v  —  the Prime Number Theorem, conditional on psi~N.*)
(*                                                                    *)
(*  The two sharp bounds                                               *)
(*    (1-eps)(N/ln N) <= pi(N)   (ThetaPiBound.pi_lower_of_theta)      *)
(*    pi(N) <= (1+eps)(N/ln N)   (PiUpperAssembly.pi_upper_of_theta)   *)
(*  combine to the sharp asymptotic                                    *)
(*      Un_cv (pi(N)/(N/ln N)) 1                                       *)
(*  from theta ~ N (pi_asymp_of_theta), and via psi~N => theta~N        *)
(*  (ThetaLimit) from psi ~ N (pi_asymp_of_psi).                       *)
(*                                                                    *)
(*  This is the Prime Number Theorem pi(x) ~ x/ln x, CONDITIONAL on     *)
(*  psi(x) ~ x -- the single remaining input being the Erdos-Selberg    *)
(*  limit argument (Step 3) from the (unconditional) Selberg inequality.*)
(*  Axiom-clean.                                                        *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia Arith.
Require Import Chebyshev ChebyshevBound ChebyshevPrime PrimePowerReindex
        ThetaPiBound PiUpperAssembly ThetaLimit.
Open Scope R_scope.

Theorem pi_asymp_of_theta :
  Un_cv (fun N => theta N / INR N) 1 ->
  Un_cv (fun N => pi_count N / (INR N / ln (INR N))) 1.
Proof.
  intros Hth eps Heps.
  destruct (pi_lower_of_theta Hth (eps / 2) ltac:(lra)) as [Nlo Hlo].
  destruct (pi_upper_of_theta Hth (eps / 2) ltac:(lra)) as [Nhi Hhi].
  exists (Nat.max (Nat.max Nlo Nhi) 2); intros N HN.
  assert (HN2 : (2 <= N)%nat) by lia.
  assert (Hlnpos : 0 < ln (INR N)) by (apply ln_INR_pos; exact HN2).
  assert (HNpos : 0 < INR N) by (apply lt_0_INR; lia).
  assert (Hpos : 0 < INR N / ln (INR N)) by (apply Rdiv_lt_0_compat; assumption).
  specialize (Hlo N ltac:(lia)); specialize (Hhi N ltac:(lia)).
  assert (Hlnne : ln (INR N) <> 0) by lra.
  assert (HNne : INR N <> 0) by lra.
  assert (HPlo : 1 - eps / 2 <= pi_count N / (INR N / ln (INR N))).
  { apply Rmult_le_reg_r with (INR N / ln (INR N)); [ exact Hpos | ].
    replace (pi_count N / (INR N / ln (INR N)) * (INR N / ln (INR N)))
      with (pi_count N) by (field; repeat split; lra).
    exact Hlo. }
  assert (HPhi : pi_count N / (INR N / ln (INR N)) <= 1 + eps / 2).
  { apply Rmult_le_reg_r with (INR N / ln (INR N)); [ exact Hpos | ].
    replace (pi_count N / (INR N / ln (INR N)) * (INR N / ln (INR N)))
      with (pi_count N) by (field; repeat split; lra).
    exact Hhi. }
  unfold R_dist; apply Rle_lt_trans with (eps / 2);
    [ apply Rabs_le; split; lra | lra ].
Qed.

Theorem pi_asymp_of_psi :
  Un_cv (fun N => psi N / INR N) 1 ->
  Un_cv (fun N => pi_count N / (INR N / ln (INR N))) 1.
Proof.
  intro Hpsi; apply pi_asymp_of_theta, theta_asymp_of_psi; exact Hpsi.
Qed.

Print Assumptions pi_asymp_of_psi.

(* ================================================================= *)
(*  END PNTConditional.v  —  psi ~ x  =>  pi(x) ~ x / ln x.             *)
(* ================================================================= *)
