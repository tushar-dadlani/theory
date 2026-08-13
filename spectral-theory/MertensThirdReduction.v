(* ================================================================= *)
(*  MertensThirdReduction.v                                          *)
(*                                                                    *)
(*  Reducing the EXACT-CONSTANT Mertens third theorem to a single      *)
(*  deep input.  Everything here is limit-arithmetic over already-     *)
(*  proven pieces; no new analysis.                                    *)
(*                                                                    *)
(*  Proven ingredients reused (all Qed):                              *)
(*   - logProd_decomp : logProd N = - primeRecip N - Rrem N            *)
(*       (the finite bridge: sum of ln(1-1/p) = -sum 1/p - tail);      *)
(*   - P2_exists : the prime-power tail Rrem converges to some         *)
(*       P2 in [0,1]  (monotone + bounded);                            *)
(*   - EulerMascheroni.gamma : the Euler-Mascheroni constant as the    *)
(*       genuine limit of H_N - ln N.                                  *)
(*                                                                    *)
(*  RESULTS:                                                          *)
(*   - mertens_third_from_second: IF the Mertens-2 sum has an exact    *)
(*     constant M (sum_{p<=N} 1/p - ln ln N -> M), THEN the Mertens-3  *)
(*     log-sum has the exact constant -(M + P2):                       *)
(*        logProd N + ln ln N  ->  -(M + P2).                          *)
(*   - mertens_third_gamma / mertens_third_log_form: additionally      *)
(*     assuming the classical identity  M + P2 = gamma, the constant   *)
(*     is exactly -gamma -- i.e. prod_{p<=N}(1-1/p) ~ e^{-gamma}/ln N, *)
(*     Mertens' third theorem with the correct constant.              *)
(*                                                                    *)
(*  So the ONLY remaining deep input (mertens_deep_input) is: the      *)
(*  Mertens-2 sum converges to some M with M + P2 = gamma.  This       *)
(*  isolates the classical Euler-product / analytic step and discharges *)
(*  everything else.  Axiom-clean (standard classical-Reals only).     *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra.
Require Import MertensPrime MertensThirdThm EulerMascheroni.
Open Scope R_scope.

(* The exact Mertens-3 constant equals -(M + P2), given the exact       *)
(* Mertens-2 constant M.  Pure limit arithmetic on logProd_decomp.      *)
Theorem mertens_third_from_second :
  forall M,
    Un_cv (fun N => primeRecip N - ln (ln (INR N))) M ->
    Un_cv (fun N => logProd N + ln (ln (INR N))) (- (M + proj1_sig P2_exists)).
Proof.
  intros M HM.
  set (P2 := proj1_sig P2_exists).
  assert (HP2 : Un_cv Rrem P2) by exact (proj1 (proj2_sig P2_exists)).
  assert (Hopp : Un_cv (opp_seq (fun N => primeRecip N - ln (ln (INR N)))) (- M))
    by (apply CV_opp; exact HM).
  assert (Hcomb :
    Un_cv (fun N => opp_seq (fun N => primeRecip N - ln (ln (INR N))) N - Rrem N)
          (- M - P2))
    by (apply CV_minus; [ exact Hopp | exact HP2 ]).
  replace (- (M + P2)) with (- M - P2) by ring.
  eapply Un_cv_ext; [ | exact Hcomb ].
  intro N. unfold opp_seq. rewrite logProd_decomp. ring.
Qed.

(* Assuming the classical identity M + P2 = gamma, the Mertens-3        *)
(* log-sum constant is exactly -gamma.                                  *)
Corollary mertens_third_gamma :
  forall M,
    Un_cv (fun N => primeRecip N - ln (ln (INR N))) M ->
    M + proj1_sig P2_exists = gamma ->
    Un_cv (fun N => logProd N + ln (ln (INR N))) (- gamma).
Proof.
  intros M HM Hid.
  pose proof (mertens_third_from_second M HM) as H.
  rewrite Hid in H. exact H.
Qed.

(* The single remaining deep input, packaged as one Prop: the Mertens-2 *)
(* sum converges to some M, and M + P2 = gamma (the Euler-product step). *)
Definition mertens_deep_input : Prop :=
  exists M, Un_cv (fun N => primeRecip N - ln (ln (INR N))) M
            /\ M + proj1_sig P2_exists = gamma.

(* Mertens' third theorem (exact constant, log-sum form) follows        *)
(* entirely from that one input.                                        *)
Theorem mertens_third_log_form :
  mertens_deep_input ->
  Un_cv (fun N => logProd N + ln (ln (INR N))) (- gamma).
Proof.
  intros [M [HM Hid]]. exact (mertens_third_gamma M HM Hid).
Qed.

Print Assumptions mertens_third_from_second.
Print Assumptions mertens_third_log_form.
