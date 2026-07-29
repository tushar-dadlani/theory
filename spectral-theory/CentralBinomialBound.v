(* ================================================================= *)
(*  CentralBinomialBound.v                                           *)
(*                                                                    *)
(*  THE CENTRAL-BINOMIAL SANDWICH, over ℕ, axiom-free:               *)
(*                                                                    *)
(*     4^M / (2M+1)  ≤  C(2M,M)  ≤  4^M.                              *)
(*                                                                    *)
(*  Since C(2M,M) = (2M)! / (M!)², we state it as pure factorial      *)
(*  inequalities (no binomial / Pascal / unimodality needed):        *)
(*                                                                    *)
(*     central_upper : (2M)!            ≤ 4^M · (M!)²                 *)
(*     central_lower : 4^M · (M!)²      ≤ (2M+1) · (2M)!              *)
(*                                                                    *)
(*  Each is a one-line induction: the factorial recurrence turns the  *)
(*  step into  (2M+2)(2M+1) ≤ 4(M+1)²  (upper) and  2(M+1) ≤ 2M+3     *)
(*  (lower), which `nia` closes.  This is EXACTLY the numerical input  *)
(*  the contour-free Chebyshev bound needs: with D(N) = log(N!) −     *)
(*  2·log(⌊N/2⌋!) = log( (2M)!/(M!)² ), these give                    *)
(*     (log2)·N − log(N+1)  ≤  D(N)  ≤  (log2)·N,                     *)
(*  i.e. D(N) ≍ N, the missing ingredient behind  ψ(x) ≍ x.          *)
(*  AXIOM-FREE (Closed under the global context).                    *)
(* ================================================================= *)

From Stdlib Require Import Arith Lia Factorial.

Lemma fact_S : forall n, fact (S n) = (S n * fact n)%nat.
Proof. reflexivity. Qed.

Lemma central_upper : forall M, (fact (2 * M) <= 4 ^ M * (fact M * fact M))%nat.
Proof.
  induction M as [| M IH]; [ cbn; lia | ].
  replace (2 * S M)%nat with (S (S (2 * M))) by lia.
  rewrite (fact_S (S (2 * M))), (fact_S (2 * M)).
  replace (fact (S M)) with (S M * fact M)%nat by (rewrite fact_S; reflexivity).
  replace (4 ^ S M)%nat with (4 * 4 ^ M)%nat by (rewrite Nat.pow_succ_r'; reflexivity).
  set (p := (4 ^ M)%nat) in *; set (f := fact M) in *; set (g := fact (2 * M)) in *.
  nia.
Qed.

Lemma central_lower : forall M, (4 ^ M * (fact M * fact M) <= (2 * M + 1) * fact (2 * M))%nat.
Proof.
  induction M as [| M IH]; [ cbn; lia | ].
  replace (2 * S M)%nat with (S (S (2 * M))) by lia.
  rewrite (fact_S (S (2 * M))), (fact_S (2 * M)).
  replace (fact (S M)) with (S M * fact M)%nat by (rewrite fact_S; reflexivity).
  replace (4 ^ S M)%nat with (4 * 4 ^ M)%nat by (rewrite Nat.pow_succ_r'; reflexivity).
  set (p := (4 ^ M)%nat) in *; set (f := fact M) in *; set (g := fact (2 * M)) in *.
  nia.
Qed.

(* spot-check, M=3:  C(6,3)=20,  4³=64,  so 64/7≈9.1 ≤ 20 ≤ 64,        *)
(* equivalently  720 = 6! ≤ 64·(3!)² = 2304 ≤ 7·6! = 5040.             *)
Remark central_bounds_M3 :
  (Nat.leb (fact 6) (4 ^ 3 * (fact 3 * fact 3))
   && Nat.leb (4 ^ 3 * (fact 3 * fact 3)) ((2 * 3 + 1) * fact 6))%bool = true.
Proof. vm_compute. reflexivity. Qed.

Print Assumptions central_upper.
Print Assumptions central_lower.

(* ================================================================= *)
(*  END CentralBinomialBound.v                                       *)
(*  4^M/(2M+1) ≤ C(2M,M) ≤ 4^M, as axiom-free factorial inequalities  *)
(*  — the numerical input for the Chebyshev bound ψ(x) ≍ x.           *)
(*  Closed under the global context.                                 *)
(* ================================================================= *)
