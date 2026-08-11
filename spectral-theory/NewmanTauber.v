(* ================================================================= *)
(*  NewmanTauber.v  —  Newman A3: the quantitative gap engine of the      *)
(*  Tauberian squeeze.                                                   *)
(*                                                                    *)
(*  Newman's Tauberian step (convergence of int_1^oo (psi(u)-u)/u^2 du,    *)
(*  psi nondecreasing => psi(x) ~ x) turns on a strict log-gap:  for any   *)
(*  ratio lam != 1, the "block" contribution                             *)
(*    int_a^{lam a} (lam a - t)/t^2 dt = lam - 1 - ln lam                 *)
(*  is a FIXED POSITIVE constant.  If psi(x) >= lam x for arbitrarily      *)
(*  large x, monotonicity forces the tail integral to keep gaining this    *)
(*  constant, contradicting Cauchy convergence.  The engine is the         *)
(*  positivity  0 < lam - 1 - ln lam  (lam != 1), from the strict          *)
(*  logarithmic inequality  ln lam < lam - 1.  Axiom-clean.               *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Open Scope R_scope.

(*  the strict logarithmic inequality  ln x < x - 1  for x != 1  *)
Lemma ln_lt_lin : forall x, 0 < x -> x <> 1 -> ln x < x - 1.
Proof.
  intros x Hx Hne; assert (Hxm : x - 1 <> 0) by lra.
  pose proof (exp_ineq1 (x - 1) Hxm) as H.
  replace (1 + (x - 1)) with x in H by ring.
  rewrite <- (ln_exp (x - 1)); apply ln_increasing; [ exact Hx | exact H ].
Qed.

(*  the gap constant  lam - 1 - ln lam  is positive for lam != 1          *)
(*  (this is the quantitative core of Newman's monotonicity contradiction, *)
(*   for both the upper lam>1 and lower lam<1 halves)                     *)
Lemma gap_pos : forall lam, 0 < lam -> lam <> 1 -> 0 < lam - 1 - ln lam.
Proof. intros lam Hl Hne; pose proof (ln_lt_lin lam Hl Hne); lra. Qed.

(*  explicit upper-half form:  lam > 1  *)
Corollary gap_pos_gt : forall lam, 1 < lam -> 0 < lam - 1 - ln lam.
Proof. intros lam Hl; apply gap_pos; lra. Qed.

(*  explicit lower-half form:  0 < mu < 1  *)
Corollary gap_pos_lt : forall mu, 0 < mu -> mu < 1 -> 0 < mu - 1 - ln mu.
Proof. intros mu H0 H1; apply gap_pos; lra. Qed.

Print Assumptions gap_pos.

(* ================================================================= *)
(*  END NewmanTauber.v — the positive log-gap lam-1-ln lam.               *)
(*  Remaining for the full Tauberian squeeze: the block integral           *)
(*  int_a^{lam a}(lam a - t)/t^2 dt = lam - 1 - ln lam (FTC on the          *)
(*  antiderivative -lam a/t - ln t), the monotonicity lower bound          *)
(*  (psi nondecreasing => the block gains >= gap_pos), and the Cauchy      *)
(*  contradiction => Un_cv (fun N => psi N / INR N) 1, feeding the          *)
(*  already-proved PNTConditional.pi_asymp_of_psi.  (This step also         *)
(*  needs the contour conclusion int_1^oo (psi(u)-u)/u^2 du converges.)     *)
(* ================================================================= *)
