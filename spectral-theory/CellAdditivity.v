(* ================================================================= *)
(*  CellAdditivity.v  —  Newman A3: additivity of the complex integral    *)
(*  over a partition (the cell-assembly backbone).                       *)
(*                                                                    *)
(*  Cintf_partition : for any breakpoint sequence p,                     *)
(*     int_{p 0}^{p (J+1)} K  =  sum_{k<=J} int_{p k}^{p (k+1)} K,        *)
(*  the finite additivity of Cintf over consecutive cells (Cintf_additive *)
(*  telescoped).  Instantiated to the two Newman partitions:             *)
(*    logpart_additive : the ln-partition 0 = ln 1 < ln 2 < ... (t-space, *)
(*                       the Laplace form),                              *)
(*    upart_additive   : the integer partition 1 < 2 < 3 < ... (u-space,  *)
(*                       matching the Abel/phi_integral_rep cells).       *)
(*  Axiom-clean.                                                         *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import ComplexField Cmodulus CSeries CIntegral2 CSegInt CLeibniz
        Chebyshev ChebyshevPsiR PiecewiseTransform.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  general finite additivity over a partition                         *)
(* ----------------------------------------------------------------- *)

Lemma Cintf_partition : forall K HK (p : nat -> R) J,
  Cintf K HK (p O) (p (S J)) = Cpsum (fun k => Cintf K HK (p k) (p (S k))) J.
Proof.
  intros K HK p J; induction J as [|J IH]; [ reflexivity | ].
  simpl (Cpsum (fun k => Cintf K HK (p k) (p (S k))) (S J)); rewrite <- IH.
  apply Cintf_additive.
Qed.

(* ----------------------------------------------------------------- *)
(*  the ln-partition (t-space, Newman's Laplace variable)              *)
(* ----------------------------------------------------------------- *)

Lemma logpart_additive : forall K HK J,
  Cintf K HK 0 (ln (INR (S (S J))))
  = Cpsum (fun k => Cintf K HK (ln (INR (S k))) (ln (INR (S (S k))))) J.
Proof.
  intros K HK J.
  rewrite <- (Cintf_partition K HK (fun n => ln (INR (S n))) J).
  replace (ln (INR (S O))) with 0 by (rewrite INR_1, ln_1; reflexivity).
  reflexivity.
Qed.

(* ----------------------------------------------------------------- *)
(*  the integer partition (u-space, matching phi_integral_rep cells)   *)
(* ----------------------------------------------------------------- *)

Lemma upart_additive : forall K HK J,
  Cintf K HK 1 (INR (S (S J)))
  = Cpsum (fun k => Cintf K HK (INR (S k)) (INR (S (S k)))) J.
Proof.
  intros K HK J.
  rewrite <- (Cintf_partition K HK (fun n => INR (S n)) J).
  replace (INR (S O)) with 1 by (rewrite INR_1; reflexivity).
  reflexivity.
Qed.

(* ----------------------------------------------------------------- *)
(*  the truncated step transform, as the cell sum                      *)
(* ----------------------------------------------------------------- *)

(*  int_0^{ln(J+2)} [step] K  =  sum_{k<=J} psi(k+1) * int_{cell (k+1)} K *)
Definition step_transform (J : nat) (K : R -> C) (HK : Ccont K) : C :=
  Cpsum (fun k => cell_contrib (S k) K HK) J.

Lemma step_transform_S : forall J K HK,
  step_transform (S J) K HK = Cadd (step_transform J K HK) (cell_contrib (S (S J)) K HK).
Proof. intros J K HK; unfold step_transform; reflexivity. Qed.

Print Assumptions Cintf_partition.
Print Assumptions logpart_additive.
Print Assumptions upart_additive.

(* ================================================================= *)
(*  END CellAdditivity.v — partition additivity of Cintf.                 *)
(*  Next: with K = gderivC (= d/du u^{-s}), each cell integral is the      *)
(*  increment gC s(N+1)-gC s(N) (gC_FTC), so the weighted cell sum IS      *)
(*  the Abel correction (correction_cells); phi_integral_rep then gives    *)
(*  the u-space identity  int_1^oo psiR(u) u^{-s-1} du = Phi(s)/s.          *)
(* ================================================================= *)
