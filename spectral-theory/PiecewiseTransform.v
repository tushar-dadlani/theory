(* ================================================================= *)
(*  PiecewiseTransform.v  —  Newman A3: the cell foundation for the       *)
(*  transform of the step function psiR(e^t).                            *)
(*                                                                    *)
(*  psiR(e^t) is constant = psi N on each cell t in (ln N, ln(N+1)),      *)
(*  so it is discontinuous only at t = ln n.  Since Cintf needs GLOBAL    *)
(*  continuity, the transform of psiR(e^t)*K(t) cannot be one Cintf;      *)
(*  it is assembled cell-by-cell from the continuous representative       *)
(*  psi N * K.  This file provides the two foundations:                   *)
(*    Cintf_ext_ab      : interval-local congruence of Cintf (open (a,b), *)
(*                        so an integrand may be replaced by any function *)
(*                        agreeing on the interior -- RiemannInt_P18),    *)
(*    psiRexp_const_cell: psiR(e^t) = psi N on the open cell,             *)
(*  and the per-cell contribution  cell_contrib N K = psi N * int_cell K. *)
(*  Axiom-clean.                                                         *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import ComplexField Cmodulus CIntegral2 CSegInt CLeibniz Chebyshev ChebyshevPsiR.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  interval-local congruence of the complex integral                  *)
(* ----------------------------------------------------------------- *)

Lemma Cintf_ext_ab : forall f g Hf Hg a b, a <= b ->
  (forall u, a < u < b -> f u = g u) ->
  Cintf f Hf a b = Cintf g Hg a b.
Proof.
  intros f g Hf Hg a b Hab Heq; apply Ceq.
  - rewrite !Re_Cintf; apply RiemannInt_P18;
      [ exact Hab | intros x Hx; rewrite (Heq x Hx); reflexivity ].
  - rewrite !Im_Cintf; apply RiemannInt_P18;
      [ exact Hab | intros x Hx; rewrite (Heq x Hx); reflexivity ].
Qed.

(* ----------------------------------------------------------------- *)
(*  psiR(e^t) is constant on each cell                                 *)
(* ----------------------------------------------------------------- *)

Lemma psiRexp_const_cell : forall (N : nat) t, (1 <= N)%nat ->
  ln (INR N) < t < ln (INR (S N)) -> psiR (exp t) = psi N.
Proof.
  intros N t HN [Hlo Hhi]; apply psiR_step; split.
  - rewrite <- (exp_ln (INR N)) by (apply lt_0_INR; lia).
    left; apply exp_increasing; exact Hlo.
  - rewrite <- (exp_ln (INR (S N))) by (apply lt_0_INR; lia).
    apply exp_increasing; exact Hhi.
Qed.

(* ----------------------------------------------------------------- *)
(*  the per-cell contribution to the transform                         *)
(*  (the continuous representative psi N * K over cell N)               *)
(* ----------------------------------------------------------------- *)

Definition cell_contrib (N : nat) (K : R -> C) (HK : Ccont K) : C :=
  Cmul (RtoC (psi N)) (Cintf K HK (ln (INR N)) (ln (INR (S N)))).

(*  on a subinterval [a,b] of the open cell, the psiR-weighted integral    *)
(*  of any continuous representative equals psi N times the plain integral  *)
Lemma cell_reduce : forall (N : nat) (K : R -> C) (HK : Ccont K)
  (Hc : Ccont (fun t => Cmul (RtoC (psi N)) (K t))) a b, a <= b ->
  Cintf (fun t => Cmul (RtoC (psi N)) (K t)) Hc a b
  = Cmul (RtoC (psi N)) (Cintf K HK a b).
Proof. intros N K HK Hc a b Hab; apply Cintf_cmul_l; exact Hab. Qed.

(*  the psiR-weighted integral over a subinterval strictly inside cell N,   *)
(*  where psiR(e^t) is genuinely constant (hence continuous)               *)
Lemma cell_transform_inner : forall (N : nat) (K : R -> C) (HK : Ccont K)
  (Hc : Ccont (fun t => Cmul (RtoC (psiR (exp t))) (K t)))
  (Hc' : Ccont (fun t => Cmul (RtoC (psi N)) (K t))) a b, a <= b ->
  (forall u, a < u < b -> psiR (exp u) = psi N) ->
  Cintf (fun t => Cmul (RtoC (psiR (exp t))) (K t)) Hc a b
  = Cmul (RtoC (psi N)) (Cintf K HK a b).
Proof.
  intros N K HK Hc Hc' a b Hab Hcell.
  rewrite (Cintf_ext_ab (fun t => Cmul (RtoC (psiR (exp t))) (K t))
             (fun t => Cmul (RtoC (psi N)) (K t)) Hc Hc' a b Hab)
    by (intros u Hu; rewrite (Hcell u Hu); reflexivity).
  apply Cintf_cmul_l; exact Hab.
Qed.

Print Assumptions Cintf_ext_ab.
Print Assumptions psiRexp_const_cell.

(* ================================================================= *)
(*  END PiecewiseTransform.v — cell foundation for the step transform.    *)
(*  Next: assemble the truncated transform int_0^{ln M} psiR(e^t)K dt      *)
(*  = sum_{N<M} cell_contrib N K (cell additivity over the ln-partition),  *)
(*  and tie back to phi_integral_rep / the Abel representation.            *)
(* ================================================================= *)
