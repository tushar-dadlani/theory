(* ================================================================= *)
(*  WeylTerm.v                                                        *)
(*                                                                    *)
(*  The WEYL MAIN TERM of the Riemann-von Mangoldt zero-counting       *)
(*  formula, formalised with its exact calculus.                      *)
(*                                                                    *)
(*  The smooth part of N(T) (# zeros of zeta with 0 < Im rho <= T) is  *)
(*     Nsmooth T = (T/2pi) ln(T/2pi) - T/2pi.                          *)
(*  PROVED here (axiom-clean, standard classical-Reals only):          *)
(*   - Nsmooth_deriv: its derivative is the zero DENSITY               *)
(*        dens T = (1/2pi) ln(T/2pi)   -- the analytic heart;          *)
(*   - dens_pos: the density is positive for T > 2pi;                  *)
(*   - Nsmooth_increasing: the smooth count is strictly increasing     *)
(*        above 2pi (positive derivative, via MVT);                    *)
(*   - dens_gap: density * mean gap = 1, the mean spacing              *)
(*        2pi / ln(T/2pi) near height T.                               *)
(*                                                                    *)
(*  SCOPE / HONEST GAP: this is the SMOOTH main term only.  The full   *)
(*  Riemann-von Mangoldt statement  N(T) = Nsmooth T + S(T) + O(1),    *)
(*  identifying Nsmooth with the ACTUAL zero count, needs the argument *)
(*  principle as a theorem plus Gamma/Stirling asymptotics on vertical *)
(*  lines -- not in this repo.  What the repo already proves           *)
(*  unconditionally is that the actual count equals the number of      *)
(*  half-windings of the Weyl phase Wxi through the Dirichlet phase -1 *)
(*  (WeylWinding.weyl_winding_count); Nsmooth is the smooth RATE of     *)
(*  that winding.                                                      *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Rpower MVT Ranalysis1.
Open Scope R_scope.

Definition twopi : R := 2 * PI.

Lemma twopi_pos : 0 < twopi.
Proof. unfold twopi; pose proof PI_RGT_0; lra. Qed.

(* the zero density and the smooth counting function *)
Definition dens (T : R) : R := / twopi * ln (T / twopi).
Definition Nsmooth (T : R) : R := T / twopi * ln (T / twopi) - T / twopi.

(* T/2pi > 1 exactly when T > 2pi *)
Lemma quotient_gt_1 : forall T, twopi < T -> 1 < T / twopi.
Proof.
  intros T HT. pose proof twopi_pos as Hp.
  apply Rmult_lt_reg_r with (r := twopi); [ exact Hp | ]. rewrite Rmult_1_l.
  replace (T / twopi * twopi) with T by (field; lra). exact HT.
Qed.

Lemma dens_pos : forall T, twopi < T -> 0 < dens T.
Proof.
  intros T HT. unfold dens. apply Rmult_lt_0_compat.
  - apply Rinv_0_lt_compat, twopi_pos.
  - rewrite <- ln_1. apply ln_increasing; [ lra | apply quotient_gt_1; exact HT ].
Qed.

(* helper: derivative of the linear map x |-> x/twopi is /twopi *)
Lemma deriv_lin : forall T, derivable_pt_lim (fun x => x / twopi) T (/ twopi).
Proof.
  intro T.
  assert (H := derivable_pt_lim_mult id (fct_cte (/ twopi)) T 1 0
                 (derivable_pt_lim_id T) (derivable_pt_lim_const (/ twopi) T)).
  replace (1 * fct_cte (/ twopi) T + id T * 0) with (/ twopi) in H
    by (unfold fct_cte, id; ring).
  exact H.
Qed.

(* CORE: the derivative of the smooth count is the density. *)
Lemma Nsmooth_deriv : forall T, 0 < T -> derivable_pt_lim Nsmooth T (dens T).
Proof.
  intros T HT. pose proof twopi_pos as Hp.
  assert (Hq : 0 < T / twopi) by (apply Rdiv_lt_0_compat; lra).
  assert (Heq :
    (/ twopi * ln (T / twopi) + T / twopi * (/ (T / twopi) * / twopi)) - / twopi
    = dens T).
  { unfold dens. field. split; lra. }
  rewrite <- Heq. unfold Nsmooth.
  apply (derivable_pt_lim_minus
           (fun x => x / twopi * ln (x / twopi)) (fun x => x / twopi) T).
  - apply (derivable_pt_lim_mult (fun x => x / twopi) (fun x => ln (x / twopi)) T).
    + apply deriv_lin.
    + apply (derivable_pt_lim_comp (fun x => x / twopi) ln T (/ twopi) (/ (T / twopi))).
      * apply deriv_lin.
      * apply derivable_pt_lim_ln; exact Hq.
  - apply deriv_lin.
Qed.

(* the smooth count is strictly increasing above 2pi (positive density). *)
Lemma Nsmooth_increasing : forall a b, twopi < a -> a < b -> Nsmooth a < Nsmooth b.
Proof.
  intros a b Ha Hab. pose proof twopi_pos as Hp.
  assert (Hd : forall c, a <= c <= b -> derivable_pt_lim Nsmooth c (dens c)).
  { intros c [Hc1 Hc2]. apply Nsmooth_deriv. lra. }
  destruct (MVT_cor2 Nsmooth dens a b Hab Hd) as [c [Hval [Hc1 Hc2]]].
  assert (0 < dens c) by (apply dens_pos; lra).
  nra.
Qed.

(* density * mean gap = 1: the mean spacing near height T is 2pi/ln(T/2pi). *)
Definition mean_gap (T : R) : R := twopi / ln (T / twopi).

Lemma dens_gap : forall T, twopi < T -> dens T * mean_gap T = 1.
Proof.
  intros T HT. pose proof twopi_pos as Hp.
  assert (Hln : 0 < ln (T / twopi))
    by (rewrite <- ln_1; apply ln_increasing; [ lra | apply quotient_gt_1; exact HT ]).
  unfold dens, mean_gap. field. split; lra.
Qed.

Print Assumptions Nsmooth_deriv.
Print Assumptions Nsmooth_increasing.
