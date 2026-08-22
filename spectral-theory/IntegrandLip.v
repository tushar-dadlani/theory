(* ================================================================= *)
(*  IntegrandLip.v  --  midpoint_single, DISCHARGED for the integrand. *)
(*                                                                    *)
(*    gint t x  =  Psi(e^x) . e^{x/4} . cos(t x / 2)                   *)
(*                                                                    *)
(*    gint_midpoint : 0 <= r -> 0 <= c - r -> c + r <= L ->            *)
(*      |int_{c-r}^{c+r} gint t - 2 r . gint t c| <= 2 Mfin r^3 / 3    *)
(*                                                                    *)
(*  Stage 4b/4c join.  MidpointQuad.midpoint_single has been proved    *)
(*  since the quadrature brick; this is the first time its hypotheses  *)
(*  are actually met by the object the sign change needs.  Three       *)
(*  things had to exist first: Psi differentiable (ThetaDeriv, via     *)
(*  CVU), Psi' Lipschitz (ThetaDeriv2, via MVT on the partials), and   *)
(*  those transported into x-space WITHOUT going through the chain     *)
(*  rule on the constants (PsiXDeriv).                                 *)
(*                                                                    *)
(*  Everything here is bookkeeping over LipCalc.  The derivative is a  *)
(*  sum of two products of two factors each, and each factor needs a   *)
(*  bound AND a Lipschitz constant, so the raw obligation is twelve    *)
(*  facts; lip_mult / lip_plus / lip_of_deriv supply the closure and   *)
(*  the only genuinely analytic inputs are DG_bound and DG_lipschitz.  *)
(*                                                                    *)
(*  Mfin is left as an explicit expression in Kg1, Kg2, e^{L/4} and    *)
(*  |t| rather than a numeral, so the node count can be re-derived     *)
(*  when L and t are fixed.  At t = 16, L = ln 5 it is about 190,      *)
(*  against a true max|g''| of 2.5 -- a factor 76, i.e. ~8000          *)
(*  quadrature nodes for a total error of 1e-6.  Axiom-clean.          *)
(* ================================================================= *)

From Stdlib Require Import Reals Ranalysis5 Lra Lia.
Require Import JacobiTheta RiemannPsi ThetaTailSharp PsiXSpace
        ThetaDerivMajorant ThetaDeriv ThetaDeriv2 PsiXDeriv
        LipCalc MidpointQuad.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  A.  the pieces                                                    *)
(* ----------------------------------------------------------------- *)
Definition Qe   (x : R) : R := exp (/ 4 * x).
Definition Qe'  (x : R) : R := / 4 * Qe x.
Definition Qe'' (x : R) : R := / 4 * Qe' x.

Definition Ct   (t x : R) : R := cos (t / 2 * x).
Definition Ct'  (t x : R) : R := - (t / 2 * sin (t / 2 * x)).
Definition Ct'' (t x : R) : R := - (t / 2 * (t / 2 * cos (t / 2 * x))).

Definition gint  (t x : R) : R := GPsi x * Qe x * Ct t x.
Definition dgint (t x : R) : R :=
  (DG x * Qe x + GPsi x * Qe' x) * Ct t x + GPsi x * Qe x * Ct' t x.

(* --- elementary chain rules --- *)
Lemma dexp_scal : forall a x, derivable_pt_lim (fun s => exp (a * s)) x (a * exp (a * x)).
Proof.
  intros a x.
  assert (H1 : derivable_pt_lim (fun s => a * s) x (a * 1))
    by (apply derivable_pt_lim_scal; apply derivable_pt_lim_id).
  pose proof (derivable_pt_lim_comp (fun s => a * s) exp x (a * 1) (exp (a * x))
                H1 (derivable_pt_lim_exp _)) as Hc.
  replace (a * exp (a * x)) with (exp (a * x) * (a * 1)) by ring. exact Hc.
Qed.

Lemma dsin_scal : forall a x,
  derivable_pt_lim (fun s => sin (a * s)) x (a * cos (a * x)).
Proof.
  intros a x.
  assert (H1 : derivable_pt_lim (fun s => a * s) x (a * 1))
    by (apply derivable_pt_lim_scal; apply derivable_pt_lim_id).
  pose proof (derivable_pt_lim_comp (fun s => a * s) sin x (a * 1) (cos (a * x))
                H1 (derivable_pt_lim_sin _)) as Hc.
  replace (a * cos (a * x)) with (cos (a * x) * (a * 1)) by ring. exact Hc.
Qed.

Lemma dcos_scal : forall a x,
  derivable_pt_lim (fun s => cos (a * s)) x (- (a * sin (a * x))).
Proof.
  intros a x.
  assert (H1 : derivable_pt_lim (fun s => a * s) x (a * 1))
    by (apply derivable_pt_lim_scal; apply derivable_pt_lim_id).
  pose proof (derivable_pt_lim_comp (fun s => a * s) cos x (a * 1) (- sin (a * x))
                H1 (derivable_pt_lim_cos _)) as Hc.
  replace (- (a * sin (a * x))) with (- sin (a * x) * (a * 1)) by ring. exact Hc.
Qed.

Lemma Qe_deriv  : forall x, derivable_pt_lim Qe x (Qe' x).
Proof. intro x. unfold Qe', Qe. apply dexp_scal. Qed.

Lemma Qe'_deriv : forall x, derivable_pt_lim Qe' x (Qe'' x).
Proof.
  intro x. unfold Qe''. apply derivable_pt_lim_scal. apply Qe_deriv.
Qed.

Lemma Ct_deriv  : forall t x, derivable_pt_lim (Ct t) x (Ct' t x).
Proof. intros t x. unfold Ct, Ct'. apply dcos_scal. Qed.

Lemma Ct'_deriv : forall t x, derivable_pt_lim (Ct' t) x (Ct'' t x).
Proof.
  intros t x. unfold Ct'', Ct'.
  apply derivable_pt_lim_opp. apply derivable_pt_lim_scal. apply dsin_scal.
Qed.

(* ----------------------------------------------------------------- *)
(*  B.  bounds on [0, L]                                              *)
(* ----------------------------------------------------------------- *)
Lemma GPsi_bdd : forall L, BddOn GPsi 0 L (/ 2).
Proof.
  intros L x Hx. destruct Hx as [Hx0 HxL].
  assert (Hu : 1 <= exp x) by (apply exp_ge_1; exact Hx0).
  pose proof PI_RGT_0.
  destruct (Psi_simple (exp x) Hu) as [Hlo Hhi].
  pose proof (Psi_nonneg (exp x)) as Hnn.
  assert (H1 : exp (- (PI * exp x)) <= / 8) by (apply exp_neg_pi_small; exact Hu).
  assert (H2 : exp (- (PI * 4 * exp x)) <= / 8)
    by (apply Rle_trans with (exp (- (PI * exp x)));
        [ apply exp_le_compat; nra | exact H1 ]).
  assert (H3 : exp (- (9 * (PI * exp x))) <= / 8)
    by (apply Rle_trans with (exp (- (PI * exp x)));
        [ apply exp_le_compat; nra | exact H1 ]).
  unfold GPsi. rewrite Rabs_pos_eq by exact Hnn. lra.
Qed.

Lemma DG_bdd : forall L, BddOn DG 0 L Kg1.
Proof. intros L x Hx. apply DG_bound. apply Hx. Qed.

Lemma GPsi_lip : forall L, LipOn GPsi 0 L Kg1.
Proof.
  intro L. apply (lip_of_deriv GPsi DG 0 L Kg1).
  - intros x Hx. apply GPsi_deriv. apply Hx.
  - apply DG_bdd.
Qed.

Lemma DG_lip : forall L, LipOn DG 0 L Kg2.
Proof.
  intros L x y Hx Hy. apply DG_lipschitz; [ apply Hx | apply Hy ].
Qed.

Lemma Qe_pos : forall x, 0 < Qe x. Proof. intro x. apply exp_pos. Qed.

Lemma Qe_bdd : forall L, BddOn Qe 0 L (exp (/ 4 * L)).
Proof.
  intros L x Hx. unfold Qe. rewrite Rabs_pos_eq by (left; apply exp_pos).
  apply exp_le_compat. destruct Hx. lra.
Qed.

Lemma Qe'_bdd : forall L, BddOn Qe' 0 L (/ 4 * exp (/ 4 * L)).
Proof.
  intros L x Hx. unfold Qe'.
  rewrite Rabs_pos_eq by (left; apply Rmult_lt_0_compat; [ lra | apply Qe_pos ]).
  apply Rmult_le_compat_l; [ lra | ].
  pose proof (Qe_bdd L x Hx) as H. rewrite Rabs_pos_eq in H by (left; apply Qe_pos).
  exact H.
Qed.

Lemma Qe''_bdd : forall L, BddOn Qe'' 0 L (/ 16 * exp (/ 4 * L)).
Proof.
  intros L x Hx. unfold Qe''.
  assert (H := Qe'_bdd L x Hx).
  rewrite Rabs_mult, Rabs_pos_eq in * by lra.
  replace (/ 16 * exp (/ 4 * L)) with (/ 4 * (/ 4 * exp (/ 4 * L))) by field.
  apply Rmult_le_compat_l; [ lra | exact H ].
Qed.

Lemma Qe_lip : forall L, LipOn Qe 0 L (/ 4 * exp (/ 4 * L)).
Proof.
  intro L. apply (lip_of_deriv Qe Qe' 0 L).
  - intros x _. apply Qe_deriv.
  - apply Qe'_bdd.
Qed.

Lemma Qe'_lip : forall L, LipOn Qe' 0 L (/ 16 * exp (/ 4 * L)).
Proof.
  intro L. apply (lip_of_deriv Qe' Qe'' 0 L).
  - intros x _. apply Qe'_deriv.
  - apply Qe''_bdd.
Qed.

Lemma Rabs_half : forall t, Rabs (t / 2) = Rabs t / 2.
Proof.
  intro t. unfold Rdiv. rewrite Rabs_mult, (Rabs_pos_eq (/ 2)) by lra. reflexivity.
Qed.

Lemma abs_cos_le1 : forall x, Rabs (cos x) <= 1.
Proof. intro x. apply Rabs_le. pose proof (COS_bound x). lra. Qed.

Lemma abs_sin_le1 : forall x, Rabs (sin x) <= 1.
Proof. intro x. apply Rabs_le. pose proof (SIN_bound x). lra. Qed.

Lemma Ct_bdd : forall t L, BddOn (Ct t) 0 L 1.
Proof. intros t L x _. unfold Ct. apply abs_cos_le1. Qed.

Lemma Ct'_bdd : forall t L, BddOn (Ct' t) 0 L (Rabs t / 2).
Proof.
  intros t L x _. unfold Ct'. rewrite Rabs_Ropp, Rabs_mult, Rabs_half.
  pose proof (abs_sin_le1 (t / 2 * x)) as Hs.
  pose proof (Rabs_pos t).
  assert (0 <= Rabs t / 2) by lra. nra.
Qed.

Lemma Ct''_bdd : forall t L, BddOn (Ct'' t) 0 L (Rabs t / 2 * (Rabs t / 2)).
Proof.
  intros t L x _. unfold Ct''.
  rewrite Rabs_Ropp, Rabs_mult, Rabs_mult, Rabs_half.
  pose proof (abs_cos_le1 (t / 2 * x)) as Hc.
  pose proof (Rabs_pos t). pose proof (Rabs_pos (cos (t / 2 * x))).
  assert (0 <= Rabs t / 2) by lra. nra.
Qed.

Lemma Ct_lip : forall t L, LipOn (Ct t) 0 L (Rabs t / 2).
Proof.
  intros t L. apply (lip_of_deriv (Ct t) (Ct' t) 0 L).
  - intros x _. apply Ct_deriv.
  - apply Ct'_bdd.
Qed.

Lemma Ct'_lip : forall t L, LipOn (Ct' t) 0 L (Rabs t / 2 * (Rabs t / 2)).
Proof.
  intros t L. apply (lip_of_deriv (Ct' t) (Ct'' t) 0 L).
  - intros x _. apply Ct'_deriv.
  - apply Ct''_bdd.
Qed.

(* ----------------------------------------------------------------- *)
(*  C.  the derivative of the integrand                               *)
(* ----------------------------------------------------------------- *)
Lemma gint_deriv : forall t x, 0 <= x -> derivable_pt_lim (gint t) x (dgint t x).
Proof.
  intros t x Hx.
  assert (HP : derivable_pt_lim (fun s => GPsi s * Qe s) x
                 (DG x * Qe x + GPsi x * Qe' x))
    by (apply derivable_pt_lim_mult;
        [ apply GPsi_deriv; exact Hx | apply Qe_deriv ]).
  pose proof (derivable_pt_lim_mult (fun s => GPsi s * Qe s) (Ct t) x
                (DG x * Qe x + GPsi x * Qe' x) (Ct' t x)
                HP (Ct_deriv t x)) as Hm.
  unfold gint, dgint. exact Hm.
Qed.

Lemma gint_cont : forall t x, 0 <= x -> continuity_pt (gint t) x.
Proof.
  intros t x Hx. apply derivable_continuous_pt.
  exists (dgint t x). apply gint_deriv; exact Hx.
Qed.

Theorem gint_RI : forall t a b, 0 <= a -> a <= b -> Riemann_integrable (gint t) a b.
Proof.
  intros t a b Ha Hab. apply continuity_implies_RiemannInt; [ exact Hab | ].
  intros x Hx. apply gint_cont. lra.
Qed.

(* ----------------------------------------------------------------- *)
(*  D.  the Lipschitz constant of the derivative                      *)
(* ----------------------------------------------------------------- *)
Definition EL (L : R) : R := exp (/ 4 * L).
Definition Tt (t : R) : R := Rabs t / 2.

Definition Mfin (t L : R) : R :=
  ((Kg1 * EL L + / 2 * (/ 4 * EL L)) * Tt t
   + 1 * ((Kg1 * (/ 4 * EL L) + EL L * Kg2)
          + (/ 2 * (/ 16 * EL L) + / 4 * EL L * Kg1)))
  + (/ 2 * EL L * (Tt t * Tt t)
     + Tt t * (/ 2 * (/ 4 * EL L) + EL L * Kg1)).

Lemma EL_pos : forall L, 0 < EL L. Proof. intro L. apply exp_pos. Qed.
Lemma Tt_nonneg : forall t, 0 <= Tt t.
Proof. intro t. unfold Tt. pose proof (Rabs_pos t). lra. Qed.

Lemma Mfin_nonneg : forall t L, 0 <= Mfin t L.
Proof.
  intros t L. unfold Mfin.
  pose proof (EL_pos L). pose proof (Tt_nonneg t).
  pose proof Kg1_nonneg. pose proof Kg2_nonneg.
  assert (G1 : 0 <= Kg1 * EL L) by (apply Rmult_le_pos; lra).
  assert (G3 : 0 <= Kg1 * (/ 4 * EL L)) by (apply Rmult_le_pos; lra).
  assert (G4 : 0 <= EL L * Kg2) by (apply Rmult_le_pos; lra).
  assert (G6 : 0 <= / 4 * EL L * Kg1) by (apply Rmult_le_pos; lra).
  assert (G8 : 0 <= Tt t * Tt t) by (apply Rmult_le_pos; lra).
  assert (Ha : 0 <= (Kg1 * EL L + / 2 * (/ 4 * EL L)) * Tt t)
    by (apply Rmult_le_pos; lra).
  assert (Hb : 0 <= / 2 * EL L * (Tt t * Tt t)) by (apply Rmult_le_pos; lra).
  assert (Hc : 0 <= Tt t * (/ 2 * (/ 4 * EL L) + EL L * Kg1))
    by (apply Rmult_le_pos; lra).
  lra.
Qed.

Theorem dgint_lip : forall t L, LipOn (dgint t) 0 L (Mfin t L).
Proof.
  intros t L.
  pose proof (EL_pos L) as HE. pose proof (Tt_nonneg t) as HT.
  pose proof Kg1_nonneg as HK1. pose proof Kg2_nonneg as HK2.
  assert (HQ  : 0 <= EL L) by lra.
  assert (HQ' : 0 <= / 4 * EL L) by lra.
  (* DG * Qe *)
  assert (HA_b : BddOn (fun x => DG x * Qe x) 0 L (Kg1 * EL L))
    by (apply bdd_mult; [ exact HK1 | apply DG_bdd | apply Qe_bdd ]).
  assert (HA_l : LipOn (fun x => DG x * Qe x) 0 L
                   (Kg1 * (/ 4 * EL L) + EL L * Kg2)).
  { apply lip_mult; try assumption; try lra.
    - apply DG_bdd.
    - apply Qe_bdd.
    - apply DG_lip.
    - apply Qe_lip. }
  (* GPsi * Qe' *)
  assert (HB_b : BddOn (fun x => GPsi x * Qe' x) 0 L (/ 2 * (/ 4 * EL L)))
    by (apply bdd_mult; [ lra | apply GPsi_bdd | apply Qe'_bdd ]).
  assert (HB_l : LipOn (fun x => GPsi x * Qe' x) 0 L
                   (/ 2 * (/ 16 * EL L) + / 4 * EL L * Kg1)).
  { apply lip_mult; try assumption; try lra.
    - apply GPsi_bdd.
    - apply Qe'_bdd.
    - apply GPsi_lip.
    - apply Qe'_lip. }
  (* their sum *)
  assert (HS_b : BddOn (fun x => DG x * Qe x + GPsi x * Qe' x) 0 L
                   (Kg1 * EL L + / 2 * (/ 4 * EL L)))
    by (apply bdd_plus; assumption).
  assert (HS_l : LipOn (fun x => DG x * Qe x + GPsi x * Qe' x) 0 L
                   ((Kg1 * (/ 4 * EL L) + EL L * Kg2)
                    + (/ 2 * (/ 16 * EL L) + / 4 * EL L * Kg1)))
    by (apply lip_plus; assumption).
  (* GPsi * Qe *)
  assert (HP_b : BddOn (fun x => GPsi x * Qe x) 0 L (/ 2 * EL L))
    by (apply bdd_mult; [ lra | apply GPsi_bdd | apply Qe_bdd ]).
  assert (HP_l : LipOn (fun x => GPsi x * Qe x) 0 L
                   (/ 2 * (/ 4 * EL L) + EL L * Kg1)).
  { apply lip_mult; try assumption; try lra.
    - apply GPsi_bdd.
    - apply Qe_bdd.
    - apply GPsi_lip.
    - apply Qe_lip. }
  (* assemble *)
  unfold dgint, Mfin.
  apply lip_plus.
  - apply lip_mult with (M1 := Kg1 * EL L + / 2 * (/ 4 * EL L)) (M2 := 1);
      try assumption; try nra.
    + apply Ct_bdd.
    + apply Ct_lip.
  - apply lip_mult with (M1 := / 2 * EL L) (M2 := Tt t);
      try assumption; try nra.
    + apply Ct'_bdd.
    + apply Ct'_lip.
Qed.

(* ----------------------------------------------------------------- *)
(*  E.  midpoint_single, DISCHARGED                                   *)
(* ----------------------------------------------------------------- *)
Theorem gint_midpoint : forall t L c r
  (prf : Riemann_integrable (gint t) (c - r) (c + r)),
  0 <= r -> 0 <= c - r -> c + r <= L ->
  Rabs (RiemannInt prf - 2 * r * gint t c) <= 2 * Mfin t L * r ^ 3 / 3.
Proof.
  intros t L c r prf Hr Hlo Hhi.
  apply (midpoint_single (gint t) (dgint t) c (Mfin t L) r prf).
  - exact Hr.
  - apply Mfin_nonneg.
  - intros y Hy. apply gint_deriv. lra.
  - intros y z Hy Hz. apply (dgint_lip t L); split; lra.
Qed.

Print Assumptions dgint_lip.
Print Assumptions gint_RI.
Print Assumptions gint_midpoint.
