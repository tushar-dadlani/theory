(* ================================================================= *)
(*  RiemannPsi.v  —  Riemann FE milestone R1, file 1:                 *)
(*  the total Jacobi ψ-function and its reciprocal functional eq.    *)
(*                                                                    *)
(*  ψ(t) = (θ(t)−1)/2 = Σ_{n≥1} e^{−πn²t}.  We package it as a TOTAL   *)
(*  function `Psi : R→R` (via an Rlt_dec guard, since `theta t Ht`    *)
(*  carries its positivity proof and is not total), so it can be fed  *)
(*  to `RiemannInt`.  The one nontrivial fact is the reciprocal       *)
(*  functional equation `Psi_FE`, read straight off `theta_transform` *)
(*  (θ(1/t)=√t·θ(t)):                                                 *)
(*     ψ(1/t) = −1/2 + (1/2)√t + √t·ψ(t).                             *)
(*  Continuity of ψ is deferred to RiemannPsiCont.v.                  *)
(*  No new axioms (classical Reals only).                            *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra.
Require Import JacobiTheta GaussThetaTransform.
Open Scope R_scope.

(* --- proof-irrelevance of θ in its positivity witness --- *)

Lemma theta_pirr : forall t (H1 H2 : 0 < t), theta t H1 = theta t H2.
Proof.
  intros t H1 H2; unfold theta.
  destruct (theta_half_converges t H1) as [L1 HL1].
  destruct (theta_half_converges t H2) as [L2 HL2]; simpl.
  assert (L1 = L2) by (apply (UL_sequence (theta_partial t)); assumption).
  rewrite H; reflexivity.
Qed.

(* --- the total ψ --- *)

Definition Psi (t : R) : R :=
  match Rlt_dec 0 t with
  | left H => (theta t H - 1) / 2
  | right _ => 0
  end.

Lemma Psi_val : forall t (Ht : 0 < t), Psi t = (theta t Ht - 1) / 2.
Proof.
  intros t Ht; unfold Psi; destruct (Rlt_dec 0 t) as [H | H].
  - rewrite (theta_pirr t H Ht); reflexivity.
  - exfalso; lra.
Qed.

Lemma Psi_nonneg : forall t, 0 <= Psi t.
Proof.
  intro t; unfold Psi; destruct (Rlt_dec 0 t) as [H | H].
  - pose proof (theta_gt_1 t H); lra.
  - apply Rle_refl.
Qed.

Lemma Psi_pos : forall t, 0 < t -> 0 < Psi t.
Proof. intros t Ht; rewrite (Psi_val t Ht); pose proof (theta_gt_1 t Ht); lra. Qed.

Lemma Psi_antitone : forall t1 t2 (H1 : 0 < t1) (H2 : 0 < t2),
  t1 <= t2 -> Psi t2 <= Psi t1.
Proof.
  intros t1 t2 H1 H2 Hle; rewrite (Psi_val t1 H1), (Psi_val t2 H2).
  pose proof (theta_antitone t1 t2 H1 H2 Hle); lra.
Qed.

(* the exponential upper bound: ψ(t) ≤ q/(1−q), q = e^{−πt} → 0 *)
Lemma Psi_upper : forall t (Ht : 0 < t),
  Psi t <= exp (- (PI * t)) / (1 - exp (- (PI * t))).
Proof.
  intros t Ht; rewrite (Psi_val t Ht); pose proof (theta_upper t Ht); lra.
Qed.

(* --- the reciprocal functional equation (consumes theta_transform) --- *)

Theorem Psi_FE : forall t (Ht : 0 < t) (H1t : 0 < / t),
  Psi (/ t) = - (1 / 2) + (1 / 2) * sqrt t + sqrt t * Psi t.
Proof.
  intros t Ht H1t.
  rewrite (Psi_val (/ t) H1t), (Psi_val t Ht), (theta_transform t Ht H1t).
  field.
Qed.

Print Assumptions Psi_FE.

(* ================================================================= *)
(*  END RiemannPsi.v                                                 *)
(*  ψ total, ψ(1/t) = −1/2 + (1/2)√t + √t·ψ(t).                       *)
(* ================================================================= *)
