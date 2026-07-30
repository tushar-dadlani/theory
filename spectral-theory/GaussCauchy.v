(* ================================================================= *)
(*  GaussCauchy.v  —  Leibniz-gap Phase 1 (core): the Cauchy engine    *)
(*  and the dominating sequences.                                     *)
(*                                                                    *)
(*  The oscillatory transform integrands e^{−πx²}cos(2πxξ) and         *)
(*  −2πx e^{−πx²}sin(2πxξ) are not sign-definite, so the monotone       *)
(*  ImproperCvR scaffold does not apply.  Instead the partial          *)
(*  integrals S_k = ∫_{−k}^k are CAUCHY, because their increments are   *)
(*  DOMINATED by the increments of a convergent sequence:             *)
(*    • the cos-transform by  D_k = ∫_{−k}^k e^{−πx²}  (→ 1, gauss_pi); *)
(*    • the sin-derivative by  E_k = e^{−πk²}          (decreasing).   *)
(*  This file builds the engine and those two dominating sequences.    *)
(*                                                                    *)
(*    cauchy_dominated_cv : |S i − S j| ≤ |C i − C j| and C convergent  *)
(*                          ⇒ S converges (R_complete);                *)
(*    E_cv : e^{−πk²} converges (decreasing, bounded below);           *)
(*    D_cv : ∫_{−k}^k e^{−πx²} → 1 (gauss_pi at the sequence INR k).    *)
(*                                                                    *)
(*  No new axioms (classical Reals only).                             *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import GaussFull GaussPiValue.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  The engine: domination by a convergent sequence ⇒ Cauchy ⇒ conv. *)
(* ----------------------------------------------------------------- *)

Lemma cauchy_dominated_cv : forall (S C : nat -> R) (Lc : R),
  (forall i j, Rabs (S i - S j) <= Rabs (C i - C j)) ->
  Un_cv C Lc -> { l : R | Un_cv S l }.
Proof.
  intros S C Lc Hdom HC.
  apply R_complete; intros eps He.
  destruct (HC (eps / 2) ltac:(lra)) as [N HN].
  exists N; intros n m Hn Hm.
  unfold R_dist; eapply Rle_lt_trans; [ apply Hdom | ].
  replace (C n - C m) with ((C n - Lc) + (Lc - C m)) by ring.
  eapply Rle_lt_trans; [ apply Rabs_triang | ].
  pose proof (HN n Hn) as H1; pose proof (HN m Hm) as H2; unfold R_dist in H1, H2.
  rewrite (Rabs_minus_sym Lc (C m)); lra.
Qed.

(* ----------------------------------------------------------------- *)
(*  E_k = e^{−πk²} is decreasing and bounded below ⇒ convergent.     *)
(* ----------------------------------------------------------------- *)

Lemma exp_pi_decr : forall a b, 0 <= a -> a <= b -> exp_pi b <= exp_pi a.
Proof.
  intros a b Ha Hab; unfold exp_pi.
  assert (Hle : - (PI * b ^ 2) <= - (PI * a ^ 2)).
  { apply Ropp_le_contravar; apply Rmult_le_compat_l;
      [ pose proof PI_RGT_0; lra | apply pow_incr; split; [ exact Ha | exact Hab ] ]. }
  destruct (Rle_lt_or_eq_dec _ _ Hle) as [Hlt | Heq].
  - apply Rlt_le; apply exp_increasing; exact Hlt.
  - rewrite Heq; apply Rle_refl.
Qed.

Lemma E_cv : { L : R | Un_cv (fun k => exp_pi (INR k)) L }.
Proof.
  apply decreasing_cv.
  - intro n; apply exp_pi_decr; [ apply pos_INR | rewrite S_INR; lra ].
  - exists 0; intros x [i Hx]; rewrite Hx; unfold opp_seq.
    rewrite <- Ropp_0; apply Ropp_le_contravar; apply Rlt_le; apply exp_pos.
Qed.

(* ----------------------------------------------------------------- *)
(*  D_k = ∫_{−k}^k e^{−πx²} → 1.                                     *)
(* ----------------------------------------------------------------- *)

Lemma cv_infty_INR : cv_infty (fun k => INR k).
Proof.
  intro M; destruct (INR_unbounded M) as [N HN]; exists N; intros n Hn.
  apply Rlt_le_trans with (INR N); [ exact HN | apply le_INR; exact Hn ].
Qed.

Lemma D_cv : Un_cv (fun k => pintR exp_pi exp_pi_int (INR k)) 1.
Proof.
  exact (gauss_pi (fun k => INR k) (fun k => pos_INR k) cv_infty_INR).
Qed.

Print Assumptions cauchy_dominated_cv.
Print Assumptions E_cv.
Print Assumptions D_cv.

(* ================================================================= *)
(*  END GaussCauchy.v (Phase 1 core)                                *)
(*  The Cauchy engine + the two convergent dominators.  Next: the     *)
(*  tail bounds |S_transform i − S_transform j| ≤ |D i − D j| and       *)
(*  |S_deriv i − S_deriv j| ≤ 2|E i − E j| (RiemannInt_P17 abs +        *)
(*  Chasles + evenness), giving the transform value F and derivative   *)
(*  value g with pointwise convergence and the ξ-uniform tail (CVU).   *)
(* ================================================================= *)
