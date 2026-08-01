(* ================================================================= *)
(*  XiReflection.v  —  assembling Riemann's functional equation.      *)
(*                                                                    *)
(*  The completed zeta ξ(s) := J(s) (the symmetric θ-integral, R1)     *)
(*  equals π^{−s/2}·Γ(s/2)·ζ(s) for s>1 (R3), and is symmetric,        *)
(*  ξ(s)=ξ(1−s) (R1) — Riemann's functional equation.  We also solve  *)
(*  for ζ (needing Γ(s/2)>0, proved here) giving the explicit         *)
(*  continuation ζ(s) = J(s)·π^{s/2}/Γ(s/2).                          *)
(*  No new axioms (classical Reals only).                            *)
(* ================================================================= *)

From Stdlib Require Import Reals Rpower Lra Lia.
Require Import GammaReal ImproperCv1 MellinElem RiemannThetaFE ZetaCompleted
        Ell2ZetaCont HagedornTransition.
Open Scope R_scope.

(* --- strict positivity of Γ --- *)

Lemma int12_pos : forall a, 0 < RiemannInt (gtk_int a 1 1 2).
Proof.
  intro a.
  set (m := Rmin (exp (- 2)) (Rpower 2 (a - 1) * exp (- 2))).
  assert (Hm : 0 < m).
  { unfold m; apply Rmin_pos;
      [ apply exp_pos | apply Rmult_lt_0_compat; [ unfold Rpower; apply exp_pos | apply exp_pos ] ]. }
  apply Rlt_le_trans with (RiemannInt (RiemannInt_P14 1 2 m)).
  - rewrite (RiemannInt_P15 (RiemannInt_P14 1 2 m)); replace (2 - 1) with 1 by ring;
      rewrite Rmult_1_r; exact Hm.
  - apply RiemannInt_P19; [ lra | intros u [Hu1 Hu2]; unfold fct_cte ].
    assert (Hu0 : 0 < u) by lra.
    unfold gtk; rewrite (clamp_id u) by lra; replace (1 * u) with u by ring.
    destruct (Rle_dec 1 a) as [Ha1 | Ha1].
    + apply Rle_trans with (exp (- 2)); [ apply Rmin_l | ].
      apply Rle_trans with (1 * exp (- u)).
      * rewrite Rmult_1_l; apply Rlt_le; apply exp_increasing; lra.
      * apply Rmult_le_compat_r; [ left; apply exp_pos | ].
        pose proof (Rle_Rpower u 0 (a - 1) ltac:(lra) ltac:(lra)) as HR;
          rewrite (Rpower_O u Hu0) in HR; exact HR.
    + apply Rle_trans with (Rpower 2 (a - 1) * exp (- 2)); [ apply Rmin_r | ].
      apply Rmult_le_compat.
      * left; unfold Rpower; apply exp_pos.
      * left; apply exp_pos.
      * replace (a - 1) with (- (1 - a)) by ring;
          apply Rpower_negexp_antimono; [ exact Hu0 | lra | lra ].
      * apply Rlt_le; apply exp_increasing; lra.
Qed.

Theorem Gam_pos : forall a (Ha : 0 < a), 0 < Gam a Ha.
Proof.
  intros a Ha; unfold Gam, mellin.
  assert (Ht : 0 < gtail a 1 Rlt_0_1).
  { unfold gtail; destruct (gtail_sig a 1 Rlt_0_1) as [I HI]; simpl.
    apply Rlt_le_trans with (RiemannInt (gtk_int a 1 1 2)); [ apply int12_pos | ].
    exact (pint1_le_improper (gtk a 1) (gtk_int a 1) I HI
             (fun x _ => gtk_nonneg a 1 x) 2 ltac:(lra)). }
  pose proof (gnear_pos a 1 Ha Rlt_0_1); lra.
Qed.

(* --- the completed zeta and the functional equation --- *)

Definition Xi (s : R) : R := J s.

Theorem Xi_completed : forall s (Hs0 : 0 < s) (Hs1 : s <> 1) (Hs2 : 0 < s / 2), 1 < s ->
  Xi s = Rpower PI (- (s / 2)) * Gam (s / 2) Hs2 * zeta_cont s Hs0 Hs1.
Proof. intros s Hs0 Hs1 Hs2 Hs; unfold Xi; symmetry; apply zeta_completed_eq_J; exact Hs. Qed.

Theorem Xi_symmetric : forall s, s <> 0 -> s <> 1 -> Xi s = Xi (1 - s).
Proof. intros s Hs0 Hs1; unfold Xi; apply J_symmetric; assumption. Qed.

(* the functional equation: completed zeta at s = its value at the reflected 1−s *)
Theorem functional_equation : forall s (Hs0 : 0 < s) (Hs1 : s <> 1) (Hs2 : 0 < s / 2), 1 < s ->
  Rpower PI (- (s / 2)) * Gam (s / 2) Hs2 * zeta_cont s Hs0 Hs1 = Xi (1 - s).
Proof.
  intros s Hs0 Hs1 Hs2 Hs; unfold Xi.
  rewrite (zeta_completed_eq_J s Hs0 Hs1 Hs2 Hs); apply J_symmetric; lra.
Qed.

(* ζ expressed via the completed θ-integral J (an explicit continuation) *)
Theorem zeta_solved : forall s (Hs0 : 0 < s) (Hs1 : s <> 1) (Hs2 : 0 < s / 2), 1 < s ->
  zeta_cont s Hs0 Hs1 = J s * Rpower PI (s / 2) / Gam (s / 2) Hs2.
Proof.
  intros s Hs0 Hs1 Hs2 Hs.
  pose proof (zeta_completed_eq_J s Hs0 Hs1 Hs2 Hs) as HE.
  pose proof (Gam_pos (s / 2) Hs2) as HG.
  rewrite <- HE, (Rpower_Ropp PI (s / 2)).
  field; split; [ apply Rgt_not_eq; unfold Rpower; apply exp_pos | apply Rgt_not_eq; exact HG ].
Qed.

Print Assumptions functional_equation.
Print Assumptions zeta_solved.

(* ================================================================= *)
(*  END XiReflection.v.  π^{−s/2}·Γ(s/2)·ζ(s) = J(s) = J(1−s).         *)
(* ================================================================= *)
