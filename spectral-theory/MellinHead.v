(* ================================================================= *)
(*  MellinHead.v  —  Riemann FE milestone R1, file 6:               *)
(*  the head integral and the fold that consumes the θ-transform.    *)
(*                                                                    *)
(*  Hu(s) = ∫₁^∞ ψ(1/u)·u^{−s/2−1} du  (defined on the reciprocal     *)
(*  side, so the integrand is continuous on [1,∞) — no t→0            *)
(*  singularity).  The reciprocal functional equation Psi_FE          *)
(*  (θ(1/t)=√t·θ(t)) rewrites the integrand into three terms whose    *)
(*  improper integrals are elementary (MellinElem) or T(1−s):         *)
(*     Hu(s) = T(1−s) − 1/s + 1/(s−1)   (s > 1).                      *)
(*  This is the sole place theta_transform is consumed.              *)
(*  No new axioms (classical Reals only).                            *)
(* ================================================================= *)

From Stdlib Require Import Reals Rpower Lra Lia.
Require Import RiemannPsi RiemannPsiCont MellinElem MellinTail ImproperCv1.
Open Scope R_scope.

(* --- the clamped head integrand --- *)

Definition hker (s : R) (u : R) : R := Psi (/ clamp u) * Rpower (clamp u) (- (s / 2) - 1).

Lemma cont_hker : forall s, continuity (hker s).
Proof.
  intros s u; unfold hker; apply continuity_pt_mult.
  - apply (continuity_pt_comp clamp (fun w => Psi (/ w)) u);
      [ apply cont_clamp | apply Psi_recip_cont; apply clamp_pos ].
  - apply (cont_eker (- (s / 2) - 1)).
Qed.

Lemma hker_int : forall s x y, Riemann_integrable (hker s) x y.
Proof.
  intros s x y; destruct (Rle_dec x y) as [H | H].
  - apply continuity_implies_RiemannInt; [ exact H | intros u _; apply cont_hker ].
  - apply RiemannInt_P1; apply continuity_implies_RiemannInt;
      [ lra | intros u _; apply cont_hker ].
Qed.

(* --- the pointwise Psi_FE expansion on [1,∞) --- *)

Lemma hker_eq_expand : forall s u, 1 <= u ->
  hker s u = wker (1 - s) u + (1 / 2) * eker (- (s + 1) / 2) u
                            + (- (1 / 2)) * eker (- (s / 2) - 1) u.
Proof.
  intros s u Hu.
  assert (Hu0 : 0 < u) by lra.
  assert (H1u : 0 < / u) by (apply Rinv_0_lt_compat; exact Hu0).
  set (P1 := Rpower u (- (s / 2) - 1)).
  set (P2 := Rpower u (- (s + 1) / 2)).
  assert (Hsqrt : sqrt u * P1 = P2).
  { unfold P1, P2; rewrite <- (Rpower_sqrt u Hu0), <- Rpower_plus;
      apply (f_equal (Rpower u)); field. }
  assert (Hwk : wker (1 - s) u = P2 * Psi u).
  { unfold wker, P2; rewrite (clamp_id u Hu).
    replace ((1 - s) / 2 - 1) with (- (s + 1) / 2) by field; reflexivity. }
  unfold hker, eker; rewrite !(clamp_id u Hu); rewrite (Psi_FE u Hu0 H1u).
  rewrite Hwk; fold P1 P2.
  replace ((- (1 / 2) + (1 / 2) * sqrt u + sqrt u * Psi u) * P1)
    with (- (1 / 2) * P1 + (1 / 2) * (sqrt u * P1) + (sqrt u * P1) * Psi u) by ring.
  rewrite Hsqrt; ring.
Qed.

(* --- the fold --- *)

Definition Hu (s : R) : R := T (1 - s) - / s + / (s - 1).

Theorem Hu_spec : forall s, 1 < s -> ImproperCv1 (hker s) (hker_int s) (Hu s).
Proof.
  intros s Hs.
  set (a1 := - (s / 2) - 1).
  set (a2 := - (s + 1) / 2).
  assert (Ha1 : a1 < -1) by (unfold a1; lra).
  assert (Ha2 : a2 < -1) by (unfold a2; lra).
  assert (contA : continuity (fun u => wker (1 - s) u + (1 / 2) * eker a2 u))
    by (intro x; apply continuity_pt_plus;
        [ apply cont_wker | apply continuity_pt_scal; apply cont_eker ]).
  assert (HA : forall x y, Riemann_integrable (fun u => wker (1 - s) u + (1 / 2) * eker a2 u) x y).
  { intros x y; destruct (Rle_dec x y) as [H | H];
      [ apply continuity_implies_RiemannInt; [ exact H | intros z _; apply contA ]
      | apply RiemannInt_P1; apply continuity_implies_RiemannInt; [ lra | intros z _; apply contA ] ]. }
  assert (contB : continuity (fun u => (wker (1 - s) u + (1 / 2) * eker a2 u) + (- (1 / 2)) * eker a1 u))
    by (intro x; apply continuity_pt_plus;
        [ apply contA | apply continuity_pt_scal; apply cont_eker ]).
  assert (HB : forall x y, Riemann_integrable
                 (fun u => (wker (1 - s) u + (1 / 2) * eker a2 u) + (- (1 / 2)) * eker a1 u) x y).
  { intros x y; destruct (Rle_dec x y) as [H | H];
      [ apply continuity_implies_RiemannInt; [ exact H | intros z _; apply contB ]
      | apply RiemannInt_P1; apply continuity_implies_RiemannInt; [ lra | intros z _; apply contB ] ]. }
  pose proof (improper_linear (wker (1 - s)) (eker a2) (1 / 2) (wker_int (1 - s)) (eker_int a2)
                HA (T (1 - s)) (- / (a2 + 1)) (T_spec (1 - s)) (eker_improper a2 Ha2)) as StepA.
  pose proof (improper_linear (fun u => wker (1 - s) u + (1 / 2) * eker a2 u) (eker a1) (- (1 / 2))
                HA (eker_int a1) HB (T (1 - s) + (1 / 2) * (- / (a2 + 1))) (- / (a1 + 1))
                StepA (eker_improper a1 Ha1)) as StepB.
  assert (Hval : T (1 - s) + (1 / 2) * (- / (a2 + 1)) + (- (1 / 2)) * (- / (a1 + 1)) = Hu s).
  { unfold Hu, a1, a2; field; repeat split; lra. }
  rewrite <- Hval.
  apply (improper_ext (fun u => (wker (1 - s) u + (1 / 2) * eker a2 u) + (- (1 / 2)) * eker a1 u)
           (hker s) HB (hker_int s)
           (T (1 - s) + (1 / 2) * (- / (a2 + 1)) + (- (1 / 2)) * (- / (a1 + 1)))).
  - intros x Hx; unfold a1, a2; symmetry; apply hker_eq_expand; exact Hx.
  - exact StepB.
Qed.

Print Assumptions Hu_spec.

(* ================================================================= *)
(*  END MellinHead.v                                                 *)
(*  Hu(s) = ∫₁^∞ ψ(1/u)·u^{−s/2−1} du = T(1−s) − 1/s + 1/(s−1)  (s>1). *)
(* ================================================================= *)
