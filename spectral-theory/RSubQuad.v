(* ================================================================= *)
(*  RSubQuad.v  —  o(r^2) as a COMPOSABLE property.                    *)
(*                                                                    *)
(*    SubQuad f  :=  forall eps > 0, eventually  f r <= eps r^2        *)
(*    MonoR f    :=  f is nondecreasing                                *)
(*                                                                    *)
(*  SubQuadLog's majorant Mf has to be monotone, dominate ln |H|, AND  *)
(*  be o(r^2).  Building it as one closed-form expression and proving  *)
(*  all three at once means chasing a single global constant through   *)
(*  every estimate.  Both properties are CLOSED UNDER SUM, so it is    *)
(*  much cheaper to assemble Mf from pieces and discharge each piece   *)
(*  separately -- no global constant ever has to be named.             *)
(*                                                                    *)
(*  SubQuad_le is the workhorse: it only asks for domination           *)
(*  EVENTUALLY, which is what the estimates actually give (each one    *)
(*  needs its own threshold, and the thresholds never have to be       *)
(*  reconciled).  Axiom-clean.                                         *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra.
Require Import RLogPower.
Open Scope R_scope.

Definition SubQuad (f : R -> R) : Prop :=
  forall eps, 0 < eps -> exists R0, 0 < R0 /\ forall r, R0 <= r -> f r <= eps * r ^ 2.

Definition MonoR (f : R -> R) : Prop := forall a b, a <= b -> f a <= f b.

(* ----------------------------------------------------------------- *)
(*  A.  SubQuad is closed under the operations Mf is built from        *)
(* ----------------------------------------------------------------- *)
Lemma SubQuad_const : forall c, SubQuad (fun _ => c).
Proof.
  intros c eps Heps.
  exists (Rmax 1 (Rabs c / eps + 1)).
  split; [ apply Rlt_le_trans with 1; [ lra | apply Rmax_l ] | ].
  intros r Hr.
  assert (Hr1 : 1 <= r)
    by (apply Rle_trans with (Rmax 1 (Rabs c / eps + 1)); [ apply Rmax_l | exact Hr ]).
  assert (Hr2 : Rabs c / eps + 1 <= r)
    by (apply Rle_trans with (Rmax 1 (Rabs c / eps + 1)); [ apply Rmax_r | exact Hr ]).
  assert (Hc : Rabs c / eps <= r) by lra.
  assert (Hc2 : Rabs c <= eps * r).
  { apply (Rmult_le_reg_r (/ eps)); [ apply Rinv_0_lt_compat; lra | ].
    replace (eps * r * / eps) with r by (field; lra).
    replace (Rabs c * / eps) with (Rabs c / eps) by (unfold Rdiv; ring).
    exact Hc. }
  pose proof (Rle_abs c) as Hac.
  assert (Hrr : r <= r ^ 2) by nra.
  assert (Hstep : eps * r <= eps * r ^ 2)
    by (apply Rmult_le_compat_l; lra).
  lra.
Qed.

Lemma SubQuad_plus : forall f g, SubQuad f -> SubQuad g ->
  SubQuad (fun r => f r + g r).
Proof.
  intros f g Hf Hg eps Heps.
  destruct (Hf (eps / 2) ltac:(lra)) as [R1 [HR1 Hb1]].
  destruct (Hg (eps / 2) ltac:(lra)) as [R2 [HR2 Hb2]].
  exists (Rmax R1 R2). split; [ apply Rlt_le_trans with R1; [ lra | apply Rmax_l ] | ].
  intros r Hr.
  assert (H1 : R1 <= r) by (apply Rle_trans with (Rmax R1 R2); [ apply Rmax_l | exact Hr ]).
  assert (H2 : R2 <= r) by (apply Rle_trans with (Rmax R1 R2); [ apply Rmax_r | exact Hr ]).
  pose proof (Hb1 r H1). pose proof (Hb2 r H2). lra.
Qed.

Lemma SubQuad_le : forall f g, SubQuad g ->
  (exists R1, forall r, R1 <= r -> f r <= g r) -> SubQuad f.
Proof.
  intros f g Hg [R1 Hdom] eps Heps.
  destruct (Hg eps Heps) as [R0 [HR0 Hb]].
  exists (Rmax R0 (Rmax R1 1)).
  split; [ apply Rlt_le_trans with R0; [ lra | apply Rmax_l ] | ].
  intros r Hr.
  assert (H0 : R0 <= r)
    by (apply Rle_trans with (Rmax R0 (Rmax R1 1)); [ apply Rmax_l | exact Hr ]).
  assert (H1 : R1 <= r).
  { apply Rle_trans with (Rmax R1 1); [ apply Rmax_l | ].
    apply Rle_trans with (Rmax R0 (Rmax R1 1)); [ apply Rmax_r | exact Hr ]. }
  pose proof (Hdom r H1). pose proof (Hb r H0). lra.
Qed.

Lemma SubQuad_scal : forall c f, 0 <= c -> SubQuad f ->
  SubQuad (fun r => c * f r).
Proof.
  intros c f Hc Hf.
  destruct Hc as [Hpos | Hzero].
  - intros eps Heps.
    destruct (Hf (eps / c) ltac:(apply Rdiv_lt_0_compat; lra)) as [R0 [HR0 Hb]].
    exists R0. split; [ exact HR0 | ].
    intros r Hr. pose proof (Hb r Hr) as H.
    assert (Hstep : c * f r <= c * (eps / c * r ^ 2))
      by (apply Rmult_le_compat_l; lra).
    replace (c * (eps / c * r ^ 2)) with (eps * r ^ 2) in Hstep by (field; lra).
    exact Hstep.
  - intros eps Heps.
    exists 1. split; [ lra | ]. intros r Hr.
    rewrite <- Hzero. rewrite Rmult_0_l.
    assert (0 <= r ^ 2) by nra. nra.
Qed.

Lemma SubQuad_rln2 : SubQuad (fun r => r * (ln r) ^ 2).
Proof.
  intros eps Heps.
  destruct (r_ln2_subquad 1 eps ltac:(lra) Heps) as [R0 [HR0 Hb]].
  exists R0. split; [ exact HR0 | ].
  intros r Hr. pose proof (Hb r Hr). lra.
Qed.

(* ----------------------------------------------------------------- *)
(*  B.  monotonicity, likewise                                         *)
(* ----------------------------------------------------------------- *)
Lemma MonoR_const : forall c, MonoR (fun _ => c).
Proof. intros c a b Hab. apply Rle_refl. Qed.

Lemma MonoR_plus : forall f g, MonoR f -> MonoR g -> MonoR (fun r => f r + g r).
Proof. intros f g Hf Hg a b Hab. pose proof (Hf a b Hab). pose proof (Hg a b Hab). lra. Qed.

Lemma MonoR_comp : forall f g, MonoR f -> MonoR g -> MonoR (fun r => f (g r)).
Proof. intros f g Hf Hg a b Hab. apply Hf, Hg, Hab. Qed.

Lemma MonoR_shift : forall c, MonoR (fun r => Rmax r 0 + c).
Proof.
  intros c a b Hab.
  assert (H : Rmax a 0 <= Rmax b 0).
  { apply Rmax_lub; [ apply Rle_trans with b; [ exact Hab | apply Rmax_l ]
                    | apply Rmax_r ]. }
  lra.
Qed.

Print Assumptions SubQuad_le.
Print Assumptions SubQuad_rln2.
