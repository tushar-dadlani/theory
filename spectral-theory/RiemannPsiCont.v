(* ================================================================= *)
(*  RiemannPsiCont.v  —  Riemann FE milestone R1, file 2:            *)
(*  continuity of ψ on (0,∞).                                        *)
(*                                                                    *)
(*  ψ = Σ e^{−πn²t} is a uniform limit of its partial sums on every   *)
(*  compact [a,b] ⊂ (0,∞): on a ball around t₀>0 with lower edge      *)
(*  a = t₀/2, each term is dominated by qₐ^{n+1} (qₐ = e^{−πa} < 1),  *)
(*  so the geometric tail bound (geom_tail_est) is uniform in y.      *)
(*  Weierstrass M-test ⟹ CVU ⟹ CVU_continuity gives continuity of ψ. *)
(*  Also the reciprocal composition u ↦ ψ(1/u) is continuous on       *)
(*  (0,∞), the form the head integrand needs.                        *)
(*  No new axioms (classical Reals only).                            *)
(* ================================================================= *)

From Stdlib Require Import Reals Ranalysis5 PSeries_reg Lra Lia.
Require Import JacobiTheta RiemannPsi GaussPeriodDeriv.
Open Scope R_scope.

(* --- continuity of the finite partial sums in t --- *)

Lemma cont_theta_term : forall k, continuity (fun y => theta_term y k).
Proof.
  intros k y; unfold theta_term.
  apply (continuity_pt_comp (fun y => - (PI * INR (S k) ^ 2 * y)) exp y).
  - apply continuity_pt_opp.
    apply (continuity_pt_scal (fun y => y) (PI * INR (S k) ^ 2) y).
    apply derivable_continuous_pt; exists 1; apply derivable_pt_lim_id.
  - apply derivable_continuous_pt; apply derivable_pt_exp.
Qed.

Lemma cont_theta_partial : forall N, continuity (fun y => theta_partial y N).
Proof.
  intro N; apply (cont_sum (fun k s => theta_term s k) N); intro k; apply cont_theta_term.
Qed.

(* --- ψ equals the bare series limit (θ = 1 + 2·Σ) --- *)

Lemma Psi_eq_proj : forall t (Ht : 0 < t),
  Psi t = proj1_sig (theta_half_converges t Ht).
Proof. intros t Ht; rewrite (Psi_val t Ht); unfold theta; field. Qed.

(* --- uniform termwise domination on [a,∞) --- *)

Lemma theta_term_dom : forall a y k, 0 < a -> a <= y ->
  Rabs (theta_term y k) <= exp (- (PI * a)) * exp (- (PI * a)) ^ k.
Proof.
  intros a y k Ha Hay.
  rewrite Rabs_right by (apply Rle_ge; left; unfold theta_term; apply exp_pos).
  apply Rle_trans with (theta_term a k); [ apply theta_term_antitone; exact Hay | ].
  change (exp (- (PI * a)) * exp (- (PI * a)) ^ k) with (exp (- (PI * a)) ^ (S k)).
  apply theta_term_le'; exact Ha.
Qed.

(* --- continuity of ψ on (0,∞) via the M-test / CVU --- *)

Theorem Psi_cont : forall t0, 0 < t0 -> continuity_pt Psi t0.
Proof.
  intros t0 Ht0.
  set (a := t0 / 2).
  assert (Ha : 0 < a) by (unfold a; lra).
  set (r := t0 / 2).
  assert (Hr : 0 < r) by (unfold r; lra).
  set (q := exp (- (PI * a))).
  assert (Hqpos : 0 < q) by (unfold q; apply exp_pos).
  assert (Hq0 : 0 <= q) by lra.
  assert (Hq1 : q < 1) by (unfold q; apply theta_ratio_lt1; exact Ha).
  set (K := q / (1 - q)).
  assert (HK : 0 < K) by (unfold K; apply Rdiv_lt_0_compat; lra).
  assert (Hcvu : CVU (fun N y => theta_partial y N) Psi t0 (mkposreal r Hr)).
  { intros eps Heps.
    destruct (pow_lt_1_zero q ltac:(rewrite Rabs_right; [ exact Hq1 | apply Rle_ge; exact Hq0 ])
                (eps / K) ltac:(apply Rdiv_lt_0_compat; [ exact Heps | exact HK ])) as [N0 HN0].
    exists N0; intros n y Hn Hy.
    assert (Hay : a <= y).
    { unfold Boule in Hy; simpl in Hy; apply Rabs_def2 in Hy; unfold a, r in *; lra. }
    assert (Hy0 : 0 < y) by lra.
    rewrite (Psi_eq_proj y Hy0).
    destruct (theta_half_converges y Hy0) as [L HL]; simpl.
    eapply Rle_lt_trans.
    - apply (geom_tail_est (theta_term y) L q q Hq0 Hq1 Hq0 HL
               (fun k => theta_term_dom a y k Ha Hay) n).
    - assert (Hbnd : q * q ^ (S n) / (1 - q) = K * q ^ (S n)) by (unfold K; field; lra).
      rewrite Hbnd.
      assert (Hqn : q ^ (S n) < eps / K).
      { specialize (HN0 (S n) ltac:(lia)); rewrite Rabs_right in HN0 by
          (apply Rle_ge; apply pow_le; exact Hq0); exact HN0. }
      replace eps with (K * (eps / K)) by (field; apply Rgt_not_eq; exact HK).
      apply Rmult_lt_compat_l; [ exact HK | exact Hqn ]. }
  apply (CVU_continuity (fun N y => theta_partial y N) Psi t0 (mkposreal r Hr) Hcvu
           (fun n y _ => cont_theta_partial n y) t0).
  unfold Boule; simpl; replace (t0 - t0) with 0 by ring; rewrite Rabs_R0; exact Hr.
Qed.

(* --- the reciprocal composition, continuous on (0,∞) --- *)

Theorem Psi_recip_cont : forall u, 0 < u -> continuity_pt (fun u => Psi (/ u)) u.
Proof.
  intros u Hu.
  apply (continuity_pt_comp (fun u => / u) Psi u).
  - apply (continuity_pt_inv (fun u => u) u);
      [ apply derivable_continuous_pt; exists 1; apply derivable_pt_lim_id | simpl; lra ].
  - apply Psi_cont; apply Rinv_0_lt_compat; exact Hu.
Qed.

Print Assumptions Psi_cont.

(* ================================================================= *)
(*  END RiemannPsiCont.v                                             *)
(*  ψ continuous on (0,∞); u ↦ ψ(1/u) continuous on (0,∞).           *)
(* ================================================================= *)
