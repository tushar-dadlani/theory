(* ================================================================= *)
(*  EulerMascheroni.v                                                 *)
(*                                                                    *)
(*  THE EULER-MASCHERONI CONSTANT gamma, CONSTRUCTED AS A LIMIT.      *)
(*                                                                    *)
(*     gamma := lim_{N->oo} ( H_N - ln N ),   H_N = sum_{m<=N} 1/m.    *)
(*                                                                    *)
(*  The sequence g_N = H_N - ln N is decreasing (per-step MVT bracket  *)
(*  1/(n+1) <= ln(n+1)-ln n) and bounded below by 0 (H_N >= ln N),     *)
(*  so it converges by monotone convergence (growing_cv on -g).       *)
(*                                                                    *)
(*  We then define  egamma := exp gamma  and prove  1 <= egamma <= e.  *)
(*  This DISCHARGES the abstract `egamma` parameter used to state the  *)
(*  Nicolas criterion (see NicolasCriterion.v): the constant in        *)
(*  RH <-> N/phi(N) > e^gamma * ln ln N is now a constructed real.     *)
(*                                                                    *)
(*  Reuses HarmonicSum.v (Harm, harm_step, Harm_bracket) -- itself     *)
(*  axiom-clean (MVT-based).  The only axioms are the standard         *)
(*  classical-Reals ones inherent to Coq's R.                          *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia Arith List.
Require Import HarmonicSum.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  The sequence g_N = H_N - ln N and its monotonicity / bounds       *)
(* ----------------------------------------------------------------- *)

Definition gseq (N : nat) : R := Harm N - ln (INR N).

Lemma gseq_decr : forall n, (1 <= n)%nat -> gseq (S n) <= gseq n.
Proof.
  intros n Hn. unfold gseq. rewrite Harm_rec.
  pose proof (harm_step n Hn) as [Hlo _]. lra.
Qed.

Lemma gseq_nonneg : forall n, (1 <= n)%nat -> 0 <= gseq n.
Proof.
  intros n Hn. unfold gseq. pose proof (Harm_bracket n Hn) as [Hlo _]. lra.
Qed.

Lemma gseq_1 : gseq 1 = 1.
Proof.
  unfold gseq. rewrite INR_1, ln_1.
  rewrite (Harm_rec 0).
  assert (H0 : Harm 0 = 0) by reflexivity.
  rewrite H0, INR_1, Rinv_1. ring.
Qed.

(* ----------------------------------------------------------------- *)
(*  A small limit-vs-upper-bound helper                              *)
(* ----------------------------------------------------------------- *)

Lemma cv_le_ub : forall u l M,
  Un_cv u l -> (forall n, u n <= M) -> l <= M.
Proof.
  intros u l M Hcv Hub. destruct (Rle_or_lt l M) as [Hle | Hlt]; [ exact Hle | ].
  exfalso. destruct (Hcv ((l - M) / 2) ltac:(lra)) as [N HN].
  specialize (HN N (Nat.le_refl N)). specialize (Hub N).
  unfold R_dist in HN. apply Rabs_def2 in HN. lra.
Qed.

(* ----------------------------------------------------------------- *)
(*  Monotone convergence: gamma := lim (H_N - ln N)                  *)
(* ----------------------------------------------------------------- *)

Definition Vn (n : nat) : R := - gseq (S n).

Lemma Vn_growing : Un_growing Vn.
Proof.
  intro n. unfold Vn. pose proof (gseq_decr (S n) ltac:(lia)) as H. lra.
Qed.

Lemma Vn_ub : has_ub Vn.
Proof.
  exists 0. intros x [i ->]. unfold Vn.
  pose proof (gseq_nonneg (S i) ltac:(lia)) as H. lra.
Qed.

Definition gamma : R := - proj1_sig (growing_cv Vn Vn_growing Vn_ub).

Lemma gamma_limit : Un_cv Vn (- gamma).
Proof.
  unfold gamma. rewrite Ropp_involutive.
  exact (proj2_sig (growing_cv Vn Vn_growing Vn_ub)).
Qed.

(* gamma really is the limit of H_N - ln N (the shifted sequence).    *)
Lemma gamma_is_limit : Un_cv (fun n => gseq (S n)) gamma.
Proof.
  assert (Hopp : Un_cv (fun n => - Vn n) (- - gamma))
    by (apply CV_opp; exact gamma_limit).
  rewrite Ropp_involutive in Hopp.
  eapply Un_cv_ext; [ | exact Hopp ].
  intro n. unfold Vn. rewrite Ropp_involutive. reflexivity.
Qed.

(* ----------------------------------------------------------------- *)
(*  Bounds:  0 <= gamma <= 1                                          *)
(* ----------------------------------------------------------------- *)

Lemma gamma_nonneg : 0 <= gamma.
Proof.
  assert (Hl : - gamma <= 0).
  { apply (cv_le_ub Vn (- gamma) 0 gamma_limit).
    intro n. unfold Vn. pose proof (gseq_nonneg (S n) ltac:(lia)) as H. lra. }
  lra.
Qed.

Lemma gamma_le_1 : gamma <= 1.
Proof.
  pose proof (growing_ineq Vn (- gamma) Vn_growing gamma_limit 0%nat) as H.
  unfold Vn in H. cbv beta in H.
  change (gseq (S 0)) with (gseq 1) in H. rewrite gseq_1 in H. lra.
Qed.

(* ----------------------------------------------------------------- *)
(*  egamma := exp gamma, and  1 <= egamma <= e                        *)
(* ----------------------------------------------------------------- *)

Lemma exp_le_mono : forall x y, x <= y -> exp x <= exp y.
Proof.
  intros x y [H | H]; [ left; apply exp_increasing; exact H | right; rewrite H; reflexivity ].
Qed.

Definition egamma : R := exp gamma.

Lemma egamma_ge_1 : 1 <= egamma.
Proof. unfold egamma. rewrite <- exp_0. apply exp_le_mono, gamma_nonneg. Qed.

Lemma egamma_le_e : egamma <= exp 1.
Proof. unfold egamma. apply exp_le_mono, gamma_le_1. Qed.

Lemma egamma_pos : 0 < egamma.
Proof. unfold egamma. apply exp_pos. Qed.

Print Assumptions gamma.
Print Assumptions egamma_ge_1.
