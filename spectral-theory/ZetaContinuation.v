(* ================================================================= *)
(*  ZetaContinuation.v                                              *)
(*                                                                    *)
(*  ANALYTIC CONTINUATION of ζ to Re(s) > 0 (real axis), via         *)
(*  EULER–MACLAURIN / Abel summation — the honest analytic successor  *)
(*  to `HagedornTransition` (the pole at s=1 is the b_c=1 divergence).*)
(*                                                                    *)
(*  Writing the closed-form unit-interval integral                    *)
(*    ∫_n^{n+1} x^(−s) dx = ((n+1)^(1−s) − n^(1−s))/(1−s),            *)
(*  the term  gterm s n = (n+1)^(−s) − ∫_{n+1}^{n+2} x^(−s) dx       *)
(*  gives the Euler–Maclaurin partial identity (`zeta_EM_identity`)   *)
(*    Zpart s N = Σ_{n≤N} gterm s n + ((N+2)^(1−s) − 1)/(1−s).        *)
(*  The series Σ gterm s converges for ALL s>0 (`gterm_cv`, via a     *)
(*  MVT per-term bound 0 ≤ gterm s n ≤ (n+1)^(−s) − (n+2)^(−s) and    *)
(*  a telescoping majorant), so                                       *)
(*    ζ̃(s) := 1/(s−1) + Σ_{n≥0} gterm s n                            *)
(*  is defined on (0,∞)∖{1}, and for s>1 it EQUALS the Dirichlet      *)
(*  value ζ(s) = Σ n^(−s)  (`zeta_analytic_continuation`).            *)
(*                                                                    *)
(*  This is the real-variable Euler–Maclaurin formula — the exact     *)
(*  expression whose ℂ-version is the analytic continuation.  It does *)
(*  NOT prove holomorphy (that needs the complex-analysis / contour   *)
(*  layer this stdlib-only repo does not build).  Over the classical  *)
(*  `Reals` (quarantined).                                            *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia Arith.
Require Import HagedornTransition.
Local Open Scope R_scope.

(* derivative of x^c *)
Lemma Rpower_deriv : forall c x, 0 < x -> derivable_pt_lim (fun y => Rpower y c) x (c * Rpower x (c - 1)).
Proof.
  intros c x Hx.
  assert (Hln : derivable_pt_lim (fun y => c * ln y) x (c * / x))
    by (apply derivable_pt_lim_scal, derivable_pt_lim_ln; exact Hx).
  pose proof (derivable_pt_lim_comp (fun y => c * ln y) exp x (c * / x) (exp (c * ln x)) Hln
                (derivable_pt_lim_exp (c * ln x))) as H.
  unfold Rpower.
  replace (c * exp ((c - 1) * ln x)) with (exp (c * ln x) * (c * / x)); [ exact H | ].
  replace (/ x) with (exp (- ln x)) by (rewrite exp_Ropp, exp_ln by exact Hx; reflexivity).
  rewrite <- Rmult_assoc, (Rmult_comm (exp (c * ln x)) c), Rmult_assoc, <- exp_plus.
  replace (c * ln x + - ln x) with ((c - 1) * ln x) by ring. reflexivity.
Qed.

Definition gterm (s : R) (n : nat) : R :=
  Rpower (INR (S n)) (- s)
  - (Rpower (INR (S (S n))) (1 - s) - Rpower (INR (S n)) (1 - s)) / (1 - s).

(* MVT: the "integral" (n+1)^{1-s}-n^{1-s})/(1-s) = xi^{-s} for some xi in (n+1,n+2) *)
Lemma g_middle : forall s n, s <> 1 ->
  exists xi, INR (S n) < xi < INR (S (S n)) /\
    (Rpower (INR (S (S n))) (1 - s) - Rpower (INR (S n)) (1 - s)) / (1 - s) = Rpower xi (- s).
Proof.
  intros s n Hs.
  destruct (MVT_cor2 (fun y => Rpower y (1 - s)) (fun y => (1 - s) * Rpower y (- s))
             (INR (S n)) (INR (S (S n)))) as [xi [Hxi Hrange]].
  - apply lt_INR; lia.
  - intros c Hc. assert (0 < c) by (apply Rlt_le_trans with (INR (S n)); [ apply lt_0_INR; lia | lra ]).
    replace (- s) with (1 - s - 1) by ring. apply Rpower_deriv; assumption.
  - exists xi; split; [ exact Hrange | ].
    replace (INR (S (S n)) - INR (S n)) with 1 in Hxi by (rewrite (S_INR (S n)); ring).
    rewrite Rmult_1_r in Hxi. rewrite Hxi. field. lra.
Qed.

Lemma g_bound : forall s n, 0 < s -> s <> 1 ->
  0 <= gterm s n <= Rpower (INR (S n)) (- s) - Rpower (INR (S (S n))) (- s).
Proof.
  intros s n Hs0 Hs1. destruct (g_middle s n Hs1) as [xi [[Ha Hb] Hmid]].
  unfold gterm. rewrite Hmid.
  assert (Hxipos : 0 < xi) by (apply Rlt_trans with (INR (S n)); [ apply lt_0_INR; lia | exact Ha ]).
  assert (H1 : Rpower xi (- s) <= Rpower (INR (S n)) (- s))
    by (apply Rpower_negexp_antimono; [ apply lt_0_INR; lia | lra | lra ]).
  assert (H2 : Rpower (INR (S (S n))) (- s) <= Rpower xi (- s))
    by (apply Rpower_negexp_antimono; [ exact Hxipos | lra | lra ]).
  lra.
Qed.

Lemma Rpower_base1 : forall y, Rpower 1 y = 1.
Proof. intro y; unfold Rpower; rewrite ln_1, Rmult_0_r, exp_0; reflexivity. Qed.

Lemma Zpart_tech5 : forall s N, Zpart s (S N) = Zpart s N + Rpower (INR (S (S N))) (- s).
Proof. intros s N; unfold Zpart; rewrite tech5; reflexivity. Qed.

Lemma zeta_EM_identity : forall s N, s <> 1 ->
  Zpart s N = sum_f_R0 (gterm s) N + (Rpower (INR (S (S N))) (1 - s) - 1) / (1 - s).
Proof.
  intros s N Hs. assert (H1s : 1 - s <> 0) by (intro Hc; apply Hs; lra).
  induction N as [|N IH].
  - unfold gterm, Zpart; cbn [sum_f_R0]; rewrite INR_1; repeat rewrite Rpower_base1.
    field; exact H1s.
  - rewrite Zpart_tech5, IH, tech5; unfold gterm; field; exact H1s.
Qed.

Lemma sum_telescope_dec : forall (a : nat -> R) N,
  sum_f_R0 (fun n => a n - a (S n)) N = a 0%nat - a (S N).
Proof.
  intros a N; induction N as [|N IH]; [ cbn [sum_f_R0]; reflexivity | ].
  rewrite tech5, IH; ring.
Qed.

Lemma gterm_cv : forall s, 0 < s -> s <> 1 -> { L : R | Un_cv (sum_f_R0 (gterm s)) L }.
Proof.
  intros s Hs0 Hs1; apply growing_cv.
  - intro N; rewrite tech5; destruct (g_bound s (S N) Hs0 Hs1) as [Hge _]; lra.
  - unfold has_ub, bound, is_upper_bound, EUn.
    exists 1. intros x [N Hx]; rewrite Hx.
    apply Rle_trans with (sum_f_R0 (fun n => Rpower (INR (S n)) (- s) - Rpower (INR (S (S n))) (- s)) N).
    + apply sum_Rle; intros k Hk; destruct (g_bound s k Hs0 Hs1) as [_ Hle]; exact Hle.
    + rewrite (sum_telescope_dec (fun n => Rpower (INR (S n)) (- s))).
      rewrite INR_1, Rpower_base1.
      assert (0 <= Rpower (INR (S (S N))) (- s)) by (left; apply Rpower_pos); lra.
Qed.

Lemma Un_cv_ext : forall u v L, (forall n, u n = v n) -> Un_cv u L -> Un_cv v L.
Proof. intros u v L He Hu eps Heps; destruct (Hu eps Heps) as [N HN]; exists N; intros n Hn; rewrite <- He; apply HN; exact Hn. Qed.

Lemma Un_cv_S : forall u L, Un_cv u L -> Un_cv (fun n => u (S n)) L.
Proof. intros u L Hu eps Heps; destruct (Hu eps Heps) as [N HN]; exists N; intros n Hn; apply HN; lia. Qed.

Lemma Un_cv_const : forall c : R, Un_cv (fun _ => c) c.
Proof. intros c eps He; exists 0%nat; intros n _; unfold R_dist; rewrite Rminus_diag, Rabs_R0; exact He. Qed.

Lemma Rpower_neg_cv0 : forall c, c < 0 -> Un_cv (fun n => Rpower (INR (S n)) c) 0.
Proof.
  intros c Hc eps Heps.
  destruct (INR_unbounded (exp (ln eps / c))) as [N HN].
  exists N; intros n Hn.
  unfold R_dist; rewrite Rminus_0_r, Rabs_right by (left; apply Rpower_pos).
  unfold Rpower; rewrite <- (exp_ln eps Heps); apply exp_increasing.
  assert (Hbig : exp (ln eps / c) < INR (S n))
    by (apply Rlt_le_trans with (INR N); [ exact HN | apply le_INR; lia ]).
  assert (HL : ln eps / c < ln (INR (S n)))
    by (rewrite <- (ln_exp (ln eps / c)); apply ln_increasing; [ apply exp_pos | exact Hbig ]).
  pose proof (Rmult_lt_gt_compat_neg_l c (ln eps / c) (ln (INR (S n))) Hc HL) as H.
  replace (c * (ln eps / c)) with (ln eps) in H by (field; lra). lra.
Qed.

Lemma zeta_continuation_extends : forall s Z, 1 < s -> Un_cv (Zpart s) Z ->
  Un_cv (fun N => / (s - 1) + sum_f_R0 (gterm s) N) Z.
Proof.
  intros s Z Hs HZ.
  assert (Hs1 : s <> 1) by lra.
  assert (Hsm : s - 1 <> 0) by (apply Rgt_not_eq; lra).
  assert (H1s : 1 - s <> 0) by (apply Rlt_not_eq; lra).
  apply (Un_cv_ext (fun N => Zpart s N + Rpower (INR (S (S N))) (1 - s) * / (s - 1))).
  - intro N; rewrite (zeta_EM_identity s N Hs1); field; split; assumption.
  - replace Z with (Z + 0) by ring; apply CV_plus; [ exact HZ | ].
    replace 0 with (0 * / (s - 1)) by ring; apply CV_mult; [ | apply Un_cv_const ].
    apply (Un_cv_S (fun n => Rpower (INR (S n)) (1 - s))); apply Rpower_neg_cv0; lra.
Qed.

Theorem zeta_analytic_continuation :
  forall s, 0 < s -> s <> 1 ->
  exists Z : R,
    Un_cv (fun N => / (s - 1) + sum_f_R0 (gterm s) N) Z /\
    (1 < s -> Un_cv (Zpart s) Z).
Proof.
  intros s Hs0 Hs1. destruct (gterm_cv s Hs0 Hs1) as [L HL].
  assert (Hval : Un_cv (fun N => / (s - 1) + sum_f_R0 (gterm s) N) (/ (s - 1) + L))
    by (apply CV_plus; [ apply Un_cv_const | exact HL ]).
  exists (/ (s - 1) + L); split; [ exact Hval | ].
  intro Hs. destruct (Zpart_cv s Hs) as [Z' HZ'].
  assert (Hext : Un_cv (fun N => / (s - 1) + sum_f_R0 (gterm s) N) Z')
    by (apply zeta_continuation_extends; [ exact Hs | exact HZ' ]).
  assert (Heq : / (s - 1) + L = Z')
    by (apply (UL_sequence (fun N => / (s - 1) + sum_f_R0 (gterm s) N)); [ exact Hval | exact Hext ]).
  rewrite Heq; exact HZ'.
Qed.

Print Assumptions zeta_analytic_continuation.

(* ================================================================= *)
(*  END ZetaContinuation.v.  ζ continued to (0,∞)∖{1} on the real     *)
(*  axis via Euler–Maclaurin, agreeing with Σ n^(−s) for s>1.         *)
(* ================================================================= *)
