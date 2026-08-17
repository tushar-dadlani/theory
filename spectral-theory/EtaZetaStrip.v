(* ================================================================= *)
(*  EtaZetaStrip.v  —  eta(s) = (1 - 2^{1-s}) zeta(s) INTO THE STRIP 0<s<1. *)
(*                                                                    *)
(*  EtaZeta.eta_zeta_cont proved the identity only for real s>1 (where the *)
(*  zeta SERIES converges).  Here it is extended to ALL 0<s, s<>1 -- in     *)
(*  particular the critical strip 0<s<1, where the zeta series DIVERGES.    *)
(*                                                                    *)
(*    eta_zeta_cont_strip : forall s (Hs0:0<s)(Hs1:s<>1),                   *)
(*      Un_cv (eta_partial s) ((1 - 2^{1-s}) * zeta_cont s Hs0 Hs1).        *)
(*                                                                    *)
(*  Method (Euler-Maclaurin cancellation, NOT analytic continuation).       *)
(*  The algebraic identity eta_partial s M = Zpart(2M+1) - 2^{1-s} Zpart M  *)
(*  (EtaZeta.eta_partial_id, valid for ALL s) is combined with the exact    *)
(*  regularization Zpart s N = sum gterm + ((N+2)^{1-s}-1)/(1-s)            *)
(*  (ZetaContinuation.zeta_EM_identity).  The DIVERGENT (N+2)^{1-s}/(1-s)   *)
(*  parts cancel exactly because 2M+2 = 2(M+1): the leftover is the         *)
(*  consecutive difference  (2M+3)^{1-s} - (2M+4)^{1-s} = -int_diff,        *)
(*  which -> 0 for every s>0 (consec_Rpow_diff_cv0, bounded via g_bound     *)
(*  by |1-s|.(2M+3)^{-s} -> 0).  The convergent gterm part gives            *)
(*  (1-2^{1-s})(zeta_cont - 1/(s-1)) and the constants reassemble to        *)
(*  (1-2^{1-s}) zeta_cont.  Valid uniformly for s>1 too (there both terms   *)
(*  vanish separately), so this subsumes eta_zeta_cont.                     *)
(*                                                                    *)
(*  Consequence: the ZeroAsLimit collapse argument now reaches the strip    *)
(*  where the NONTRIVIAL zeros live -- a zeta zero at 0<s<1 is exactly the   *)
(*  alternating sum collapsing to 0 at infinity (no 1<s gate).             *)
(*                                                                    *)
(*  Axioms: standard classical-Reals only.                            *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import Ell2Zeta EtaZeta ZeroAsLimit HagedornTransition ZetaContinuation Ell2ZetaCont
        CountTwoCollapse BaselZeta.
Open Scope R_scope.

Lemma zp_eq_zpart : forall s N, sum_f_R0 (fun i => z s (S i)) N = Zpart s N.
Proof.
  intros s N. unfold Zpart. apply sum_eq. intros i _. unfold z. simpl. reflexivity.
Qed.

(* the integral-comparison term difference, and its bound from g_bound *)
Definition int_diff (s : R) (n : nat) : R :=
  Rpower (INR (S (S n))) (1 - s) - Rpower (INR (S n)) (1 - s).

Lemma int_diff_bound : forall s n, 0 < s -> s <> 1 ->
  Rabs (int_diff s n) <= Rabs (1 - s) * Rpower (INR (S n)) (- s).
Proof.
  intros s n Hs0 Hs1.
  assert (Hq : gterm s n = Rpower (INR (S n)) (- s) - int_diff s n / (1 - s))
    by (unfold gterm, int_diff; reflexivity).
  pose proof (g_bound s n Hs0 Hs1) as [Hlo Hhi].
  set (q := int_diff s n / (1 - s)) in *.
  (* from Hq + g_bound: 0 <= q <= Rpower (INR (S n)) (- s) *)
  assert (Hq_hi : q <= Rpower (INR (S n)) (- s)) by lra.
  assert (Hq_lo : 0 <= q).
  { assert (0 <= Rpower (INR (S (S n))) (- s)) by (left; apply exp_pos).
    lra. }
  (* int_diff s n = (1 - s) * q *)
  assert (Hid : int_diff s n = (1 - s) * q)
    by (unfold q; field; lra).
  rewrite Hid, Rabs_mult, (Rabs_right q) by lra.
  apply Rmult_le_compat_l; [ apply Rabs_pos | exact Hq_hi ].
Qed.

Lemma consec_Rpow_diff_cv0 : forall s, 0 < s -> s <> 1 ->
  Un_cv (fun n => int_diff s n) 0.
Proof.
  intros s Hs0 Hs1.
  apply (Un_cv_maj_0 (fun n => int_diff s n)
                     (fun n => Rabs (1 - s) * Rpower (INR (S n)) (- s))).
  - intro n. apply int_diff_bound; assumption.
  - apply Un_cv_scal_0. apply Rpower_neg_cv0. lra.
Qed.


Lemma eta_partial_decomp : forall s (Hs1 : s <> 1) M,
  eta_partial s M
  = (sum_f_R0 (gterm s) (2 * M + 1) - 2 * z s 2 * sum_f_R0 (gterm s) M)
    + (- int_diff s (2 * M + 2) + (2 * z s 2 - 1)) / (1 - s).
Proof.
  intros s Hs1 M. unfold eta_partial.
  rewrite eta_partial_id, !zp_eq_zpart.
  rewrite (zeta_EM_identity s (2 * M + 1) Hs1), (zeta_EM_identity s M Hs1).
  assert (Ha : Rpower (INR (S (S (2 * M + 1)))) (1 - s)
             = Rpower (INR (S (2 * M + 2))) (1 - s)) by (f_equal; f_equal; lia).
  assert (Hb : 2 * z s 2 * Rpower (INR (S (S M))) (1 - s)
             = Rpower (INR (S (S (2 * M + 2)))) (1 - s)).
  { rewrite two_z2, Rpower_mult_distr by (try lra; apply lt_0_INR; lia).
    replace (2 * INR (S (S M))) with (INR (2 * S (S M)))
      by (rewrite mult_INR; replace (INR 2) with 2 by (simpl; ring); ring).
    f_equal. f_equal. lia. }
  unfold int_diff. rewrite Ha, <- Hb. field. lra.
Qed.

Lemma Un_cv_const_loc2 : forall c, Un_cv (fun _ => c) c.
Proof.
  intros c eps Heps. exists 0%nat. intros n _. unfold R_dist.
  replace (c - c) with 0 by ring. rewrite Rabs_R0. exact Heps.
Qed.

Theorem eta_zeta_cont_strip : forall s (Hs0 : 0 < s) (Hs1 : s <> 1),
  Un_cv (eta_partial s) ((1 - Rpower 2 (1 - s)) * zeta_cont s Hs0 Hs1).
Proof.
  intros s Hs0 Hs1.
  set (G := proj1_sig (gterm_cv s Hs0 Hs1)).
  assert (HG : Un_cv (sum_f_R0 (gterm s)) G) by exact (proj2_sig (gterm_cv s Hs0 Hs1)).
  replace ((1 - Rpower 2 (1 - s)) * zeta_cont s Hs0 Hs1)
    with ((G - 2 * z s 2 * G) + (0 + (2 * z s 2 - 1)) * / (1 - s)).
  2:{ unfold zeta_cont. rewrite <- two_z2. fold G. field. lra. }
  apply (Un_cv_ext (fun M =>
      (sum_f_R0 (gterm s) (2 * M + 1) - 2 * z s 2 * sum_f_R0 (gterm s) M)
      + (- int_diff s (2 * M + 2) + (2 * z s 2 - 1)) * / (1 - s))).
  - intro M. rewrite (eta_partial_decomp s Hs1 M). unfold Rdiv. reflexivity.
  - apply CV_plus.
    + apply CV_minus.
      * apply (Un_cv_subseq (sum_f_R0 (gterm s)) G (fun M => (2 * M + 1)%nat));
          [ intro M; lia | exact HG ].
      * apply (CV_mult (fun _ => 2 * z s 2) (sum_f_R0 (gterm s)) (2 * z s 2) G);
          [ apply Un_cv_const_loc2 | exact HG ].
    + apply (CV_mult (fun M => - int_diff s (2 * M + 2) + (2 * z s 2 - 1))
                     (fun _ => / (1 - s)) (0 + (2 * z s 2 - 1)) (/ (1 - s))).
      * apply CV_plus.
        -- apply (Un_cv_ext (fun M => (-1) * int_diff s (2 * M + 2))).
           ++ intro M. ring.
           ++ apply Un_cv_scal_0.
              apply (Un_cv_subseq (fun n => int_diff s n) 0 (fun M => (2 * M + 2)%nat));
                [ intro M; lia | apply consec_Rpow_diff_cv0; assumption ].
        -- apply Un_cv_const_loc2.
      * apply Un_cv_const_loc2.
Qed.

Print Assumptions eta_zeta_cont_strip.
