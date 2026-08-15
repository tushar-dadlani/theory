(* ================================================================= *)
(*  Ell2VMPartition.v   (the von Mangoldt spectral trace is -zeta'/zeta) *)
(*                                                                    *)
(*  Companion to Ell2Partition.  With the same heat semigroup           *)
(*  e^{-bH} = diag(n^{-b}) (H = diag(log n)), the "prime-energy"         *)
(*  observable D_Lam = diag(Lam n) has spectral trace                   *)
(*                                                                    *)
(*     Tr_N(D_Lam e^{-bH}) = sum_{n=1}^N Lam(n) n^{-b}                  *)
(*                        ---> -zeta'/zeta(b)      (converges for b>1)   *)
(*                                                                    *)
(*  Convergence for b>1 comes from the log-weighted majorant             *)
(*  CVonMangoldtSeries.blam_sum_cv  (Lam n <= ln n, Lam_le_ln).          *)
(*                                                                    *)
(*  Axioms: standard classical-Reals only.                            *)
(* ================================================================= *)

From Stdlib Require Import Reals Rpower Lra Lia List.
Require Import ComplexField Ell2 Ell2Operator Ell2Zeta VonMangoldtGlobal Chebyshev
        CVonMangoldtSeries Ell2ZetaConverge Ell2Partition.
Open Scope R_scope.

Lemma dvmzeta_succ : forall b N, dvmzeta b (S N) = dvmzeta b N + Lam (S N) * z b (S N).
Proof.
  intros b N; unfold dvmzeta.
  rewrite seq_S, map_app, fold_Rplus_app; simpl.
  replace (1 + N)%nat with (S N) by lia; ring.
Qed.

Lemma ln_INR_Sn_nonneg : forall n, 0 <= ln (INR (S n)).
Proof.
  intro n. assert (H1 : 1 <= INR (S n)) by (rewrite <- INR_1; apply le_INR; lia).
  rewrite <- ln_1. destruct (Rle_lt_or_eq_dec 1 (INR (S n)) H1) as [Hlt | Heq].
  - left; apply ln_increasing; lra.
  - rewrite <- Heq; apply Rle_refl.
Qed.

Lemma blam_nonneg : forall b n, 0 <= blam (RtoC b) n.
Proof.
  intros b n. unfold blam. apply Rmult_le_pos.
  - apply ln_INR_Sn_nonneg.
  - left; unfold Rpower; apply exp_pos.
Qed.

Lemma blam_growing : forall b, Un_growing (sum_f_R0 (blam (RtoC b))).
Proof.
  intros b N. rewrite tech5. pose proof (blam_nonneg b (S N)); lra.
Qed.

(* the vM spectral trace is dominated by the log-weighted p-series *)
Lemma dvm_le_blam : forall b N, dvmzeta b (S N) <= sum_f_R0 (blam (RtoC b)) N.
Proof.
  intros b N. induction N as [| N IH].
  - rewrite dvmzeta_succ. replace (dvmzeta b 0) with 0 by reflexivity.
    rewrite Rplus_0_l, Lam_1, Rmult_0_l. cbn [sum_f_R0].
    unfold blam. replace (INR (S 0)) with 1 by (simpl; ring).
    rewrite ln_1, Rmult_0_l. apply Rle_refl.
  - rewrite dvmzeta_succ, tech5. apply Rplus_le_compat; [ exact IH | ].
    assert (Hz : z b (S (S N)) = Rpower (INR (S (S N))) (- b)) by (unfold z; reflexivity).
    rewrite Hz. unfold blam. cbn [Re RtoC].
    apply Rmult_le_compat_r; [ left; unfold Rpower; apply exp_pos | apply Lam_le_ln; lia ].
Qed.

(* ------------------------------------------------------------------ *)
(*  the bundled statement:  Tr(D_Lam e^{-bH}) converges (to -zeta'/zeta) *)
(* ------------------------------------------------------------------ *)

Theorem vm_partition_converges : forall b, 1 < b ->
  { W : R |
    Un_cv (fun N => diag_trace (fun n => Lam n * z b n) N) W /\
    (forall N, diag_trace (fun n => Lam n * z b n) N
               = diag_trace (fun n => Lam n * exp ((- b) * Hlog n)) N) }.
Proof.
  intros b Hb.
  assert (HbC : 1 < Re (RtoC b)) by (cbn [Re RtoC]; exact Hb).
  destruct (blam_sum_cv (RtoC b) HbC) as [T HT].
  assert (Hb0 : 0 <= b) by lra.
  assert (Hgrow : Un_growing (dvmzeta b)).
  { intro N. rewrite dvmzeta_succ.
    assert (0 <= Lam (S N) * z b (S N))
      by (apply Rmult_le_pos; [ apply Lam_nonneg | apply (z_bounds b (S N) Hb0) ]). lra. }
  assert (HT0 : 0 <= T).
  { apply Rle_trans with (sum_f_R0 (blam (RtoC b)) 0);
      [ cbn [sum_f_R0]; apply blam_nonneg
      | apply (growing_ineq (sum_f_R0 (blam (RtoC b))) T (blam_growing b) HT) ]. }
  assert (Hub : has_ub (dvmzeta b)).
  { exists T. intros v [N ->]. destruct N as [| M].
    - replace (dvmzeta b 0) with 0 by reflexivity. exact HT0.
    - apply Rle_trans with (sum_f_R0 (blam (RtoC b)) M);
        [ apply dvm_le_blam
        | apply (growing_ineq (sum_f_R0 (blam (RtoC b))) T (blam_growing b) HT) ]. }
  destruct (growing_cv (dvmzeta b) Hgrow Hub) as [W HW]. exists W. split.
  - apply (Un_cv_ext' (dvmzeta b));
      [ intro N; symmetry; apply vonmangoldt_zeta_trace | exact HW ].
  - intro N. rewrite !diag_trace_eq. f_equal. apply map_ext_in.
    intros n Hn. apply in_seq in Hn. rewrite (zeta_is_exp_neg_sH b n) by lia. reflexivity.
Qed.

Print Assumptions vm_partition_converges.
