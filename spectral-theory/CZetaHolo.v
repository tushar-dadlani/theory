(* ================================================================= *)
(*  CZetaHolo.v  —  item 4: zetaC is holomorphic on the strip.         *)
(*                                                                    *)
(*  Part 1: the per-term second-order remainder bound.  Along the      *)
(*  segment s' = z + t*h, phi(t) = Re/Im(gtermC(z+t h,n)) is C^2 with   *)
(*    phi'(t)  = Re/Im(dgtermC(z+t h)·h)        (line-bridge o 2b.2),   *)
(*    phi''(t) = Re/Im(d2gtermC(z+t h)·h·h)     (line-bridge o 2b.2),   *)
(*  so order2_bound gives  |phi(1)-phi(0)-phi'(0)| <= B_n·|h|^2 for any  *)
(*  uniform bound B_n on Cmod(d2gtermC) over the segment.  Axiom-clean. *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia FunctionalExtensionality.
Require Import ComplexField Cmodulus CexpFull Holomorphic CexpRemainder
               CSeries CDeriv CDerivLine CBaseDeriv CBaseDeriv2
               CZetaTerm CZetaTerm2 CZetaDeriv2.
Open Scope R_scope.

(* derivative of  w |-> F w · c  (c constant) is  dF · c *)
Lemma Cderiv_mul_const_r : forall F z dF c,
  is_Cderiv F z dF -> is_Cderiv (fun w => Cmul (F w) c) z (Cmul dF c).
Proof.
  intros F z dF c HF.
  apply (is_Cderiv_eq _ _ (Cadd (Cmul dF c) (Cmul (F z) C0))).
  - apply Cderiv_mul; [ exact HF | apply Cderiv_const ].
  - ring.
Qed.

Section Remainder.
Variables (z h : C) (n : nat).
Hypothesis Hseg : forall t, 0 <= t <= 1 -> Cminus C1 (Cadd z (Cmul (RtoC t) h)) <> C0.

Lemma line_phi'_Re : forall t, 0 <= t <= 1 ->
  derivable_pt_lim (fun u => Re (gtermC (Cadd z (Cmul (RtoC u) h)) n)) t
    (Re (Cmul (dgtermC (Cadd z (Cmul (RtoC t) h)) n) h)).
Proof.
  intros t Ht.
  apply (is_Cderiv_line_Re (fun w => gtermC w n) z h).
  apply gtermC_sderiv; apply Hseg; exact Ht.
Qed.

Lemma line_phi''_Re : forall t, 0 <= t <= 1 ->
  derivable_pt_lim (fun u => Re (Cmul (dgtermC (Cadd z (Cmul (RtoC u) h)) n) h)) t
    (Re (Cmul (Cmul (d2gtermC (Cadd z (Cmul (RtoC t) h)) n) h) h)).
Proof.
  intros t Ht.
  apply (is_Cderiv_line_Re (fun w => Cmul (dgtermC w n) h) z h).
  apply Cderiv_mul_const_r; apply dgtermC_sderiv; apply Hseg; exact Ht.
Qed.

Lemma line_phi'_Im : forall t, 0 <= t <= 1 ->
  derivable_pt_lim (fun u => Im (gtermC (Cadd z (Cmul (RtoC u) h)) n)) t
    (Im (Cmul (dgtermC (Cadd z (Cmul (RtoC t) h)) n) h)).
Proof.
  intros t Ht.
  apply (is_Cderiv_line_Im (fun w => gtermC w n) z h).
  apply gtermC_sderiv; apply Hseg; exact Ht.
Qed.

Lemma line_phi''_Im : forall t, 0 <= t <= 1 ->
  derivable_pt_lim (fun u => Im (Cmul (dgtermC (Cadd z (Cmul (RtoC u) h)) n) h)) t
    (Im (Cmul (Cmul (d2gtermC (Cadd z (Cmul (RtoC t) h)) n) h) h)).
Proof.
  intros t Ht.
  apply (is_Cderiv_line_Im (fun w => Cmul (dgtermC w n) h) z h).
  apply Cderiv_mul_const_r; apply dgtermC_sderiv; apply Hseg; exact Ht.
Qed.

(* the second-order remainder along the segment, both components *)
Lemma remainder_Re : forall Bn, 0 <= Bn ->
  (forall t, 0 <= t <= 1 -> Cmod (d2gtermC (Cadd z (Cmul (RtoC t) h)) n) <= Bn) ->
  Rabs (Re (gtermC (Cadd z (Cmul (RtoC 1) h)) n)
        - Re (gtermC (Cadd z (Cmul (RtoC 0) h)) n)
        - Re (Cmul (dgtermC (Cadd z (Cmul (RtoC 0) h)) n) h))
    <= Bn * (Cmod h * Cmod h).
Proof.
  intros Bn HBn Hbd.
  apply (order2_bound
    (fun u => Re (gtermC (Cadd z (Cmul (RtoC u) h)) n))
    (fun t => Re (Cmul (dgtermC (Cadd z (Cmul (RtoC t) h)) n) h))
    (fun t => Re (Cmul (Cmul (d2gtermC (Cadd z (Cmul (RtoC t) h)) n) h) h))).
  - apply Rmult_le_pos; [ exact HBn | apply Rmult_le_pos; apply Cmod_nonneg ].
  - apply line_phi'_Re.
  - apply line_phi''_Re.
  - intros t Ht.
    eapply Rle_trans; [ apply Cmod_Re_le | ].
    rewrite !Cmod_mul.
    replace (Bn * (Cmod h * Cmod h)) with (Bn * Cmod h * Cmod h) by ring.
    apply Rmult_le_compat_r; [ apply Cmod_nonneg | ].
    apply Rmult_le_compat_r; [ apply Cmod_nonneg | ].
    apply Hbd; exact Ht.
Qed.

Lemma remainder_Im : forall Bn, 0 <= Bn ->
  (forall t, 0 <= t <= 1 -> Cmod (d2gtermC (Cadd z (Cmul (RtoC t) h)) n) <= Bn) ->
  Rabs (Im (gtermC (Cadd z (Cmul (RtoC 1) h)) n)
        - Im (gtermC (Cadd z (Cmul (RtoC 0) h)) n)
        - Im (Cmul (dgtermC (Cadd z (Cmul (RtoC 0) h)) n) h))
    <= Bn * (Cmod h * Cmod h).
Proof.
  intros Bn HBn Hbd.
  apply (order2_bound
    (fun u => Im (gtermC (Cadd z (Cmul (RtoC u) h)) n))
    (fun t => Im (Cmul (dgtermC (Cadd z (Cmul (RtoC t) h)) n) h))
    (fun t => Im (Cmul (Cmul (d2gtermC (Cadd z (Cmul (RtoC t) h)) n) h) h))).
  - apply Rmult_le_pos; [ exact HBn | apply Rmult_le_pos; apply Cmod_nonneg ].
  - apply line_phi'_Im.
  - apply line_phi''_Im.
  - intros t Ht.
    eapply Rle_trans; [ apply Cmod_Im_le | ].
    rewrite !Cmod_mul.
    replace (Bn * (Cmod h * Cmod h)) with (Bn * Cmod h * Cmod h) by ring.
    apply Rmult_le_compat_r; [ apply Cmod_nonneg | ].
    apply Rmult_le_compat_r; [ apply Cmod_nonneg | ].
    apply Hbd; exact Ht.
Qed.

End Remainder.

Print Assumptions remainder_Re.

(* ================================================================= *)
(*  Part 2: the uniform (ln)^2-weighted p-series with free parameters. *)
(* ================================================================= *)

(* generalizes d2bound_sum_cv to an arbitrary exponent q>0 and
   coefficient M>=0 (needed for the segment-uniform bound). *)
Lemma weighted_pseries_cv : forall q M, 0 < q -> 0 <= M ->
  { T | Un_cv (sum_f_R0 (fun n =>
    (2 * ln (INR (S (S n))) + ln (INR (S (S n))) * ln (INR (S (S n))) * M)
    * Rpower (INR (S n)) (- q - 1))) T }.
Proof.
  intros q M Hq HM.
  set (c := q / 2).
  assert (Hc : 0 <= c) by (unfold c; lra).
  destruct (lnpow_pseries_cv c (q + 1) Hc ltac:(unfold c; lra)) as [T' HT'].
  set (term := fun n => Rpower (INR (S (S n))) c * Rpower (INR (S n)) (- (q + 1))).
  set (K := 4 / q + M * (4 / q) * (4 / q)).
  assert (HK : 0 <= K) by (unfold K;
    apply Rplus_le_le_0_compat; [ | apply Rmult_le_pos; [ apply Rmult_le_pos | ] ];
    try assumption; apply Rlt_le; apply Rdiv_lt_0_compat; lra).
  set (d2 := fun n =>
    (2 * ln (INR (S (S n))) + ln (INR (S (S n))) * ln (INR (S (S n))) * M)
    * Rpower (INR (S n)) (- q - 1)).
  assert (Hd0 : forall n, 0 <= d2 n).
  { intro n; unfold d2.
    assert (Hb1 : 1 <= INR (S (S n))) by (rewrite <- INR_1; apply le_INR; lia).
    assert (0 <= ln (INR (S (S n)))) by (rewrite <- ln_1; apply ln_le'; lra).
    apply Rmult_le_pos; [ | apply Rlt_le; unfold Rpower; apply exp_pos ].
    apply Rplus_le_le_0_compat; [ apply Rmult_le_pos; lra
      | apply Rmult_le_pos; [ apply Rmult_le_pos; assumption | assumption ] ]. }
  assert (Hbound : forall n, d2 n <= K * term n).
  { intro n; unfold d2, term.
    set (b := INR (S (S n))).
    assert (Hb1 : 1 <= b) by (unfold b; rewrite <- INR_1; apply le_INR; lia).
    assert (Hlnb0 : 0 <= ln b) by (rewrite <- ln_1; apply ln_le'; lra).
    assert (Hlin : ln b <= 2 / q * Rpower b c).
    { replace (2 / q) with (/ c) by (unfold c; field; lra).
      apply ln_le_rpow; [ unfold c; lra | exact Hb1 ]. }
    assert (Hsq : ln b * ln b <= (4 / q) * (4 / q) * Rpower b c).
    { assert (Hqq : ln b <= 4 / q * Rpower b (q / 4)).
      { replace (4 / q) with (/ (q / 4)) by (field; lra).
        apply ln_le_rpow; [ lra | exact Hb1 ]. }
      apply Rle_trans with ((4 / q * Rpower b (q / 4)) * (4 / q * Rpower b (q / 4))).
      - apply Rmult_le_compat; assumption.
      - replace ((4 / q * Rpower b (q / 4)) * (4 / q * Rpower b (q / 4)))
          with ((4 / q) * (4 / q) * (Rpower b (q / 4) * Rpower b (q / 4))) by ring.
        rewrite <- Rpower_plus; replace (q / 4 + q / 4) with c by (unfold c; field).
        apply Rle_refl. }
    replace (- q - 1) with (- (q + 1)) by ring.
    rewrite <- Rmult_assoc.
    apply Rmult_le_compat_r; [ apply Rlt_le; unfold Rpower; apply exp_pos | ].
    unfold K.
    replace ((4 / q + M * (4 / q) * (4 / q)) * Rpower b c)
      with ((4 / q * Rpower b c) + M * ((4 / q) * (4 / q) * Rpower b c)) by ring.
    apply Rplus_le_compat.
    - apply Rle_trans with (2 * (2 / q * Rpower b c));
        [ apply Rmult_le_compat_l; lra | apply Req_le; field; lra ].
    - rewrite (Rmult_comm (ln b * ln b) M).
      apply Rmult_le_compat_l; [ exact HM | exact Hsq ]. }
  apply growing_cv.
  - intro N; rewrite tech5; pose proof (Hd0 (S N)); unfold d2 in *; lra.
  - unfold has_ub, bound, is_upper_bound, EUn.
    exists (K * T'); intros y [N Hy]; rewrite Hy; clear Hy y.
    apply Rle_trans with (sum_f_R0 (fun m => K * term m) N).
    + apply sum_Rle; intros i _; apply Hbound.
    + replace (fun m => K * term m) with (fun m => term m * K)
        by (apply functional_extensionality; intro m; ring).
      rewrite <- scal_sum; apply Rmult_le_compat_l; [ exact HK | ].
      apply (growing_ineq (sum_f_R0 term) T'); [ | exact HT' ].
      intro M0; rewrite tech5.
      assert (0 <= term (S M0)) by (unfold term; apply Rmult_le_pos; apply Rlt_le;
        unfold Rpower; apply exp_pos); lra.
Qed.

Print Assumptions weighted_pseries_cv.

(* ================================================================= *)
(*  END CZetaHolo.v (parts 1-2).                                      *)
(* ================================================================= *)
