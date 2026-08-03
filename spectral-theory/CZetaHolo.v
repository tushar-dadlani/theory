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
               CSeries CSeriesLin CDeriv CDerivLine CBaseDeriv CBaseDeriv2
               CZetaTerm CZetaTerm2 CZetaDeriv CZetaDeriv2 CZetaDeriv3 CZeta.
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
(*  Part 3: the segment stays in the domain {Re > Re z/2, <> 1}.       *)
(* ================================================================= *)

Lemma Cmod_rev_triangle : forall a b, Cmod a - Cmod b <= Cmod (Cadd a b).
Proof.
  intros a b.
  pose proof (Cmod_triangle (Cadd a b) (Copp b)) as H.
  rewrite Cmod_opp in H.
  replace (Cadd (Cadd a b) (Copp b)) with a in H by ring; lra.
Qed.

Lemma Cmod_C0 : Cmod C0 = 0.
Proof.
  unfold Cmod, Cnorm2, C0; cbn; replace (0 * 0 + 0 * 0) with 0 by ring; apply sqrt_0.
Qed.

Lemma Cmod_gt0_ne0 : forall c, 0 < Cmod c -> c <> C0.
Proof. intros c H Heq; rewrite Heq, Cmod_C0 in H; lra. Qed.

Lemma seg_Re : forall z h t, 0 <= t <= 1 -> Cmod h < Re z / 2 ->
  Re z / 2 <= Re (Cadd z (Cmul (RtoC t) h)).
Proof.
  intros z h t Ht Hh.
  assert (HRe : Re (Cadd z (Cmul (RtoC t) h)) = Re z + t * Re h)
    by (rewrite Re_Cadd, Re_RtoC_mul; reflexivity).
  rewrite HRe.
  pose proof (Cmod_Re_le h) as Hrh.
  assert (Habs : Rabs (t * Re h) <= Cmod h).
  { rewrite Rabs_mult, (Rabs_right t) by lra.
    apply Rle_trans with (1 * Cmod h);
      [ apply Rmult_le_compat; [ lra | apply Rabs_pos | lra | exact Hrh ] | lra ]. }
  pose proof (Rle_abs (t * Re h)) as U.
  pose proof (Rle_abs (- (t * Re h))) as W; rewrite Rabs_Ropp in W.
  lra.
Qed.

Lemma seg_ne1 : forall z h t, 0 <= t <= 1 -> Cmod h < Cmod (Cminus z C1) / 2 ->
  Cminus C1 (Cadd z (Cmul (RtoC t) h)) <> C0.
Proof.
  intros z h t Ht Hh.
  apply Cmod_gt0_ne0.
  assert (Heq : Cminus C1 (Cadd z (Cmul (RtoC t) h))
              = Copp (Cadd (Cminus z C1) (Cmul (RtoC t) h)))
    by (unfold Cminus, Cadd, Copp, Cmul, RtoC, C1; apply Ceq; cbn; ring).
  rewrite Heq, Cmod_opp.
  assert (Hmul : Cmod (Cmul (RtoC t) h) <= Cmod h).
  { rewrite Cmod_mul, Cmod_RtoC, (Rabs_right t) by lra.
    apply Rle_trans with (1 * Cmod h); [ apply Rmult_le_compat_r; [ apply Cmod_nonneg | lra ] | lra ]. }
  pose proof (Cmod_rev_triangle (Cminus z C1) (Cmul (RtoC t) h)) as Hrt.
  pose proof (Cmod_nonneg h); lra.
Qed.

Print Assumptions seg_ne1.

(* ================================================================= *)
(*  Part 4: the Cseries assembly -> zetaC_holo.                        *)
(* ================================================================= *)

(* a nonneg real series dominated by a convergent one converges, to a
   limit no larger. *)
Lemma Rseries_le_cv : forall (a b : nat -> R) Sb,
  (forall n, 0 <= a n) -> (forall n, a n <= b n) -> Un_cv (sum_f_R0 b) Sb ->
  { Sa | Un_cv (sum_f_R0 a) Sa /\ Sa <= Sb }.
Proof.
  intros a b Sb Ha0 Hab HSb.
  assert (Hb0 : forall n, 0 <= b n) by (intro n; apply Rle_trans with (a n); auto).
  assert (Hbnd : forall N, sum_f_R0 a N <= Sb).
  { intro N. apply Rle_trans with (sum_f_R0 b N); [ apply sum_Rle; intros; auto | ].
    apply (growing_ineq (sum_f_R0 b) Sb);
      [ intro M; rewrite tech5; pose proof (Hb0 (S M)); lra | exact HSb ]. }
  assert (Hgrow : Un_growing (sum_f_R0 a))
    by (intro N; rewrite tech5; pose proof (Ha0 (S N)); lra).
  assert (Hub : has_ub (sum_f_R0 a))
    by (unfold has_ub, bound, is_upper_bound, EUn; exists Sb;
        intros y [N Hy]; rewrite Hy; apply Hbnd).
  destruct (growing_cv (sum_f_R0 a) Hgrow Hub) as [Sa HSa].
  exists Sa; split; [ exact HSa | ].
  apply Rnot_lt_le; intro Hlt.
  destruct (HSa (Sa - Sb) ltac:(lra)) as [N HN].
  pose proof (HN N (Nat.le_refl N)) as HNN.
  unfold R_dist in HNN; apply Rabs_def2 in HNN.
  pose proof (Hbnd N); lra.
Qed.

(* the segment-uniform weight:  q = Re z/2,  M = Cmod z + 1 *)
Definition Wsummand (z : C) (n : nat) : R :=
  (2 * ln (INR (S (S n))) + ln (INR (S (S n))) * ln (INR (S (S n))) * (Cmod z + 1))
  * Rpower (INR (S n)) (- (Re z / 2) - 1).

Lemma seg_d2_bound : forall z h n t, 0 <= t <= 1 -> 0 < Re z ->
  Cmod h < Re z / 2 -> Cmod h < Cmod (Cminus z C1) / 2 -> Cmod h < 1 ->
  Cmod (d2gtermC (Cadd z (Cmul (RtoC t) h)) n) <= 2 * Wsummand z n.
Proof.
  intros z h n t Ht Hz Hh1 Hh2 Hh3.
  set (s' := Cadd z (Cmul (RtoC t) h)).
  assert (HRe : Re z / 2 <= Re s') by (apply seg_Re; assumption).
  assert (Hne : Cminus C1 s' <> C0) by (apply seg_ne1; assumption).
  assert (Hlnb : 0 <= ln (INR (S (S n))))
    by (rewrite <- ln_1; apply ln_le'; [ lra | rewrite <- INR_1; apply le_INR; lia ]).
  assert (HsM : Cmod s' <= Cmod z + 1).
  { unfold s'. eapply Rle_trans; [ apply Cmod_triangle | ].
    assert (Cmod (Cmul (RtoC t) h) <= Cmod h).
    { rewrite Cmod_mul, Cmod_RtoC, (Rabs_right t) by lra.
      apply Rle_trans with (1 * Cmod h); [ apply Rmult_le_compat_r; [ apply Cmod_nonneg | lra ] | lra ]. }
    lra. }
  eapply Rle_trans; [ apply Cmod_d2gtermC_bound; [ lra | exact Hne ] | ].
  apply Rmult_le_compat_l; [ lra | ].
  unfold d2bound, Wsummand.
  apply Rmult_le_compat.
  - apply Rplus_le_le_0_compat; [ lra | apply Rmult_le_pos;
      [ apply Rmult_le_pos; assumption | apply Cmod_nonneg ] ].
  - apply Rlt_le; unfold Rpower; apply exp_pos.
  - apply Rplus_le_compat_l; apply Rmult_le_compat_l;
      [ apply Rmult_le_pos; assumption | exact HsM ].
  - apply Rle_Rpower; [ rewrite <- INR_1; apply le_INR; lia | lra ].
Qed.

Lemma seg_pt_1 : forall z h, Cadd z (Cmul (RtoC 1) h) = Cadd z h.
Proof. intros z h; unfold Cadd, Cmul, RtoC; apply Ceq; cbn; ring. Qed.
Lemma seg_pt_0 : forall z h, Cadd z (Cmul (RtoC 0) h) = z.
Proof. intros z h; unfold Cadd, Cmul, RtoC; apply Ceq; cbn; ring. Qed.

(* the per-term remainder bound with the segment-uniform weight *)
Lemma Rn_bound : forall z h n, 0 < Re z ->
  Cmod h < Re z / 2 -> Cmod h < Cmod (Cminus z C1) / 2 -> Cmod h < 1 ->
  Cmod (Cminus (Cminus (gtermC (Cadd z h) n) (gtermC z n)) (Cmul (dgtermC z n) h))
    <= 4 * Wsummand z n * (Cmod h * Cmod h).
Proof.
  intros z h n Hz Hh1 Hh2 Hh3.
  assert (Hseg : forall t, 0 <= t <= 1 -> Cminus C1 (Cadd z (Cmul (RtoC t) h)) <> C0)
    by (intros t Ht; apply seg_ne1; assumption).
  assert (HW0 : 0 <= 2 * Wsummand z n).
  { pose proof (seg_d2_bound z h n 0 ltac:(lra) Hz Hh1 Hh2 Hh3) as H.
    eapply Rle_trans; [ apply Cmod_nonneg | exact H ]. }
  assert (Hbd : forall t, 0 <= t <= 1 -> Cmod (d2gtermC (Cadd z (Cmul (RtoC t) h)) n) <= 2 * Wsummand z n)
    by (intros t Ht; apply seg_d2_bound; assumption).
  pose proof (remainder_Re z h n Hseg (2 * Wsummand z n) HW0 Hbd) as HRe.
  pose proof (remainder_Im z h n Hseg (2 * Wsummand z n) HW0 Hbd) as HIm.
  rewrite seg_pt_1, seg_pt_0 in HRe, HIm.
  eapply Rle_trans; [ apply Cmod_le_sum | ].
  rewrite !Re_Cminus, !Im_Cminus.
  replace (4 * Wsummand z n * (Cmod h * Cmod h))
    with (2 * Wsummand z n * (Cmod h * Cmod h) + 2 * Wsummand z n * (Cmod h * Cmod h)) by ring.
  apply Rplus_le_compat; assumption.
Qed.

Lemma Wsummand_nonneg : forall z n, 0 <= Wsummand z n.
Proof.
  intros z n; unfold Wsummand.
  assert (0 <= ln (INR (S (S n))))
    by (rewrite <- ln_1; apply ln_le'; [ lra | rewrite <- INR_1; apply le_INR; lia ]).
  apply Rmult_le_pos; [ | apply Rlt_le; unfold Rpower; apply exp_pos ].
  apply Rplus_le_le_0_compat; [ lra | apply Rmult_le_pos;
    [ apply Rmult_le_pos; assumption | pose proof (Cmod_nonneg z); lra ] ].
Qed.

Lemma Un_cv_nonneg : forall u l, Un_cv u l -> (forall n, 0 <= u n) -> 0 <= l.
Proof.
  intros u l Hcv Hu; apply Rnot_lt_le; intro Hlt.
  destruct (Hcv (- l) ltac:(lra)) as [N HN].
  pose proof (HN N (Nat.le_refl N)) as H; unfold R_dist in H.
  apply Rabs_def2 in H; pose proof (Hu N); lra.
Qed.

(* the sum S(w) = sum gtermC(w,.) is differentiable at z with derivative
   D = sum dgtermC(z,.), stated over the convergence witnesses. *)
Lemma sum_deriv : forall z (H0 : 0 < Re z) (H1 : Cminus C1 z <> C0),
  forall eps, 0 < eps -> exists del, 0 < del /\
    forall h Vzh Vz, Cmod h < del ->
      Cseries_cv (gtermC (Cadd z h)) Vzh -> Cseries_cv (gtermC z) Vz ->
      Cmod (Cminus (Cminus Vzh Vz) (Cmul (proj1_sig (dgtermC_cv z H0 H1)) h)) <= eps * Cmod h.
Proof.
  intros z H0 H1 eps Heps.
  destruct (dgtermC_cv z H0 H1) as [D HD]; cbn [proj1_sig].
  destruct (weighted_pseries_cv (Re z / 2) (Cmod z + 1) ltac:(lra)
             ltac:(pose proof (Cmod_nonneg z); lra)) as [T HT].
  assert (HTsum : Un_cv (sum_f_R0 (Wsummand z)) T) by exact HT.
  assert (HT0 : 0 <= T).
  { apply (Un_cv_nonneg (sum_f_R0 (Wsummand z))); [ exact HTsum | ].
    intro N; induction N; [ simpl; apply Wsummand_nonneg
      | rewrite tech5; pose proof (Wsummand_nonneg z (S N)); lra ]. }
  assert (Hz1 : 0 < Cmod (Cminus z C1))
    by (apply Cmod_pos_ne0; intro Hc;
        apply H1; replace (Cminus C1 z) with (Copp (Cminus z C1)) by ring;
        rewrite Hc; unfold Copp, C0; apply Ceq; cbn; ring).
  set (del := Rmin (Re z / 2) (Rmin (Cmod (Cminus z C1) / 2) (Rmin 1 (eps / (4 * T + 1))))).
  assert (Hdiv : 0 < eps / (4 * T + 1)) by (apply Rdiv_lt_0_compat; lra).
  exists del; split.
  { unfold del; repeat apply Rmin_glb_lt; lra. }
  intros h Vzh Vz Hh HVzh HVz.
  assert (Hh1 : Cmod h < Re z / 2) by (apply Rlt_le_trans with del; [ exact Hh | apply Rmin_l ]).
  assert (Hh2 : Cmod h < Cmod (Cminus z C1) / 2)
    by (apply Rlt_le_trans with del; [ exact Hh | eapply Rle_trans; [ apply Rmin_r | apply Rmin_l ] ]).
  assert (Hh3 : Cmod h < 1)
    by (apply Rlt_le_trans with del; [ exact Hh
        | eapply Rle_trans; [ apply Rmin_r | eapply Rle_trans; [ apply Rmin_r | apply Rmin_l ] ] ]).
  assert (Hh4 : Cmod h < eps / (4 * T + 1))
    by (apply Rlt_le_trans with del; [ exact Hh
        | eapply Rle_trans; [ apply Rmin_r | eapply Rle_trans; [ apply Rmin_r | apply Rmin_r ] ] ]).
  (* the remainder series *)
  assert (Hcs : Cseries_cv (fun n => Cmul (dgtermC z n) h) (Cmul D h)).
  { replace (fun n => Cmul (dgtermC z n) h) with (fun n => Cmul h (dgtermC z n))
      by (apply functional_extensionality; intro n; ring).
    replace (Cmul D h) with (Cmul h D) by ring.
    apply Cseries_cv_cscal; exact HD. }
  assert (HR : Cseries_cv
    (fun n => Cminus (Cminus (gtermC (Cadd z h) n) (gtermC z n)) (Cmul (dgtermC z n) h))
    (Cminus (Cminus Vzh Vz) (Cmul D h))).
  { apply Cseries_cv_minus; [ apply Cseries_cv_minus; assumption | exact Hcs ]. }
  (* the absolute-value series is dominated by 4 (Cmod h)^2 Wsummand *)
  assert (Hb_cv : Un_cv (sum_f_R0 (fun n => 4 * Wsummand z n * (Cmod h * Cmod h)))
                        (4 * (Cmod h * Cmod h) * T)).
  { replace (fun n => 4 * Wsummand z n * (Cmod h * Cmod h))
      with (fun n => 4 * (Cmod h * Cmod h) * Wsummand z n)
      by (apply functional_extensionality; intro n; ring).
    replace (sum_f_R0 (fun n => 4 * (Cmod h * Cmod h) * Wsummand z n))
      with (fun N => 4 * (Cmod h * Cmod h) * sum_f_R0 (Wsummand z) N)
      by (apply functional_extensionality; intro N;
          rewrite (scal_sum (Wsummand z) N (4 * (Cmod h * Cmod h))); apply sum_eq; intros; ring).
    apply (CV_mult (fun _ => 4 * (Cmod h * Cmod h)) (sum_f_R0 (Wsummand z)) _ T);
      [ apply Un_cv_const | exact HTsum ]. }
  destruct (Rseries_le_cv
    (fun n => Cmod (Cminus (Cminus (gtermC (Cadd z h) n) (gtermC z n)) (Cmul (dgtermC z n) h)))
    (fun n => 4 * Wsummand z n * (Cmod h * Cmod h))
    (4 * (Cmod h * Cmod h) * T)
    (fun n => Cmod_nonneg _)
    (fun n => Rn_bound z h n H0 Hh1 Hh2 Hh3)
    Hb_cv) as [Sa [HSa HSale]].
  eapply Rle_trans; [ apply (Cseries_triangle _ _ Sa HR HSa) | ].
  eapply Rle_trans; [ exact HSale | ].
  assert (Hkey : (4 * T + 1) * Cmod h < eps).
  { apply Rlt_le_trans with ((4 * T + 1) * (eps / (4 * T + 1)));
      [ apply Rmult_lt_compat_l; lra | apply Req_le; field; lra ]. }
  pose proof (Cmod_nonneg h); nra.
Qed.

(* the 1/(s-1) head derivative, explicit *)
Lemma head_deriv : forall z, Cminus z C1 <> C0 ->
  is_Cderiv (fun w => Cinv (Cminus w C1)) z
    (Cmul C1 (Copp (Cinv (Cmul (Cminus z C1) (Cminus z C1))))).
Proof.
  intros z Hz.
  apply (is_Cderiv_ext (fun w => Cinv (Cadd (Cmul C1 w) (Copp C1)))).
  - intro w; f_equal; ring.
  - eapply is_Cderiv_eq.
    + apply Cderiv_comp_affine; apply Cderiv_inv;
        replace (Cadd (Cmul C1 z) (Copp C1)) with (Cminus z C1) by ring; exact Hz.
    + replace (Cadd (Cmul C1 z) (Copp C1)) with (Cminus z C1) by ring; reflexivity.
Qed.

(* ================================================================= *)
(*  THE THEOREM: zetaC is holomorphic on the strip 0 < Re z, z <> 1.   *)
(* ================================================================= *)
Theorem zetaC_holo : forall z (H0 : 0 < Re z) (H1 : Cminus C1 z <> C0),
  exists D, forall eps, 0 < eps -> exists del, 0 < del /\
    forall h (K0 : 0 < Re (Cadd z h)) (K1 : Cminus C1 (Cadd z h) <> C0),
      Cmod h < del ->
      Cmod (Cminus (Cminus (zetaC (Cadd z h) K0 K1) (zetaC z H0 H1)) (Cmul D h))
        <= eps * Cmod h.
Proof.
  intros z H0 H1.
  assert (H1' : Cminus z C1 <> C0)
    by (intro Hc; apply H1; replace (Cminus C1 z) with (Copp (Cminus z C1)) by ring;
        rewrite Hc; unfold Copp, C0; apply Ceq; cbn; ring).
  set (Dhead := Cmul C1 (Copp (Cinv (Cmul (Cminus z C1) (Cminus z C1))))).
  exists (Cadd Dhead (proj1_sig (dgtermC_cv z H0 H1))).
  intros eps Heps.
  destruct (head_deriv z H1' (eps / 2) ltac:(lra)) as [delh [Hdelh Hhead]].
  destruct (sum_deriv z H0 H1 (eps / 2) ltac:(lra)) as [dels [Hdels Hsum]].
  exists (Rmin delh dels); split; [ apply Rmin_glb_lt; assumption | ].
  intros h K0 K1 Hh.
  assert (Hh_h : Cmod h < delh) by (apply Rlt_le_trans with (Rmin delh dels); [ exact Hh | apply Rmin_l ]).
  assert (Hh_s : Cmod h < dels) by (apply Rlt_le_trans with (Rmin delh dels); [ exact Hh | apply Rmin_r ]).
  unfold zetaC.
  set (A1 := Cinv (Cminus (Cadd z h) C1)); set (A2 := Cinv (Cminus z C1)).
  set (B1 := proj1_sig (gtermC_cv (Cadd z h) K0 K1)); set (B2 := proj1_sig (gtermC_cv z H0 H1)).
  set (Ds := proj1_sig (dgtermC_cv z H0 H1)).
  replace (Cminus (Cminus (Cadd A1 B1) (Cadd A2 B2)) (Cmul (Cadd Dhead Ds) h))
    with (Cadd (Cminus (Cminus A1 A2) (Cmul Dhead h)) (Cminus (Cminus B1 B2) (Cmul Ds h)))
    by ring.
  eapply Rle_trans; [ apply Cmod_triangle | ].
  replace (eps * Cmod h) with (eps / 2 * Cmod h + eps / 2 * Cmod h) by field.
  apply Rplus_le_compat.
  - apply (Hhead h Hh_h).
  - apply (Hsum h B1 B2 Hh_s); [ exact (proj2_sig (gtermC_cv (Cadd z h) K0 K1))
                               | exact (proj2_sig (gtermC_cv z H0 H1)) ].
Qed.

Print Assumptions zetaC_holo.

(* ================================================================= *)
(*  END CZetaHolo.v  —  zeta is holomorphic on the critical strip.     *)
(* ================================================================= *)
