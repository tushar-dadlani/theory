(* ================================================================= *)
(*  PiUpperAssembly.v  —  theta ~ x => limsup pi/(x/ln x) <= 1 (Step 4b).*)
(*                                                                    *)
(*  Split pi(N) at the threshold y = N/(ln N)^2, M = floor(y).  For      *)
(*  n > M, ln(INR n) > ln y = ln N - 2 ln ln N =: L, so pi_upper_split    *)
(*  gives pi(N) <= M + theta(N)/L <= y + theta(N)/L = D(N)*(N/ln N),      *)
(*  where D(N) = 1/ln N + (theta N/N)*(ln N/(ln N - 2 ln ln N)).          *)
(*  Since D(N) -> 1 (inv_ln_cv0 + ratio_cv1 + theta~N), for every eps    *)
(*  eventually D < 1+eps, hence                                          *)
(*      pi(N) <= (1+eps) * (N/ln N)   (pi_upper_of_theta).              *)
(*  Combined with ThetaPiBound (lower) this is the sharp PNT for pi,     *)
(*  conditional on psi~N (Step 3).  Axiom-clean.                        *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia Arith ZArith.
Require Import Chebyshev ChebyshevBound PrimePowerReindex ChebyshevPrime
        PiUpperSplit LnLimits LnLnLimits RatioLimit.
Open Scope R_scope.

Definition Dseq (N : nat) : R :=
  / ln (INR N)
  + theta N / INR N * (ln (INR N) / (ln (INR N) - 2 * ln (ln (INR N)))).

Lemma Dseq_cv1 :
  Un_cv (fun N => theta N / INR N) 1 -> Un_cv Dseq 1.
Proof.
  intro Hth; unfold Dseq.
  replace 1 with (0 + 1 * 1) by ring.
  apply CV_plus; [ apply inv_ln_cv0 | apply CV_mult; [ exact Hth | apply ratio_cv1 ] ].
Qed.

Lemma pi_le_Dseq : forall N,
  (2 <= N)%nat -> 1 < ln (INR N) -> ln (ln (INR N)) / ln (INR N) <= 1 / 4 ->
  pi_count N <= Dseq N * (INR N / ln (INR N)).
Proof.
  intros N HN2 Hln1 Hs14.
  assert (Hlnpos : 0 < ln (INR N)) by lra.
  assert (HNpos : 0 < INR N) by (apply lt_0_INR; lia).
  assert (Hlnln0 : 0 <= ln (ln (INR N))) by (rewrite <- ln_1; apply ln_le; lra).
  assert (H4 : 4 * ln (ln (INR N)) <= ln (INR N)).
  { apply Rmult_le_reg_r with (/ ln (INR N)); [ apply Rinv_0_lt_compat; exact Hlnpos | ].
    replace (4 * ln (ln (INR N)) * / ln (INR N))
      with (4 * (ln (ln (INR N)) / ln (INR N))) by (unfold Rdiv; ring).
    replace (ln (INR N) * / ln (INR N)) with 1 by (field; lra).
    lra. }
  assert (HL : 0 < ln (INR N) - 2 * ln (ln (INR N))) by lra.
  assert (Hlnne : ln (INR N) <> 0) by lra.
  assert (HNne : INR N <> 0) by lra.
  assert (HLne : ln (INR N) - 2 * ln (ln (INR N)) <> 0) by lra.
  assert (Hllne : ln (INR N) * ln (INR N) <> 0)
    by (assert (0 < ln (INR N) * ln (INR N)) by nra; lra).
  set (y := INR N / (ln (INR N) * ln (INR N))).
  assert (Hy0 : 0 < y) by (unfold y; apply Rdiv_lt_0_compat; [ exact HNpos | nra ]).
  assert (H1ll : 1 <= ln (INR N) * ln (INR N)) by nra.
  assert (HyleN : y <= INR N).
  { unfold y; apply Rmult_le_reg_r with (ln (INR N) * ln (INR N)); [ nra | ].
    unfold Rdiv; rewrite Rmult_assoc, Rinv_l by exact Hllne; rewrite Rmult_1_r; nra. }
  assert (Hlny : ln y = ln (INR N) - 2 * ln (ln (INR N))).
  { unfold y, Rdiv; rewrite ln_mult by (try exact HNpos; apply Rinv_0_lt_compat; nra).
    rewrite ln_Rinv by nra; rewrite (ln_mult (ln (INR N)) (ln (INR N)) Hlnpos Hlnpos); ring. }
  pose proof (base_Int_part y) as [Hple Hplt].
  assert (Hup : (0 < up y)%Z)
    by (apply lt_IZR; pose proof (archimed y) as [Ha _]; simpl; lra).
  assert (HIP0 : (0 <= Int_part y)%Z) by (unfold Int_part; lia).
  set (M := Z.to_nat (Int_part y)).
  assert (HMval : INR M = IZR (Int_part y))
    by (unfold M; rewrite INR_IZR_INZ, Z2Nat.id by exact HIP0; reflexivity).
  assert (HMy : INR M <= y) by (rewrite HMval; exact Hple).
  assert (HyM1 : y < INR M + 1) by (rewrite HMval; lra).
  assert (HMN : (M <= N)%nat) by (apply INR_le; lra).
  eapply Rle_trans.
  - apply (pi_upper_split N M (ln (INR N) - 2 * ln (ln (INR N))) HMN HL).
    intros n Hn1 Hn2.
    assert (Hyn : y < INR n).
    { apply Rlt_le_trans with (INR (S M)); [ rewrite S_INR; lra | apply le_INR; lia ]. }
    apply Rle_trans with (ln y); [ rewrite Hlny; apply Rle_refl | ].
    left; apply ln_increasing; [ exact Hy0 | exact Hyn ].
  - apply Rle_trans with (y + theta N / (ln (INR N) - 2 * ln (ln (INR N)))).
    + apply Rplus_le_compat_r; exact HMy.
    + apply Req_le; unfold Dseq, y; field; repeat split; assumption.
Qed.

Theorem pi_upper_of_theta :
  Un_cv (fun N => theta N / INR N) 1 ->
  forall eps, 0 < eps -> exists N0, forall N, (N0 <= N)%nat ->
    pi_count N <= (1 + eps) * (INR N / ln (INR N)).
Proof.
  intros Hth eps Heps.
  pose proof (Dseq_cv1 Hth) as HD.
  destruct (HD eps Heps) as [Neps HNeps].
  destruct (cv_infty_ln 1) as [N1 HN1].
  destruct (lnln_over_ln_cv0 (1 / 4) ltac:(lra)) as [N2 HN2].
  exists (Nat.max (Nat.max Neps N1) (Nat.max N2 2)); intros N HN.
  assert (Hln1 : 1 < ln (INR N)) by (apply HN1; lia).
  assert (HN2' : (2 <= N)%nat) by lia.
  assert (Hlnpos : 0 < ln (INR N)) by lra.
  assert (HNpos : 0 < INR N) by (apply lt_0_INR; lia).
  assert (Hs14 : ln (ln (INR N)) / ln (INR N) <= 1 / 4).
  { specialize (HN2 N ltac:(lia)); unfold R_dist in HN2; rewrite Rminus_0_r in HN2.
    assert (Hnn : 0 <= ln (ln (INR N)) / ln (INR N)).
    { unfold Rdiv; apply Rmult_le_pos;
        [ rewrite <- ln_1; apply ln_le; lra | left; apply Rinv_0_lt_compat; exact Hlnpos ]. }
    rewrite Rabs_right in HN2 by (apply Rle_ge; exact Hnn); lra. }
  eapply Rle_trans; [ apply pi_le_Dseq; [ exact HN2' | exact Hln1 | exact Hs14 ] | ].
  assert (HDlt : Dseq N < 1 + eps).
  { specialize (HNeps N ltac:(lia)); unfold R_dist in HNeps; apply Rabs_def2 in HNeps; lra. }
  assert (Hpos : 0 < INR N / ln (INR N)) by (apply Rdiv_lt_0_compat; [ exact HNpos | exact Hlnpos ]).
  apply Rmult_le_compat_r; [ left; exact Hpos | left; exact HDlt ].
Qed.

Print Assumptions pi_upper_of_theta.

(* ================================================================= *)
(*  END PiUpperAssembly.v  —  theta~N => eventually pi(N) <= (1+eps)N/ln N.*)
(* ================================================================= *)
