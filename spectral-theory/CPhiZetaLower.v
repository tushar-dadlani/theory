(* ================================================================= *)
(*  CPhiZetaLower.v  --  sum Lambda(n) n^{-sigma} is UNBOUNDED as     *)
(*  sigma -> 1+.                                                      *)
(*                                                                    *)
(*  The divergent half of Dirichlet's theorem.  CLPhiBounded shows     *)
(*  every non-principal chi stays bounded; this shows the untwisted    *)
(*  series does not, and CLPrincipalLogDeriv.pchi0_val says            *)
(*  Phi(s,chi_0) is this series with only the (bounded) p-part removed.*)
(*                                                                    *)
(*  THE INPUT IS ALREADY IN THE REPO.                                  *)
(*  MertensTailBound.mertens_first_prime gives                         *)
(*      | sum_{p<=N} (ln p)/p  -  ln N |  <=  C,                       *)
(*  and MertensPrime.tterm_le_Lam says the prime part is dominated by  *)
(*  the von Mangoldt part, so sum_{n<=N} Lambda(n)/n >= ln N - C.      *)
(*  Nothing about primes is proved here.                               *)
(*                                                                    *)
(*  THE ONLY REAL STEP is passing from sigma = 1 to sigma near 1 on a  *)
(*  FIXED finite sum, and it is done with one inequality rather than   *)
(*  a term-by-term epsilon: for d <= N,                                *)
(*      d^{-sigma} = d^{-1} d^{-(sigma-1)} >= d^{-1} N^{-(sigma-1)},   *)
(*  so the whole partial sum only loses the factor N^{-(sigma-1)}.     *)
(*  Choosing del = ln 2 / ln N makes that factor at least 1/2.         *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia Arith List ZArith.
Require Import ChebyshevBound ChebyshevPrime VonMangoldtGlobal Chebyshev
        MertensPrime MertensTailBound CVonMangoldtZeta CZetaTerm2
        CLWeightAnti RealMobius.
Open Scope R_scope.

Definition PhiR (sig : R) (N : nat) : R :=
  sum_f_R0 (fun k => Lam (S k) * Rpower (INR (S k)) (- sig)) N.

Lemma Rpower_neg1 : forall x, 0 < x -> Rpower x (-1) = / x.
Proof.
  intros x Hx. replace (-1) with (- (1)) by ring.
  rewrite Rpower_Ropp, Rpower_1 by lra. reflexivity.
Qed.

(* sigma = 1 : dominated below by Mertens *)
Lemma PhiR_one_ge_mprime : forall N, mprime (S N) <= PhiR 1 N.
Proof.
  intro N.
  assert (Hm : mprime (S N) = sum_f_R0 (fun k => tterm (S k) / INR (S k)) N).
  { unfold mprime.
    change (Rsum (fun d => tterm d / INR d) 1 (S N))
      with (Rls (seq 1 (S N)) (fun d => tterm d / INR d)).
    apply Rls_seq_S_eq_sumf. }
  rewrite Hm. unfold PhiR. apply sum_Rle. intros k _.
  assert (Hx : 0 < INR (S k)) by (apply lt_0_INR; lia).
  rewrite Rpower_neg1 by exact Hx.
  unfold Rdiv. apply Rmult_le_compat_r.
  - apply Rlt_le, Rinv_0_lt_compat, Hx.
  - apply tterm_le_Lam.
Qed.

(* the loss in moving from sigma = 1 to sigma *)
Lemma PhiR_sigma_ge : forall sig N, 1 <= sig ->
  Rpower (INR (S N)) (- (sig - 1)) * PhiR 1 N <= PhiR sig N.
Proof.
  intros sig N Hs. unfold PhiR.
  rewrite (scal_sum (fun k => Lam (S k) * Rpower (INR (S k)) (- (1)))
             N (Rpower (INR (S N)) (- (sig - 1)))).
  apply sum_Rle. intros k Hk.
  assert (Hx1 : 1 <= INR (S k)) by (rewrite <- INR_1; apply le_INR; lia).
  assert (Hxle : INR (S k) <= INR (S N)) by (apply le_INR; lia).
  assert (Hbase : Rpower (INR (S N)) (- (sig - 1)) <= Rpower (INR (S k)) (- (sig - 1))).
  { unfold Rpower. apply exp_mono_le.
    assert (Hl1 : 0 <= ln (INR (S k))) by (rewrite <- ln_1; apply ln_le'; lra).
    assert (Hl : ln (INR (S k)) <= ln (INR (S N)))
      by (apply ln_le'; lra).
    nra. }
  assert (Hsplit : Rpower (INR (S k)) (- (1)) * Rpower (INR (S k)) (- (sig - 1))
                   = Rpower (INR (S k)) (- sig))
    by (rewrite <- Rpower_plus; f_equal; ring).
  assert (HL : 0 <= Lam (S k)) by apply Lam_nonneg.
  assert (Hp1 : 0 < Rpower (INR (S k)) (- (1))) by (unfold Rpower; apply exp_pos).
  apply Rle_trans with (Lam (S k) * Rpower (INR (S k)) (- (1))
                        * Rpower (INR (S k)) (- (sig - 1))).
  - apply Rmult_le_compat_l; [ nra | exact Hbase ].
  - rewrite Rmult_assoc, Hsplit. apply Rle_refl.
Qed.

Lemma PhiR_nonneg : forall sig N, 0 <= PhiR sig N.
Proof.
  intros sig N. unfold PhiR. induction N as [| N IH].
  - cbn [sum_f_R0]. apply Rmult_le_pos;
      [ apply Lam_nonneg | apply Rlt_le; unfold Rpower; apply exp_pos ].
  - rewrite tech5.
    assert (0 <= Lam (S (S N)) * Rpower (INR (S (S N))) (- sig))
      by (apply Rmult_le_pos;
          [ apply Lam_nonneg | apply Rlt_le; unfold Rpower; apply exp_pos ]).
    lra.
Qed.

(* an integer with a prescribed logarithm *)
Lemma exists_big_ln : forall t, exists N, (1 <= N)%nat /\ t < ln (INR (S N)).
Proof.
  intro t.
  destruct (archimed (exp t)) as [Ha _].
  assert (Hz : (0 < up (exp t))%Z)
    by (apply lt_IZR; change (IZR 0) with 0; pose proof (exp_pos t); lra).
  exists (Z.to_nat (up (exp t))). split; [ lia | ].
  assert (HNR : INR (Z.to_nat (up (exp t))) = IZR (up (exp t)))
    by (rewrite INR_IZR_INZ, Z2Nat.id by lia; reflexivity).
  assert (Hbig : exp t < INR (S (Z.to_nat (up (exp t)))))
    by (rewrite S_INR, HNR; lra).
  assert (Hgoal : ln (exp t) < ln (INR (S (Z.to_nat (up (exp t))))))
    by (apply ln_increasing; [ apply exp_pos | exact Hbig ]).
  rewrite ln_exp in Hgoal. exact Hgoal.
Qed.

(* ---- THE divergence ---- *)

Theorem PhiR_unbounded : forall M, exists N del, 0 < del /\
  forall sig, 1 <= sig -> sig <= 1 + del -> M <= PhiR sig N.
Proof.
  intro M.
  destruct mertens_first_prime as [C HC].
  destruct (exists_big_ln (Rmax (2 * M + C) 1)) as [N [HN1 HlnN]].
  assert (HlnN1 : 1 < ln (INR (S N)))
    by (eapply Rle_lt_trans; [ apply Rmax_r | exact HlnN ]).
  assert (Hln0 : 0 < ln (INR (S N))) by lra.
  assert (Hmert : ln (INR (S N)) - C <= mprime (S N)).
  { pose proof (HC (S N) ltac:(lia)) as H.
    destruct (Rle_lt_dec (mprime (S N) - ln (INR (S N))) 0) as [Hd | Hd].
    - rewrite Rabs_left1 in H by exact Hd. lra.
    - rewrite Rabs_pos_eq in H by lra. lra. }
  assert (H2M : 2 * M <= PhiR 1 N).
  { pose proof (PhiR_one_ge_mprime N).
    assert (2 * M + C <= ln (INR (S N)))
      by (eapply Rle_trans; [ apply Rmax_l | apply Rlt_le; exact HlnN ]).
    lra. }
  exists N, (ln 2 / ln (INR (S N))). split.
  { apply Rdiv_lt_0_compat; [ | exact Hln0 ].
    rewrite <- ln_1. apply ln_increasing; lra. }
  intros sig Hs1 Hs2.
  assert (Hhalf : / 2 <= Rpower (INR (S N)) (- (sig - 1))).
  { unfold Rpower.
    replace (/ 2) with (exp (- ln 2))
      by (rewrite exp_Ropp, exp_ln by lra; reflexivity).
    apply exp_mono_le.
    assert (Hle : (sig - 1) * ln (INR (S N)) <= ln 2).
    { apply Rle_trans with (ln 2 / ln (INR (S N)) * ln (INR (S N))).
      - apply Rmult_le_compat_r; lra.
      - apply Req_le. unfold Rdiv.
        replace (ln 2 * / ln (INR (S N)) * ln (INR (S N)))
          with (ln 2 * (/ ln (INR (S N)) * ln (INR (S N)))) by ring.
        rewrite Rinv_l by lra. ring. }
    nra. }
  pose proof (PhiR_sigma_ge sig N Hs1) as Hsig.
  pose proof (PhiR_nonneg 1 N) as HP0.
  nra.
Qed.

Print Assumptions PhiR_unbounded.

(* ================================================================= *)
(*  END CPhiZetaLower.v                                               *)
(* ================================================================= *)
