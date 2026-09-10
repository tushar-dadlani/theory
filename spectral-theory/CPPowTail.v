(* ================================================================= *)
(*  CPPowTail.v  --  prime powers with exponent >= 2 contribute O(1). *)
(*                                                                    *)
(*    sum_{n <= N} bpp(n) n^{-sigma}  <=  Kpp   for every sigma >= 1  *)
(*                                                                    *)
(*  where bpp n = Lam n - [n prime] ln n, so bpp is Lambda restricted  *)
(*  to prime powers p^k with k >= 2 (and zero elsewhere).              *)
(*                                                                    *)
(*  This is what turns "infinitely many prime POWERS in the class"     *)
(*  into "infinitely many PRIMES in the class".  It is needed: for a   *)
(*  fixed p the powers p^k cycle through residues, so a class can      *)
(*  contain infinitely many prime powers while containing only         *)
(*  finitely many primes.                                             *)
(*                                                                    *)
(*  NO POINTWISE BOUND CAN WORK.  bpp(n)/n is (ln n)/(2n) on squares   *)
(*  of primes, and sum (ln n)/n diverges -- what saves it is that the  *)
(*  prime powers are SPARSE.  So the proof has to see the counting     *)
(*  function, and it does, through PsiThetaTail.psi_minus_theta_bound: *)
(*      0 <= psi N - theta N <= sqrt N ln N.                           *)
(*  Partial summation against 1/n (AbelSummation.abel_summation) turns *)
(*  that into sum bpp(n)/n <= 2 + sum ln n n^{-3/2}, and the latter    *)
(*  converges by CVonMangoldtSeries.blam_sum_cv at Re s = 3/2.         *)
(*                                                                    *)
(*  sigma >= 1 reduces to sigma = 1 because bpp >= 0 and               *)
(*  n^{-sigma} <= n^{-1}: no extra work per sigma.                     *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia List.
Require Import ComplexField VonMangoldtGlobal Ell2Primes Chebyshev
        ChebyshevBound ChebyshevPrime PrimePowerReindex PsiThetaTail
        CZetaTerm CZetaTerm2 CVonMangoldtSeries CVonMangoldtZeta
        AbelSummation RealMobius CLWeightAnti.
Import ListNotations.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  Part A -- bpp and its partial sums.                                *)
(* ----------------------------------------------------------------- *)

Definition bpp (n : nat) : R := Lam n - tterm n.

Lemma Rsum_minus : forall f g a n,
  Rsum (fun x => f x - g x) a n = Rsum f a n - Rsum g a n.
Proof.
  intros f g a n. unfold Rsum. generalize (seq a n) as l.
  induction l as [| x l IH]; simpl; [ ring | rewrite IH; ring ].
Qed.

Lemma bpp_sum : forall N, Rsum bpp 1 N = psi N - theta N.
Proof.
  intro N. unfold bpp. rewrite Rsum_minus. reflexivity.
Qed.

Lemma bpp_nonneg : forall n, 0 <= bpp n.
Proof.
  intro n. unfold bpp, tterm.
  destruct (primeb n) eqn:E.
  - rewrite (Lam_prime n (primeb_nprime n E)). lra.
  - pose proof (Lam_nonneg n). lra.
Qed.

Lemma bpp_psum : forall M, sum_f_R0 (fun k => bpp (S k)) M = psi (S M) - theta (S M).
Proof.
  intro M. rewrite <- bpp_sum.
  change (Rsum bpp 1 (S M)) with (Rls (seq 1 (S M)) bpp).
  symmetry. apply Rls_seq_S_eq_sumf.
Qed.

Lemma sum_f_R0_opp : forall f M, sum_f_R0 (fun k => - f k) M = - sum_f_R0 f M.
Proof.
  intros f M. induction M as [| M IH]; [ reflexivity | ].
  rewrite !tech5, IH. ring.
Qed.

Lemma bpp_psum_nonneg : forall M, 0 <= sum_f_R0 (fun k => bpp (S k)) M.
Proof.
  induction M as [| M IH]; [ cbn [sum_f_R0]; apply bpp_nonneg | ].
  rewrite tech5. pose proof (bpp_nonneg (S (S M))). lra.
Qed.

Lemma bpp_psum_bound : forall M,
  sum_f_R0 (fun k => bpp (S k)) M <= sqrt (INR (S M)) * ln (INR (S M)).
Proof.
  intro M. rewrite bpp_psum.
  destruct M as [| M].
  - (* psi 1 - theta 1 = 0 *)
    assert (Hp1 : psi 1 - theta 1 = 0).
    { unfold psi, theta, Rsum. cbn [seq map fold_right].
      unfold tterm. replace (primeb 1) with false by reflexivity.
      rewrite Lam_1. ring. }
    rewrite Hp1.
    replace (INR 1) with 1 by (simpl; ring). rewrite ln_1, sqrt_1. lra.
  - apply (psi_minus_theta_bound (S (S M))). lia.
Qed.

(* ----------------------------------------------------------------- *)
(*  Part B -- the majorant  ln n * n^{-3/2}.                           *)
(* ----------------------------------------------------------------- *)

Definition s32 : C := mkC (3 / 2) 0.

Lemma Hs32 : 1 < Re s32. Proof. cbn. lra. Qed.

Definition Tpp : R := proj1_sig (blam_sum_cv s32 Hs32).

Lemma Tpp_spec : Un_cv (sum_f_R0 (blam s32)) Tpp.
Proof. unfold Tpp. exact (proj2_sig (blam_sum_cv s32 Hs32)). Qed.

Lemma blam_nonneg : forall s n, 0 <= blam s n.
Proof.
  intros s n. unfold blam. apply Rmult_le_pos.
  - rewrite <- ln_1. apply ln_le'; [ lra | rewrite <- INR_1; apply le_INR; lia ].
  - apply Rlt_le. unfold Rpower. apply exp_pos.
Qed.

Lemma Tpp_ub : forall N, sum_f_R0 (blam s32) N <= Tpp.
Proof.
  intro N. apply (growing_ineq (sum_f_R0 (blam s32)) Tpp); [ | apply Tpp_spec ].
  intro M. rewrite tech5. pose proof (blam_nonneg s32 (S M)). lra.
Qed.

(* ln x / sqrt x <= 2 *)
Lemma ln_over_sqrt_le2 : forall x, 1 <= x -> ln x <= 2 * sqrt x.
Proof.
  intros x Hx.
  pose proof (ln_le_rpow (/ 2) x ltac:(lra) Hx) as H.
  assert (Hsq : Rpower x (/ 2) = sqrt x)
    by (first [ symmetry; apply Rpower_sqrt; lra | apply Rpower_sqrt; lra ]).
  rewrite Hsq in H.
  replace (/ / 2) with 2 in H by (field; lra). exact H.
Qed.

(* the per-term majorant *)
Lemma step_bound : forall k,
  sqrt (INR (S k)) * ln (INR (S k)) * (/ INR (S k) - / INR (S (S k)))
  <= blam s32 k.
Proof.
  intro k.
  set (x := INR (S k)). set (y := INR (S (S k))).
  assert (Hx1 : 1 <= x) by (unfold x; rewrite <- INR_1; apply le_INR; lia).
  assert (Hx0 : 0 < x) by lra.
  assert (Hxy : x + 1 = y) by (unfold x, y; rewrite (S_INR (S k)); ring).
  assert (Hy0 : 0 < y) by lra.
  assert (Hln0 : 0 <= ln x) by (rewrite <- ln_1; apply ln_le'; lra).
  assert (Hs0 : 0 < sqrt x) by (apply sqrt_lt_R0; lra).
  assert (Hx0' : x <> 0) by (apply Rgt_not_eq; lra).
  assert (Hxp0 : x + 1 <> 0) by (apply Rgt_not_eq; lra).
  assert (Hprod : x * (x + 1) <> 0) by (apply Rgt_not_eq; nra).
  assert (Hdiff : / x - / y = / (x * y)).
  { rewrite <- Hxy.
    apply (Rmult_eq_reg_r (x * (x + 1))); [ | exact Hprod ].
    rewrite Rinv_l by exact Hprod.
    replace ((/ x - / (x + 1)) * (x * (x + 1)))
      with ((/ x * x) * (x + 1) - (/ (x + 1) * (x + 1)) * x) by ring.
    rewrite Rinv_l by exact Hx0'. rewrite Rinv_l by exact Hxp0. ring. }
  assert (Hle : / (x * y) <= / (x * x)).
  { apply Rinv_le_contravar; nra. }
  assert (Hss : sqrt x * sqrt x = x) by (apply sqrt_sqrt; lra).
  assert (Hp32 : Rpower x (3 / 2) = x * sqrt x).
  { replace (3 / 2) with (1 + / 2) by field.
    rewrite Rpower_plus. rewrite (Rpower_1 x) by lra.
    rewrite Rpower_sqrt by lra. reflexivity. }
  assert (Hneg : Rpower x (- (3 / 2)) = / (x * sqrt x))
    by (rewrite Rpower_Ropp, Hp32; reflexivity).
  assert (Hne1 : x * x <> 0) by (apply Rgt_not_eq; nra).
  assert (Hne2 : x * sqrt x <> 0) by (apply Rgt_not_eq; nra).
  assert (Hkey : sqrt x * ln x * (/ (x * x)) = ln x * Rpower x (- (3 / 2))).
  { rewrite Hneg.
    apply (Rmult_eq_reg_r ((x * x) * (x * sqrt x))); [ | apply Rgt_not_eq; nra ].
    replace (sqrt x * ln x * / (x * x) * (x * x * (x * sqrt x)))
      with (sqrt x * ln x * (/ (x * x) * (x * x)) * (x * sqrt x)) by ring.
    replace (ln x * / (x * sqrt x) * (x * x * (x * sqrt x)))
      with (ln x * (/ (x * sqrt x) * (x * sqrt x)) * (x * x)) by ring.
    rewrite Rinv_l by exact Hne1. rewrite Rinv_l by exact Hne2. nra. }
  unfold blam. change (Re s32) with (3 / 2).
  fold x. rewrite Hdiff.
  eapply Rle_trans; [ | apply Req_le; exact Hkey ].
  apply Rmult_le_compat_l; [ nra | exact Hle ].
Qed.

(* ----------------------------------------------------------------- *)
(*  Part C -- the bound.                                              *)
(* ----------------------------------------------------------------- *)

Definition Kpp : R := 2 + Tpp.

Theorem ppow_tail_bound1 : forall M,
  sum_f_R0 (fun k => bpp (S k) * / INR (S k)) M <= Kpp.
Proof.
  intro M. destruct M as [| M].
  - (* the single term k = 0 vanishes *)
    cbn [sum_f_R0].
    replace (bpp 1%nat) with 0.
    2:{ unfold bpp, tterm. replace (primeb 1) with false by reflexivity.
        rewrite Lam_1. ring. }
    assert (HT : 0 <= Tpp)
      by (eapply Rle_trans; [ apply (blam_nonneg s32 0%nat) | apply (Tpp_ub 0%nat) ]).
    unfold Kpp. lra.
  - rewrite (abel_summation (fun k => bpp (S k)) (fun k => / INR (S k)) M).
    set (A := fun k => sum_f_R0 (fun i => bpp (S i)) k).
    assert (Hhead : A (S M) * / INR (S (S M)) <= 2).
    { assert (Hx1 : 1 <= INR (S (S M)))
        by (rewrite <- INR_1; apply le_INR; lia).
      assert (Hs0 : 0 < sqrt (INR (S (S M)))) by (apply sqrt_lt_R0; lra).
      assert (Hsq : sqrt (INR (S (S M))) * sqrt (INR (S (S M))) = INR (S (S M)))
        by (apply sqrt_sqrt; lra).
      assert (HA : A (S M) <= sqrt (INR (S (S M))) * ln (INR (S (S M))))
        by apply bpp_psum_bound.
      assert (Hln : ln (INR (S (S M))) <= 2 * sqrt (INR (S (S M))))
        by (apply ln_over_sqrt_le2; lra).
      assert (Hinv : 0 < / INR (S (S M))) by (apply Rinv_0_lt_compat; lra).
      assert (HA0 : 0 <= A (S M)) by (unfold A; apply bpp_psum_nonneg).
      apply Rle_trans with (sqrt (INR (S (S M))) * ln (INR (S (S M)))
                            * / INR (S (S M))).
      { apply Rmult_le_compat_r; [ lra | exact HA ]. }
      apply (Rmult_le_reg_r (INR (S (S M)))); [ lra | ].
      replace (sqrt (INR (S (S M))) * ln (INR (S (S M))) * / INR (S (S M))
               * INR (S (S M)))
        with (sqrt (INR (S (S M))) * ln (INR (S (S M)))
              * (/ INR (S (S M)) * INR (S (S M)))) by ring.
      rewrite Rinv_l by lra. nra. }
    assert (Htail : - sum_f_R0 (fun k => A k * (/ INR (S (S k)) - / INR (S k))) M
                    <= Tpp).
    { eapply Rle_trans; [ | apply (Tpp_ub M) ].
      replace (- sum_f_R0 (fun k => A k * (/ INR (S (S k)) - / INR (S k))) M)
        with (sum_f_R0 (fun k => A k * (/ INR (S k) - / INR (S (S k)))) M).
      2:{ rewrite <- sum_f_R0_opp. apply sum_eq. intros i _. ring. }
      apply sum_Rle. intros k _.
      assert (HA : A k <= sqrt (INR (S k)) * ln (INR (S k))) by apply bpp_psum_bound.
      assert (Hd0 : 0 <= / INR (S k) - / INR (S (S k))).
      { assert (H1 : 0 < INR (S k)) by (apply lt_0_INR; lia).
        assert (H2 : 0 < INR (S (S k))) by (apply lt_0_INR; lia).
        assert (H3 : INR (S k) <= INR (S (S k))) by (apply le_INR; lia).
        assert (H4 : / INR (S (S k)) <= / INR (S k))
          by (apply Rinv_le_contravar; lra). lra. }
      eapply Rle_trans; [ | apply step_bound ].
      apply Rmult_le_compat_r; [ exact Hd0 | exact HA ]. }
    unfold Kpp. lra.
Qed.

Theorem ppow_tail_bound : forall sig M, 1 <= sig ->
  sum_f_R0 (fun k => bpp (S k) * Rpower (INR (S k)) (- sig)) M <= Kpp.
Proof.
  intros sig M Hs.
  eapply Rle_trans; [ | apply (ppow_tail_bound1 M) ].
  apply sum_Rle. intros k _.
  assert (Hx1 : 1 <= INR (S k)) by (rewrite <- INR_1; apply le_INR; lia).
  assert (Hstep : Rpower (INR (S k)) (- sig) <= Rpower (INR (S k)) (-1))
    by (apply Rpower_exp_anti; lra).
  assert (Hone : Rpower (INR (S k)) (-1) = / INR (S k)).
  { replace (-1) with (- (1)) by ring. rewrite Rpower_Ropp, Rpower_1 by lra.
    reflexivity. }
  rewrite Hone in Hstep.
  pose proof (bpp_nonneg (S k)). nra.
Qed.

Print Assumptions ppow_tail_bound.

(* ================================================================= *)
(*  END CPPowTail.v                                                   *)
(* ================================================================= *)
