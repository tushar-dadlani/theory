(* ================================================================= *)
(*  CLContinue.v  --  L(s,chi) converges on Re s > 0.                 *)
(*                                                                    *)
(*  For a NON-PRINCIPAL character mod a prime p, the Dirichlet series  *)
(*  sum chi(n) n^{-s} converges on the whole half-plane Re s > 0, not  *)
(*  just Re s > 1.  This is the continuation that everything else in   *)
(*  the Dirichlet programme is blocked behind: L(1+it,chi) <> 0 needs  *)
(*  L differentiable at 1+it, and L(1,chi) needs L to exist there at   *)
(*  all.                                                              *)
(*                                                                    *)
(*  The mechanism is Abel summation against two facts:                 *)
(*                                                                    *)
(*    CCharSumBound.PS_bound     | sum_{n<=N} chi(n) | <= p            *)
(*    gC_diff_bound              |(n+1)^{-s} - n^{-s}|                 *)
(*                                    <= 2 |s| n^{-Re s - 1}          *)
(*                                                                    *)
(*  the second by the mean value theorem on x |-> x^{-s}, using        *)
(*  CZetaTerm's RegC_deriv / ImgC_deriv and Cmod_gderivC.  Note        *)
(*  ZetaDerivBound.dsk_bound is NOT usable: it assumes 1 <= Re s,      *)
(*  which is exactly the region we are trying to leave.                *)
(*                                                                    *)
(*  Everything here goes through ABSOLUTE convergence of the Abel      *)
(*  correction series, so CSeries.Cseries_abs_cv still applies; no     *)
(*  conditional-convergence theory is needed (and the repo has none).  *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia ZArith Znumtheory List
        FunctionalExtensionality.
Require Import ComplexField Cmodulus CexpFull CPowMul CPowBase CSeries
        RootsOfUnity ZmodOrder DirichletModP CZetaTerm ZetaEM
        CAbelSummation EulerProductR CEulerProductConv CEulerProductFull
        CharModulus CTwistedCoeff CLSeries CCharSumBound GaussSum.
Import ListNotations.
Open Scope R_scope.

(* ================================================================= *)
(*  1.  the consecutive-difference bound for x |-> x^{-s}             *)
(* ================================================================= *)

Lemma Re_gC_diff_bound : forall s n, (1 <= n)%nat -> 0 <= Re s ->
  Rabs (Re (Cminus (gC s (INR (S n))) (gC s (INR n))))
  <= Cmod s * Rpower (INR n) (- Re s - 1).
Proof.
  intros s n Hn Hs0.
  set (a := INR n); set (b := INR (S n)).
  assert (Ha : 0 < a) by (unfold a; apply lt_0_INR; lia).
  assert (Hab : a < b) by (unfold a, b; apply lt_INR; lia).
  assert (Hba1 : b - a = 1) by (unfold a, b; rewrite (S_INR n); ring).
  destruct (MVT_cor2 (fun t => Re (gC s t)) (fun t => Re (gderivC s t)) a b Hab
             (fun c Hc => RegC_deriv s c (Rlt_le_trans 0 a c Ha (proj1 Hc))))
    as [zeta [Hzeta [Hza Hzb]]].
  rewrite Hba1, Rmult_1_r in Hzeta.
  rewrite Re_Cminus. fold a b. rewrite Hzeta.
  eapply Rle_trans; [ apply Cmod_Re_le | ].
  rewrite Cmod_gderivC.
  apply Rmult_le_compat_l; [ apply Cmod_nonneg | ].
  replace (- Re s - 1) with (- (Re s + 1)) by ring.
  apply Rpow_negexp_anti; [ exact Ha | lra | lra ].
Qed.

Lemma Im_gC_diff_bound : forall s n, (1 <= n)%nat -> 0 <= Re s ->
  Rabs (Im (Cminus (gC s (INR (S n))) (gC s (INR n))))
  <= Cmod s * Rpower (INR n) (- Re s - 1).
Proof.
  intros s n Hn Hs0.
  set (a := INR n); set (b := INR (S n)).
  assert (Ha : 0 < a) by (unfold a; apply lt_0_INR; lia).
  assert (Hab : a < b) by (unfold a, b; apply lt_INR; lia).
  assert (Hba1 : b - a = 1) by (unfold a, b; rewrite (S_INR n); ring).
  destruct (MVT_cor2 (fun t => Im (gC s t)) (fun t => Im (gderivC s t)) a b Hab
             (fun c Hc => ImgC_deriv s c (Rlt_le_trans 0 a c Ha (proj1 Hc))))
    as [zeta [Hzeta [Hza Hzb]]].
  rewrite Hba1, Rmult_1_r in Hzeta.
  rewrite Im_Cminus. fold a b. rewrite Hzeta.
  eapply Rle_trans; [ apply Cmod_Im_le | ].
  rewrite Cmod_gderivC.
  apply Rmult_le_compat_l; [ apply Cmod_nonneg | ].
  replace (- Re s - 1) with (- (Re s + 1)) by ring.
  apply Rpow_negexp_anti; [ exact Ha | lra | lra ].
Qed.

Lemma gC_diff_bound : forall s n, (1 <= n)%nat -> 0 <= Re s ->
  Cmod (Cminus (gC s (INR (S n))) (gC s (INR n)))
  <= 2 * Cmod s * Rpower (INR n) (- Re s - 1).
Proof.
  intros s n Hn Hs0.
  pose proof (Re_gC_diff_bound s n Hn Hs0) as HR.
  pose proof (Im_gC_diff_bound s n Hn Hs0) as HI.
  eapply Rle_trans; [ apply Cmod_le_sum | ]. lra.
Qed.

Lemma Cpsum_ext : forall (f h : nat -> C) M,
  (forall k, f k = h k) -> Cpsum f M = Cpsum h M.
Proof.
  intros f h M He. induction M as [| M IH]; cbn [Cpsum].
  - apply He.
  - rewrite IH, He. reflexivity.
Qed.

Lemma CUn_cv_minus : forall (u v : nat -> C) l1 l2,
  CUn_cv u l1 -> CUn_cv v l2 ->
  CUn_cv (fun n => Cminus (u n) (v n)) (Cminus l1 l2).
Proof.
  intros u v l1 l2 Hu Hv eps Heps.
  destruct (Hu (eps / 2) ltac:(lra)) as [N1 H1].
  destruct (Hv (eps / 2) ltac:(lra)) as [N2 H2].
  exists (Nat.max N1 N2). intros n Hn.
  replace (Cminus (Cminus (u n) (v n)) (Cminus l1 l2))
    with (Cadd (Cminus (u n) l1) (Copp (Cminus (v n) l2))) by ring.
  eapply Rle_lt_trans; [ apply Cmod_triangle | ].
  rewrite Cmod_opp.
  pose proof (H1 n ltac:(lia)). pose proof (H2 n ltac:(lia)). lra.
Qed.

(* a shift lemma for complex limits *)
Lemma CUn_cv_unshift : forall (u : nat -> C) l,
  CUn_cv (fun M => u (S M)) l -> CUn_cv u l.
Proof.
  intros u l H eps Heps. destruct (H eps Heps) as [N HN].
  exists (S N). intros n Hn.
  destruct n as [| n]; [ lia | ]. apply HN. lia.
Qed.

(* ================================================================= *)
Section Cont.

Variable p g A : nat.
Hypothesis Hp : prime (Z.of_nat p).
Hypothesis Hg : (1 <= g <= p - 1)%nat.
Hypothesis Hord : ord p g = (p - 1)%nat.
Hypothesis HA : (0 < A < p - 1)%nat.

Variable s : C.
Hypothesis Hs : 0 < Re s.

Definition ac (k : nat) : C := dchar p g A (S k).
Definition cc (k : nat) : C := gC s (INR (S k)).

(* the partial sums of ac are the character partial sums *)
Lemma Cpsum_ac : forall M, Cpsum ac M = PS p g A (S M).
Proof.
  intro M. induction M as [| M IH].
  - unfold PS. cbn [Cpsum seq]. rewrite Sf_cons, Sf_empty. unfold ac. ring.
  - cbn [Cpsum]. rewrite IH. unfold PS.
    replace (seq 1 (S (S M))) with (seq 1 (S M) ++ [1 + S M]%nat)
      by (symmetry; apply seq_S).
    rewrite Sf_app, Sf_cons, Sf_empty.
    replace (1 + S M)%nat with (S (S M)) by lia.
    unfold ac. ring.
Qed.

Lemma ac_psum_bound : forall M, Cmod (Cpsum ac M) <= INR p.
Proof.
  intro M. rewrite Cpsum_ac. apply (PS_bound p g A Hp Hg Hord HA).
Qed.

Lemma cc_diff_bound : forall k,
  Cmod (Cminus (cc (S k)) (cc k))
  <= 2 * Cmod s * Rpower (INR (S k)) (- Re s - 1).
Proof.
  intro k. unfold cc. apply gC_diff_bound; [ lia | lra ].
Qed.

(* the Abel correction series converges absolutely *)
Lemma abel_tail_ex :
  { T | Cseries_cv (fun k => Cmul (Cpsum ac k) (Cminus (cc (S k)) (cc k))) T }.
Proof.
  apply (Cseries_abs_cv _
           (fun k => INR p * (2 * Cmod s) * Rpower (INR (S k)) (- (Re s + 1)))).
  - intro k. rewrite Cmod_mul.
    assert (Hb : Cmod (Cminus (cc (S k)) (cc k))
                 <= 2 * Cmod s * Rpower (INR (S k)) (- (Re s + 1))).
    { replace (- (Re s + 1)) with (- Re s - 1) by ring. apply cc_diff_bound. }
    assert (Hpos : 0 <= 2 * Cmod s * Rpower (INR (S k)) (- (Re s + 1))).
    { apply Rmult_le_pos;
        [ pose proof (Cmod_nonneg s); lra
        | left; unfold Rpower; apply exp_pos ]. }
    pose proof (ac_psum_bound k) as Ha.
    pose proof (Cmod_nonneg (Cpsum ac k)) as Ha0.
    apply Rle_trans with (INR p * Cmod (Cminus (cc (S k)) (cc k))).
    + apply Rmult_le_compat_r; [ apply Cmod_nonneg | exact Ha ].
    + assert (Hp0 : 0 <= INR p) by apply pos_INR. nra.
  - destruct (pseries_cv (Re s + 1) ltac:(lra)) as [T HT].
    exists (INR p * (2 * Cmod s) * T).
    replace (sum_f_R0 (fun k => INR p * (2 * Cmod s)
                                * Rpower (INR (S k)) (- (Re s + 1))))
      with (fun N => INR p * (2 * Cmod s)
                     * sum_f_R0 (fun k => Rpower (INR (S k)) (- (Re s + 1))) N).
    + apply (CV_mult (fun _ => INR p * (2 * Cmod s))
               (sum_f_R0 (fun k => Rpower (INR (S k)) (- (Re s + 1))))
               (INR p * (2 * Cmod s)) T);
        [ apply Un_cv_const | exact HT ].
    + apply functional_extensionality; intro N.
      rewrite (scal_sum (fun k => Rpower (INR (S k)) (- (Re s + 1))) N
                        (INR p * (2 * Cmod s))).
      apply sum_eq; intros i _; ring.
Qed.

(* the Abel head term vanishes *)
Lemma abel_head_cv : CUn_cv (fun M => Cmul (Cpsum ac (S M)) (cc (S M))) C0.
Proof.
  apply (CUn_cv_bound _ C0 (fun M => INR p * Cmod (gC s (INR (S (S M)))))).
  - intro M. replace (Cminus (Cmul (Cpsum ac (S M)) (cc (S M))) C0)
      with (Cmul (Cpsum ac (S M)) (cc (S M))) by ring.
    rewrite Cmod_mul. unfold cc.
    apply Rmult_le_compat_r; [ apply Cmod_nonneg | apply ac_psum_bound ].
  - replace 0 with (INR p * 0) by ring.
    apply CV_mult; [ apply Un_cv_const | ].
    pose proof (CUn_cv_mod0 (fun M => gC s (INR (S (S M)))) C0
                  (gC_to_0 s Hs)) as H.
    intros eps Heps. destruct (H eps Heps) as [N HN]. exists N. intros n Hn.
    specialize (HN n Hn). unfold R_dist in *.
    replace (Cminus (gC s (INR (S (S n)))) C0)
      with (gC s (INR (S (S n)))) in HN by ring.
    exact HN.
Qed.

(* ================================================================= *)
(*  THE CONTINUATION                                                  *)
(* ================================================================= *)
Theorem Lterm_cv_halfplane : { L | Cseries_cv (Lterm p g A s) L }.
Proof.
  destruct abel_tail_ex as [T HT].
  exists (Cminus C0 T).
  apply CUn_cv_unshift.
  (* Abel: Cpsum (a*c) (S M) = (Cpsum a (S M)) * c (S M) - correction M *)
  assert (Habel : forall M,
    Cpsum (Lterm p g A s) (S M)
    = Cminus (Cmul (Cpsum ac (S M)) (cc (S M)))
             (Cpsum (fun k => Cmul (Cpsum ac k) (Cminus (cc (S k)) (cc k))) M)).
  { intro M.
    replace (Cpsum (Lterm p g A s) (S M))
      with (Cpsum (fun k => Cmul (ac k) (cc k)) (S M)).
    - apply Cabel_summation.
    - apply Cpsum_ext. intro k. unfold Lterm, Gchi, ac, cc, gC. reflexivity. }
  intros eps Heps.
  assert (Hcv : CUn_cv
    (fun M => Cminus (Cmul (Cpsum ac (S M)) (cc (S M)))
                     (Cpsum (fun k => Cmul (Cpsum ac k)
                                           (Cminus (cc (S k)) (cc k))) M))
    (Cminus C0 T)).
  { apply CUn_cv_minus; [ apply abel_head_cv | exact HT ]. }
  destruct (Hcv eps Heps) as [N HN]. exists N. intros n Hn.
  rewrite Habel. apply HN; exact Hn.
Qed.

End Cont.

Print Assumptions Lterm_cv_halfplane.

(* ================================================================= *)
(*  END CLContinue.v                                                  *)
(* ================================================================= *)
