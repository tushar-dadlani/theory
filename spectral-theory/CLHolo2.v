(* ================================================================= *)
(*  CLHolo2.v  --  the L-series converges UNIFORMLY on boxes in        *)
(*  Re s > 0.                                                         *)
(*                                                                    *)
(*  The Abel bounds behind CLContinue are already uniform: the         *)
(*  character partial sums are bounded by p with no reference to s at  *)
(*  all, and |(n+1)^{-s} - n^{-s}| <= 2 |s| n^{-Re s - 1} depends on s *)
(*  only through |s| and Re s.  So on a box                            *)
(*                                                                    *)
(*        sig0 <= Re s,    Cmod s <= M                                 *)
(*                                                                    *)
(*  both the Abel head and the Abel correction tail have bounds         *)
(*  independent of s, and both tend to 0.  That is exactly the         *)
(*  hypothesis CMoreraDisk.unif_limit_holo_disk consumes.              *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia ZArith Znumtheory List
        FunctionalExtensionality.
Require Import ComplexField Cmodulus CexpFull CPower CPowMul CPowBase CSeries
        CDeriv Holomorphic RootsOfUnity ZmodOrder DirichletModP CZetaTerm
        ZetaEM CAbelSummation EulerProductR CEulerProductConv CEulerProductFull
        CharModulus CTwistedCoeff CLSeries CCharSumBound CLContinue CLHolo1
        ZetaEMExtHolo.
Import ListNotations.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  the s-free majorant for the Abel correction series                 *)
(* ----------------------------------------------------------------- *)

Definition bmaj (P sig0 M : R) (k : nat) : R :=
  P * (2 * M) * Rpower (INR (S k)) (- (sig0 + 1)).

Lemma bmaj_cv : forall P sig0 M, 0 < sig0 ->
  { T | Un_cv (sum_f_R0 (bmaj P sig0 M)) T }.
Proof.
  intros P sig0 M Hs.
  destruct (pseries_cv (sig0 + 1) ltac:(lra)) as [T HT].
  exists (P * (2 * M) * T). unfold bmaj.
  replace (sum_f_R0 (fun k => P * (2 * M) * Rpower (INR (S k)) (- (sig0 + 1))))
    with (fun N => P * (2 * M)
                   * sum_f_R0 (fun k => Rpower (INR (S k)) (- (sig0 + 1))) N).
  - apply (CV_mult (fun _ => P * (2 * M))
             (sum_f_R0 (fun k => Rpower (INR (S k)) (- (sig0 + 1))))
             (P * (2 * M)) T); [ apply Un_cv_const | exact HT ].
  - apply functional_extensionality; intro N.
    rewrite (scal_sum (fun k => Rpower (INR (S k)) (- (sig0 + 1))) N
                      (P * (2 * M))).
    apply sum_eq; intros i _; ring.
Qed.

Definition Tmaj (P sig0 M : R) (H : 0 < sig0) : R :=
  proj1_sig (bmaj_cv P sig0 M H).

Definition Ebound (P sig0 M : R) (H : 0 < sig0) (N : nat) : R :=
  P * Rpower (INR (S (S N))) (- sig0)
  + (Tmaj P sig0 M H - sum_f_R0 (bmaj P sig0 M) N).

Lemma Ebound_cv0 : forall P sig0 M (H : 0 < sig0), 0 < P ->
  Un_cv (Ebound P sig0 M H) 0.
Proof.
  intros P sig0 M H HP. unfold Ebound.
  replace 0 with (0 + 0) by ring. apply CV_plus.
  - replace 0 with (P * 0) by ring. apply CV_mult; [ apply Un_cv_const | ].
    apply (Un_cv_S (fun n => Rpower (INR (S n)) (- sig0)) 0).
    apply Rpower_to_0; exact H.
  - assert (HT : Un_cv (sum_f_R0 (bmaj P sig0 M)) (Tmaj P sig0 M H))
      by exact (proj2_sig (bmaj_cv P sig0 M H)).
    intros eps Heps. destruct (HT eps Heps) as [N HN]. exists N.
    intros n Hn. specialize (HN n Hn). unfold R_dist in *.
    replace (Tmaj P sig0 M H - sum_f_R0 (bmaj P sig0 M) n - 0)
      with (- (sum_f_R0 (bmaj P sig0 M) n - Tmaj P sig0 M H)) by ring.
    rewrite Rabs_Ropp. exact HN.
Qed.

(* ================================================================= *)
Section Unif.

Variable p g A : nat.
Hypothesis Hp : prime (Z.of_nat p).
Hypothesis Hg : (1 <= g <= p - 1)%nat.
Hypothesis Hord : ord p g = (p - 1)%nat.
Hypothesis HA : (0 < A < p - 1)%nat.

(* the Abel identity, restated here with an explicit correction limit *)
Lemma abel_id : forall s (Hs : 0 < Re s) N,
  Cpsum (Lterm p g A s) (S N)
  = Cminus (Cmul (Cpsum (ac p g A) (S N)) (cc s (S N)))
           (Cpsum (fun k => Cmul (Cpsum (ac p g A) k)
                                 (Cminus (cc s (S k)) (cc s k))) N).
Proof.
  intros s Hs N.
  replace (Cpsum (Lterm p g A s) (S N))
    with (Cpsum (fun k => Cmul (ac p g A k) (cc s k)) (S N)).
  - apply Cabel_summation.
  - apply Cpsum_ext. intro k.
    unfold Lterm, Gchi, ac, cc, gC. reflexivity.
Qed.

Lemma LFun_eq_minus_T : forall s (Hs : 0 < Re s) T,
  Cseries_cv (fun k => Cmul (Cpsum (ac p g A) k)
                            (Cminus (cc s (S k)) (cc s k))) T ->
  LFun p g A Hp Hg Hord HA s = Cminus C0 T.
Proof.
  intros s Hs T HT. symmetry.
  apply (LFun_unique p g A Hp Hg Hord HA s _ Hs).
  apply CUn_cv_unshift.
  intros eps Heps.
  assert (Hcv : CUn_cv
    (fun N => Cminus (Cmul (Cpsum (ac p g A) (S N)) (cc s (S N)))
                     (Cpsum (fun k => Cmul (Cpsum (ac p g A) k)
                                           (Cminus (cc s (S k)) (cc s k))) N))
    (Cminus C0 T)).
  { apply CUn_cv_minus;
      [ exact (abel_head_cv p g A Hp Hg Hord HA s Hs) | exact HT ]. }
  destruct (Hcv eps Heps) as [N HN]. exists N. intros n Hn.
  rewrite (abel_id s Hs n). apply HN; exact Hn.
Qed.

(* THE UNIFORM ESTIMATE *)
Theorem L_unif_tail : forall sig0 M (H : 0 < sig0),
  forall s, sig0 <= Re s -> Cmod s <= M ->
  forall N,
    Cmod (Cminus (Cpsum (Lterm p g A s) (S N))
                 (LFun p g A Hp Hg Hord HA s))
    <= Ebound (INR p) sig0 M H N.
Proof.
  intros sig0 M H s Hsig HM N.
  assert (Hs : 0 < Re s) by lra.
  assert (HM0 : 0 <= M) by (pose proof (Cmod_nonneg s); lra).
  assert (HP0 : 0 <= INR p) by apply pos_INR.
  destruct (abel_tail_ex p g A Hp Hg Hord HA s Hs) as [T HT].
  rewrite (LFun_eq_minus_T s Hs T HT), (abel_id s Hs N).
  (* difference = head + (T - correction) *)
  replace (Cminus (Cminus (Cmul (Cpsum (ac p g A) (S N)) (cc s (S N)))
                          (Cpsum (fun k => Cmul (Cpsum (ac p g A) k)
                                                (Cminus (cc s (S k)) (cc s k))) N))
                  (Cminus C0 T))
    with (Cadd (Cmul (Cpsum (ac p g A) (S N)) (cc s (S N)))
               (Cminus T (Cpsum (fun k => Cmul (Cpsum (ac p g A) k)
                                               (Cminus (cc s (S k)) (cc s k))) N)))
    by ring.
  eapply Rle_trans; [ apply Cmod_triangle | ].
  unfold Ebound. apply Rplus_le_compat.
  - (* the head *)
    rewrite Cmod_mul. unfold cc, gC. rewrite Cpw_mod.
    assert (Hre : Re (Copp s) = - Re s) by (unfold Copp; cbn [Re]; ring).
    rewrite Hre.
    assert (Hx : 1 <= INR (S (S N))) by (rewrite <- INR_1; apply le_INR; lia).
    assert (Hmono : Rpower (INR (S (S N))) (- Re s)
                    <= Rpower (INR (S (S N))) (- sig0))
      by (apply Rpower_negexp_mono; [ exact Hx | lra ]).
    assert (Hpos : 0 < Rpower (INR (S (S N))) (- Re s))
      by (unfold Rpower; apply exp_pos).
    pose proof (ac_psum_bound p g A Hp Hg Hord HA (S N)) as Hac.
    pose proof (Cmod_nonneg (Cpsum (ac p g A) (S N))) as Hac0.
    nra.
  - (* the correction tail *)
    apply (Cseries_tail_bound
             (fun k => Cmul (Cpsum (ac p g A) k)
                            (Cminus (cc s (S k)) (cc s k)))
             (bmaj (INR p) sig0 M) T (Tmaj (INR p) sig0 M H)).
    + intro k. rewrite Cmod_mul. unfold bmaj.
      assert (Hx : 1 <= INR (S k)) by (rewrite <- INR_1; apply le_INR; lia).
      assert (Hd : Cmod (Cminus (cc s (S k)) (cc s k))
                   <= 2 * Cmod s * Rpower (INR (S k)) (- Re s - 1))
        by (unfold cc; apply gC_diff_bound; [ lia | lra ]).
      assert (Hmono : Rpower (INR (S k)) (- Re s - 1)
                      <= Rpower (INR (S k)) (- (sig0 + 1))).
      { replace (- Re s - 1) with (- (Re s + 1)) by ring.
        apply Rpower_negexp_mono; [ exact Hx | lra ]. }
      assert (Hpp : 0 < Rpower (INR (S k)) (- (sig0 + 1)))
        by (unfold Rpower; apply exp_pos).
      pose proof (ac_psum_bound p g A Hp Hg Hord HA k) as Hac.
      pose proof (Cmod_nonneg (Cpsum (ac p g A) k)) as Hac0.
      pose proof (Cmod_nonneg (Cminus (cc s (S k)) (cc s k))) as Hcc0.
      pose proof (Cmod_nonneg s) as Hs0.
      apply Rle_trans with (INR p * (2 * M * Rpower (INR (S k)) (- (sig0 + 1)))).
      * apply Rmult_le_compat; try assumption. nra.
      * nra.
    + exact HT.
    + exact (proj2_sig (bmaj_cv (INR p) sig0 M H)).
Qed.

End Unif.

Print Assumptions L_unif_tail.

(* ================================================================= *)
(*  END CLHolo2.v                                                     *)
(* ================================================================= *)
