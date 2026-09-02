(* ================================================================= *)
(*  NewmanGN.v  --  gN = gext on Re z > 0.  Completes brick E4.        *)
(*                                                                    *)
(*  NewmanCellSum.LTN_stepsum already identifies the honest transform  *)
(*  at the cell endpoints with StepSum - OneSum.  What remains is      *)
(*  limit plumbing: LTN z 0 T -> gN z as T -> oo along any divergent   *)
(*  sequence, then uniqueness of limits against newman_identity, then  *)
(*  gext_eq.                                                          *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia Arith.
Require Import ComplexField Cmodulus CSeries CIntegral2 CGcutCont
        Chebyshev ChebyshevBound ChebyshevPsiR PsiRIntegrable TintCoV
        CIntegralD LaplaceFull NewmanTransform NewmanTail NewmanCellSum
        CVonMangoldtSeries NewmanIdentity CDirichlet CIdentityProp
        CZeta ZetaFn CZetaRegular CZetaRegular2 CZetaRegular6
        ZetaPoleCancel ZetaPoleCancel2 NewmanGExt.
Open Scope R_scope.

Lemma Un_cv_le_const : forall (u : nat -> R) l M N0,
  Un_cv u l -> (forall n, (N0 <= n)%nat -> u n <= M) -> l <= M.
Proof.
  intros u l M N0 Hcv Hb.
  destruct (Rle_lt_dec l M) as [H | H]; [ exact H | exfalso ].
  destruct (Hcv (l - M) ltac:(lra)) as [N1 HN1].
  specialize (HN1 (Nat.max N0 N1) ltac:(lia)).
  specialize (Hb (Nat.max N0 N1) ltac:(lia)).
  unfold R_dist in HN1.
  assert (Hs : l - u (Nat.max N0 N1) <= Rabs (u (Nat.max N0 N1) - l))
    by (rewrite Rabs_minus_sym; apply Rle_abs).
  lra.
Qed.

Section GNsec.
Variable z : C.
Hypothesis Hz : 0 < Re z.

Lemma LTNn_cv : CUn_cv (LTNn z) (gN z Hz).
Proof.
  apply CUn_cv_comp; split; [ apply gN_Re_cv | apply gN_Im_cv ].
Qed.

(* the distance from a fixed truncation to gN is controlled by the tail *)
Lemma LTN_gN_bound : forall T (HT : 0 <= T),
  Cmod (Cminus (LTN z 0 T (Rle_refl 0) HT) (gN z Hz))
  <= 2 * (Kup + 1) * exp (- (Re z * T)) / Re z.
Proof.
  intros T HT.
  (* the sequence of distances to the truncations converges to the target *)
  assert (Hseq : Un_cv (fun n => Cmod (Cminus (LTN z 0 T (Rle_refl 0) HT) (LTNn z n)))
                       (Cmod (Cminus (LTN z 0 T (Rle_refl 0) HT) (gN z Hz)))).
  { intros eps Heps. destruct (LTNn_cv eps Heps) as [N HN].
    exists N; intros n Hn. unfold R_dist.
    eapply Rle_lt_trans; [ apply Cmod_revtri | ].
    replace (Cminus (Cminus (LTN z 0 T (Rle_refl 0) HT) (LTNn z n))
                    (Cminus (LTN z 0 T (Rle_refl 0) HT) (gN z Hz)))
      with (Cminus (gN z Hz) (LTNn z n)) by ring.
    specialize (HN n Hn).
    rewrite (Cmod_min_sym (gN z Hz) (LTNn z n)). exact HN. }
  (* choose N0 with INR N0 >= T *)
  destruct (exists_nat_gt T HT) as [N0 HN0].
  apply (Un_cv_le_const _ _ _ N0 Hseq).
  intros n Hn.
  assert (HTn : T <= INR n)
    by (apply Rle_trans with (INR N0); [ lra | apply le_INR; exact Hn ]).
  assert (Hsplit : Cadd (LTN z 0 T (Rle_refl 0) HT)
                        (LTN z T (INR n) HT HTn)
                   = LTN z 0 (INR n) (Rle_refl 0) (pos_INR n))
    by apply LTN_split.
  assert (Heq : Cminus (LTN z 0 T (Rle_refl 0) HT) (LTNn z n)
                = Copp (LTN z T (INR n) HT HTn))
    by (unfold LTNn; rewrite <- Hsplit; ring).
  rewrite Heq, Cmod_opp.
  apply LTN_tail_le; exact Hz.
Qed.

(* hence convergence along any divergent nonnegative sequence *)
Theorem LTN_seq_cv : forall (Ts : nat -> R) (HT : forall M, 0 <= Ts M),
  cv_infty Ts ->
  CUn_cv (fun M => LTN z 0 (Ts M) (Rle_refl 0) (HT M)) (gN z Hz).
Proof.
  intros Ts HT Hinf.
  assert (Hmaj : Un_cv (fun M => 2 * (Kup + 1) / Re z * exp (- (Re z * Ts M))) 0).
  { assert (Hinf2 : cv_infty (fun M => Re z * Ts M))
      by (apply cv_infty_scal_pos; [ exact Hz | exact Hinf ]).
    pose proof (exp_neg_cv0 _ Hinf2) as Hexp.
    pose proof (Un_cv_cscal_R _ _ (2 * (Kup + 1) / Re z) Hexp) as Hsc.
    intros eps Heps; destruct (Hsc eps Heps) as [N HN]; exists N; intros n Hn.
    specialize (HN n Hn); unfold R_dist in *.
    replace (2 * (Kup + 1) / Re z * exp (- (Re z * Ts n)) - 0)
      with (2 * (Kup + 1) / Re z * exp (- (Re z * Ts n))
            - 2 * (Kup + 1) / Re z * 0) by ring.
    exact HN. }
  intros eps Heps. destruct (Hmaj eps Heps) as [N HN]; exists N; intros n Hn.
  specialize (HN n Hn); unfold R_dist in HN.
  rewrite Rminus_0_r, Rabs_pos_eq in HN.
  - eapply Rle_lt_trans; [ | exact HN ].
    eapply Rle_trans; [ apply LTN_gN_bound | ]. apply Req_le; field; lra.
  - pose proof Kup_pos. pose proof (exp_pos (- (Re z * Ts n))).
    assert (0 < / Re z) by (apply Rinv_0_lt_compat; exact Hz).
    unfold Rdiv. apply Rmult_le_pos; [ apply Rmult_le_pos; lra | lra ].
Qed.

(* ----------------------------------------------------------------- *)
(*  The identification.                                               *)
(* ----------------------------------------------------------------- *)

Theorem gN_eq_gext : gN z Hz = gext z.
Proof.
  assert (HTn : forall M : nat, 0 <= ln (INR (S (S M))))
    by (intro M; apply (ln_SS_nonneg (S M))).
  assert (Hcv1 : CUn_cv (fun M => LTN z 0 (ln (INR (S (S M)))) (Rle_refl 0) (HTn M))
                        (gN z Hz))
    by (apply LTN_seq_cv; apply cv_infty_ln_INR).
  assert (Hcv2 : CUn_cv (fun M => Cminus (StepSum z M) (OneSum z M)) (gN z Hz)).
  { apply (CUn_cv_ext (fun M => LTN z 0 (ln (INR (S (S M)))) (Rle_refl 0) (HTn M)));
      [ intro M; apply LTN_stepsum | exact Hcv1 ]. }
  pose proof (newman_identity z Hz) as HNI.
  pose proof (CUn_cv_unique _ _ _ Hcv2 HNI) as Heq.
  rewrite Heq. symmetry. apply gext_eq.
Qed.

End GNsec.

Print Assumptions gN_eq_gext.
