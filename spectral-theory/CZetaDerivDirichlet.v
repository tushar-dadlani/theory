(* ================================================================= *)
(*  CZetaDerivDirichlet.v  —  the Dirichlet form of zeta'(s).          *)
(*                                                                    *)
(*  Milestone A, file B2.  dcterm s n = -ln(n+1)(n+1)^{-s} is the       *)
(*  termwise s-derivative of cterm; the series Sum dcterm converges for *)
(*  Re s > 1 and equals the genuine zeta-derivative Dhead + Sum dgtermC *)
(*  (= the derivative from zetaC_holo), via differentiating the         *)
(*  telescoping EM identity: dgtermC = dsk - (dsGC(n+2) - dsGC(n+1)) is  *)
(*  DEFINITIONAL, so Cpsum(dcterm) N = Cpsum(dgtermC) N +               *)
(*  (dsGC(N+2) - dsGC 1), and dsGC decays (ln x * x^{1-Re s} -> 0).      *)
(*  Hence zeta'(s) = Sum (-ln n) n^{-s}  (dcterm_series_eq).            *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import ComplexField Cmodulus CDeriv CexpFull CSeries CDirichlet
        CZetaTerm CZetaTerm2 CZetaDeriv2 CZetaDeriv3 CZeta ZetaContinuation
        CPowMul CVonMangoldtSeries GammaFunction.
Open Scope R_scope.

(* ---- termwise derivative dcterm = dsk s (n+1) = -ln(n+1)(n+1)^{-s} ---- *)
Definition dcterm (s : C) (n : nat) : C := dsk s (INR (S n)).

Lemma Cmod_dcterm : forall s n, Cmod (dcterm s n) = blam s n.
Proof.
  intros s n; unfold dcterm, dsk, blam.
  rewrite !Cmod_mul, Cmod_opp, Cmod_RtoC, Cpw_mod.
  assert (HC1 : Cmod C1 = 1)
    by (change C1 with (RtoC 1); rewrite Cmod_RtoC; apply Rabs_R1).
  rewrite HC1, Rmult_1_l.
  rewrite (Rabs_pos_eq (ln (INR (S n))))
    by (rewrite <- ln_1; apply ln_le'; [ lra | rewrite <- INR_1; apply le_INR; lia ]).
  replace (Re (Copp s)) with (- Re s) by (unfold Copp; cbn [Re]; ring); reflexivity.
Qed.

Lemma dcterm_cv : forall s, 1 < Re s -> { Z' | Cseries_cv (dcterm s) Z' }.
Proof.
  intros s Hs; apply (Cseries_abs_cv (dcterm s) (blam s)).
  - intro n; rewrite Cmod_dcterm; apply Rle_refl.
  - apply blam_sum_cv; exact Hs.
Qed.

(* ---- the definitional per-term telescoping of the derivative ---- *)
Lemma dcterm_split : forall s n,
  dcterm s n = Cadd (dgtermC s n) (Cminus (dsGC s (INR (S (S n)))) (dsGC s (INR (S n)))).
Proof. intros s n; unfold dcterm, dgtermC; ring. Qed.

Lemma dczeta_EM_identity : forall s N,
  Cpsum (dcterm s) N
  = Cadd (Cpsum (dgtermC s) N) (Cminus (dsGC s (INR (S (S N)))) (dsGC s (INR 1))).
Proof.
  intros s N; induction N as [| N IH]; cbn [Cpsum].
  - exact (dcterm_split s 0).
  - rewrite IH, (dcterm_split s (S N)); ring.
Qed.

(* ---- ln x * x^{-a} -> 0  (a > 0) ---- *)
Lemma lnrpow_cv0 : forall a, 0 < a ->
  Un_cv (fun N => ln (INR (S (S N))) * Rpower (INR (S (S N))) (- a)) 0.
Proof.
  intros a Ha.
  apply (Un_cv_squeeze0 _ (fun N => / (a / 2) * Rpower (INR (S (S N))) (- (a / 2)))).
  - exists 0%nat; intros N _.
    assert (Hx : 1 <= INR (S (S N))) by (rewrite <- INR_1; apply le_INR; lia).
    assert (Hx0 : 0 < INR (S (S N))) by lra.
    split.
    + apply Rmult_le_pos;
        [ rewrite <- ln_1; apply ln_le'; lra | apply Rlt_le; unfold Rpower; apply exp_pos ].
    + assert (Hln : ln (INR (S (S N))) <= / (a / 2) * Rpower (INR (S (S N))) (a / 2))
        by (apply ln_le_rpow; [ lra | exact Hx ]).
      apply Rle_trans with (/ (a / 2) * Rpower (INR (S (S N))) (a / 2) *
                            Rpower (INR (S (S N))) (- a)).
      * apply Rmult_le_compat_r; [ apply Rlt_le; unfold Rpower; apply exp_pos | exact Hln ].
      * rewrite Rmult_assoc, <- Rpower_plus.
        replace (a / 2 + - a) with (- (a / 2)) by lra; apply Req_le; reflexivity.
  - replace 0 with (/ (a / 2) * 0) by ring.
    apply CV_mult; [ apply Un_cv_const | ].
    apply (Un_cv_S (fun n => Rpower (INR (S n)) (- (a / 2)))).
    apply Rpower_neg_cv0; lra.
Qed.

(* ---- dsGC decays: Cmod(dsGC s x) <= (ln x * M + M^2) x^{1-Re s} -> 0 ---- *)
Lemma dsGC_decay : forall s, 1 < Re s -> Cminus C1 s <> C0 ->
  CUn_cv (fun N => dsGC s (INR (S (S N)))) C0.
Proof.
  intros s Hs Hs1; apply CUn_cv_mod0.
  set (M := / Cmod (Cminus C1 s)).
  assert (Hcm : 0 < Cmod (Cminus C1 s)) by (apply Cmod_pos_ne0; exact Hs1).
  assert (HM : 0 <= M) by (unfold M; apply Rlt_le, Rinv_0_lt_compat; exact Hcm).
  apply (Un_cv_squeeze0 _
    (fun N => M * (ln (INR (S (S N))) * Rpower (INR (S (S N))) (- (Re s - 1)))
              + M * M * Rpower (INR (S (S N))) (- (Re s - 1)))).
  - exists 0%nat; intros N _.
    set (x := INR (S (S N))).
    assert (Hx : 1 <= x) by (unfold x; rewrite <- INR_1; apply le_INR; lia).
    assert (Hx0 : 0 < x) by lra.
    assert (HA : Cmod (Cpw x (Cminus C1 s)) = Rpower x (- (Re s - 1))).
    { rewrite Cpw_mod; f_equal; rewrite Re_Cminus; unfold C1; cbn [Re]; ring. }
    assert (HB : Cmod (Cinv (Cminus C1 s)) = M) by (unfold M; apply Cmod_inv; exact Hs1).
    split.
    + apply Cmod_nonneg.
    + unfold dsGC.
      eapply Rle_trans; [ apply Cmod_triangle | ].
      rewrite !Cmod_mul, Cmod_RtoC, HA, HB.
      rewrite (Rabs_left1 (- ln x)) by
        (assert (0 <= ln x) by (rewrite <- ln_1; apply ln_le'; lra); lra).
      rewrite Ropp_involutive; apply Req_le; ring.
  - replace 0 with (M * 0 + M * M * 0) by ring.
    apply CV_plus.
    + replace (M * 0) with (M * 0) by ring; apply CV_mult;
        [ apply Un_cv_const | apply lnrpow_cv0; lra ].
    + apply CV_mult; [ apply Un_cv_const | ].
      apply (Un_cv_S (fun n => Rpower (INR (S n)) (- (Re s - 1)))).
      apply Rpower_neg_cv0; lra.
Qed.

Lemma dsGC_at_1 : forall s,
  dsGC s (INR 1) = Cmul (Cinv (Cminus C1 s)) (Cinv (Cminus C1 s)).
Proof.
  intro s; unfold dsGC; replace (INR 1) with 1 by (simpl; ring).
  rewrite Cpw_one, ln_1, Ropp_0.
  replace (RtoC 0) with C0 by (unfold RtoC, C0; reflexivity); ring.
Qed.

(* ---- local: componentwise limit of a difference ---- *)
Lemma CUn_cv_minus : forall u v a b, CUn_cv u a -> CUn_cv v b ->
  CUn_cv (fun n => Cminus (u n) (v n)) (Cminus a b).
Proof.
  intros u v a b Hu Hv.
  apply CUn_cv_comp; rewrite CUn_cv_comp in Hu, Hv.
  destruct Hu as [HuR HuI]; destruct Hv as [HvR HvI]; split.
  - apply (Un_cv_ext (fun n => Re (u n) - Re (v n)));
      [ intro n; rewrite Re_Cminus; reflexivity | ].
    rewrite Re_Cminus; apply CV_minus; assumption.
  - apply (Un_cv_ext (fun n => Im (u n) - Im (v n)));
      [ intro n; rewrite Im_Cminus; reflexivity | ].
    rewrite Im_Cminus; apply CV_minus; assumption.
Qed.

(* ---- THE Dirichlet form of zeta':  Sum (-ln n) n^{-s} = Dhead + Sum dgtermC ---- *)
Theorem dcterm_series_eq : forall s (H0 : 0 < Re s) (H1 : Cminus C1 s <> C0) (H : 1 < Re s),
  proj1_sig (dcterm_cv s H)
  = Cadd (Copp (dsGC s (INR 1))) (proj1_sig (dgtermC_cv s H0 H1)).
Proof.
  intros s H0 H1 H.
  apply (CUn_cv_unique (Cpsum (dcterm s))).
  - exact (proj2_sig (dcterm_cv s H)).
  - apply (CUn_cv_ext
      (fun N => Cadd (Cpsum (dgtermC s) N)
                     (Cminus (dsGC s (INR (S (S N)))) (dsGC s (INR 1))))).
    + intro N; symmetry; apply dczeta_EM_identity.
    + replace (Cadd (Copp (dsGC s (INR 1))) (proj1_sig (dgtermC_cv s H0 H1)))
        with (Cadd (proj1_sig (dgtermC_cv s H0 H1)) (Cminus C0 (dsGC s (INR 1))))
        by ring.
      apply CUn_cv_add.
      * exact (proj2_sig (dgtermC_cv s H0 H1)).
      * apply CUn_cv_minus; [ apply dsGC_decay; assumption | apply CUn_cv_const ].
Qed.

Print Assumptions dcterm_series_eq.

(* ================================================================= *)
(*  END CZetaDerivDirichlet.v  —  zeta'(s) = Sum (-ln n) n^{-s}.        *)
(* ================================================================= *)
