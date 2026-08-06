(* ================================================================= *)
(*  CVonMangoldtZeta.v  —  Milestone A, file B4:  Phi = -zeta'/zeta.     *)
(*                                                                    *)
(*  The capstone.  With A_d = Lam(d) d^{-s} (the Phi terms) and         *)
(*  B_m = m^{-s} (the zeta terms), the Dirichlet product (B3) gives     *)
(*     Phi(s) * zeta(s) = Sum_{n>=1} ( Sum_{d|n} Lam(d) n^{-s} )         *)
(*                      = Sum_{n>=1} (Sum_{d|n} Lam d) n^{-s}            *)
(*                      = Sum_{n>=1} ln(n) n^{-s}   (vonmangoldt_identity)*)
(*                      = -zeta'(s)                 (B2, dcterm_series).  *)
(*  Dividing by zeta(s) (nonzero for Re s>1) yields Phi = -zeta'/zeta.   *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia Arith List FunctionalExtensionality.
Require Import ComplexField Cmodulus CexpFull CPowMul CSeries CListSum
        CDirichletProduct CDirichlet CZetaTerm CZetaTerm2 CZetaDeriv2
        CZetaDerivDirichlet CVonMangoldtSeries Chebyshev CEulerProductZeta
        CZeta GammaFunction RealMobius MobiusOverD VonMangoldtGlobal.
Import ListNotations.
Open Scope R_scope.

(* ================================================================= *)
(*  0.  generic bridges: index shift and linearity                    *)
(* ================================================================= *)

Lemma CUn_cv_pred_S : forall (u : nat -> C) L,
  CUn_cv (fun N => u (S N)) L -> CUn_cv u L.
Proof.
  intros u L H eps Heps; destruct (H eps Heps) as [M HM].
  exists (S M); intros n Hn; destruct n as [|n']; [ lia | apply HM; lia ].
Qed.

Lemma Un_cv_pred_S : forall (u : nat -> R) L,
  Un_cv (fun N => u (S N)) L -> Un_cv u L.
Proof.
  intros u L H eps Heps; destruct (H eps Heps) as [M HM].
  exists (S M); intros n Hn; destruct n as [|n']; [ lia | apply HM; lia ].
Qed.

Lemma Rls_seq_S_eq_sumf : forall (g : nat -> R) N,
  Rls (seq 1 (S N)) g = sum_f_R0 (fun k => g (S k)) N.
Proof.
  intros g N; induction N as [|N IH];
    [ cbn [seq]; rewrite Rls_cons, Rls_nil2; simpl; ring | ].
  rewrite (List.seq_S (S N) 1), Rls_app, IH.
  replace (1 + S N)%nat with (S (S N)) by lia.
  simpl; cbn [Rls map fold_right]; ring.
Qed.

Lemma Cpsum_opp : forall (f : nat -> C) N, Cpsum (fun k => Copp (f k)) N = Copp (Cpsum f N).
Proof.
  intros f N; induction N as [|N IH]; [ reflexivity | cbn [Cpsum]; rewrite IH; ring ].
Qed.

Lemma Cpsum_ext : forall (f g : nat -> C) N, (forall k, f k = g k) -> Cpsum f N = Cpsum g N.
Proof.
  intros f g N Hfg; induction N as [|N IH]; cbn [Cpsum];
    [ apply Hfg | rewrite IH, Hfg; reflexivity ].
Qed.

Lemma CUn_cv_opp : forall u L, CUn_cv u L -> CUn_cv (fun n => Copp (u n)) (Copp L).
Proof.
  intros u L H; apply CUn_cv_comp; rewrite CUn_cv_comp in H; destruct H as [HR HI]; split.
  - apply (Un_cv_ext (fun n => 0 - Re (u n)));
      [ intro n; unfold Copp; cbn [Re]; ring | ].
    replace (Re (Copp L)) with (0 - Re L) by (unfold Copp; cbn [Re]; ring).
    apply CV_minus; [ apply Un_cv_const | exact HR ].
  - apply (Un_cv_ext (fun n => 0 - Im (u n)));
      [ intro n; unfold Copp; cbn [Im]; ring | ].
    replace (Im (Copp L)) with (0 - Im L) by (unfold Copp; cbn [Im]; ring).
    apply CV_minus; [ apply Un_cv_const | exact HI ].
Qed.

Lemma Cls_RtoC : forall A (l : list A) (f : A -> R),
  Cls l (fun x => RtoC (f x)) = RtoC (Rls l f).
Proof.
  intros A l f; induction l as [|a l IH];
    [ unfold RtoC, C0; reflexivity | ].
  rewrite Cls_cons, Rls_cons, IH, RtoC_add; reflexivity.
Qed.

Lemma Cls_scal_r : forall A (l : list A) (f : A -> C) (c : C),
  Cls l (fun d => Cmul (f d) c) = Cmul (Cls l f) c.
Proof.
  intros A l f c.
  transitivity (Cls l (fun d => Cmul c (f d))).
  - apply Cls_ext; intros d _; ring.
  - rewrite <- Cls_scal; ring.
Qed.

(* ================================================================= *)
(*  1.  the two Dirichlet-series terms A_d, B_m (1-based)             *)
(* ================================================================= *)

Definition aterm (s : C) (n : nat) : C := Cmul (RtoC (Lam n)) (gC s (INR n)).
Definition bterm (s : C) (n : nat) : C := gC s (INR n).

Lemma aterm_S : forall s k, aterm s (S k) = pterm s k.
Proof. intros s k; unfold aterm, pterm, cterm; reflexivity. Qed.

Lemma bterm_S : forall s k, bterm s (S k) = cterm s k.
Proof. intros s k; unfold bterm, cterm; reflexivity. Qed.

(* ---- their partial sums converge to Phi and zeta ---- *)
Lemma aterm_cv : forall s (H : 1 < Re s),
  CUn_cv (fun N => Cls (seq 1 N) (aterm s)) (Phi s H).
Proof.
  intros s H; apply CUn_cv_pred_S.
  apply (CUn_cv_ext (fun N => Cpsum (pterm s) N)); [ | exact (Phi_spec s H) ].
  intro N; rewrite <- (Cpsum_shift_eq_Cls (aterm s) N).
  assert (Hf : pterm s = (fun k => aterm s (S k)))
    by (apply functional_extensionality; intro k; symmetry; apply aterm_S).
  rewrite Hf; reflexivity.
Qed.

Lemma bterm_cv : forall s (H0 : 0 < Re s) (H1 : Cminus C1 s <> C0) (H : 1 < Re s),
  CUn_cv (fun N => Cls (seq 1 N) (bterm s)) (zetaC s H0 H1).
Proof.
  intros s H0 H1 H; apply CUn_cv_pred_S.
  apply (CUn_cv_ext (fun N => Cpsum (cterm s) N)); [ | exact (zetaC_eq_dirichlet s H0 H1 H) ].
  intro N; rewrite <- (Cpsum_shift_eq_Cls (bterm s) N).
  assert (Hf : cterm s = (fun k => bterm s (S k)))
    by (apply functional_extensionality; intro k; symmetry; apply bterm_S).
  rewrite Hf; reflexivity.
Qed.

(* ---- absolute convergence of both series ---- *)
Lemma bterm_abs_cv : forall s (H : 1 < Re s),
  { T | Un_cv (fun N => Rls (seq 1 N) (fun m => Cmod (bterm s m))) T }.
Proof.
  intros s H; destruct (pseries_cv (Re s) H) as [T HT].
  exists T; apply Un_cv_pred_S.
  apply (Un_cv_ext (fun N => sum_f_R0 (fun k => Rpower (INR (S k)) (- Re s)) N));
    [ | exact HT ].
  intro N; rewrite Rls_seq_S_eq_sumf.
  apply sum_eq; intros k _; symmetry.
  unfold bterm, gC; rewrite Cpw_mod; f_equal; unfold Copp; cbn [Re]; ring.
Qed.

Lemma aterm_abs_cv : forall s (H : 1 < Re s),
  { T | Un_cv (fun N => Rls (seq 1 N) (fun d => Cmod (aterm s d))) T }.
Proof.
  intros s H; destruct (blam_sum_cv s H) as [B HB].
  assert (Hbn : forall n, 0 <= blam s n).
  { intro n; unfold blam; apply Rmult_le_pos;
      [ rewrite <- ln_1; apply ln_le'; [ lra | rewrite <- INR_1; apply le_INR; lia ]
      | apply Rlt_le; unfold Rpower; apply exp_pos ]. }
  assert (Hpcv : { T | Un_cv (sum_f_R0 (fun k => Cmod (pterm s k))) T }).
  { apply growing_cv.
    - intro N; rewrite tech5; pose proof (Cmod_nonneg (pterm s (S N))); lra.
    - unfold has_ub, bound, is_upper_bound, EUn; exists B.
      intros y [N Hy]; rewrite Hy; clear Hy y.
      apply Rle_trans with (sum_f_R0 (blam s) N).
      + apply sum_Rle; intros k _; rewrite Cmod_pterm; unfold blam.
        apply Rmult_le_compat_r; [ apply Rlt_le; unfold Rpower; apply exp_pos | ].
        apply Lam_le_ln; lia.
      + apply (growing_ineq (sum_f_R0 (blam s)) B); [ | exact HB ].
        intro M; rewrite tech5; pose proof (Hbn (S M)); lra. }
  destruct Hpcv as [T HT]; exists T; apply Un_cv_pred_S.
  apply (Un_cv_ext (fun N => sum_f_R0 (fun k => Cmod (pterm s k)) N)); [ | exact HT ].
  intro N; rewrite Rls_seq_S_eq_sumf.
  apply sum_eq; intros k _; rewrite aterm_S; reflexivity.
Qed.

(* ================================================================= *)
(*  2.  the convolution coefficient collapses to ln(n) n^{-s}         *)
(* ================================================================= *)

Lemma conv_term_eq : forall s n, (1 <= n)%nat ->
  Cls (divisors n) (fun d => Cmul (aterm s d) (bterm s (n / d)%nat))
  = Cmul (RtoC (ln (INR n))) (gC s (INR n)).
Proof.
  intros s n Hn.
  rewrite (Cls_ext nat
             (fun d => Cmul (aterm s d) (bterm s (n / d)%nat))
             (fun d => Cmul (RtoC (Lam d)) (gC s (INR n)))
             (divisors n)).
  2:{ intros d Hd; apply in_divisors in Hd; destruct Hd as [[Hd1 Hdn] Hdvd].
      assert (Hqe : (n / d >= 1)%nat) by (apply Nat.div_le_lower_bound; lia).
      assert (Hgmul : Cmul (gC s (INR d)) (gC s (INR (n / d)%nat)) = gC s (INR n)).
      { unfold gC; rewrite <- Cpw_base_mul by (apply lt_0_INR; lia).
        rewrite <- mult_INR; do 2 f_equal.
        destruct Hdvd as [q Hq]; rewrite Hq, Nat.div_mul by lia; lia. }
      unfold aterm, bterm; rewrite <- Hgmul; ring. }
  rewrite Cls_scal_r, Cls_RtoC.
  replace (Rls (divisors n) Lam) with (dsum Lam n) by reflexivity.
  rewrite (vonmangoldt_identity n Hn); reflexivity.
Qed.

Lemma cterm_conv_S : forall s k,
  Cmul (RtoC (ln (INR (S k)))) (gC s (INR (S k))) = Copp (dcterm s k).
Proof. intros s k; unfold dcterm, dsk, gC; ring. Qed.

(* ================================================================= *)
(*  3.  the product identity  Phi * zeta = -zeta'                     *)
(* ================================================================= *)

Theorem phi_zeta_eq_neg_zeta' :
  forall s (H0 : 0 < Re s) (H1 : Cminus C1 s <> C0) (H : 1 < Re s),
  Cmul (Phi s H) (zetaC s H0 H1) = Copp (proj1_sig (dcterm_cv s H)).
Proof.
  intros s H0 H1 H.
  destruct (aterm_abs_cv s H) as [TA HTA].
  destruct (bterm_abs_cv s H) as [TB HTB].
  pose proof (cdirichlet_product (aterm s) (bterm s) (Phi s H) (zetaC s H0 H1) TA TB
                (aterm_cv s H) (bterm_cv s H0 H1 H) HTA HTB) as Hcp.
  (* rewrite the convolution coefficient to ln(n) n^{-s} *)
  assert (Hconv : CUn_cv (fun N => Cls (seq 1 N)
      (fun n => Cmul (RtoC (ln (INR n))) (gC s (INR n)))) (Cmul (Phi s H) (zetaC s H0 H1))).
  { apply (CUn_cv_ext (fun N => Cls (seq 1 N)
        (fun n => Cls (divisors n) (fun d => Cmul (aterm s d) (bterm s (n / d)%nat)))));
      [ | exact Hcp ].
    intro N; apply Cls_ext; intros n Hn; apply in_seq in Hn.
    apply conv_term_eq; lia. }
  (* the same series is -zeta' *)
  assert (Hneg : CUn_cv (fun N => Cls (seq 1 N)
      (fun n => Cmul (RtoC (ln (INR n))) (gC s (INR n)))) (Copp (proj1_sig (dcterm_cv s H)))).
  { apply CUn_cv_pred_S.
    apply (CUn_cv_ext (fun N => Copp (Cpsum (dcterm s) N))).
    - intro N.
      rewrite <- (Cpsum_shift_eq_Cls (fun n => Cmul (RtoC (ln (INR n))) (gC s (INR n))) N).
      rewrite <- Cpsum_opp.
      apply Cpsum_ext; intro k; symmetry; apply cterm_conv_S.
    - apply CUn_cv_opp; exact (proj2_sig (dcterm_cv s H)). }
  exact (CUn_cv_unique _ _ _ Hconv Hneg).
Qed.

(* ================================================================= *)
(*  4.  divide by zeta:  Phi = -zeta'/zeta                            *)
(* ================================================================= *)

Theorem phi_eq_neg_zeta_ratio :
  forall s (H0 : 0 < Re s) (H1 : Cminus C1 s <> C0) (H : 1 < Re s),
  Phi s H = Copp (Cmul (proj1_sig (dcterm_cv s H)) (Cinv (zetaC s H0 H1))).
Proof.
  intros s H0 H1 H.
  pose proof (phi_zeta_eq_neg_zeta' s H0 H1 H) as Hk.
  pose proof (zetaC_nonzero s H H0 H1) as Hnz.
  assert (Hzz : Cmul (zetaC s H0 H1) (Cinv (zetaC s H0 H1)) = C1)
    by (replace (Cmul (zetaC s H0 H1) (Cinv (zetaC s H0 H1)))
          with (Cmul (Cinv (zetaC s H0 H1)) (zetaC s H0 H1)) by ring;
        apply Cinv_l; exact Hnz).
  transitivity (Cmul (Cmul (Phi s H) (zetaC s H0 H1)) (Cinv (zetaC s H0 H1))).
  - replace (Cmul (Cmul (Phi s H) (zetaC s H0 H1)) (Cinv (zetaC s H0 H1)))
      with (Cmul (Phi s H) (Cmul (zetaC s H0 H1) (Cinv (zetaC s H0 H1)))) by ring.
    rewrite Hzz; ring.
  - rewrite Hk; ring.
Qed.

Print Assumptions phi_eq_neg_zeta_ratio.

(* ================================================================= *)
(*  END CVonMangoldtZeta.v  —  Milestone A complete: Phi = -zeta'/zeta. *)
(* ================================================================= *)
