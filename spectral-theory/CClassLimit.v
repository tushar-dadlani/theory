(* ================================================================= *)
(*  CClassLimit.v  --  passing the finite orthogonality identity to   *)
(*  the limit, and reading off a lower bound for the class sum.       *)
(*                                                                    *)
(*    (p-1) * (limit of the real class sum)                           *)
(*        =  Re (sum_{a<p-1} chi_a(m) Phi(sigma,chi_a))               *)
(*        >= Phi(sigma,chi_0)  -  (p-2) K                             *)
(*                                                                    *)
(*  The a = 0 term is real and equals Phi(sigma,chi_0) because         *)
(*  chi_0(m) = 1 when p does not divide m; every other term is capped  *)
(*  by CLPhiUniform.Phi_bounded_uniform.  So the class sum inherits    *)
(*  the divergence of the principal character.                        *)
(*                                                                    *)
(*  The real limit is extracted rather than assumed: the complex       *)
(*  partial sums converge (Phichi_spec), CClassPartial identifies them *)
(*  with RtoC of (p-1) times the real partial sums, and CSeries.       *)
(*  CUn_cv_comp then hands back convergence of the real sequence.      *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia List ZArith Znumtheory.
Require Import ComplexField Cmodulus CexpFull CSeries CListSum CDirichlet
        CZetaTerm RootsOfUnity ZmodOrder DirichletModP CTwistedCoeff CLSeries
        VonMangoldtGlobal CVonMangoldtChi CharSelectorSeries CDirichletClass
        CClassPartial CLPhiBounded CLPhiUniform CLPrincipal CTwist341 CharModulus.
Import ListNotations.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  Part A -- generic.                                                 *)
(* ----------------------------------------------------------------- *)

Lemma Un_cv_scal : forall (u : nat -> R) l c,
  Un_cv u l -> Un_cv (fun n => c * u n) (c * l).
Proof.
  intros u l c H eps He.
  destruct (Req_dec c 0) as [Hc0 | Hc0].
  - exists 0%nat. intros n _. unfold R_dist. rewrite Hc0.
    replace (0 * u n - 0 * l) with 0 by ring. rewrite Rabs_R0. exact He.
  - assert (Hc : 0 < Rabs c) by (apply Rabs_pos_lt; exact Hc0).
    destruct (H (eps / Rabs c) ltac:(apply Rdiv_lt_0_compat; lra)) as [N HN].
    exists N. intros n Hn. unfold R_dist.
    replace (c * u n - c * l) with (c * (u n - l)) by ring.
    rewrite Rabs_mult.
    apply Rlt_le_trans with (Rabs c * (eps / Rabs c)).
    + apply Rmult_lt_compat_l; [ lra | apply HN; exact Hn ].
    + apply Req_le. field. lra.
Qed.

Lemma Csum_peel0 : forall f M,
  Csum f (S M) = Cadd (f 0%nat) (Csum (fun a => f (S a)) M).
Proof.
  intros f M. induction M as [| M IH]; [ cbn [Csum]; ring | ].
  replace (Csum f (S (S M))) with (Cadd (Csum f (S M)) (f (S M))) by reflexivity.
  rewrite IH.
  replace (Csum (fun a => f (S a)) (S M))
    with (Cadd (Csum (fun a => f (S a)) M) (f (S M))) by reflexivity.
  ring.
Qed.

Lemma Cmod_Csum_bound : forall f M B,
  (forall a, (a < M)%nat -> Cmod (f a) <= B) -> 0 <= B ->
  Cmod (Csum f M) <= INR M * B.
Proof.
  intros f M B H HB. induction M as [| M IH].
  - replace (Csum f 0%nat) with C0 by reflexivity.
    rewrite (proj2 (Cmod0 C0) eq_refl). simpl. lra.
  - replace (Csum f (S M)) with (Cadd (Csum f M) (f M)) by reflexivity.
    eapply Rle_trans; [ apply Cmod_triangle | ].
    rewrite S_INR.
    assert (HM : Cmod (f M) <= B) by (apply H; lia).
    assert (IH' : Cmod (Csum f M) <= INR M * B)
      by (apply IH; intros a Ha; apply H; lia).
    lra.
Qed.

(* ----------------------------------------------------------------- *)
(*  Part B -- the limit.                                              *)
(* ----------------------------------------------------------------- *)

Section CL.

Variable p g m : nat.
Hypothesis Hp : prime (Z.of_nat p).
Hypothesis Hg : (1 <= g <= p - 1)%nat.
Hypothesis Hord : ord p g = (p - 1)%nat.
Hypothesis Hm : (m mod p <> 0)%nat.

Lemma Hp2 : (2 <= p)%nat.
Proof. pose proof (prime_ge_2 _ Hp); lia. Qed.

Notation SC := (CClassPartial.sc).

Definition Ftot (sig : R) (Hs : 1 < Re (SC sig)) : C :=
  Csum (fun a => Cmul (dchar p g a m) (Phichi p g a Hg Hord (SC sig) Hs)) (p - 1).

Lemma Ftot_cv : forall sig (Hs : 1 < Re (SC sig)),
  CUn_cv (fun N => Csum (fun a =>
            Cmul (dchar p g a m) (Cpsum (pchi p g a (SC sig)) N)) (p - 1))
         (Ftot sig Hs).
Proof.
  intros sig Hs. unfold Ftot.
  apply CUn_cv_Csum. intro a.
  apply CUn_cv_scal_l. apply (Phichi_spec p g a Hg Hord (SC sig) Hs).
Qed.

Definition Cinf (sig : R) (Hs : 1 < Re (SC sig)) : R :=
  Re (Ftot sig Hs) / INR (p - 1).

Lemma INRp1_pos : 0 < INR (p - 1).
Proof.
  apply lt_0_INR. pose proof Hp2. lia.
Qed.

Theorem class_cv : forall sig (Hs : 1 < Re (SC sig)),
  Un_cv (fun N => sum_f_R0 (CDirichletClass.Ares p m sig) N) (Cinf sig Hs).
Proof.
  intros sig Hs.
  assert (Hc : CUn_cv (fun N =>
      RtoC (INR (p - 1) * sum_f_R0 (CDirichletClass.Ares p m sig) N))
      (Ftot sig Hs)).
  { apply (CUn_cv_ext (fun N => Csum (fun a =>
             Cmul (dchar p g a m) (Cpsum (pchi p g a (SC sig)) N)) (p - 1)));
      [ | apply Ftot_cv ].
    intro N. apply (class_partial_identity p g m Hp Hg Hord). }
  rewrite CUn_cv_comp in Hc. destruct Hc as [HRe _].
  assert (HRe' : Un_cv (fun N => INR (p - 1)
                        * sum_f_R0 (CDirichletClass.Ares p m sig) N)
                       (Re (Ftot sig Hs))).
  { apply (Un_cv_ext (fun N => Re (RtoC (INR (p - 1)
             * sum_f_R0 (CDirichletClass.Ares p m sig) N))));
      [ intro n; unfold RtoC; cbn [Re]; reflexivity | exact HRe ]. }
  pose proof INRp1_pos as Hpos.
  apply (Un_cv_ext (fun N => / INR (p - 1)
           * (INR (p - 1) * sum_f_R0 (CDirichletClass.Ares p m sig) N))).
  - intro n. rewrite <- Rmult_assoc, Rinv_l by lra. ring.
  - unfold Cinf, Rdiv. rewrite Rmult_comm.
    apply Un_cv_scal. exact HRe'.
Qed.

(* ---- the a = 0 term is Phi(sigma,chi_0), and the rest is capped ---- *)

Theorem class_lower : forall K, 0 <= K ->
  (forall A, (0 < A < p - 1)%nat -> forall sig (Hs : 1 < Re (SC sig)),
     Cmod (Phichi p g A Hg Hord (SC sig) Hs) <= K) ->
  forall sig (Hs : 1 < Re (SC sig)),
    Re (Phichi p g 0 Hg Hord (SC sig) Hs) - INR (p - 2) * K
    <= INR (p - 1) * Cinf sig Hs.
Proof.
  intros K HK HB sig Hs.
  assert (Hpos := INRp1_pos).
  assert (Heq : INR (p - 1) * Cinf sig Hs = Re (Ftot sig Hs)).
  { unfold Cinf, Rdiv. field. lra. }
  rewrite Heq. unfold Ftot.
  assert (Hp1 : (p - 1 = S (p - 2))%nat) by (pose proof Hp2; lia).
  rewrite Hp1, Csum_peel0.
  assert (Hd0 : dchar p g 0 m = C1)
    by (rewrite dchar0_val; replace (m mod p =? 0)%nat with false
          by (symmetry; apply Nat.eqb_neq; exact Hm); reflexivity).
  rewrite Hd0.
  set (T := Csum (fun a => Cmul (dchar p g (S a) m)
                    (Phichi p g (S a) Hg Hord (SC sig) Hs)) (p - 2)).
  assert (HT : Cmod T <= INR (p - 2) * K).
  { unfold T. apply Cmod_Csum_bound; [ | exact HK ].
    intros a Ha. rewrite Cmod_mul.
    assert (Hc1 : Cmod (dchar p g (S a) m) <= 1) by apply Cmod_dchar_le.
    assert (HPh : Cmod (Phichi p g (S a) Hg Hord (SC sig) Hs) <= K)
      by (apply HB; pose proof Hp2; lia).
    apply Rle_trans with (1 * Cmod (Phichi p g (S a) Hg Hord (SC sig) Hs)).
    - apply Rmult_le_compat_r; [ apply Cmod_nonneg | exact Hc1 ].
    - rewrite Rmult_1_l. exact HPh. }
  assert (HRe : Rabs (Re T) <= Cmod T) by apply Re_le_Cmod.
  assert (HReT : - Cmod T <= Re T).
  { destruct (Rle_lt_dec 0 (Re T)) as [H | H];
      [ pose proof (Cmod_nonneg T); lra | ].
    rewrite Rabs_left in HRe by exact H. lra. }
  assert (Hadd : Re (Cadd (Cmul C1 (Phichi p g 0 Hg Hord (SC sig) Hs)) T)
                 = Re (Phichi p g 0 Hg Hord (SC sig) Hs) + Re T).
  { apply f_equal2 with (f := Rplus); [ | reflexivity ].
    unfold Cmul, C1; cbn [Re Im]; ring. }
  rewrite Hadd. lra.
Qed.

End CL.

Print Assumptions class_cv.
Print Assumptions class_lower.

(* ================================================================= *)
(*  END CClassLimit.v                                                 *)
(* ================================================================= *)
