(* ================================================================= *)
(*  ZetaStripBound.v  --  a QUANTITATIVE bound on zeta in the strip.   *)
(*                                                                    *)
(*    zetaC_bound : 0 < Re s  ==>                                     *)
(*        |zeta(s)|  <=  1/|s-1|  +  2 |s| (1 + 1/Re s)               *)
(*                                                                    *)
(*  Everything the repo had about zeta in the strip was QUALITATIVE:   *)
(*  zetaC <> 0 for Re > 1, zetaC <> 0 on Re = 1, holomorphy.  No       *)
(*  bound on |zeta| anywhere.  That is the missing input for a         *)
(*  quantitative zero-free region, and hence for a depth bound that    *)
(*  grows with the height rather than being merely finite on disks.    *)
(*                                                                    *)
(*  The bound falls out of the representation zeta already HAS.        *)
(*  CZeta defines                                                      *)
(*                                                                    *)
(*    zeta(s) = 1/(s-1) + Sum_n [ (n+1)^{-s} - Int_{n+1}^{n+2} x^{-s} ] *)
(*                                                                    *)
(*  (first-order Euler-Maclaurin), and CZetaTerm.Cmod_gtermC_bound     *)
(*  already bounds the n-th summand by 2|s|(n+1)^{-Re s - 1}.  What    *)
(*  was missing is only the CONSTANT: CZetaTerm.pseries_cv proves the  *)
(*  p-series converges but discards the upper bound 1 + 1/(p-1) that   *)
(*  its own has_ub argument establishes.  pseries_partial_ub below     *)
(*  keeps it, and the rest is the triangle inequality plus passing to  *)
(*  the limit (Rle_cv_lim).                                           *)
(*                                                                    *)
(*  SCOPE, stated honestly.  This is O(|s|) growth, not the classical  *)
(*  O(ln|t|).  Getting ln requires truncating the sum at N ~ |t| and   *)
(*  estimating the head separately; first-order Euler-Maclaurin with   *)
(*  no truncation cannot do better than linear.  O(|s|) is still       *)
(*  POLYNOMIAL, which is what the Borel-Caratheodory / Landau route to *)
(*  the zero-free region actually consumes -- that argument takes a    *)
(*  logarithm of the bound, so |zeta| = O(|t|^A) suffices for any A.   *)
(*  Axiom-clean.                                                      *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia FunctionalExtensionality.
Require Import ComplexField Cmodulus CexpFull CSeries CPowBase CZetaTerm CZeta.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  A.  the p-series partial sums, WITH the constant                   *)
(* ----------------------------------------------------------------- *)
Lemma pseries_partial_ub : forall p, 1 < p -> forall N,
  sum_f_R0 (fun n => Rpower (INR (S n)) (- p)) N <= 1 + / (p - 1).
Proof.
  intros p Hp.
  set (q := p - 1). assert (Hq : 0 < q) by (unfold q; lra).
  assert (Hqi : 0 < / q) by (apply Rinv_0_lt_compat; exact Hq).
  set (t := fun n => Rpower (INR (S n)) (- q)).
  assert (Ht0 : forall n, 0 <= t n)
    by (intro n; unfold t; apply Rlt_le; unfold Rpower; apply exp_pos).
  assert (Ht00 : t 0%nat = 1) by (unfold t; rewrite INR_1, Rpow1; reflexivity).
  assert (Habound : forall n, Rpower (INR (S (S n))) (- p) <= (t n - t (S n)) / q).
  { intro n.
    assert (Hu : 0 < INR (S n)) by (apply lt_0_INR; lia).
    assert (Huv : INR (S n) < INR (S (S n))) by (apply lt_INR; lia).
    assert (Hvu1 : INR (S (S n)) - INR (S n) = 1) by (rewrite (S_INR (S n)); ring).
    assert (Hd : forall c, INR (S n) <= c <= INR (S (S n)) ->
                 derivable_pt_lim (fun y => Rpower y (- q)) c (- q * Rpower c (- p))).
    { intros c Hc; replace (- p) with (- q - 1) by (unfold q; ring).
      apply Rpow_deriv; apply Rlt_le_trans with (INR (S n)); [ exact Hu | apply (proj1 Hc) ]. }
    destruct (MVT_cor2 (fun y => Rpower y (- q)) (fun y => - q * Rpower y (- p))
               (INR (S n)) (INR (S (S n))) Huv Hd) as [xi [Hxi [Hxu Hxv]]].
    rewrite Hvu1, Rmult_1_r in Hxi.
    assert (Hxipos : 0 < xi) by (apply Rlt_trans with (INR (S n)); [ exact Hu | exact Hxu ]).
    assert (Htt : t n - t (S n) = q * Rpower xi (- p)) by (unfold t; nra).
    rewrite Htt; replace (q * Rpower xi (- p) / q) with (Rpower xi (- p)) by (field; lra).
    apply Rpow_negexp_anti; [ exact Hxipos | lra | lra ]. }
  intro N. destruct N as [| N].
  - cbn [sum_f_R0]; rewrite INR_1, Rpow1; lra.
  - rewrite decomp_sum by lia; rewrite INR_1, Rpow1.
    apply Rplus_le_compat_l.
    apply Rle_trans with (sum_f_R0 (fun i => (t i - t (S i)) / q) N).
    + apply sum_Rle; intros i _; apply Habound.
    + replace (fun i => (t i - t (S i)) / q) with (fun i => (t i - t (S i)) * / q)
        by (apply functional_extensionality; intro i; unfold Rdiv; reflexivity).
      rewrite <- scal_sum, sum_tele, Ht00.
      pose proof (Ht0 (S N)); nra.
Qed.

(* ----------------------------------------------------------------- *)
(*  B.  the modulus is continuous along a complex limit                *)
(* ----------------------------------------------------------------- *)
Lemma Cmod_opp' : forall a, Cmod (Copp a) = Cmod a.
Proof.
  intro a; unfold Cmod, Cnorm2, Copp; cbn [Re Im]; f_equal; ring.
Qed.

Lemma Cmod_rev : forall a b, Rabs (Cmod a - Cmod b) <= Cmod (Cminus a b).
Proof.
  intros a b.
  assert (E : Cmod (Cminus b a) = Cmod (Cminus a b))
    by (replace (Cminus b a) with (Copp (Cminus a b)) by ring; apply Cmod_opp').
  assert (H1 : Cmod a <= Cmod (Cminus a b) + Cmod b).
  { pose proof (Cmod_triangle (Cminus a b) b) as HT.
    replace (Cadd (Cminus a b) b) with a in HT by ring. exact HT. }
  assert (H2 : Cmod b <= Cmod (Cminus a b) + Cmod a).
  { pose proof (Cmod_triangle (Cminus b a) a) as HT.
    replace (Cadd (Cminus b a) a) with b in HT by ring. lra. }
  apply Rabs_le. lra.
Qed.

Lemma CUn_cv_Cmod : forall u l, CUn_cv u l -> Un_cv (fun n => Cmod (u n)) (Cmod l).
Proof.
  intros u l H eps Heps. destruct (H eps Heps) as [N HN].
  exists N. intros n Hn. unfold R_dist.
  eapply Rle_lt_trans; [ apply Cmod_rev | apply HN; exact Hn ].
Qed.

(* ----------------------------------------------------------------- *)
(*  C.  the Euler-Maclaurin tail is bounded                            *)
(* ----------------------------------------------------------------- *)
Theorem Cmod_zeta_tail : forall s (H0 : 0 < Re s) (H1 : Cminus C1 s <> C0),
  Cmod (proj1_sig (gtermC_cv s H0 H1)) <= 2 * Cmod s * (1 + / Re s).
Proof.
  intros s H0 H1.
  pose proof (proj2_sig (gtermC_cv s H0 H1)) as HZ.
  pose proof (Cmod_nonneg s) as Hs0.
  assert (Hpb : forall N, Cmod (Cpsum (gtermC s) N) <= 2 * Cmod s * (1 + / Re s)).
  { intro N. eapply Rle_trans; [ apply Cmod_Cpsum_le | ].
    eapply Rle_trans.
    - apply sum_Rle. intros n _. apply Cmod_gtermC_bound; [ lra | exact H1 ].
    - assert (Heq : sum_f_R0 (fun n => 2 * (Cmod s * Rpower (INR (S n)) (- Re s - 1))) N
                  = 2 * Cmod s * sum_f_R0 (fun n => Rpower (INR (S n)) (- (Re s + 1))) N).
      { rewrite (scal_sum (fun n => Rpower (INR (S n)) (- (Re s + 1))) N (2 * Cmod s)).
        apply sum_eq; intros i _.
        replace (- (Re s + 1)) with (- Re s - 1) by ring. ring. }
      rewrite Heq.
      pose proof (pseries_partial_ub (Re s + 1) ltac:(lra) N) as Hub.
      replace (Re s + 1 - 1) with (Re s) in Hub by ring.
      nra. }
  eapply Rle_cv_lim.
  - exact Hpb.
  - apply CUn_cv_Cmod. exact HZ.
  - apply Un_cv_const.
Qed.

(* ----------------------------------------------------------------- *)
(*  D.  THE BOUND                                                      *)
(* ----------------------------------------------------------------- *)
Lemma Cmod_pos_of_ne0 : forall w, w <> C0 -> 0 < Cmod w.
Proof.
  intros w Hw. destruct (Cmod_nonneg w) as [H | H]; [ exact H | ].
  exfalso; apply Hw; apply (proj1 (Cmod0 w)); lra.
Qed.

Lemma Cmod_one : Cmod C1 = 1.
Proof.
  unfold Cmod, Cnorm2, C1; cbn [Re Im].
  replace (1 * 1 + 0 * 0) with 1 by ring. apply sqrt_1.
Qed.

Lemma Cmod_Cinv : forall w, w <> C0 -> Cmod (Cinv w) = / Cmod w.
Proof.
  intros w Hw. pose proof (Cmod_pos_of_ne0 w Hw) as Hp.
  assert (Hid : Cmod w * Cmod (Cinv w) = 1).
  { rewrite <- Cmod_mul.
    assert (Hone : Cmul w (Cinv w) = C1) by (field; exact Hw).
    rewrite Hone. apply Cmod_one. }
  apply (Rmult_eq_reg_l (Cmod w)); [ rewrite Hid; field; lra | lra ].
Qed.

Theorem zetaC_bound : forall s (H0 : 0 < Re s) (H1 : Cminus C1 s <> C0),
  Cmod (zetaC s H0 H1)
  <= / Cmod (Cminus s C1) + 2 * Cmod s * (1 + / Re s).
Proof.
  intros s H0 H1.
  assert (Hne : Cminus s C1 <> C0)
    by (intro Hc; apply H1; replace (Cminus C1 s) with (Copp (Cminus s C1)) by ring;
        rewrite Hc; unfold Copp, C0; cbn; apply Ceq; cbn; ring).
  unfold zetaC.
  eapply Rle_trans; [ apply Cmod_triangle | ].
  rewrite (Cmod_Cinv (Cminus s C1) Hne).
  apply Rplus_le_compat_l.
  apply Cmod_zeta_tail.
Qed.

(* ----------------------------------------------------------------- *)
(*  E.  the shape that matters: POLYNOMIAL growth on Re s >= 1         *)
(* ----------------------------------------------------------------- *)
Corollary zetaC_bound_ge1 : forall s (H0 : 0 < Re s) (H1 : Cminus C1 s <> C0),
  1 <= Re s -> 1 <= Cmod (Cminus s C1) ->
  Cmod (zetaC s H0 H1) <= 1 + 4 * Cmod s.
Proof.
  intros s H0 H1 Hre Hmod.
  pose proof (zetaC_bound s H0 H1) as HB.
  pose proof (Cmod_nonneg s) as Hs0.
  assert (Hinv1 : / Cmod (Cminus s C1) <= 1).
  { rewrite <- Rinv_1. apply Rinv_le_contravar; lra. }
  assert (Hinv2 : / Re s <= 1) by (rewrite <- Rinv_1; apply Rinv_le_contravar; lra).
  nra.
Qed.

Print Assumptions pseries_partial_ub.
Print Assumptions Cmod_zeta_tail.
Print Assumptions zetaC_bound.
Print Assumptions zetaC_bound_ge1.
