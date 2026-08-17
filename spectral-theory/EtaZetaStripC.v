(* ================================================================= *)
(*  EtaZetaStripC.v  —  the COMPLEX eta identity on the strip, and the   *)
(*  collapse argument on the FULL critical line 1/2 + i t.               *)
(*                                                                    *)
(*  The complex mirror of EtaZetaStrip.v.  CriticalLine.v reached the       *)
(*  critical line at its single REAL point s = 1/2; to reach the whole      *)
(*  line 1/2 + i t we lift the entire count-2 -> eta -> collapse arc over   *)
(*  C.  The lift uses the SAME Euler-Maclaurin telescoping cancellation as  *)
(*  the real proof (CDirichlet.czeta_EM_identity) -- NO analytic            *)
(*  continuation / identity theorem is invoked.                            *)
(*                                                                    *)
(*   ceta_partial_id       : the alternating-sum <-> partial-sum identity   *)
(*        over C  (via cterm(2n) = 2^{-s} cterm(n), the complex z_mult2).   *)
(*   cint_diff_cv0         : the two divergent Euler-Maclaurin tails cancel *)
(*        and the leftover consecutive difference -> 0  (0 < Re s).         *)
(*   ceta_zeta_cont_strip  : eta_C(s) = (1 - 2^{1-s}) zetaC(s) as a LIMIT    *)
(*        of complex alternating partial sums, valid on ALL Re s > 0,       *)
(*        s <> 1  (the strip, complex).                                     *)
(*   ceta_collapse_iff_zeta_zero : away from the first-prime factor zeros    *)
(*        (1 - 2^{1-s} <> 0),  zetaC(s) = 0  <->  the complex alternating   *)
(*        sum COLLAPSES to 0 at infinity -- the same "limit -> 0" as        *)
(*        (x +/- y)/2^n from the count-2 thread.                            *)
(*   crit_line_zero_iff_collapse : specialised to s = 1/2 + i t.  On the    *)
(*        whole critical line the first-prime factor is non-zero            *)
(*        (|2^{1-s}| = sqrt 2 <> 1, crit_factor_ne0), so a NONTRIVIAL zeta  *)
(*        zero at 1/2 + i t IS exactly the complex alternating sum          *)
(*        sum (-1)^i (i+1)^{-(1/2+it)} collapsing to 0 at infinity.         *)
(*                                                                    *)
(*  HONEST HORIZON.  This proves the EQUIVALENCE on the line -- a zero is a  *)
(*  collapse -- for every t.  It does NOT claim any such t exists, nor that *)
(*  EVERY nontrivial zero lies on this line: RH stays open and is not       *)
(*  asserted anywhere here.  The content is that the count-2 collapse now    *)
(*  *sees* the nontrivial zeros, on the full line, with no continuation.    *)
(*                                                                    *)
(*  Axioms: standard classical-Reals only.                            *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import ComplexField Cmodulus CSeries CSeriesLin CZetaTerm CDirichlet
        CPowMul CexpFull CZeta EtaZeta CountTwoCollapse BaselZeta ZetaContinuation.
Open Scope R_scope.

(* ===== complex CUn_cv algebra (local mirrors) ===== *)
Lemma CUn_cv_plus : forall u v a b, CUn_cv u a -> CUn_cv v b ->
  CUn_cv (fun n => Cadd (u n) (v n)) (Cadd a b).
Proof.
  intros u v a b Hu Hv eps Heps.
  destruct (Hu (eps/2) ltac:(lra)) as [Nu HNu].
  destruct (Hv (eps/2) ltac:(lra)) as [Nv HNv].
  exists (Nat.max Nu Nv). intros n Hn.
  replace (Cminus (Cadd (u n) (v n)) (Cadd a b))
    with (Cadd (Cminus (u n) a) (Cminus (v n) b)) by ring.
  eapply Rle_lt_trans; [ apply Cmod_triangle | ].
  assert (Cmod (Cminus (u n) a) < eps/2) by (apply HNu; lia).
  assert (Cmod (Cminus (v n) b) < eps/2) by (apply HNv; lia). lra.
Qed.

Lemma CUn_cv_minus : forall u v a b, CUn_cv u a -> CUn_cv v b ->
  CUn_cv (fun n => Cminus (u n) (v n)) (Cminus a b).
Proof.
  intros u v a b Hu Hv eps Heps.
  destruct (Hu (eps/2) ltac:(lra)) as [Nu HNu].
  destruct (Hv (eps/2) ltac:(lra)) as [Nv HNv].
  exists (Nat.max Nu Nv). intros n Hn.
  replace (Cminus (Cminus (u n) (v n)) (Cminus a b))
    with (Cadd (Cminus (u n) a) (Copp (Cminus (v n) b))) by ring.
  eapply Rle_lt_trans; [ apply Cmod_triangle | ]. rewrite Cmod_opp.
  assert (Cmod (Cminus (u n) a) < eps/2) by (apply HNu; lia).
  assert (Cmod (Cminus (v n) b) < eps/2) by (apply HNv; lia). lra.
Qed.

Lemma CUn_cv_const : forall c, CUn_cv (fun _ => c) c.
Proof.
  intros c eps Heps. exists 0%nat. intros n _.
  replace (Cminus c c) with C0 by ring. rewrite (proj2 (Cmod0 C0) eq_refl). exact Heps.
Qed.

Lemma CUn_cv_scal : forall c u l, CUn_cv u l -> CUn_cv (fun n => Cmul c (u n)) (Cmul c l).
Proof.
  intros c u l Hu eps Heps.
  destruct (Hu (eps / (Cmod c + 1)) ltac:(apply Rdiv_lt_0_compat; [ lra | pose proof (Cmod_nonneg c); lra ])) as [N HN].
  exists N. intros n Hn.
  replace (Cminus (Cmul c (u n)) (Cmul c l)) with (Cmul c (Cminus (u n) l)) by ring.
  rewrite Cmod_mul. pose proof (Cmod_nonneg c). pose proof (HN n Hn).
  apply Rle_lt_trans with (Cmod c * (eps / (Cmod c + 1))).
  - apply Rmult_le_compat_l; [ lra | left; exact H0 ].
  - replace (Cmod c * (eps / (Cmod c + 1))) with (eps * (Cmod c / (Cmod c + 1)))
      by (field; lra).
    rewrite <- (Rmult_1_r eps) at 2. apply Rmult_lt_compat_l; [ exact Heps | ].
    apply Rmult_lt_reg_r with (Cmod c + 1); [ lra | ].
    unfold Rdiv; rewrite Rmult_assoc, Rinv_l by lra; lra.
Qed.

Lemma CUn_cv_subseq : forall u l (phi : nat -> nat),
  (forall M, (M <= phi M)%nat) -> CUn_cv u l -> CUn_cv (fun M => u (phi M)) l.
Proof.
  intros u l phi Hphi Hu eps Heps. destruct (Hu eps Heps) as [N HN].
  exists N. intros M HM. apply HN. apply Nat.le_trans with M; [ exact HM | apply Hphi ].
Qed.

Lemma Cmod_cv0 : forall u, Un_cv (fun n => Cmod (u n)) 0 -> CUn_cv u C0.
Proof.
  intros u Hu eps Heps. destruct (Hu eps Heps) as [N HN]. exists N. intros n Hn.
  replace (Cminus (u n) C0) with (u n) by ring.
  pose proof (HN n Hn) as H. unfold R_dist in H. rewrite Rminus_0_r, Rabs_right in H
    by (apply Rle_ge, Cmod_nonneg). exact H.
Qed.

Print Assumptions CUn_cv_plus.
Lemma CUn_cv_scal_r : forall a u l, CUn_cv u l -> CUn_cv (fun n => Cmul (u n) a) (Cmul l a).
Proof.
  intros a u l Hu.
  apply (CUn_cv_ext (fun n => Cmul a (u n))); [ intro n; ring | ].
  replace (Cmul l a) with (Cmul a l) by ring. apply CUn_cv_scal; exact Hu.
Qed.

Print Assumptions CUn_cv_scal.
Print Assumptions Cmod_cv0.

(* ===== complex z helpers ===== *)
Lemma Cpsum_S : forall a N, Cpsum a (S N) = Cadd (Cpsum a N) (a (S N)).
Proof. reflexivity. Qed.

Lemma cterm_0 : forall s, cterm s 0 = C1.
Proof.
  intro s. unfold cterm, gC. replace (INR (S 0)) with 1 by (simpl; ring). apply Cpw_one.
Qed.
Lemma cterm_1 : forall s, cterm s 1 = Cpw 2 (Copp s).
Proof.
  intro s. unfold cterm, gC. replace (INR (S 1)) with 2 by (simpl; ring). reflexivity.
Qed.

Lemma czmult2 : forall s n, (1 <= n)%nat ->
  Cpw (INR (2 * n)) (Copp s) = Cmul (Cpw 2 (Copp s)) (Cpw (INR n) (Copp s)).
Proof.
  intros s n Hn.
  replace (INR (2 * n)) with (2 * INR n)
    by (rewrite mult_INR; replace (INR 2) with 2 by (simpl; ring); ring).
  apply Cpw_base_mul; [ lra | apply lt_0_INR; lia ].
Qed.

Lemma csign_even : forall k, RtoC ((-1) ^ (2 * k)) = C1.
Proof. intro k. rewrite m1_pow_even. reflexivity. Qed.
Lemma csign_odd : forall k, RtoC ((-1) ^ (S (2 * k))) = Copp C1.
Proof.
  intro k. rewrite m1_pow_odd. unfold RtoC, Copp, C1. apply Ceq; cbn [Re Im]; ring.
Qed.

Lemma ceta_partial_id : forall s M,
  Cpsum (fun i => Cmul (RtoC ((-1) ^ i)) (cterm s i)) (2 * M + 1)
  = Cminus (Cpsum (cterm s) (2 * M + 1))
           (Cmul (Cmul (RtoC 2) (Cpw 2 (Copp s))) (Cpsum (cterm s) M)).
Proof.
  intros s. induction M as [| M IH].
  - replace (2 * 0 + 1)%nat with 1%nat by lia. cbn [Cpsum]. rewrite cterm_0, cterm_1.
    replace (RtoC ((-1) ^ 0)) with C1 by (unfold RtoC, C1; reflexivity).
    replace (RtoC ((-1) ^ 1)) with (Copp C1)
      by (unfold RtoC, Copp, C1; apply Ceq; cbn [Re Im]; ring).
    replace (RtoC 2) with (Cadd C1 C1)
      by (apply Ceq; unfold RtoC, Cadd, C1; cbn [Re Im]; ring).
    set (q := Cpw 2 (Copp s)). ring.
  - replace (2 * S M + 1)%nat with (S (S (2 * M + 1))) by lia.
    rewrite (Cpsum_S (fun i => Cmul (RtoC ((-1) ^ i)) (cterm s i)) (S (2 * M + 1))).
    rewrite (Cpsum_S (fun i => Cmul (RtoC ((-1) ^ i)) (cterm s i)) (2 * M + 1)).
    rewrite (Cpsum_S (cterm s) (S (2 * M + 1))), (Cpsum_S (cterm s) (2 * M + 1)).
    rewrite (Cpsum_S (cterm s) M).
    replace (RtoC ((-1) ^ (S (2 * M + 1)))) with C1
      by (replace (S (2 * M + 1)) with (2 * (M + 1))%nat by lia; symmetry; apply csign_even).
    replace (RtoC ((-1) ^ (S (S (2 * M + 1))))) with (Copp C1)
      by (replace (S (S (2 * M + 1))) with (S (2 * (M + 1)))%nat by lia; symmetry; apply csign_odd).
    (* cterm s (S (S (2*M+1))) = cterm s (S(S M))-mult:  Cpw(INR(2*(M+2)))(-s) *)
    assert (Hc : cterm s (S (S (2 * M + 1))) = Cmul (Cpw 2 (Copp s)) (cterm s (S M))).
    { unfold cterm, gC.
      replace (INR (S (S (S (2 * M + 1))))) with (INR (2 * (S (S M))))
        by (f_equal; lia).
      apply czmult2; lia. }
    rewrite Hc, IH.
    replace (RtoC 2) with (Cadd C1 C1)
      by (apply Ceq; unfold RtoC, Cadd, C1; cbn [Re Im]; ring).
    set (a := Cpw 2 (Copp s)).
    set (c1 := cterm s (S (2 * M + 1))). set (c2 := cterm s (S M)).
    set (g1 := Cpsum (cterm s) (2 * M + 1)). set (g2 := Cpsum (cterm s) M).
    ring.
Qed.

Print Assumptions ceta_partial_id.

(* ===== complex consecutive difference -> 0 ===== *)
Definition cint_diff (s : C) (n : nat) : C :=
  Cminus (Cpw (INR (S (S n))) (Cminus C1 s)) (Cpw (INR (S n)) (Cminus C1 s)).

Lemma cint_diff_eq : forall s n, Cminus C1 s <> C0 ->
  cint_diff s n = Cmul (Cminus (cterm s n) (gtermC s n)) (Cminus C1 s).
Proof.
  intros s n Hs. unfold cint_diff, cterm, gtermC, gC, GC. field. exact Hs.
Qed.

Lemma Cmod_cterm : forall s n, Cmod (cterm s n) = Rpower (INR (S n)) (- Re s).
Proof.
  intros s n. unfold cterm, gC. rewrite Cpw_mod. reflexivity.
Qed.

Lemma Un_cv_plus0 : forall a b, Un_cv a 0 -> Un_cv b 0 -> Un_cv (fun n => a n + b n) 0.
Proof. intros a b Ha Hb. replace 0 with (0 + 0) by ring. apply CV_plus; assumption. Qed.

Lemma cint_diff_cv0 : forall s, 0 < Re s -> Cminus C1 s <> C0 ->
  CUn_cv (fun n => cint_diff s n) C0.
Proof.
  intros s Hs0 Hs1. apply Cmod_cv0.
  apply (Un_cv_maj_0 (fun n => Cmod (cint_diff s n))
    (fun n => Cmod (Cminus C1 s) *
       (Rpower (INR (S n)) (- Re s) + 2 * (Cmod s * Rpower (INR (S n)) (- Re s - 1))))).
  - intro n. rewrite Rabs_right by (apply Rle_ge, Cmod_nonneg).
    rewrite (cint_diff_eq s n Hs1), Cmod_mul, Rmult_comm.
    apply Rmult_le_compat_l; [ apply Cmod_nonneg | ].
    replace (Cminus (cterm s n) (gtermC s n))
      with (Cadd (cterm s n) (Copp (gtermC s n))) by ring.
    eapply Rle_trans; [ apply Cmod_triangle | ]. rewrite Cmod_opp.
    apply Rplus_le_compat.
    + rewrite Cmod_cterm. apply Rle_refl.
    + apply Cmod_gtermC_bound; [ lra | exact Hs1 ].
  - apply Un_cv_scal_0. apply Un_cv_plus0.
    + apply Rpower_neg_cv0; lra.
    + apply Un_cv_scal_0. apply Un_cv_scal_0. apply Rpower_neg_cv0; lra.
Qed.

Lemma ctwo_z2 : forall s, Cmul (RtoC 2) (Cpw 2 (Copp s)) = Cpw 2 (Cminus C1 s).
Proof.
  intro s.
  replace (RtoC 2) with (Cpw 2 C1)
    by (change C1 with (RtoC 1); rewrite Cpw_RtoC, Rpower_1 by lra; reflexivity).
  rewrite <- Cpw_split. reflexivity.
Qed.

Lemma CUn_cv_opp : forall u l, CUn_cv u l -> CUn_cv (fun n => Copp (u n)) (Copp l).
Proof.
  intros u l Hu eps Heps. destruct (Hu eps Heps) as [N HN]. exists N. intros n Hn.
  replace (Cminus (Copp (u n)) (Copp l)) with (Copp (Cminus (u n) l)) by ring.
  rewrite Cmod_opp. apply HN; exact Hn.
Qed.

Lemma cGC_one : forall s, Cminus C1 s <> C0 -> GC s (INR 1) = Cinv (Cminus C1 s).
Proof.
  intros s H1. unfold GC. replace (INR 1) with 1 by (simpl; ring).
  rewrite Cpw_one. ring.
Qed.

Lemma two_INR_mul : forall k, 2 * INR k = INR (2 * k).
Proof. intro k. rewrite mult_INR. replace (INR 2) with 2 by (simpl; ring). ring. Qed.

Lemma ceta_partial_decomp : forall s (H1 : Cminus C1 s <> C0) M,
  Cpsum (fun i => Cmul (RtoC ((-1) ^ i)) (cterm s i)) (2 * M + 1)
  = Cadd (Cminus (Cpsum (gtermC s) (2 * M + 1))
                 (Cmul (Cmul (RtoC 2) (Cpw 2 (Copp s))) (Cpsum (gtermC s) M)))
         (Cmul (Cadd (Copp (cint_diff s (2 * M + 2)))
                     (Cminus (Cmul (RtoC 2) (Cpw 2 (Copp s))) C1))
               (Cinv (Cminus C1 s))).
Proof.
  intros s H1 M. rewrite ceta_partial_id.
  rewrite (czeta_EM_identity s (2 * M + 1)), (czeta_EM_identity s M).
  rewrite !(cGC_one s H1). unfold GC, cint_diff.
  assert (cHa : Cpw (INR (S (S (2 * M + 1)))) (Cminus C1 s)
              = Cpw (INR (S (2 * M + 2))) (Cminus C1 s)) by (f_equal; f_equal; lia).
  assert (cHb : Cmul (Cmul (RtoC 2) (Cpw 2 (Copp s))) (Cpw (INR (S (S M))) (Cminus C1 s))
              = Cpw (INR (S (S (2 * M + 2)))) (Cminus C1 s)).
  { rewrite ctwo_z2, <- Cpw_base_mul by (try lra; apply lt_0_INR; lia).
    f_equal. rewrite two_INR_mul. f_equal. lia. }
  rewrite cHa, <- cHb. field. exact H1.
Qed.

Theorem ceta_zeta_cont_strip : forall s (H0 : 0 < Re s) (H1 : Cminus C1 s <> C0),
  CUn_cv (fun M => Cpsum (fun i => Cmul (RtoC ((-1) ^ i)) (cterm s i)) (2 * M + 1))
         (Cmul (Cminus C1 (Cpw 2 (Cminus C1 s))) (zetaC s H0 H1)).
Proof.
  intros s H0 H1.
  set (G := proj1_sig (gtermC_cv s H0 H1)).
  assert (HG : CUn_cv (Cpsum (gtermC s)) G) by exact (proj2_sig (gtermC_cv s H0 H1)).
  assert (Hsm1 : Cminus s C1 <> C0)
    by (intro Hc; apply H1; replace (Cminus C1 s) with (Copp (Cminus s C1)) by ring;
        rewrite Hc; unfold Copp, C0; apply Ceq; cbn [Re Im]; ring).
  replace (Cmul (Cminus C1 (Cpw 2 (Cminus C1 s))) (zetaC s H0 H1))
    with (Cadd (Cminus G (Cmul (Cmul (RtoC 2) (Cpw 2 (Copp s))) G))
               (Cmul (Cadd C0 (Cminus (Cmul (RtoC 2) (Cpw 2 (Copp s))) C1))
                     (Cinv (Cminus C1 s)))).
  2:{ unfold zetaC. fold G. rewrite <- ctwo_z2. field. split; [ exact Hsm1 | exact H1 ]. }
  apply (CUn_cv_ext (fun M => Cadd
     (Cminus (Cpsum (gtermC s) (2 * M + 1))
             (Cmul (Cmul (RtoC 2) (Cpw 2 (Copp s))) (Cpsum (gtermC s) M)))
     (Cmul (Cadd (Copp (cint_diff s (2 * M + 2)))
                 (Cminus (Cmul (RtoC 2) (Cpw 2 (Copp s))) C1)) (Cinv (Cminus C1 s))))).
  - intro M. symmetry. apply ceta_partial_decomp; exact H1.
  - apply CUn_cv_plus.
    + apply CUn_cv_minus.
      * apply (CUn_cv_subseq (Cpsum (gtermC s)) G (fun M => (2 * M + 1)%nat));
          [ intro M; lia | exact HG ].
      * apply (CUn_cv_scal (Cmul (RtoC 2) (Cpw 2 (Copp s))) (Cpsum (gtermC s)) G HG).
    + apply (CUn_cv_scal_r (Cinv (Cminus C1 s))
               (fun M => Cadd (Copp (cint_diff s (2 * M + 2)))
                             (Cminus (Cmul (RtoC 2) (Cpw 2 (Copp s))) C1))
               (Cadd C0 (Cminus (Cmul (RtoC 2) (Cpw 2 (Copp s))) C1))).
      apply CUn_cv_plus.
      * replace C0 with (Copp C0) by (unfold Copp, C0; apply Ceq; cbn [Re Im]; ring).
        apply CUn_cv_opp.
        apply (CUn_cv_subseq (fun n => cint_diff s n) C0 (fun M => (2 * M + 2)%nat));
          [ intro M; lia | apply cint_diff_cv0; assumption ].
      * apply CUn_cv_const.
Qed.

Print Assumptions ceta_zeta_cont_strip.

(* ===== payoff: a zeta zero as the complex alternating sum collapsing to 0 ===== *)
Definition ceta_partial (s : C) (M : nat) : C :=
  Cpsum (fun i => Cmul (RtoC ((-1) ^ i)) (cterm s i)) (2 * M + 1).

Definition ccollapses (u : nat -> C) : Prop := CUn_cv u C0.

Theorem ceta_zero_iff_collapse : forall s (H0 : 0 < Re s) (H1 : Cminus C1 s <> C0),
  (Cmul (Cminus C1 (Cpw 2 (Cminus C1 s))) (zetaC s H0 H1) = C0
   <-> ccollapses (ceta_partial s)).
Proof.
  intros s H0 H1. unfold ccollapses, ceta_partial. split.
  - intro Hz. pose proof (ceta_zeta_cont_strip s H0 H1) as H. rewrite Hz in H. exact H.
  - intro Hc. pose proof (ceta_zeta_cont_strip s H0 H1) as H.
    exact (CUn_cv_unique _ _ _ H Hc).
Qed.

Corollary ceta_collapse_iff_zeta_zero : forall s (H0 : 0 < Re s) (H1 : Cminus C1 s <> C0),
  Cminus C1 (Cpw 2 (Cminus C1 s)) <> C0 ->
  (ccollapses (ceta_partial s) <-> zetaC s H0 H1 = C0).
Proof.
  intros s H0 H1 Hfac. rewrite <- (ceta_zero_iff_collapse s H0 H1). split.
  - intro Hz.
    assert (Hstep : Cmul (Cmul (Cinv (Cminus C1 (Cpw 2 (Cminus C1 s))))
                               (Cminus C1 (Cpw 2 (Cminus C1 s)))) (zetaC s H0 H1) = C0).
    { transitivity (Cmul (Cinv (Cminus C1 (Cpw 2 (Cminus C1 s))))
                         (Cmul (Cminus C1 (Cpw 2 (Cminus C1 s))) (zetaC s H0 H1))).
      - ring.
      - rewrite Hz. ring. }
    rewrite (Cinv_l _ Hfac) in Hstep.
    replace (Cmul C1 (zetaC s H0 H1)) with (zetaC s H0 H1) in Hstep by ring.
    exact Hstep.
  - intro Hz. rewrite Hz. ring.
Qed.

(* ===== the critical line: s = 1/2 + i t, Re s = 1/2 ===== *)
Definition crit_s (t : R) : C := mkC (/ 2) t.

Lemma crit_Re : forall t, Re (crit_s t) = / 2. Proof. reflexivity. Qed.
Lemma crit_pos : forall t, 0 < Re (crit_s t). Proof. intro t. rewrite crit_Re; lra. Qed.

Lemma crit_H1 : forall t, Cminus C1 (crit_s t) <> C0.
Proof.
  intros t Hc. apply (f_equal Re) in Hc.
  rewrite Re_Cminus, crit_Re in Hc. unfold C1, C0 in Hc; cbn [Re] in Hc. lra.
Qed.

(* the first-prime factor 1 - 2^{1-s} is NON-zero on the whole critical line:
   |2^{1-s}| = 2^{Re(1-s)} = 2^{1/2} = sqrt 2 <> 1. *)
Lemma crit_factor_ne0 : forall t, Cminus C1 (Cpw 2 (Cminus C1 (crit_s t))) <> C0.
Proof.
  intros t Hc.
  assert (Hval : Cpw 2 (Cminus C1 (crit_s t)) = C1).
  { transitivity (Cminus C1 (Cminus C1 (Cpw 2 (Cminus C1 (crit_s t))))).
    - ring.
    - rewrite Hc. ring. }
  assert (Hmod : Cmod (Cpw 2 (Cminus C1 (crit_s t))) = sqrt 2).
  { rewrite Cpw_mod, Re_Cminus, crit_Re. unfold C1; cbn [Re].
    replace (1 - / 2) with (/ 2) by lra. apply Rpower_sqrt; lra. }
  rewrite Hval in Hmod.
  change C1 with (RtoC 1) in Hmod. rewrite Cmod_RtoC, Rabs_R1 in Hmod.
  assert (sqrt 2 > 1)
    by (rewrite <- sqrt_1; apply sqrt_lt_1; lra). lra.
Qed.

(* THE CAPSTONE ON THE CRITICAL LINE.  For every t, a nontrivial zero of zeta at
   1/2 + i t is EXACTLY the complex alternating sum sum (-1)^i (i+1)^{-(1/2+it)}
   collapsing to 0 at infinity -- the same "limit -> 0" collapse as (x+/-y)/2^n.
   (Whether such a t EXISTS, and whether ALL nontrivial zeros have this form (RH),
   is NOT decided here -- only the equivalence on the line is proved.) *)
Theorem crit_line_zero_iff_collapse : forall t H0 H1,
  ccollapses (ceta_partial (crit_s t)) <-> zetaC (crit_s t) H0 H1 = C0.
Proof.
  intros t H0 H1. apply ceta_collapse_iff_zeta_zero. apply crit_factor_ne0.
Qed.

Print Assumptions ceta_zero_iff_collapse.
Print Assumptions crit_line_zero_iff_collapse.
