(* ================================================================= *)
(*  CLHolo3.v  --  L(s,chi) is HOLOMORPHIC on Re s > 0.               *)
(*                                                                    *)
(*  The Morera/Weierstrass assembly.  CLHolo1 gives entire partial     *)
(*  sums, CLHolo2 gives convergence uniform on boxes; this feeds them  *)
(*  to CMoreraDisk.unif_limit_holo_disk and transports the result      *)
(*  back to the point.                                                *)
(*                                                                    *)
(*  Simpler than the zeta extension (ZetaEMExtHolo): there the         *)
(*  approximants had a pole at s = 1 and the clamp had to be threaded  *)
(*  through the PARTIAL SUMS as well as the limit.  Here each partial  *)
(*  sum is entire, so the clamp is needed only for the limit function, *)
(*  whose domain is a half-plane.                                     *)
(*                                                                    *)
(*  This is the brick L(1+it,chi) <> 0 needs: the sequence argument    *)
(*  bounds |L(sigma+it0)| = |L(sigma+it0) - L(1+it0)| <= C (sigma - 1) *)
(*  at a putative zero, which is differentiability AT the line.        *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia ZArith Znumtheory List
        FunctionalExtensionality.
Require Import ComplexField Cmodulus CexpFull CPower CPowMul CSeries CDeriv
        Holomorphic CIntegral2 CSegInt CHoloCalculus RootsOfUnity ZmodOrder
        DirichletModP CZetaTerm CCauchyAnalytic CClampCont PerronRemovable
        CMorera CMoreraDisk CEulerProductConv EulerProductR
        CharModulus CTwistedCoeff CLSeries CCharSumBound CLContinue
        CLHolo1 CLHolo2 CPeelAtCentre ZetaEMExtHolo CZeroListFactor.
Import ListNotations.
Open Scope R_scope.

Section Weier.

Variable p g A : nat.
Hypothesis Hp : prime (Z.of_nat p).
Hypothesis Hg : (1 <= g <= p - 1)%nat.
Hypothesis Hord : ord p g = (p - 1)%nat.
Hypothesis HA : (0 < A < p - 1)%nat.

Variable s0 : C.
Hypothesis Hs0 : 0 < Re s0.

Definition lamL : R := Re s0 / 16.
Definition sig0L : R := 3 * Re s0 / 4.
Definition MboxL : R := Cmod s0 + Re s0 / 4.
Definition shwL (w : C) : C := Cadd s0 (Cmul (RtoC lamL) (clampw 8 C0 w)).

Lemma lamL_pos : 0 < lamL. Proof. unfold lamL; lra. Qed.
Lemma sig0L_pos : 0 < sig0L. Proof. unfold sig0L; lra. Qed.

Lemma shwL_near : forall w, Cmod (Cminus (shwL w) s0) <= Re s0 / 4.
Proof.
  intro w. unfold shwL.
  replace (Cminus (Cadd s0 (Cmul (RtoC lamL) (clampw 8 C0 w))) s0)
    with (Cmul (RtoC lamL) (clampw 8 C0 w)) by ring.
  rewrite Cmod_mul, Cmod_RtoC, Rabs_pos_eq by (pose proof lamL_pos; lra).
  pose proof (clamp8_mod w) as Hc.
  pose proof (Cmod_nonneg (clampw 8 C0 w)) as Hc0.
  unfold lamL. nra.
Qed.

Lemma shwL_re : forall w, sig0L <= Re (shwL w).
Proof.
  intro w. pose proof (shwL_near w) as H.
  pose proof (Cmod_Re_le (Cminus (shwL w) s0)) as HR.
  rewrite Re_Cminus in HR.
  pose proof (Rabs_le_both _ _ (Rle_trans _ _ _ HR H)) as [Hlo _].
  unfold sig0L. lra.
Qed.

Lemma shwL_mod : forall w, Cmod (shwL w) <= MboxL.
Proof.
  intro w. pose proof (shwL_near w) as H.
  pose proof (Cmod_triangle (Cminus (shwL w) s0) s0) as HT.
  replace (Cadd (Cminus (shwL w) s0) s0) with (shwL w) in HT by ring.
  unfold MboxL. lra.
Qed.

Lemma shwL_re_pos : forall w, 0 < Re (shwL w).
Proof. intro w. pose proof (shwL_re w). pose proof sig0L_pos. lra. Qed.

Lemma shwL_lip : forall w1 w2,
  Cmod (Cminus (shwL w1) (shwL w2)) <= 2 * lamL * Cmod (Cminus w1 w2).
Proof.
  intros w1 w2. unfold shwL.
  rewrite (Cmod_shift_scal s0 lamL _ _ ltac:(pose proof lamL_pos; lra)).
  pose proof (clampw_lipschitz 8 C0 w1 w2 ltac:(lra)) as HL.
  pose proof lamL_pos. nra.
Qed.

(* the approximants and their limit, in the clamped coordinate *)
Definition fnwL (n : nat) (w : C) : C := Lpart p g A n (shwL w).
Definition gwL (w : C) : C := LFun p g A Hp Hg Hord HA (shwL w).

Lemma fnwL_ptcont : forall n, ptcont (fnwL n).
Proof.
  intros n z.
  apply (ptcont_at_comp_lip (Lpart p g A n) shwL (2 * lamL) z);
    [ pose proof lamL_pos; lra | apply shwL_lip | ].
  intros eps Heps.
  destruct (Lpart_holo_ex p g A n (shwL z)) as [d Hd].
  destruct (is_Cderiv_cont (Lpart p g A n) (shwL z) d Hd eps Heps)
    as [del [Hdel HD]].
  exists del. split; [ exact Hdel | ]. intros z' Hz'.
  pose proof (HD (Cminus z' (shwL z)) Hz') as H.
  replace (Cadd (shwL z) (Cminus z' (shwL z))) with z' in H by ring. exact H.
Qed.

Lemma fnwL_CcontC : forall n, CcontC (fnwL n).
Proof. intro n. apply ptcont_CcontC. apply fnwL_ptcont. Qed.

(* the uniform estimate, transported into the w-coordinate *)
Lemma unifL : forall eps, 0 < eps -> exists N, forall n, (N <= n)%nat ->
  forall w, Cmod (Cminus (fnwL n w) (gwL w)) <= eps.
Proof.
  intros eps Heps.
  pose proof sig0L_pos as Hs.
  destruct (Ebound_cv0 (INR p) sig0L MboxL Hs
              ltac:(apply lt_0_INR; destruct Hp; lia) eps Heps) as [N0 HN0].
  exists (S N0). intros n Hn w.
  destruct n as [| m]; [ lia | ].
  assert (Hm : (N0 <= m)%nat) by lia.
  eapply Rle_trans.
  - unfold fnwL, gwL, Lpart.
    apply (L_unif_tail p g A Hp Hg Hord HA sig0L MboxL Hs (shwL w)
             (shwL_re w) (shwL_mod w) m).
  - specialize (HN0 m Hm). unfold R_dist in HN0.
    rewrite Rminus_0_r in HN0.
    eapply Rle_trans; [ apply Rle_abs | left; exact HN0 ].
Qed.

Lemma gwL_ptcont : ptcont gwL.
Proof.
  intros z eps Heps.
  apply (unif_limit_ptcont fnwL gwL); [ | | exact Heps ].
  - intros n z1 e He. exact (fnwL_ptcont n z1 e He).
  - intro z0. exists 1. split; [ lra | ].
    intros e He. destruct (unifL e He) as [N HN].
    exists N. intros n Hn w _. exact (HN n Hn w).
Qed.

Lemma gwL_CcontC : CcontC gwL.
Proof. apply ptcont_CcontC. apply gwL_ptcont. Qed.

(* holomorphy of the approximants inside the clamp radius *)
Definition afnL (n : nat) (w : C) : C :=
  Lpart p g A n (Cadd s0 (Cmul (RtoC lamL) w)).

Lemma afnL_holo : forall n w, exists d, is_Cderiv (afnL n) w d.
Proof.
  intros n w.
  destruct (Lpart_holo_ex p g A n (Cadd (Cmul (RtoC lamL) w) s0)) as [d Hd].
  eexists. unfold afnL.
  apply (is_Cderiv_ext
           (fun v => Lpart p g A n (Cadd (Cmul (RtoC lamL) v) s0))).
  - intro v; f_equal; ring.
  - apply (Cderiv_comp_affine (Lpart p g A n) (RtoC lamL) s0 w d). exact Hd.
Qed.

Lemma fnwL_eq_afnL : forall n w, Cmod w < 4 -> fnwL n w = afnL n w.
Proof.
  intros n w Hw. unfold fnwL, afnL, shwL. rewrite (clamp8_id w Hw). reflexivity.
Qed.

Lemma fnwL_holo_disk : forall n z, Cmod z < 3 ->
  exists d, is_Cderiv (fnwL n) z d.
Proof.
  intros n z Hz.
  destruct (afnL_holo n z) as [d Hd]. exists d.
  apply (is_Cderiv_congr (fnwL n) (afnL n) z d 1).
  - lra.
  - intros z' Hz'.
    assert (Hz'4 : Cmod z' < 4).
    { pose proof (Cmod_triangle (Cminus z' z) z) as HT.
      replace (Cadd (Cminus z' z) z) with z' in HT by ring. lra. }
    apply fnwL_eq_afnL; exact Hz'4.
  - exact Hd.
Qed.

Lemma gwL_holo0 : exists d, is_Cderiv gwL C0 d.
Proof.
  apply (unif_limit_holo_disk fnwL gwL 3).
  - lra.
  - exact fnwL_CcontC.
  - intros n z Hz. apply fnwL_holo_disk; exact Hz.
  - exact gwL_CcontC.
  - intros z eps Heps. exact (gwL_ptcont z eps Heps).
  - intros eps Heps. destruct (unifL eps Heps) as [N HN].
    exists N. intros n Hn w _. exact (HN n Hn w).
  - rewrite (proj2 (Cmod0 C0) eq_refl). lra.
Qed.

Theorem LFun_holo_at : exists d,
  is_Cderiv (LFun p g A Hp Hg Hord HA) s0 d.
Proof.
  pose proof lamL_pos as Hl.
  destruct gwL_holo0 as [d Hd].
  assert (Hli : lamL <> 0) by lra.
  set (aa := RtoC (/ lamL)).
  set (bb := Copp (Cmul (RtoC (/ lamL)) s0)).
  assert (Hz0 : Cadd (Cmul aa s0) bb = C0) by (unfold aa, bb; ring).
  assert (Haff : is_Cderiv (fun v => gwL (Cadd (Cmul aa v) bb)) s0 (Cmul aa d)).
  { apply (Cderiv_comp_affine gwL aa bb s0 d). rewrite Hz0. exact Hd. }
  exists (Cmul aa d).
  apply (is_Cderiv_congr (LFun p g A Hp Hg Hord HA)
           (fun v => gwL (Cadd (Cmul aa v) bb)) s0 (Cmul aa d) (4 * lamL)).
  - lra.
  - intros s' Hs'.
    assert (Hmod : Cmod (Cadd (Cmul aa s') bb) < 4).
    { replace (Cadd (Cmul aa s') bb)
        with (Cmul (RtoC (/ lamL)) (Cminus s' s0)) by (unfold aa, bb; ring).
      rewrite Cmod_mul, Cmod_RtoC, Rabs_pos_eq
        by (left; apply Rinv_0_lt_compat; lra).
      apply (Rmult_lt_reg_l lamL); [ lra | ].
      replace (lamL * (/ lamL * Cmod (Cminus s' s0)))
        with (Cmod (Cminus s' s0)) by (field; lra).
      lra. }
    assert (Hll : Cmul (RtoC lamL) (RtoC (/ lamL)) = C1)
      by (apply Ceq; cbn; [ field; exact Hli | ring ]).
    assert (HE : Cadd s0 (Cmul (RtoC lamL) (Cadd (Cmul aa s') bb)) = s').
    { unfold aa, bb.
      replace (Cadd s0 (Cmul (RtoC lamL)
                 (Cadd (Cmul (RtoC (/ lamL)) s')
                       (Copp (Cmul (RtoC (/ lamL)) s0)))))
        with (Cadd s0 (Cmul (Cmul (RtoC lamL) (RtoC (/ lamL)))
                            (Cminus s' s0))) by ring.
      rewrite Hll. ring. }
    unfold gwL, shwL. rewrite (clamp8_id _ Hmod), HE. reflexivity.
  - exact Haff.
Qed.

End Weier.

(* ================================================================= *)
(*  L IS HOLOMORPHIC ON Re s > 0                                      *)
(* ================================================================= *)
Theorem LFun_holo : forall p g A
  (Hp : prime (Z.of_nat p)) (Hg : (1 <= g <= p - 1)%nat)
  (Hord : ord p g = (p - 1)%nat) (HA : (0 < A < p - 1)%nat),
  forall s, 0 < Re s -> exists d, is_Cderiv (LFun p g A Hp Hg Hord HA) s d.
Proof.
  intros p g A Hp Hg Hord HA s Hs.
  exact (LFun_holo_at p g A Hp Hg Hord HA s Hs).
Qed.

Print Assumptions LFun_holo.

(* ================================================================= *)
(*  END CLHolo3.v                                                     *)
(* ================================================================= *)
