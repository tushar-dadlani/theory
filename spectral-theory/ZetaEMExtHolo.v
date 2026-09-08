(* ================================================================= *)
(*  ZetaEMExtHolo.v  --  holomorphy of the trapezoid terms in s.       *)
(*                                                                    *)
(*  Step one of Bfn1_holo: each htermC (. ) n is holomorphic in s away *)
(*  from s = 1.  htermC is built from exactly the atoms CZetaDeriv     *)
(*  already differentiates for gtermC --                               *)
(*                                                                    *)
(*     gC s x = x^{-s}                     (Cpw o affine)              *)
(*     GC s x = x^{1-s} / (1-s)            (product of Cpw o affine    *)
(*                                          and Cinv o affine)         *)
(*                                                                    *)
(*  so this is CZetaDeriv.gtermC_holo's proof with the trapezoid       *)
(*  combination in place of the rectangle one.  The 1/(1-s) is the     *)
(*  only source of the s <> 1 side condition.                          *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import ComplexField Cmodulus CexpFull CPower Holomorphic CDeriv
        CZetaTerm CZetaDeriv CSeries CIntegral2 CSegInt CHoloCalculus
        ZetaTrap ZetaEM ZetaEMExt ZetaStripBound CPeelAtCentre
        CCauchyAnalytic CClampCont PerronRemovable CMorera CMoreraDisk
        CZeroListFactor.
From Stdlib Require Import FunctionalExtensionality.
Open Scope R_scope.

(* x^{-s}, holomorphic in s for x > 0 *)
Lemma gC_holo_s : forall (x : R) (s : C), 0 < x ->
  exists d, is_Cderiv (fun w => gC w x) s d.
Proof.
  intros x s Hx; eexists; unfold gC.
  apply (is_Cderiv_ext (fun w => Cpw x (Cadd (Cmul (Copp C1) w) C0))).
  - intro w; f_equal; ring.
  - apply Cderiv_comp_affine; apply Cpw_deriv; exact Hx.
Qed.

(* x^{1-s}/(1-s), holomorphic in s for x > 0 away from s = 1 *)
Lemma GC_holo_s : forall (x : R) (s : C), 0 < x -> Cminus C1 s <> C0 ->
  exists d, is_Cderiv (fun w => GC w x) s d.
Proof.
  intros x s Hx Hs; eexists; unfold GC.
  apply Cderiv_mul.
  - apply (is_Cderiv_ext (fun w => Cpw x (Cadd (Cmul (Copp C1) w) C1))).
    + intro w; f_equal; ring.
    + apply Cderiv_comp_affine; apply Cpw_deriv; exact Hx.
  - apply (is_Cderiv_ext (fun w => Cinv (Cadd (Cmul (Copp C1) w) C1))).
    + intro w; f_equal; ring.
    + apply Cderiv_comp_affine; apply Cderiv_inv;
        replace (Cadd (Cmul (Copp C1) s) C1) with (Cminus C1 s) by ring; exact Hs.
Qed.

(* the trapezoid defect, holomorphic in s away from s = 1 *)
Theorem htermC_holo_s : forall n s, Cminus C1 s <> C0 ->
  exists d, is_Cderiv (fun w => htermC w n) s d.
Proof.
  intros n s Hs.
  assert (H1 : 0 < INR (S n)) by (apply lt_0_INR; lia).
  assert (H2 : 0 < INR (S (S n))) by (apply lt_0_INR; lia).
  destruct (gC_holo_s (INR (S n)) s H1) as [d1 Hd1].
  destruct (gC_holo_s (INR (S (S n))) s H2) as [d2 Hd2].
  destruct (GC_holo_s (INR (S (S n))) s H2 Hs) as [e2 He2].
  destruct (GC_holo_s (INR (S n)) s H1 Hs) as [e1 He1].
  eexists; unfold htermC.
  apply Cderiv_minus.
  - apply (Cderiv_mul (fun _ => RtoC (/ 2))
             (fun w => Cadd (gC w (INR (S n))) (gC w (INR (S (S n)))))).
    + apply Cderiv_const.
    + apply Cderiv_add; [ exact Hd1 | exact Hd2 ].
  - apply Cderiv_minus; [ exact He2 | exact He1 ].
Qed.

(* ================================================================= *)
(*  2.  general machinery for the Weierstrass step                    *)
(* ================================================================= *)

Lemma Rabs_le_both : forall y a, Rabs y <= a -> - a <= y <= a.
Proof.
  intros y a H. split.
  - pose proof (Rle_abs (- y)) as H1. rewrite Rabs_Ropp in H1. lra.
  - pose proof (Rle_abs y). lra.
Qed.

Lemma exp_mono_le : forall a b, a <= b -> exp a <= exp b.
Proof.
  intros a b H. destruct (Rle_lt_or_eq_dec a b H) as [Hl | He];
    [ left; apply exp_increasing; exact Hl | rewrite He; apply Rle_refl ].
Qed.

(* x^{-p} is antitone in the EXPONENT for x >= 1 (Rpow_negexp_anti is
   antitonicity in the BASE, which is not what the majorant needs) *)
Lemma Rpower_negexp_mono : forall x p q, 1 <= x -> p <= q ->
  Rpower x (- q) <= Rpower x (- p).
Proof.
  intros x p q Hx Hpq. unfold Rpower. apply exp_mono_le.
  assert (Hl : 0 <= ln x).
  { rewrite <- ln_1. destruct (Rle_lt_or_eq_dec 1 x Hx) as [Hlt | He];
      [ left; apply ln_increasing; lra | rewrite <- He; apply Rle_refl ]. }
  nra.
Qed.

(* the Weierstrass M-test, in the form the uniform estimate needs:
   the distance from a partial sum to the limit is at most the
   majorant's own tail *)
Lemma Cseries_tail_bound : forall (a : nat -> C) (b : nat -> R) (Sl : C) (T : R),
  (forall k, Cmod (a k) <= b k) ->
  Cseries_cv a Sl ->
  Un_cv (sum_f_R0 b) T ->
  forall n, Cmod (Cminus Sl (Cpsum a n)) <= T - sum_f_R0 b n.
Proof.
  intros a b Sl T Hab HS HT n.
  (* the finite increments are controlled *)
  assert (Hstep : forall j, Cmod (Cminus (Cpsum a (n + j)) (Cpsum a n))
                            <= sum_f_R0 b (n + j) - sum_f_R0 b n).
  { induction j as [| j IH].
    - rewrite Nat.add_0_r.
      replace (Cminus (Cpsum a n) (Cpsum a n)) with C0 by ring.
      rewrite (proj2 (Cmod0 C0) eq_refl). lra.
    - assert (Hidx : (n + S j)%nat = S (n + j)) by lia.
      rewrite Hidx. cbn [Cpsum sum_f_R0].
      replace (Cminus (Cadd (Cpsum a (n + j)) (a (S (n + j)))) (Cpsum a n))
        with (Cadd (Cminus (Cpsum a (n + j)) (Cpsum a n)) (a (S (n + j))))
        by ring.
      eapply Rle_trans; [ apply Cmod_triangle | ].
      pose proof (Hab (S (n + j))). lra. }
  (* pass to the limit in j *)
  apply Rle_cv_lim
    with (Un := fun j => Cmod (Cminus (Cpsum a (n + j)) (Cpsum a n)))
         (Vn := fun j => sum_f_R0 b (n + j) - sum_f_R0 b n).
  - exact Hstep.
  - apply CUn_cv_Cmod.
    intros eps Heps. destruct (HS eps Heps) as [N HN].
    exists N. intros j Hj.
    replace (Cminus (Cminus (Cpsum a (n + j)) (Cpsum a n))
                    (Cminus Sl (Cpsum a n)))
      with (Cminus (Cpsum a (n + j)) Sl) by ring.
    apply HN. lia.
  - intros eps Heps. destruct (HT eps Heps) as [N HN].
    exists N. intros j Hj. unfold R_dist in *.
    replace (sum_f_R0 b (n + j) - sum_f_R0 b n - (T - sum_f_R0 b n))
      with (sum_f_R0 b (n + j) - T) by ring.
    apply HN. lia.
Qed.

(* ---- pointwise continuity helpers ---- *)

Lemma ptcont_at_add : forall F G z,
  ptcont_at F z -> ptcont_at G z ->
  ptcont_at (fun w => Cadd (F w) (G w)) z.
Proof.
  intros F G z HF HG eps Heps.
  destruct (HF (eps / 2) ltac:(lra)) as [d1 [Hd1 H1]].
  destruct (HG (eps / 2) ltac:(lra)) as [d2 [Hd2 H2]].
  exists (Rmin d1 d2). split; [ apply Rmin_pos; assumption | ].
  intros z' Hz'.
  assert (Ha : Cmod (Cminus z' z) < d1)
    by (eapply Rlt_le_trans; [ exact Hz' | apply Rmin_l ]).
  assert (Hb : Cmod (Cminus z' z) < d2)
    by (eapply Rlt_le_trans; [ exact Hz' | apply Rmin_r ]).
  replace (Cminus (Cadd (F z') (G z')) (Cadd (F z) (G z)))
    with (Cadd (Cminus (F z') (F z)) (Cminus (G z') (G z))) by ring.
  eapply Rle_lt_trans; [ apply Cmod_triangle | ].
  pose proof (H1 z' Ha); pose proof (H2 z' Hb). lra.
Qed.

Lemma ptcont_at_ext : forall F G z,
  (forall w, F w = G w) -> ptcont_at G z -> ptcont_at F z.
Proof.
  intros F G z HE HG eps Heps.
  destruct (HG eps Heps) as [d [Hd HD]].
  exists d. split; [ exact Hd | ]. intros z' Hz'.
  rewrite !HE. apply HD; exact Hz'.
Qed.

(* composition with a Lipschitz inner map *)
Lemma ptcont_at_comp_lip : forall (F h : C -> C) (L : R) (z : C), 0 < L ->
  (forall w1 w2, Cmod (Cminus (h w1) (h w2)) <= L * Cmod (Cminus w1 w2)) ->
  ptcont_at F (h z) ->
  ptcont_at (fun w => F (h w)) z.
Proof.
  intros F h L z HL Hlip HF eps Heps.
  destruct (HF eps Heps) as [d [Hd HD]].
  exists (d / L). split; [ apply Rdiv_lt_0_compat; assumption | ].
  intros z' Hz'. apply HD.
  eapply Rle_lt_trans; [ apply Hlip | ].
  apply (Rmult_lt_reg_l (/ L)); [ apply Rinv_0_lt_compat; exact HL | ].
  replace (/ L * (L * Cmod (Cminus z' z))) with (Cmod (Cminus z' z))
    by (field; lra).
  replace (/ L * d) with (d / L) by (field; lra). exact Hz'.
Qed.

(* ================================================================= *)
(*  3.  the Weierstrass assembly, at a fixed centre s0                *)
(*                                                                    *)
(*  The clamp is threaded through the PARTIAL SUMS as well as the     *)
(*  limit.  It has to be: CcontC is a global property (composition    *)
(*  with every continuous path), and Cpsum (htermC .) n has a pole at *)
(*  s = 1, so it is not globally CcontC on its own.  With the clamp,  *)
(*  every evaluation lands in a closed disk about s0 that avoids 1    *)
(*  and sits inside Re s > -1, so the uniform estimate is GLOBAL in w *)
(*  -- which is also what makes unif_limit_ptcont's local hypothesis  *)
(*  trivial to supply.                                                *)
(* ================================================================= *)

Section Weier.

Variable s0 : C.
Hypothesis Hs0re : -1 < Re s0.
Hypothesis Hs0ne : Cminus C1 s0 <> C0.

Definition qrad : R := Rmin ((Re s0 + 1) / 2) (Cmod (Cminus s0 C1) / 2).
Definition lamw : R := qrad / 8.
Definition sigl : R := Re s0 - (Re s0 + 1) / 4.
Definition shw (w : C) : C := Cadd s0 (Cmul (RtoC lamw) (clampw 8 C0 w)).

Lemma s0_sub1_ne : Cminus s0 C1 <> C0.
Proof. apply sub1_ne0; exact Hs0ne. Qed.

Lemma qrad_pos : 0 < qrad.
Proof.
  unfold qrad. apply Rmin_pos; [ lra | ].
  pose proof (Cmod_pos_of_ne0 (Cminus s0 C1) s0_sub1_ne). lra.
Qed.

Lemma lamw_pos : 0 < lamw.
Proof. unfold lamw. pose proof qrad_pos. lra. Qed.

Lemma sigl_gt : -1 < sigl.
Proof. unfold sigl. lra. Qed.

Lemma clamp8_mod : forall w, Cmod (clampw 8 C0 w) <= 4.
Proof.
  intro w. pose proof (clampw_mod 8 C0 ltac:(lra) w) as H.
  unfold rho in H. rewrite (proj2 (Cmod0 C0) eq_refl) in H. lra.
Qed.

Lemma clamp8_id : forall w, Cmod w < 4 -> clampw 8 C0 w = w.
Proof.
  intros w Hw. apply clampw_id.
  rewrite (proj2 (Cmod0 C0) eq_refl).
  replace (Cminus w C0) with w by ring. lra.
Qed.

Lemma shw_near : forall w, Cmod (Cminus (shw w) s0) <= qrad / 2.
Proof.
  intro w. unfold shw.
  replace (Cminus (Cadd s0 (Cmul (RtoC lamw) (clampw 8 C0 w))) s0)
    with (Cmul (RtoC lamw) (clampw 8 C0 w)) by ring.
  rewrite Cmod_mul, Cmod_RtoC, Rabs_pos_eq by (pose proof lamw_pos; lra).
  pose proof (clamp8_mod w) as Hc.
  pose proof (Cmod_nonneg (clampw 8 C0 w)) as Hc0.
  pose proof qrad_pos as Hq. unfold lamw. nra.
Qed.

Lemma shw_re : forall w, sigl <= Re (shw w).
Proof.
  intro w. pose proof (shw_near w) as H.
  pose proof (Cmod_Re_le (Cminus (shw w) s0)) as HR.
  rewrite Re_Cminus in HR.
  pose proof (Rabs_le_both _ _ (Rle_trans _ _ _ HR H)) as [Hlo _].
  unfold sigl, qrad in *.
  pose proof (Rmin_l ((Re s0 + 1) / 2) (Cmod (Cminus s0 C1) / 2)). lra.
Qed.

Lemma shw_ne1 : forall w, Cminus C1 (shw w) <> C0.
Proof.
  intro w.
  assert (Hlow : Cmod (Cminus s0 C1) / 2 <= Cmod (Cminus (shw w) C1)).
  { pose proof (Cmod_rev (Cminus s0 C1) (Cminus (shw w) C1)) as HT.
    replace (Cminus (Cminus s0 C1) (Cminus (shw w) C1))
      with (Cminus s0 (shw w)) in HT by ring.
    assert (HE : Cmod (Cminus s0 (shw w)) = Cmod (Cminus (shw w) s0))
      by (replace (Cminus s0 (shw w)) with (Copp (Cminus (shw w) s0)) by ring;
          apply Cmod_opp').
    rewrite HE in HT.
    pose proof (shw_near w) as Hn.
    pose proof (Rabs_le_both _ _ HT) as [_ Hhi].
    unfold qrad in Hn.
    pose proof (Cmod_nonneg (Cminus s0 C1)).
    pose proof (Rmin_r ((Re s0 + 1) / 2) (Cmod (Cminus s0 C1) / 2)). lra. }
  pose proof (Cmod_pos_of_ne0 (Cminus s0 C1) s0_sub1_ne) as Hp.
  intro Hc.
  assert (Hz : Cminus (shw w) C1 = C0).
  { replace (Cminus (shw w) C1) with (Copp (Cminus C1 (shw w))) by ring.
    rewrite Hc. apply Ceq; cbn; ring. }
  assert (Hz0 : Cmod (Cminus (shw w) C1) = 0)
    by (rewrite Hz; apply (proj2 (Cmod0 C0) eq_refl)).
  lra.
Qed.

(* ---- the fixed majorant ---- *)
Definition KM : R := / 6 * ((Cmod s0 + qrad) * (Cmod s0 + qrad + 1)).
Definition bmaj (k : nat) : R := KM * Rpower (INR (S k)) (- (sigl + 2)).

Lemma KM_bound : forall w, Kh (shw w) <= KM.
Proof.
  intro w. pose proof (shw_near w) as Hn. pose proof qrad_pos as Hq.
  assert (H1 : Cmod (shw w) <= Cmod s0 + qrad).
  { pose proof (Cmod_triangle (Cminus (shw w) s0) s0) as HT.
    replace (Cadd (Cminus (shw w) s0) s0) with (shw w) in HT by ring. lra. }
  assert (H2 : Cmod (Cadd (shw w) C1) <= Cmod s0 + qrad + 1).
  { pose proof (Cmod_triangle (shw w) C1) as HT. rewrite Cmod_one in HT. lra. }
  unfold Kh, KM.
  pose proof (Cmod_nonneg (shw w)); pose proof (Cmod_nonneg (Cadd (shw w) C1)).
  pose proof (Cmod_nonneg s0). nra.
Qed.

Lemma bmaj_bound : forall w k, Cmod (htermC (shw w) k) <= bmaj k.
Proof.
  intros w k.
  pose proof (Kh_htermC_bound (shw w) k ltac:(pose proof (shw_re w);
    pose proof sigl_gt; lra) (shw_ne1 w)) as H.
  assert (Hx : 1 <= INR (S k)) by (rewrite <- INR_1; apply le_INR; lia).
  assert (Hp : Rpower (INR (S k)) (- (Re (shw w) + 2))
               <= Rpower (INR (S k)) (- (sigl + 2))).
  { apply Rpower_negexp_mono; [ exact Hx | pose proof (shw_re w); lra ]. }
  pose proof (KM_bound w) as HK. pose proof (Kh_nonneg (shw w)) as HK0.
  assert (Hpp : 0 < Rpower (INR (S k)) (- (sigl + 2)))
    by (unfold Rpower; apply exp_pos).
  unfold bmaj. nra.
Qed.

Lemma Tmaj_ex : { T | Un_cv (sum_f_R0 bmaj) T }.
Proof.
  destruct (pseries_cv (sigl + 2) ltac:(pose proof sigl_gt; lra)) as [T HT].
  exists (KM * T). unfold bmaj.
  replace (sum_f_R0 (fun k => KM * Rpower (INR (S k)) (- (sigl + 2))))
    with (fun N => KM * sum_f_R0 (fun k => Rpower (INR (S k)) (- (sigl + 2))) N).
  - apply (CV_mult (fun _ => KM)
             (sum_f_R0 (fun k => Rpower (INR (S k)) (- (sigl + 2)))) KM T);
      [ apply Un_cv_const | exact HT ].
  - apply functional_extensionality; intro N.
    rewrite (scal_sum (fun k => Rpower (INR (S k)) (- (sigl + 2))) N KM).
    apply sum_eq; intros i _; ring.
Qed.

Definition Tmaj : R := proj1_sig Tmaj_ex.

(* ---- the approximants and their limit ---- *)
Definition fnw (n : nat) (w : C) : C := Cpsum (fun k => htermC (shw w) k) n.
Definition gw (w : C) : C := HsumT (shw w).

Lemma gw_cv : forall w, Cseries_cv (fun k => htermC (shw w) k) (gw w).
Proof.
  intro w. unfold gw.
  apply HsumT_cv; [ pose proof (shw_re w); pose proof sigl_gt; lra
                  | apply shw_ne1 ].
Qed.

Lemma unif_all : forall n w,
  Cmod (Cminus (fnw n w) (gw w)) <= Tmaj - sum_f_R0 bmaj n.
Proof.
  intros n w.
  assert (HE : Cmod (Cminus (fnw n w) (gw w))
               = Cmod (Cminus (gw w) (fnw n w)))
    by (replace (Cminus (fnw n w) (gw w))
          with (Copp (Cminus (gw w) (fnw n w))) by ring; apply Cmod_opp').
  rewrite HE. unfold fnw.
  apply (Cseries_tail_bound (fun k => htermC (shw w) k) bmaj (gw w) Tmaj).
  - intro k. apply bmaj_bound.
  - apply gw_cv.
  - exact (proj2_sig Tmaj_ex).
Qed.

Lemma unif_eps : forall eps, 0 < eps -> exists N, forall n, (N <= n)%nat ->
  forall w, Cmod (Cminus (fnw n w) (gw w)) <= eps.
Proof.
  intros eps Heps.
  assert (HT : Un_cv (sum_f_R0 bmaj) Tmaj) by exact (proj2_sig Tmaj_ex).
  destruct (HT eps Heps) as [N HN].
  exists N. intros n Hn w.
  pose proof (HN n Hn) as HD. unfold R_dist in HD.
  pose proof (Rabs_le_both _ _ (Rlt_le _ _ HD)) as [Hlo Hhi].
  pose proof (unif_all n w). lra.
Qed.

(* ---- pointwise continuity of the approximants ---- *)
Lemma shw_lip : forall w1 w2,
  Cmod (Cminus (shw w1) (shw w2)) <= 2 * lamw * Cmod (Cminus w1 w2).
Proof.
  intros w1 w2. unfold shw.
  rewrite (Cmod_shift_scal s0 lamw _ _ ltac:(pose proof lamw_pos; lra)).
  pose proof (clampw_lipschitz 8 C0 w1 w2 ltac:(lra)) as HL.
  pose proof lamw_pos. nra.
Qed.

Lemma htermC_ptcont_at : forall k s, Cminus C1 s <> C0 ->
  ptcont_at (fun w => htermC w k) s.
Proof.
  intros k s Hs eps Heps.
  destruct (htermC_holo_s k s Hs) as [d Hd].
  destruct (is_Cderiv_cont (fun w => htermC w k) s d Hd eps Heps)
    as [del [Hdel HD]].
  exists del. split; [ exact Hdel | ]. intros z' Hz'.
  pose proof (HD (Cminus z' s) Hz') as H.
  replace (Cadd s (Cminus z' s)) with z' in H by ring. exact H.
Qed.

Lemma fnw_term_ptcont : forall k z, ptcont_at (fun w => htermC (shw w) k) z.
Proof.
  intros k z.
  apply (ptcont_at_comp_lip (fun w => htermC w k) shw (2 * lamw) z);
    [ pose proof lamw_pos; lra | apply shw_lip
    | apply htermC_ptcont_at; apply shw_ne1 ].
Qed.

Lemma fnw_ptcont : forall n, ptcont (fnw n).
Proof.
  intro n. induction n as [| n IH]; intro z.
  - apply (ptcont_at_ext (fnw 0%nat) (fun w => htermC (shw w) 0%nat) z);
      [ intro w; reflexivity | apply fnw_term_ptcont ].
  - apply (ptcont_at_ext (fnw (S n))
             (fun w => Cadd (fnw n w) (htermC (shw w) (S n))) z);
      [ intro w; reflexivity | ].
    apply ptcont_at_add; [ exact (IH z) | apply fnw_term_ptcont ].
Qed.

Lemma fnw_CcontC : forall n, CcontC (fnw n).
Proof. intro n. apply ptcont_CcontC. apply fnw_ptcont. Qed.

(* ---- pointwise continuity of the limit ---- *)
Lemma gw_ptcont : ptcont gw.
Proof.
  intros z eps Heps.
  apply (unif_limit_ptcont fnw gw); [ | | exact Heps ].
  - intros n z1 e He. exact (fnw_ptcont n z1 e He).
  - intro z0. exists 1. split; [ lra | ].
    intros e He. destruct (unif_eps e He) as [N HN].
    exists N. intros n Hn w _. exact (HN n Hn w).
Qed.

Lemma gw_CcontC : CcontC gw.
Proof. apply ptcont_CcontC. apply gw_ptcont. Qed.

(* ---- holomorphy of the approximants inside the clamp radius ---- *)
Definition afn (n : nat) (w : C) : C :=
  Cpsum (fun k => htermC (Cadd s0 (Cmul (RtoC lamw) w)) k) n.

Lemma afn_holo : forall n w, Cminus C1 (Cadd s0 (Cmul (RtoC lamw) w)) <> C0 ->
  exists d, is_Cderiv (afn n) w d.
Proof.
  intros n w Hne. induction n as [| n IH].
  - unfold afn. cbn [Cpsum].
    destruct (htermC_holo_s 0%nat (Cadd s0 (Cmul (RtoC lamw) w)) Hne) as [d Hd].
    eexists.
    apply (is_Cderiv_ext
             (fun v => htermC (Cadd (Cmul (RtoC lamw) v) s0) 0%nat)).
    + intro v; f_equal; ring.
    + apply (Cderiv_comp_affine (fun u => htermC u 0%nat) (RtoC lamw) s0 w d).
      replace (Cadd (Cmul (RtoC lamw) w) s0)
        with (Cadd s0 (Cmul (RtoC lamw) w)) by ring. exact Hd.
  - unfold afn in *. cbn [Cpsum].
    destruct IH as [d1 Hd1].
    destruct (htermC_holo_s (S n) (Cadd s0 (Cmul (RtoC lamw) w)) Hne) as [d2 Hd2].
    eexists. apply Cderiv_add; [ exact Hd1 | ].
    apply (is_Cderiv_ext
             (fun v => htermC (Cadd (Cmul (RtoC lamw) v) s0) (S n))).
    + intro v; f_equal; ring.
    + apply (Cderiv_comp_affine (fun u => htermC u (S n)) (RtoC lamw) s0 w d2).
      replace (Cadd (Cmul (RtoC lamw) w) s0)
        with (Cadd s0 (Cmul (RtoC lamw) w)) by ring. exact Hd2.
Qed.

Lemma fnw_eq_afn : forall n w, Cmod w < 4 -> fnw n w = afn n w.
Proof.
  intros n w Hw. unfold fnw, afn, shw. rewrite (clamp8_id w Hw). reflexivity.
Qed.

Lemma fnw_holo_disk : forall n z, Cmod z < 3 -> exists d, is_Cderiv (fnw n) z d.
Proof.
  intros n z Hz.
  assert (Hne : Cminus C1 (Cadd s0 (Cmul (RtoC lamw) z)) <> C0).
  { rewrite <- (clamp8_id z ltac:(lra)). exact (shw_ne1 z). }
  destruct (afn_holo n z Hne) as [d Hd].
  exists d.
  apply (is_Cderiv_congr (fnw n) (afn n) z d (1)).
  - lra.
  - intros z' Hz'.
    assert (Hz'4 : Cmod z' < 4).
    { pose proof (Cmod_triangle (Cminus z' z) z) as HT.
      replace (Cadd (Cminus z' z) z) with z' in HT by ring. lra. }
    apply fnw_eq_afn; exact Hz'4.
  - exact Hd.
Qed.

(* ---- Weierstrass ---- *)
Lemma gw_holo0 : exists d, is_Cderiv gw C0 d.
Proof.
  apply (unif_limit_holo_disk fnw gw 3).
  - lra.
  - exact fnw_CcontC.
  - intros n z Hz. apply fnw_holo_disk; exact Hz.
  - exact gw_CcontC.
  - intros z eps Heps. exact (gw_ptcont z eps Heps).
  - intros eps Heps. destruct (unif_eps eps Heps) as [N HN].
    exists N. intros n Hn w _. exact (HN n Hn w).
  - rewrite (proj2 (Cmod0 C0) eq_refl). lra.
Qed.

Theorem HsumT_holo_at : exists d, is_Cderiv HsumT s0 d.
Proof.
  pose proof lamw_pos as Hl.
  destruct gw_holo0 as [d Hd].
  assert (Hli : lamw <> 0) by lra.
  set (aa := RtoC (/ lamw)).
  set (bb := Copp (Cmul (RtoC (/ lamw)) s0)).
  assert (Hz0 : Cadd (Cmul aa s0) bb = C0) by (unfold aa, bb; ring).
  assert (Haff : is_Cderiv (fun v => gw (Cadd (Cmul aa v) bb)) s0 (Cmul aa d)).
  { apply (Cderiv_comp_affine gw aa bb s0 d). rewrite Hz0. exact Hd. }
  exists (Cmul aa d).
  apply (is_Cderiv_congr HsumT (fun v => gw (Cadd (Cmul aa v) bb)) s0
           (Cmul aa d) (4 * lamw)).
  - lra.
  - intros s' Hs'.
    assert (Hmod : Cmod (Cadd (Cmul aa s') bb) < 4).
    { replace (Cadd (Cmul aa s') bb)
        with (Cmul (RtoC (/ lamw)) (Cminus s' s0)) by (unfold aa, bb; ring).
      rewrite Cmod_mul, Cmod_RtoC, Rabs_pos_eq
        by (left; apply Rinv_0_lt_compat; lra).
      apply (Rmult_lt_reg_l lamw); [ lra | ].
      replace (lamw * (/ lamw * Cmod (Cminus s' s0))) with (Cmod (Cminus s' s0))
        by (field; lra).
      lra. }
    assert (Hll : Cmul (RtoC lamw) (RtoC (/ lamw)) = C1)
      by (apply Ceq; cbn; [ field; exact Hli | ring ]).
    assert (HE : Cadd s0 (Cmul (RtoC lamw) (Cadd (Cmul aa s') bb)) = s').
    { unfold aa, bb.
      replace (Cadd s0 (Cmul (RtoC lamw)
                 (Cadd (Cmul (RtoC (/ lamw)) s')
                       (Copp (Cmul (RtoC (/ lamw)) s0)))))
        with (Cadd s0 (Cmul (Cmul (RtoC lamw) (RtoC (/ lamw)))
                            (Cminus s' s0))) by ring.
      rewrite Hll. ring. }
    unfold gw, shw. rewrite (clamp8_id _ Hmod), HE. reflexivity.
  - exact Haff.
Qed.

Theorem Bfn1_holo_at : exists d, is_Cderiv Bfn1 s0 d.
Proof.
  destruct HsumT_holo_at as [d Hd].
  eexists. unfold Bfn1.
  apply Cderiv_add; [ apply Cderiv_const | ].
  apply Cderiv_mul.
  - apply (Cderiv_minus (fun w => w) (fun _ => C1) s0 C1 C0);
      [ apply Cderiv_id | apply Cderiv_const ].
  - apply Cderiv_add; [ apply Cderiv_const | exact Hd ].
Qed.

End Weier.

Theorem Bfn1_holo : forall s, -1 < Re s -> Cminus C1 s <> C0 ->
  exists d, is_Cderiv Bfn1 s d.
Proof. intros s H0 H1. exact (Bfn1_holo_at s H0 H1). Qed.

Theorem HsumT_holo : forall s, -1 < Re s -> Cminus C1 s <> C0 ->
  exists d, is_Cderiv HsumT s d.
Proof. intros s H0 H1. exact (HsumT_holo_at s H0 H1). Qed.

Print Assumptions Bfn1_holo.

(* ================================================================= *)
(*  END ZetaEMExtHolo.v                                               *)
(* ================================================================= *)
