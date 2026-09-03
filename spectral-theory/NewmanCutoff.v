(* ================================================================= *)
(*  NewmanCutoff.v  --  global continuity for gext, via a cutoff       *)
(*  adapted to the TRUNCATED disk.                                     *)
(*                                                                    *)
(*  trunc_cauchy (and pathint_loop_except beneath it) needs GLOBAL     *)
(*  CcontC continuity, but gext is genuinely discontinuous: BfnT       *)
(*  vanishes at the nontrivial zeta zeros, which sit at Re z in (-1,0).*)
(*  CGcutCont.gcut cannot help -- it is a RADIAL cutoff and needs the  *)
(*  function holomorphic on a whole disk, which fails once the disk is *)
(*  large enough to swallow a zero (the first is at |z| ~ 14.14).      *)
(*                                                                    *)
(*  The fix: cut off in BOTH coordinates, matching the truncated disk  *)
(*      {|z| <= R}  cap  {Re z >= -del}                                *)
(*  on which BfnUniform.gext_holo_strip guarantees holomorphy.  The    *)
(*  reusable core is cutprod_ptcont: multiplying by a continuous [0,1] *)
(*  cutoff preserves pointwise continuity, PROVIDED at each point      *)
(*  either the function is continuous or the cutoff vanishes           *)
(*  identically nearby.                                                *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import ComplexField Cmodulus Holomorphic CDeriv CHoloCalculus
        CContBounded CCutoff CGcutCont CSegInt CPrimitiveDisk PerronRemovable
        CZetaRegular6 NewmanGExt BfnUniform.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  Pointwise-continuity predicate, and the reusable cutoff lemma.     *)
(* ----------------------------------------------------------------- *)

Definition PtcontC (f : C -> C) : Prop :=
  forall z0 eps, 0 < eps -> exists d, 0 < d /\
    forall w, Cmod (Cminus w z0) < d -> Cmod (Cminus (f w) (f z0)) < eps.

Definition PtcontR (c : C -> R) : Prop :=
  forall z0 eps, 0 < eps -> exists d, 0 < d /\
    forall w, Cmod (Cminus w z0) < d -> Rabs (c w - c z0) < eps.

Theorem cutprod_ptcont : forall (g : C -> C) (c : C -> R),
  (forall z, 0 <= c z <= 1) ->
  PtcontR c ->
  (forall z0,
     (forall eps, 0 < eps -> exists d, 0 < d /\
        forall w, Cmod (Cminus w z0) < d -> Cmod (Cminus (g w) (g z0)) < eps)
     \/ (exists d, 0 < d /\ forall w, Cmod (Cminus w z0) < d -> c w = 0)) ->
  PtcontC (fun z => Cmul (g z) (RtoC (c z))).
Proof.
  intros g c Hb Hc Hdi z0 eps Heps.
  destruct (Hdi z0) as [Hgc | [d0 [Hd0 Hzero]]].
  - (* g continuous at z0: ordinary product estimate *)
    set (Mg := Cmod (g z0)).
    assert (HMg : 0 <= Mg) by (unfold Mg; apply Cmod_nonneg).
    destruct (Hgc (eps / 2) ltac:(lra)) as [d1 [Hd1 Hg1]].
    destruct (Hc z0 (eps / 2 / (Mg + 1)) ltac:(apply Rdiv_lt_0_compat; lra))
      as [d2 [Hd2 Hc2]].
    exists (Rmin d1 d2); split; [ apply Rmin_pos; assumption | ].
    intros w Hw.
    assert (Hw1 : Cmod (Cminus w z0) < d1)
      by (eapply Rlt_le_trans; [ exact Hw | apply Rmin_l ]).
    assert (Hw2 : Cmod (Cminus w z0) < d2)
      by (eapply Rlt_le_trans; [ exact Hw | apply Rmin_r ]).
    assert (Hsplit : Cminus (Cmul (g w) (RtoC (c w))) (Cmul (g z0) (RtoC (c z0)))
                   = Cadd (Cmul (Cminus (g w) (g z0)) (RtoC (c w)))
                          (Cmul (g z0) (RtoC (c w - c z0))))
      by (unfold Cmul, Cminus, Cadd, RtoC; apply Ceq; cbn; ring).
    rewrite Hsplit.
    eapply Rle_lt_trans; [ apply Cmod_triangle | ].
    rewrite !Cmod_mul, !Cmod_RtoC.
    assert (Hcw1 : Rabs (c w) <= 1)
      by (rewrite Rabs_pos_eq by apply Hb; apply Hb).
    assert (Ht1 : Cmod (Cminus (g w) (g z0)) * Rabs (c w) < eps / 2).
    { apply Rle_lt_trans with (Cmod (Cminus (g w) (g z0)) * 1);
        [ apply Rmult_le_compat_l; [ apply Cmod_nonneg | exact Hcw1 ]
        | rewrite Rmult_1_r; apply Hg1; exact Hw1 ]. }
    assert (Ht2 : Mg * Rabs (c w - c z0) <= eps / 2).
    { apply Rle_trans with (Mg * (eps / 2 / (Mg + 1))).
      - apply Rmult_le_compat_l; [ exact HMg | left; apply Hc2; exact Hw2 ].
      - apply Rle_trans with ((Mg + 1) * (eps / 2 / (Mg + 1)));
          [ apply Rmult_le_compat_r; [ | lra ]
          | apply Req_le; field; lra ].
        apply Rlt_le, Rdiv_lt_0_compat; lra. }
    unfold Mg in Ht2. lra.
  - (* the cutoff vanishes identically near z0 *)
    exists d0; split; [ exact Hd0 | ]; intros w Hw.
    assert (Hcw : c w = 0) by (apply Hzero; exact Hw).
    assert (Hcz : c z0 = 0)
      by (apply Hzero; replace (Cminus z0 z0) with C0 by ring;
          rewrite (proj2 (Cmod0 C0) eq_refl); exact Hd0).
    rewrite Hcw, Hcz.
    replace (Cminus (Cmul (g w) (RtoC 0)) (Cmul (g z0) (RtoC 0))) with C0
      by (unfold Cmul, Cminus, RtoC; apply Ceq; cbn; ring).
    rewrite (proj2 (Cmod0 C0) eq_refl); exact Heps.
Qed.

(* ----------------------------------------------------------------- *)
(*  The two-factor cutoff: radial AND half-plane.                      *)
(* ----------------------------------------------------------------- *)

Lemma Rabs_Im_le3 : forall c : C, Rabs (Im c) <= Cmod c.
Proof.
  intro c. unfold Cmod, Cnorm2.
  rewrite <- (sqrt_Rsqr_abs (Im c)). apply sqrt_le_1_alt.
  unfold Rsqr. pose proof (Rle_0_sqr (Re c)). unfold Rsqr in *. lra.
Qed.

Lemma Rabs_Re_le3 : forall c : C, Rabs (Re c) <= Cmod c.
Proof.
  intro c. unfold Cmod, Cnorm2.
  rewrite <- (sqrt_Rsqr_abs (Re c)). apply sqrt_le_1_alt.
  unfold Rsqr. pose proof (Rle_0_sqr (Im c)). unfold Rsqr in *. lra.
Qed.

Definition tcut (Rr del : R) (z : C) : R :=
  psi Rr (Rr + 1) (Cmod z) * psi (del / 2) del (- Re z).

Lemma tcut_bounds : forall Rr del z, 0 <= tcut Rr del z <= 1.
Proof.
  intros Rr del z. unfold tcut.
  pose proof (psi_bounds Rr (Rr + 1) (Cmod z)) as H1.
  pose proof (psi_bounds (del / 2) del (- Re z)) as H2.
  split; [ apply Rmult_le_pos; lra | ].
  apply Rle_trans with (1 * 1); [ apply Rmult_le_compat; lra | lra ].
Qed.

Lemma tcut_lip : forall Rr del w z, 0 < del ->
  Rabs (tcut Rr del w - tcut Rr del z) <= (1 + 2 / del) * Cmod (Cminus w z).
Proof.
  intros Rr del w z Hdel.
  pose proof (psi_bounds Rr (Rr + 1) (Cmod w)) as Hp1.
  pose proof (psi_bounds (del / 2) del (- Re z)) as Hq2.
  assert (Hrad : Rabs (psi Rr (Rr + 1) (Cmod w) - psi Rr (Rr + 1) (Cmod z))
                 <= Cmod (Cminus w z)).
  { eapply Rle_trans; [ apply psi_lip; lra | ].
    replace (/ (Rr + 1 - Rr)) with 1 by (field; lra).
    rewrite Rmult_1_l. apply Cmod_revtri. }
  assert (Hhp : Rabs (psi (del / 2) del (- Re w) - psi (del / 2) del (- Re z))
                <= 2 / del * Cmod (Cminus w z)).
  { eapply Rle_trans; [ apply psi_lip; lra | ].
    replace (/ (del - del / 2)) with (2 / del) by (field; lra).
    apply Rmult_le_compat_l; [ apply Rlt_le, Rdiv_lt_0_compat; lra | ].
    replace (- Re w - - Re z) with (- (Re w - Re z)) by ring.
    rewrite Rabs_Ropp.
    replace (Re w - Re z) with (Re (Cminus w z)) by (cbn; ring).
    apply Rabs_Re_le3. }
  unfold tcut.
  replace (psi Rr (Rr + 1) (Cmod w) * psi (del / 2) del (- Re w)
           - psi Rr (Rr + 1) (Cmod z) * psi (del / 2) del (- Re z))
    with (psi Rr (Rr + 1) (Cmod w)
            * (psi (del / 2) del (- Re w) - psi (del / 2) del (- Re z))
          + psi (del / 2) del (- Re z)
            * (psi Rr (Rr + 1) (Cmod w) - psi Rr (Rr + 1) (Cmod z))) by ring.
  eapply Rle_trans; [ apply Rabs_triang | ].
  rewrite !Rabs_mult.
  assert (HA : Rabs (psi Rr (Rr + 1) (Cmod w)) <= 1)
    by (rewrite Rabs_pos_eq; lra).
  assert (HB : Rabs (psi (del / 2) del (- Re z)) <= 1)
    by (rewrite Rabs_pos_eq; lra).
  pose proof (Rabs_pos (psi (del / 2) del (- Re w) - psi (del / 2) del (- Re z))) as Hn1.
  pose proof (Rabs_pos (psi Rr (Rr + 1) (Cmod w) - psi Rr (Rr + 1) (Cmod z))) as Hn2.
  pose proof (Cmod_nonneg (Cminus w z)) as Hcm.
  nra.
Qed.

Lemma tcut_ptcont : forall Rr del, 0 < del -> PtcontR (tcut Rr del).
Proof.
  intros Rr del Hdel z0 eps Heps.
  assert (HL : 0 < 1 + 2 / del) by (assert (0 < 2 / del) by (apply Rdiv_lt_0_compat; lra); lra).
  exists (eps / (1 + 2 / del)); split; [ apply Rdiv_lt_0_compat; lra | ].
  intros w Hw.
  eapply Rle_lt_trans; [ apply tcut_lip; exact Hdel | ].
  apply (Rmult_lt_reg_r (/ (1 + 2 / del))); [ apply Rinv_0_lt_compat; lra | ].
  replace ((1 + 2 / del) * Cmod (Cminus w z0) * / (1 + 2 / del))
    with (Cmod (Cminus w z0)) by (field; lra).
  replace (eps * / (1 + 2 / del)) with (eps / (1 + 2 / del)) by (unfold Rdiv; ring).
  exact Hw.
Qed.

Lemma tcut_one : forall Rr del z, 0 < del -> Cmod z <= Rr -> - (del / 2) <= Re z ->
  tcut Rr del z = 1.
Proof.
  intros Rr del z Hdel Hr Hre. unfold tcut.
  rewrite (psi_one Rr (Rr + 1) (Cmod z) ltac:(lra) Hr).
  rewrite (psi_one (del / 2) del (- Re z) ltac:(lra) ltac:(lra)). ring.
Qed.

(* ----------------------------------------------------------------- *)
(*  gext, cut off to the truncated disk, is GLOBALLY continuous --     *)
(*  which is what trunc_cauchy / pathint_loop_except demand -- and is  *)
(*  unchanged on the truncated disk itself.                            *)
(* ----------------------------------------------------------------- *)

Definition gtrunc (Rr del : R) (z : C) : C :=
  Cmul (gext z) (RtoC (tcut Rr del z)).

Theorem gtrunc_ptcont : forall Rr, 0 < Rr -> exists del, 0 < del /\
  PtcontC (gtrunc Rr del) /\
  (forall z, Cmod z <= Rr -> - (del / 2) <= Re z -> gtrunc Rr del z = gext z).
Proof.
  intros Rr HRr.
  destruct (BfnT_ne0_unif (Rr + 2) ltac:(lra)) as [d0 [Hd0 Hne]].
  set (del := Rmin d0 1 / 4).
  assert (Hm1 : Rmin d0 1 <= d0) by apply Rmin_l.
  assert (Hm2 : Rmin d0 1 <= 1) by apply Rmin_r.
  assert (Hm0 : 0 < Rmin d0 1) by (apply Rmin_glb_lt; lra).
  assert (Hdel : 0 < del) by (unfold del; lra).
  assert (H2del : 2 * del < d0) by (unfold del; lra).
  assert (H2del1 : 2 * del < 1) by (unfold del; lra).
  exists del. split; [ exact Hdel | ]. split.
  -
    apply (cutprod_ptcont gext (tcut Rr del)).
    + intro z; apply tcut_bounds.
    + apply tcut_ptcont; exact Hdel.
    + intro z0.
      destruct (Rlt_le_dec (Cmod z0) (Rr + 2)) as [Hin | Hout].
      * destruct (Rlt_le_dec (- (2 * del)) (Re z0)) as [Hre | Hre].
        -- (* gext is differentiable, hence continuous, at z0 *)
           left.
           assert (Hpos : 0 < Re (Cadd z0 C1)) by (cbn; lra).
           assert (Hbne : BfnT (Cadd z0 C1) <> C0).
           { destruct (Rle_lt_dec 0 (Re z0)) as [Hz | Hz].
             - apply BfnT_ne0_re_ge1. cbn. lra.
             - apply Hne.
               + cbn. replace (Re z0 + 1 - 1) with (Re z0) by ring.
                 unfold Rabs; destruct (Rcase_abs (Re z0)); lra.
               + cbn. replace (Im z0 + 0) with (Im z0) by ring.
                 eapply Rle_trans; [ apply Rabs_Im_le3 | lra ]. }
           destruct (gext_holo z0 Hpos Hbne) as [dg Hdg].
           intros eps Heps.
           destruct (Cderiv_cont_w gext z0 dg Hdg eps Heps) as [dd [Hdd Hc]].
           exists dd; split; [ exact Hdd | exact Hc ].
        -- (* far left: the half-plane factor vanishes near z0 *)
           right. exists (del / 2); split; [ lra | ].
           intros w Hw.
           assert (Hrew : Re w <= Re z0 + del / 2).
           { pose proof (Rabs_Re_le3 (Cminus w z0)) as Hb.
             replace (Re (Cminus w z0)) with (Re w - Re z0) in Hb by (cbn; ring).
             unfold Rabs in Hb; destruct (Rcase_abs (Re w - Re z0)); lra. }
           unfold tcut.
           rewrite (psi_zero (del / 2) del (- Re w) ltac:(lra) ltac:(lra)). ring.
      * (* far out: the radial factor vanishes near z0 *)
        right. exists (1 / 2); split; [ lra | ].
        intros w Hw.
        assert (Hcw : Rr + 1 <= Cmod w).
        { pose proof (Cmod_revtri w z0) as HR.
          pose proof (Rle_abs (- (Cmod w - Cmod z0))) as Hb.
          rewrite Rabs_Ropp in Hb. lra. }
        unfold tcut.
        rewrite (psi_zero Rr (Rr + 1) (Cmod w) ltac:(lra) Hcw). ring.
  - intros z Hr Hre. unfold gtrunc.
    rewrite (tcut_one Rr del z Hdel Hr Hre).
    replace (RtoC 1) with C1 by reflexivity. ring.
Qed.

(* the CcontC form the contour machinery consumes *)
Theorem gtrunc_CcontC : forall Rr, 0 < Rr -> exists del, 0 < del /\
  CcontC (gtrunc Rr del) /\
  (forall z, Cmod z <= Rr -> - (del / 2) <= Re z -> gtrunc Rr del z = gext z).
Proof.
  intros Rr HRr; destruct (gtrunc_ptcont Rr HRr) as [del [Hdel [Hpt Hag]]].
  exists del; split; [ exact Hdel | ].
  split; [ apply ptcont_CcontC; exact Hpt | exact Hag ].
Qed.

Print Assumptions cutprod_ptcont.
Print Assumptions gtrunc_ptcont.
Print Assumptions gtrunc_CcontC.
