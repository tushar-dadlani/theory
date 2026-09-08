(* ================================================================= *)
(*  CPeelAtCentre.v  --  the peel/count engine at an ARBITRARY centre. *)
(*                                                                    *)
(*  CZeroFreeGen/CPeelBoundGen count zeros of F in a disk about the    *)
(*  ORIGIN, and demand                                                 *)
(*      ptcont F         GLOBALLY (at every point of C),               *)
(*      disk_holo F R2   with Rr + 1 < R2.                             *)
(*                                                                    *)
(*  Neither is available for zeta: it is holomorphic only on a         *)
(*  half-plane, and the "+1" is a fixed absolute slack that would      *)
(*  swamp a disk of radius 2.                                          *)
(*                                                                    *)
(*  Both are removed here, by composing with an affine map and a       *)
(*  radial clamp:                                                      *)
(*                                                                    *)
(*      G w := F (c + lam * clampw w)                                  *)
(*                                                                    *)
(*  * TRANSLATION by c moves the centre.                               *)
(*  * SCALING by lam makes the absolute "+1" cost lam, so choosing lam *)
(*    small buys as much relative room as needed.  This is the whole   *)
(*    reason the engine does not have to be re-proved.                 *)
(*  * The CLAMP (CCauchyAnalytic.clampw, 2-Lipschitz by                *)
(*    CClampCont.clampw_lipschitz) makes G total and globally          *)
(*    pointwise-continuous while agreeing with the affine composite    *)
(*    on the whole disk that matters -- so F is only ever evaluated    *)
(*    inside Cmod (z - c) < rh, where it is assumed regular.           *)
(*                                                                    *)
(*  lam, Rr and R2 are left as caller-supplied parameters rather than  *)
(*  derived from rh: the caller has concrete rationals, so its side    *)
(*  conditions fall to lra, whereas deriving them here would force a   *)
(*  division-heavy nra.                                                *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia List Classical.
Require Import ComplexField Cmodulus Holomorphic CDeriv CPathIntegral
        JensenMultiZero CZeroFactorDisk CZeroListFactor
        CCauchyAnalytic CClampCont PerronRemovable
        CPeelBoundGen CZeroFreeGen.
Open Scope R_scope.

(* continuity of F at one point *)
Definition ptcont_at (F : C -> C) (z : C) : Prop :=
  forall eps, 0 < eps -> exists del, 0 < del /\
    forall z', Cmod (Cminus z' z) < del -> Cmod (Cminus (F z') (F z)) < eps.

Lemma Cmod_scal_diff : forall (lam : R) (A B : C), 0 <= lam ->
  Cmod (Cminus (Cadd C0 (Cmul (RtoC lam) A)) (Cadd C0 (Cmul (RtoC lam) B)))
  = lam * Cmod (Cminus A B).
Proof.
  intros lam A B Hl.
  replace (Cminus (Cadd C0 (Cmul (RtoC lam) A)) (Cadd C0 (Cmul (RtoC lam) B)))
    with (Cmul (RtoC lam) (Cminus A B)) by ring.
  rewrite Cmod_mul, Cmod_RtoC, Rabs_pos_eq by exact Hl. reflexivity.
Qed.

Lemma Cmod_shift_scal : forall (c : C) (lam : R) (A B : C), 0 <= lam ->
  Cmod (Cminus (Cadd c (Cmul (RtoC lam) A)) (Cadd c (Cmul (RtoC lam) B)))
  = lam * Cmod (Cminus A B).
Proof.
  intros c lam A B Hl.
  replace (Cminus (Cadd c (Cmul (RtoC lam) A)) (Cadd c (Cmul (RtoC lam) B)))
    with (Cmul (RtoC lam) (Cminus A B)) by ring.
  rewrite Cmod_mul, Cmod_RtoC, Rabs_pos_eq by exact Hl. reflexivity.
Qed.

Lemma scal_arc : forall (lam Rr u : R),
  Cmul (RtoC lam) (arc Rr u) = arc (lam * Rr) u.
Proof. intros. unfold arc, RtoC. apply Ceq; cbn; ring. Qed.

Lemma prodfac_C0_of_In : forall (l : list C) (w : C),
  In w l -> prodfac l w = C0.
Proof.
  induction l as [| a l IH]; intros w Hin; [ destruct Hin | ].
  cbn [prodfac]. destruct Hin as [E | Hin].
  - subst a. replace (Cminus w w) with C0 by ring. ring.
  - rewrite (IH w Hin). ring.
Qed.

Section AtCentre.

Variable alpha : R.
Hypothesis Halpha : 0 < alpha < / 2.

Theorem peel_count_at_centre :
  forall (F : C -> C) (c : C) (lam Rr R2 rh M : R),
  0 < lam -> 0 < Rr -> Rr + 1 < R2 -> lam * (R2 + 1) < rh ->
  (forall z, Cmod (Cminus z c) < rh -> exists d, is_Cderiv F z d) ->
  (forall z, Cmod (Cminus z c) < rh -> ptcont_at F z) ->
  F c <> C0 ->
  (forall u, Cmod (F (Cadd c (arc (lam * Rr) u))) <= M) ->
  exists l : list C,
    (forall w, In w l -> F w = C0 /\ Cmod (Cminus w c) < alpha * (lam * Rr))
    /\ (forall z, Cmod (Cminus z c) < alpha * (lam * Rr) -> F z = C0 -> In z l)
    /\ INR (length l) <= ln (2 * M / Cmod (F c)) / ln (qpeel alpha).
Proof.
  intros F c lam Rr R2 rh M Hlam HRr HRrR2 Hreach Hhol Hptc HFc HM.
  destruct Halpha as [Ha0 Ha2].
  assert (Ha1 : alpha < 1) by lra.
  set (r := R2 + 1).
  assert (Hr : 0 < r) by (unfold r; lra).
  assert (H2r : 0 < 2 * r) by lra.
  assert (HrhoR : rho (2 * r) C0 = r).
  { unfold rho. rewrite (proj2 (Cmod0 C0) eq_refl). field. }
  (* the clamp is the identity on Cmod w < r *)
  assert (Hcid : forall w, Cmod w < r -> clampw (2 * r) C0 w = w).
  { intros w Hw. apply clampw_id.
    rewrite (proj2 (Cmod0 C0) eq_refl).
    replace (Cminus w C0) with w by ring. lra. }
  assert (Hcmod : forall w, Cmod (clampw (2 * r) C0 w) <= r).
  { intro w. pose proof (clampw_mod (2 * r) C0 H2r w) as Hcm.
    rewrite HrhoR in Hcm. exact Hcm. }
  set (G := fun w => F (Cadd c (Cmul (RtoC lam) (clampw (2 * r) C0 w)))).
  (* every point G ever feeds to F lies strictly inside the good disk *)
  assert (Hin : forall w, Cmod (Cminus (Cadd c (Cmul (RtoC lam)
                                     (clampw (2 * r) C0 w))) c) < rh).
  { intro w.
    replace (Cminus (Cadd c (Cmul (RtoC lam) (clampw (2 * r) C0 w))) c)
      with (Cmul (RtoC lam) (clampw (2 * r) C0 w)) by ring.
    rewrite Cmod_mul, Cmod_RtoC, Rabs_pos_eq by lra.
    pose proof (Hcmod w). unfold r in *. nra. }
  (* --- G C0 = F c --- *)
  assert (HG0 : G C0 = F c).
  { unfold G. rewrite (Hcid C0) by (rewrite (proj2 (Cmod0 C0) eq_refl); lra).
    f_equal. ring. }
  (* --- G is globally pointwise continuous --- *)
  assert (HGptc : ptcont G).
  { intros w2 eps Heps.
    destruct (Hptc _ (Hin w2) eps Heps) as [del1 [Hd1 HD1]].
    assert (Hdl : 0 < del1 / lam) by (apply Rdiv_lt_0_compat; lra).
    destruct (clampw_ptcont (2 * r) C0 H2r w2 (del1 / lam) Hdl)
      as [del2 [Hd2 HD2]].
    exists del2. split; [ exact Hd2 | ]. intros w Hw.
    unfold G. apply HD1.
    rewrite (Cmod_shift_scal c lam _ _ ltac:(lra)).
    pose proof (HD2 w Hw) as HC.
    apply (Rmult_lt_reg_l (/ lam)); [ apply Rinv_0_lt_compat; lra | ].
    replace (/ lam * (lam * Cmod (Cminus (clampw (2 * r) C0 w)
                                         (clampw (2 * r) C0 w2))))
      with (Cmod (Cminus (clampw (2 * r) C0 w) (clampw (2 * r) C0 w2)))
      by (field; lra).
    replace (/ lam * del1) with (del1 / lam) by (field; lra). exact HC. }
  (* --- G is holomorphic on Cmod w < R2 --- *)
  assert (HGhol : disk_holo G R2).
  { intros w Hw.
    assert (HwR : Cmod w < r) by (unfold r; lra).
    assert (Haff : exists d, is_Cderiv F (Cadd (Cmul (RtoC lam) w) c) d).
    { apply Hhol.
      replace (Cminus (Cadd (Cmul (RtoC lam) w) c) c)
        with (Cmul (RtoC lam) w) by ring.
      rewrite Cmod_mul, Cmod_RtoC, Rabs_pos_eq by lra.
      unfold r in *. nra. }
    destruct Haff as [d Hd].
    exists (Cmul (RtoC lam) d).
    apply (is_Cderiv_congr G (fun w' => F (Cadd (Cmul (RtoC lam) w') c))
             w (Cmul (RtoC lam) d) (r - Cmod w)).
    - lra.
    - intros w' Hw'.
      assert (Hw'r : Cmod w' < r).
      { pose proof (Cmod_triangle (Cminus w' w) w) as HT.
        replace (Cadd (Cminus w' w) w) with w' in HT by ring. lra. }
      unfold G. rewrite (Hcid w' Hw'r). f_equal. ring.
    - apply (Cderiv_comp_affine F (RtoC lam) c w d). exact Hd. }
  (* --- the circle bound transports --- *)
  assert (HGM : forall u, Cmod (G (arc Rr u)) <= M).
  { intro u. unfold G.
    rewrite (Hcid (arc Rr u))
      by (rewrite (Cmod_arc Rr u ltac:(lra)); unfold r; lra).
    rewrite scal_arc. exact (HM u). }
  assert (HGne : G C0 <> C0) by (rewrite HG0; exact HFc).
  (* --- run the engine --- *)
  destruct (cofactor_zero_free_gen alpha Halpha G R2 Rr M
              HRr HRrR2 HGne HGptc HGhol HGM)
    as [l [Gc [Hid [Hchol [Hcptc [Hsm Hne0]]]]]].
  pose proof (peel_count_explicit_gen alpha Halpha G Gc Rr M l HRr HGne Hid
                Hcptc (fun z Hz => Hchol z ltac:(lra)) HGM
                (fun w Hw => Rlt_le _ _ (Hsm w Hw))) as Hcount.
  rewrite HG0 in Hcount.
  (* --- push the list back through the affine map --- *)
  set (phi := fun w => Cadd c (Cmul (RtoC lam) w)).
  assert (Hphi : forall w, Cmod w < r -> F (phi w) = G w)
    by (intros w Hw; unfold G, phi; rewrite (Hcid w Hw); reflexivity).
  exists (map phi l).
  split; [ | split ].
  - intros z Hz. apply in_map_iff in Hz. destruct Hz as [w [Hzw Hwl]]; subst z.
    pose proof (Hsm w Hwl) as Hwsm.
    assert (HaR : alpha * Rr < Rr) by nra.
    assert (Hwr : Cmod w < r) by (unfold r; lra).
    split.
    + rewrite (Hphi w Hwr), (Hid w), (prodfac_C0_of_In l w Hwl). ring.
    + unfold phi.
      replace (Cminus (Cadd c (Cmul (RtoC lam) w)) c)
        with (Cmul (RtoC lam) w) by ring.
      rewrite Cmod_mul, Cmod_RtoC, Rabs_pos_eq by lra. nra.
  - intros z Hz HFz.
    set (w := Cmul (RtoC (/ lam)) (Cminus z c)).
    assert (Hwmod : Cmod w = / lam * Cmod (Cminus z c)).
    { unfold w. rewrite Cmod_mul, Cmod_RtoC, Rabs_pos_eq;
        [ reflexivity | left; apply Rinv_0_lt_compat; lra ]. }
    assert (Hwsm : Cmod w < alpha * Rr).
    { rewrite Hwmod. apply (Rmult_lt_reg_l lam); [ lra | ].
      replace (lam * (/ lam * Cmod (Cminus z c))) with (Cmod (Cminus z c))
        by (field; lra).
      replace (lam * (alpha * Rr)) with (alpha * (lam * Rr)) by ring.
      exact Hz. }
    assert (HaR : alpha * Rr < Rr) by nra.
    assert (Hwr : Cmod w < r) by (unfold r; lra).
    assert (Hl0 : lam <> 0) by lra.
    assert (Hll : Cmul (RtoC lam) (RtoC (/ lam)) = C1).
    { apply Ceq; cbn; [ field; exact Hl0 | ring ]. }
    assert (Hpw : phi w = z).
    { unfold phi, w.
      replace (Cmul (RtoC lam) (Cmul (RtoC (/ lam)) (Cminus z c)))
        with (Cmul (Cmul (RtoC lam) (RtoC (/ lam))) (Cminus z c)) by ring.
      rewrite Hll. ring. }
    assert (HGw : G w = C0) by (rewrite <- (Hphi w Hwr), Hpw; exact HFz).
    assert (Hprod : prodfac l w = C0).
    { rewrite (Hid w) in HGw. apply NNPP. intro Hne.
      exact (Cmul_ne0 _ _ Hne (Hne0 w Hwsm) HGw). }
    assert (Hinl : In w l).
    { destruct (classic (In w l)) as [Hy | Hn]; [ exact Hy | ].
      exfalso. exact (prodfac_ne0_notin l w Hn Hprod). }
    rewrite <- Hpw. apply in_map. exact Hinl.
  - rewrite length_map. exact Hcount.
Qed.

End AtCentre.

Print Assumptions peel_count_at_centre.

(* ================================================================= *)
(*  END CPeelAtCentre.v                                               *)
(* ================================================================= *)
