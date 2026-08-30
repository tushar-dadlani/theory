(* ================================================================= *)
(*  SimpsonQuad.v  --  Simpson's rule, with a proved O(h^4) error.     *)
(*                                                                    *)
(*    mvt_sandwich          the one MVT argument, reusable            *)
(*    taylor3_bound         |f x - P3 x| <= M4 (x-c)^4 / 24           *)
(*    simpson_single        one panel, error <= 2 M4 r^5 / 45         *)
(*    composite_simpson_ab  |int_a^b f - ssum| <= M4 (b-a)^5/(720 n^4) *)
(*                                                                    *)
(*  WHY.  The midpoint rule of MidpointQuad/CompositeQuad is O(h^2),   *)
(*  and that is the binding constraint on exhibiting the SECOND zero   *)
(*  of Xi on the critical line: the margin there is 1.6e-8 against     *)
(*  3.3e-6 for the first, because Xi(1/2+it) decays like e^{-pi t/4},  *)
(*  so the midpoint rule would need ~32000 panels (hours) where        *)
(*  Simpson needs 512 (minutes).  The third zero is out of reach       *)
(*  altogether at O(h^2).                                             *)
(*                                                                    *)
(*  DESIGN.  Exactly as in MidpointQuad, the second-order hypothesis   *)
(*  is a LIPSCHITZ condition -- here on the third derivative -- and NOT *)
(*  a bound on the fourth.  The fourth derivative never has to exist.  That matters a  *)
(*  great deal downstream: the integrand contains Psi(e^x), an         *)
(*  infinite series, and every derivative order that must EXIST costs  *)
(*  a full uniform-convergence pass.                                   *)
(*                                                                    *)
(*  The climb from a Lipschitz third derivative to a cubic Taylor      *)
(*  remainder of size (x-c)^4 is three applications of ONE lemma,      *)
(*  which is the argument MidpointQuad.taylor1_bound already uses for  *)
(*  a single step, stated once with the majorant q abstract: form      *)
(*  G = q - g and H = q + g, note their derivatives have a sign fixed  *)
(*  by the hypothesis on each side of c, and apply MVT_cor2 once to    *)
(*  each.                                                             *)
(*                                                                    *)
(*  The constant 2/45 is 4x the classical r^5/90.  That is the price   *)
(*  of bounding the remainder termwise rather than through a Peano     *)
(*  kernel, and it costs only 4^(1/4) = 1.41 in the node count.        *)
(*  Verified against (x-c)^4, where the true error is 4r^5/15 and this *)
(*  bound gives 16r^5/15.  Axiom-clean.                                *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import ContinuousCoV MidpointQuad CompositeQuad.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  A.  the one MVT argument                                          *)
(* ----------------------------------------------------------------- *)
Lemma mvt_sandwich : forall (g g' q q' : R -> R) (A B c : R),
  A <= c <= B ->
  (forall y, A <= y <= B -> derivable_pt_lim g y (g' y)) ->
  (forall y, A <= y <= B -> derivable_pt_lim q y (q' y)) ->
  g c = 0 -> q c = 0 ->
  (forall y, c <= y <= B -> Rabs (g' y) <= q' y) ->
  (forall y, A <= y <= c -> Rabs (g' y) <= - q' y) ->
  forall x, A <= x <= B -> Rabs (g x) <= q x.
Proof.
  intros g g' q q' A B c Hc Hgd Hqd Hg0 Hq0 Hup Hlo x Hx.
  set (G := fun y => q y - g y).
  set (G' := fun y => q' y - g' y).
  set (H := fun y => q y + g y).
  set (H' := fun y => q' y + g' y).
  assert (HGd : forall y, A <= y <= B -> derivable_pt_lim G y (G' y))
    by (intros y Hy; unfold G, G';
        apply derivable_pt_lim_minus; [ apply Hqd | apply Hgd ]; exact Hy).
  assert (HHd : forall y, A <= y <= B -> derivable_pt_lim H y (H' y))
    by (intros y Hy; unfold H, H';
        apply derivable_pt_lim_plus; [ apply Hqd | apply Hgd ]; exact Hy).
  assert (HG0 : G c = 0) by (unfold G; rewrite Hq0, Hg0; ring).
  assert (HH0 : H c = 0) by (unfold H; rewrite Hq0, Hg0; ring).
  assert (Hkey : 0 <= G x /\ 0 <= H x).
  { destruct (total_order_T x c) as [[Hlt | Heq] | Hgt].
    - (* x < c : both derivatives <= 0 on [x,c], and x - c < 0 *)
      assert (Hin : forall y, x <= y <= c -> A <= y <= B)
        by (intros y Hy; split; lra).
      destruct (MVT_cor2 G G' x c Hlt
                  (fun y Hy => HGd y (Hin y (conj (proj1 Hy) (proj2 Hy)))))
        as [xg [Hxg Hrg]].
      destruct (MVT_cor2 H H' x c Hlt
                  (fun y Hy => HHd y (Hin y (conj (proj1 Hy) (proj2 Hy)))))
        as [xh [Hxh Hrh]].
      assert (Hneg : forall y, x <= y <= c -> G' y <= 0 /\ H' y <= 0).
      { intros y Hy.
        assert (Hyc : A <= y <= c) by (split; [ lra | lra ]).
        pose proof (Hlo y Hyc) as HL.
        pose proof (Rle_abs (g' y)) as A1.
        pose proof (Rle_abs (- g' y)) as A2. rewrite Rabs_Ropp in A2.
        unfold G', H'. lra. }
      split.
      + destruct (Hneg xg ltac:(lra)) as [S _]. rewrite HG0 in Hxg. nra.
      + destruct (Hneg xh ltac:(lra)) as [_ S]. rewrite HH0 in Hxh. nra.
    - subst x. rewrite HG0, HH0. lra.
    - (* c < x : both derivatives >= 0 on [c,x], and x - c > 0 *)
      assert (Hin : forall y, c <= y <= x -> A <= y <= B)
        by (intros y Hy; split; lra).
      destruct (MVT_cor2 G G' c x Hgt
                  (fun y Hy => HGd y (Hin y (conj (proj1 Hy) (proj2 Hy)))))
        as [xg [Hxg Hrg]].
      destruct (MVT_cor2 H H' c x Hgt
                  (fun y Hy => HHd y (Hin y (conj (proj1 Hy) (proj2 Hy)))))
        as [xh [Hxh Hrh]].
      assert (Hpos : forall y, c <= y <= x -> 0 <= G' y /\ 0 <= H' y).
      { intros y Hy.
        assert (Hyc : c <= y <= B) by (split; [ lra | lra ]).
        pose proof (Hup y Hyc) as HU.
        pose proof (Rle_abs (g' y)) as A1.
        pose proof (Rle_abs (- g' y)) as A2. rewrite Rabs_Ropp in A2.
        unfold G', H'. lra. }
      split.
      + destruct (Hpos xg ltac:(lra)) as [S _]. rewrite HG0 in Hxg. nra.
      + destruct (Hpos xh ltac:(lra)) as [_ S]. rewrite HH0 in Hxh. nra. }
  destruct Hkey as [HG HH]. unfold G, H in HG, HH.
  apply Rabs_le. split; lra.
Qed.

(* ----------------------------------------------------------------- *)
(*  B.  the climb: three steps from a Lipschitz third derivative       *)
(*                                                                    *)
(*  Only the middle step needs an absolute value in the majorant --    *)
(*  (y-c)^3 changes sign at c, so a single polynomial q cannot bound   *)
(*  |g| on both sides.  There it is applied twice, once per side, and  *)
(*  the sign hypothesis on the far side is vacuous.  Steps 1 and 3     *)
(*  have EVEN majorants and go through in one application.            *)
(* ----------------------------------------------------------------- *)

Lemma dlim_cube6 : forall c x,
  derivable_pt_lim (fun y => (y - c) ^ 3 / 6) x ((x - c) ^ 2 / 2).
Proof.
  intros c x.
  apply (derivable_pt_lim_ext (mult_real_fct (/ 2) (fun y => (y - c) ^ 3 / 3))).
  - intro z. unfold mult_real_fct. field.
  - replace ((x - c) ^ 2 / 2) with (/ 2 * (x - c) ^ 2) by field.
    apply derivable_pt_lim_scal. apply dlim_cube.
Qed.

Lemma dlim_cube6m : forall c x,
  derivable_pt_lim (fun y => (c - y) ^ 3 / 6) x (- ((x - c) ^ 2 / 2)).
Proof.
  intros c x.
  apply (derivable_pt_lim_ext (mult_real_fct (-1) (fun y => (y - c) ^ 3 / 6))).
  - intro z. unfold mult_real_fct. field_simplify. ring.
  - replace (- ((x - c) ^ 2 / 2)) with (-1 * ((x - c) ^ 2 / 2)) by ring.
    apply derivable_pt_lim_scal. apply dlim_cube6.
Qed.

Lemma dlim_quart : forall c x,
  derivable_pt_lim (fun y => (y - c) ^ 4 / 24) x ((x - c) ^ 3 / 6).
Proof.
  intros c x.
  apply (derivable_pt_lim_ext (mult_real_fct (/ 24) (sq c * sq c))%F).
  - intro z. unfold mult_real_fct, mult_fct, sq. field.
  - replace ((x - c) ^ 3 / 6)
      with (/ 24 * (2 * (x - c) * sq c x + sq c x * (2 * (x - c))))
      by (unfold sq; field).
    apply (derivable_pt_lim_scal (sq c * sq c)%F (/ 24) x).
    apply derivable_pt_lim_mult; apply dlim_sq2.
Qed.

Lemma climb1 : forall (g g' : R -> R) (A B c K : R),
  A <= c <= B -> 0 <= K ->
  (forall y, A <= y <= B -> derivable_pt_lim g y (g' y)) ->
  g c = 0 ->
  (forall y, A <= y <= B -> Rabs (g' y) <= K * Rabs (y - c)) ->
  forall x, A <= x <= B -> Rabs (g x) <= K * (x - c) ^ 2 / 2.
Proof.
  intros g g' A B c K Hc HK Hgd Hg0 Hb x Hx.
  assert (Hq : forall y, K * (y - c) ^ 2 / 2 = K * ((y - c) ^ 2 / 2))
    by (intro y; field).
  rewrite Hq.
  apply (mvt_sandwich g g' (fun y => K * ((y - c) ^ 2 / 2))
           (fun y => K * (y - c)) A B c Hc Hgd); try assumption.
  - intros y _. apply derivable_pt_lim_scal. apply dlim_sq.
  - field.
  - intros y Hy. eapply Rle_trans; [ apply Hb; split; lra | ].
    rewrite (Rabs_right (y - c)) by lra. apply Rle_refl.
  - intros y Hy. eapply Rle_trans; [ apply Hb; split; lra | ].
    rewrite (Rabs_left1 (y - c)) by lra. right; ring.
Qed.

Lemma climb3 : forall (g g' : R -> R) (A B c K : R),
  A <= c <= B -> 0 <= K ->
  (forall y, A <= y <= B -> derivable_pt_lim g y (g' y)) ->
  g c = 0 ->
  (forall y, A <= y <= B -> Rabs (g' y) <= K * Rabs (y - c) ^ 3 / 6) ->
  forall x, A <= x <= B -> Rabs (g x) <= K * (x - c) ^ 4 / 24.
Proof.
  intros g g' A B c K Hc HK Hgd Hg0 Hb x Hx.
  assert (Hq : forall y, K * (y - c) ^ 4 / 24 = K * ((y - c) ^ 4 / 24))
    by (intro y; field).
  rewrite Hq.
  apply (mvt_sandwich g g' (fun y => K * ((y - c) ^ 4 / 24))
           (fun y => K * ((y - c) ^ 3 / 6)) A B c Hc Hgd); try assumption.
  - intros y _. apply derivable_pt_lim_scal. apply dlim_quart.
  - field.
  - intros y Hy. eapply Rle_trans; [ apply Hb; split; lra | ].
    rewrite (Rabs_right (y - c)) by lra. right; field.
  - intros y Hy. eapply Rle_trans; [ apply Hb; split; lra | ].
    rewrite (Rabs_left1 (y - c)) by lra. right; field.
Qed.

(* the middle step: (y-c)^3 changes sign at c, so one polynomial       *)
(* majorant cannot serve both sides.  Applied once per side, with the  *)
(* far-side hypothesis vacuous (it reduces to |g' c| <= 0, which the   *)
(* input bound already forces).                                        *)
Lemma climb2 : forall (g g' : R -> R) (A B c K : R),
  A <= c <= B -> 0 <= K ->
  (forall y, A <= y <= B -> derivable_pt_lim g y (g' y)) ->
  g c = 0 ->
  (forall y, A <= y <= B -> Rabs (g' y) <= K * (y - c) ^ 2 / 2) ->
  forall x, A <= x <= B -> Rabs (g x) <= K * Rabs (x - c) ^ 3 / 6.
Proof.
  intros g g' A B c K Hc HK Hgd Hg0 Hb x Hx.
  destruct (Rle_dec c x) as [Hge | Hlt].
  - (* right side [c,B] *)
    assert (Hq : K * Rabs (x - c) ^ 3 / 6 = K * ((x - c) ^ 3 / 6)).
    { rewrite (Rabs_right (x - c)) by lra. field. }
    rewrite Hq.
    apply (mvt_sandwich g g' (fun y => K * ((y - c) ^ 3 / 6))
             (fun y => K * ((y - c) ^ 2 / 2)) c B c
             ltac:(lra) (fun y Hy => Hgd y ltac:(lra))).
    + intros y _. apply derivable_pt_lim_scal. apply dlim_cube6.
    + exact Hg0.
    + field.
    + intros y Hy. eapply Rle_trans; [ apply Hb; split; lra | ]. right; field.
    + intros y Hy. assert (Ey : y = c) by lra. subst y.
      eapply Rle_trans; [ apply Hb; split; lra | ]. right; field.
    + lra.
  - (* left side [A,c] *)
    assert (Hq : K * Rabs (x - c) ^ 3 / 6 = K * ((c - x) ^ 3 / 6)).
    { rewrite (Rabs_left (x - c)) by lra. field. }
    rewrite Hq.
    apply (mvt_sandwich g g' (fun y => K * ((c - y) ^ 3 / 6))
             (fun y => K * (- ((y - c) ^ 2 / 2))) A c c
             ltac:(lra) (fun y Hy => Hgd y ltac:(lra))).
    + intros y _. apply derivable_pt_lim_scal. apply dlim_cube6m.
    + exact Hg0.
    + field.
    + intros y Hy. assert (Ey : y = c) by lra. subst y.
      eapply Rle_trans; [ apply Hb; split; lra | ]. right; field.
    + intros y Hy. eapply Rle_trans; [ apply Hb; split; lra | ]. right; field.
    + lra.
Qed.

(* ----------------------------------------------------------------- *)
(*  C.  the cubic Taylor remainder                                    *)
(* ----------------------------------------------------------------- *)
Definition P3 (f f1 f2 f3 : R -> R) (c : R) : R -> R :=
  fun y => f c + f1 c * (y - c) + f2 c * ((y - c) ^ 2 / 2)
           + f3 c * ((y - c) ^ 3 / 6).

Theorem taylor3_bound : forall (f f1 f2 f3 : R -> R) (A B c M4 : R),
  A <= c <= B -> 0 <= M4 ->
  (forall y, A <= y <= B -> derivable_pt_lim f y (f1 y)) ->
  (forall y, A <= y <= B -> derivable_pt_lim f1 y (f2 y)) ->
  (forall y, A <= y <= B -> derivable_pt_lim f2 y (f3 y)) ->
  (forall y z, A <= y <= B -> A <= z <= B ->
     Rabs (f3 y - f3 z) <= M4 * Rabs (y - z)) ->
  forall x, A <= x <= B -> Rabs (f x - P3 f f1 f2 f3 c x) <= M4 * (x - c) ^ 4 / 24.
Proof.
  intros f f1 f2 f3 A B c M4 Hc HM Hd1 Hd2 Hd3 HLip x Hx.
  (* the three remainders, each the derivative of the next *)
  set (g3 := fun y => f3 y - f3 c).
  set (g2 := fun y => f2 y - f2 c - f3 c * (y - c)).
  set (g1 := fun y => f1 y - f1 c - f2 c * (y - c) - f3 c * ((y - c) ^ 2 / 2)).
  set (g0 := fun y => f y - P3 f f1 f2 f3 c y).
  assert (Hd_g2 : forall y, A <= y <= B -> derivable_pt_lim g2 y (g3 y)).
  { intros y Hy. unfold g2, g3.
    replace (f3 y - f3 c) with ((f3 y - 0) - f3 c * 1) by ring.
    apply derivable_pt_lim_minus.
    - apply derivable_pt_lim_minus;
        [ apply Hd3; exact Hy | apply derivable_pt_lim_const ].
    - apply (derivable_pt_lim_scal (fun z => z - c) (f3 c) y 1).
      replace 1 with (1 - 0) by ring.
      apply derivable_pt_lim_minus;
        [ apply derivable_pt_lim_id | apply derivable_pt_lim_const ]. }
  assert (Hd_g1 : forall y, A <= y <= B -> derivable_pt_lim g1 y (g2 y)).
  { intros y Hy. unfold g1, g2.
    replace (f2 y - f2 c - f3 c * (y - c))
      with ((f2 y - 0 - f2 c * 1) - f3 c * (y - c)) by ring.
    apply derivable_pt_lim_minus.
    - apply derivable_pt_lim_minus.
      + apply derivable_pt_lim_minus;
          [ apply Hd2; exact Hy | apply derivable_pt_lim_const ].
      + apply (derivable_pt_lim_scal (fun z => z - c) (f2 c) y 1).
        replace 1 with (1 - 0) by ring.
        apply derivable_pt_lim_minus;
          [ apply derivable_pt_lim_id | apply derivable_pt_lim_const ].
    - apply (derivable_pt_lim_scal (fun z => (z - c) ^ 2 / 2) (f3 c) y (y - c)).
      apply dlim_sq. }
  assert (Hd_g0 : forall y, A <= y <= B -> derivable_pt_lim g0 y (g1 y)).
  { intros y Hy. unfold g0, g1, P3.
    replace (f1 y - f1 c - f2 c * (y - c) - f3 c * ((y - c) ^ 2 / 2))
      with (f1 y - (0 + f1 c * 1 + f2 c * (y - c) + f3 c * ((y - c) ^ 2 / 2)))
      by ring.
    apply derivable_pt_lim_minus; [ apply Hd1; exact Hy | ].
    apply derivable_pt_lim_plus.
    - apply derivable_pt_lim_plus.
      + apply derivable_pt_lim_plus; [ apply derivable_pt_lim_const | ].
        apply (derivable_pt_lim_scal (fun z => z - c) (f1 c) y 1).
        replace 1 with (1 - 0) by ring.
        apply derivable_pt_lim_minus;
          [ apply derivable_pt_lim_id | apply derivable_pt_lim_const ].
      + apply (derivable_pt_lim_scal (fun z => (z - c) ^ 2 / 2) (f2 c) y (y - c)).
        apply dlim_sq.
    - apply (derivable_pt_lim_scal (fun z => (z - c) ^ 3 / 6) (f3 c) y
               ((y - c) ^ 2 / 2)).
      apply dlim_cube6. }
  (* climb *)
  assert (B3 : forall y, A <= y <= B -> Rabs (g3 y) <= M4 * Rabs (y - c))
    by (intros y Hy; unfold g3; apply HLip; assumption).
  assert (B2 : forall y, A <= y <= B -> Rabs (g2 y) <= M4 * (y - c) ^ 2 / 2)
    by (intros y Hy; apply (climb1 g2 g3 A B c M4 Hc HM Hd_g2
                              ltac:(unfold g2; ring) B3); exact Hy).
  assert (B1 : forall y, A <= y <= B -> Rabs (g1 y) <= M4 * Rabs (y - c) ^ 3 / 6)
    by (intros y Hy; apply (climb2 g1 g2 A B c M4 Hc HM Hd_g1
                              ltac:(unfold g1; field) B2); exact Hy).
  apply (climb3 g0 g1 A B c M4 Hc HM Hd_g0
           ltac:(unfold g0, P3; field) B1); exact Hx.
Qed.

(* ----------------------------------------------------------------- *)
(*  D.  the two integrals Simpson needs                               *)
(*                                                                    *)
(*  Both are done by FTC_antideriv against an EXPLICIT antiderivative  *)
(*  rather than by decomposing into RiemannInt_P10 combinations: the   *)
(*  cubic Taylor polynomial has an obvious antiderivative, so one FTC  *)
(*  application replaces four nested linearity steps.                  *)
(* ----------------------------------------------------------------- *)
Definition cub (c : R) : R -> R := fun y => (y - c) ^ 3.
Definition qrt (c : R) : R -> R := fun y => (y - c) ^ 4.

Lemma dlim_cub3 : forall c x, derivable_pt_lim (cub c) x (3 * (x - c) ^ 2).
Proof.
  intros c x. unfold cub.
  apply (derivable_pt_lim_ext (mult_real_fct 6 (fun y => (y - c) ^ 3 / 6))).
  - intro z. unfold mult_real_fct. field.
  - replace (3 * (x - c) ^ 2) with (6 * ((x - c) ^ 2 / 2)) by field.
    apply derivable_pt_lim_scal. apply dlim_cube6.
Qed.

Lemma dlim_quint : forall c x,
  derivable_pt_lim (fun y => (y - c) ^ 5 / 5) x ((x - c) ^ 4).
Proof.
  intros c x.
  apply (derivable_pt_lim_ext (mult_real_fct (/ 5) (sq c * cub c))%F).
  - intro z. unfold mult_real_fct, mult_fct, sq, cub. field.
  - replace ((x - c) ^ 4)
      with (/ 5 * (2 * (x - c) * cub c x + sq c x * (3 * (x - c) ^ 2)))
      by (unfold sq, cub; field).
    apply (derivable_pt_lim_scal (sq c * cub c)%F (/ 5) x).
    apply derivable_pt_lim_mult; [ apply dlim_sq2 | apply dlim_cub3 ].
Qed.

Lemma cont_qrt : forall c x, continuity_pt (qrt c) x.
Proof.
  intros c x. apply derivable_continuous_pt.
  exists (4 * (x - c) ^ 3). unfold qrt.
  apply (derivable_pt_lim_ext (mult_real_fct 4 (fun y => (y - c) ^ 4 / 4))).
  - intro z. unfold mult_real_fct. field.
  - replace (4 * (x - c) ^ 3) with (4 * ((x - c) ^ 3)) by ring.
    apply derivable_pt_lim_scal.
    apply (derivable_pt_lim_ext (mult_real_fct 6 (fun y => (y - c) ^ 4 / 24))).
    + intro z. unfold mult_real_fct. field.
    + replace ((x - c) ^ 3) with (6 * ((x - c) ^ 3 / 6)) by field.
      apply derivable_pt_lim_scal. apply dlim_quart.
Qed.

Theorem int_qrt_val : forall c r (pr : Riemann_integrable (qrt c) (c - r) (c + r)),
  0 <= r -> RiemannInt pr = 2 * r ^ 5 / 5.
Proof.
  intros c r pr Hr.
  assert (Hanti : antiderivative (qrt c) (fun y => (y - c) ^ 5 / 5) (c - r) (c + r)).
  { split; [ | lra ].
    intros x _. exists (exist _ ((x - c) ^ 4) (dlim_quint c x)). reflexivity. }
  rewrite (FTC_antideriv (qrt c) (fun y => (y - c) ^ 5 / 5) (c - r) (c + r)
             ltac:(lra) (fun x _ => cont_qrt c x) pr Hanti).
  field.
Qed.

(* ----------------------------------------------------------------- *)
(*  E.  ONE PANEL                                                     *)
(*                                                                    *)
(*  Simpson is EXACT on cubics: both the integral of P3 and the        *)
(*  Simpson combination applied to P3 equal 2 r f(c) + r^3 f''(c)/3,   *)
(*  the odd terms cancelling by symmetry.  So the entire error is the  *)
(*  error on the remainder, bounded termwise:                         *)
(*     |int R| <= M4 r^5/60   and   |Simpson R| <= M4 r^5/36,          *)
(*  since R(c) = 0 kills the middle node.  Sum 2 M4 r^5/45.            *)
(* ----------------------------------------------------------------- *)
Definition AP3 (f f1 f2 f3 : R -> R) (c : R) : R -> R :=
  fun y => f c * (y - c) + f1 c * ((y - c) ^ 2 / 2)
           + f2 c * ((y - c) ^ 3 / 6) + f3 c * ((y - c) ^ 4 / 24).

Lemma dlim_AP3 : forall f f1 f2 f3 c x,
  derivable_pt_lim (AP3 f f1 f2 f3 c) x (P3 f f1 f2 f3 c x).
Proof.
  intros f f1 f2 f3 c x. unfold AP3.
  replace (P3 f f1 f2 f3 c x)
    with (f c * 1 + f1 c * (x - c) + f2 c * ((x - c) ^ 2 / 2)
          + f3 c * ((x - c) ^ 3 / 6)) by (unfold P3; field).
  apply derivable_pt_lim_plus.
  - apply derivable_pt_lim_plus.
    + apply derivable_pt_lim_plus.
      * apply (derivable_pt_lim_scal (fun z => z - c) (f c) x 1).
        replace 1 with (1 - 0) by ring.
        apply derivable_pt_lim_minus;
          [ apply derivable_pt_lim_id | apply derivable_pt_lim_const ].
      * apply (derivable_pt_lim_scal (fun z => (z - c) ^ 2 / 2) (f1 c) x (x - c)).
        apply dlim_sq.
    + apply (derivable_pt_lim_scal (fun z => (z - c) ^ 3 / 6) (f2 c) x
               ((x - c) ^ 2 / 2)).
      apply dlim_cube6.
  - apply (derivable_pt_lim_scal (fun z => (z - c) ^ 4 / 24) (f3 c) x
             ((x - c) ^ 3 / 6)).
    apply dlim_quart.
Qed.

Lemma cont_P3 : forall f f1 f2 f3 c x, continuity_pt (P3 f f1 f2 f3 c) x.
Proof.
  intros f f1 f2 f3 c x. apply derivable_continuous_pt.
  unfold P3.
  exists (f1 c * 1 + f2 c * (x - c) + f3 c * ((x - c) ^ 2 / 2)).
  apply derivable_pt_lim_plus.
  - apply derivable_pt_lim_plus.
    + replace (f1 c * 1) with (0 + f1 c * 1) by ring.
      apply derivable_pt_lim_plus; [ apply derivable_pt_lim_const | ].
      apply (derivable_pt_lim_scal (fun z => z - c) (f1 c) x 1).
      replace 1 with (1 - 0) by ring.
      apply derivable_pt_lim_minus;
        [ apply derivable_pt_lim_id | apply derivable_pt_lim_const ].
    + apply (derivable_pt_lim_scal (fun z => (z - c) ^ 2 / 2) (f2 c) x (x - c)).
      apply dlim_sq.
  - apply (derivable_pt_lim_scal (fun z => (z - c) ^ 3 / 6) (f3 c) x
             ((x - c) ^ 2 / 2)).
    apply dlim_cube6.
Qed.

(* the exactness, as an equation between the two closed forms *)
Lemma int_P3_val : forall f f1 f2 f3 c r
  (pr : Riemann_integrable (P3 f f1 f2 f3 c) (c - r) (c + r)),
  0 <= r -> RiemannInt pr = 2 * r * f c + r ^ 3 * f2 c / 3.
Proof.
  intros f f1 f2 f3 c r pr Hr.
  assert (Hanti : antiderivative (P3 f f1 f2 f3 c) (AP3 f f1 f2 f3 c)
                    (c - r) (c + r)).
  { split; [ | lra ].
    intros x _.
    exists (exist _ (P3 f f1 f2 f3 c x) (dlim_AP3 f f1 f2 f3 c x)). reflexivity. }
  rewrite (FTC_antideriv (P3 f f1 f2 f3 c) (AP3 f f1 f2 f3 c) (c - r) (c + r)
             ltac:(lra) (fun x _ => cont_P3 f f1 f2 f3 c x) pr Hanti).
  unfold AP3. field.
Qed.

Lemma simpson_P3_val : forall f f1 f2 f3 c r,
  r / 3 * (P3 f f1 f2 f3 c (c - r) + 4 * P3 f f1 f2 f3 c c
           + P3 f f1 f2 f3 c (c + r))
  = 2 * r * f c + r ^ 3 * f2 c / 3.
Proof. intros. unfold P3. field. Qed.

Theorem simpson_single : forall (f f1 f2 f3 : R -> R) (c M4 r : R)
  (prf : Riemann_integrable f (c - r) (c + r)),
  0 <= r -> 0 <= M4 ->
  (forall y, c - r <= y <= c + r -> derivable_pt_lim f y (f1 y)) ->
  (forall y, c - r <= y <= c + r -> derivable_pt_lim f1 y (f2 y)) ->
  (forall y, c - r <= y <= c + r -> derivable_pt_lim f2 y (f3 y)) ->
  (forall y z, c - r <= y <= c + r -> c - r <= z <= c + r ->
     Rabs (f3 y - f3 z) <= M4 * Rabs (y - z)) ->
  Rabs (RiemannInt prf - r / 3 * (f (c - r) + 4 * f c + f (c + r)))
  <= 2 * M4 * r ^ 5 / 45.
Proof.
  intros f f1 f2 f3 c M4 r prf Hr HM Hd1 Hd2 Hd3 HLip.
  assert (Hab : c - r <= c + r) by lra.
  assert (Hc : c - r <= c <= c + r) by lra.
  assert (pr_P3 : Riemann_integrable (P3 f f1 f2 f3 c) (c - r) (c + r))
    by (apply continuity_implies_RiemannInt;
        [ exact Hab | intros x _; apply cont_P3 ]).
  assert (pr_qrt : Riemann_integrable (qrt c) (c - r) (c + r))
    by (apply continuity_implies_RiemannInt;
        [ exact Hab | intros x _; apply cont_qrt ]).
  assert (pr_z : Riemann_integrable (fct_cte 0) (c - r) (c + r))
    by (apply continuity_implies_RiemannInt;
        [ exact Hab | intros x _; apply cont_cte ]).
  pose proof (RiemannInt_P10 (-1) prf pr_P3) as pr_R.
  pose proof (RiemannInt_P16 pr_R) as pr_A.
  pose proof (RiemannInt_P10 (M4 / 24) pr_z pr_qrt) as pr_Q.
  assert (HR : RiemannInt pr_R
               = RiemannInt prf - (2 * r * f c + r ^ 3 * f2 c / 3)).
  { rewrite (RiemannInt_P13 prf pr_P3 pr_R).
    rewrite (int_P3_val f f1 f2 f3 c r pr_P3 Hr). ring. }
  assert (HQ : RiemannInt pr_Q = M4 * r ^ 5 / 60).
  { rewrite (RiemannInt_P13 pr_z pr_qrt pr_Q).
    rewrite (RiemannInt_P15 pr_z).
    rewrite (int_qrt_val c r pr_qrt Hr). field. }
  assert (HT : forall x, c - r <= x <= c + r ->
                 Rabs (f x - P3 f f1 f2 f3 c x) <= M4 * (x - c) ^ 4 / 24)
    by (intros x Hx;
        apply (taylor3_bound f f1 f2 f3 (c - r) (c + r) c M4 Hc HM
                 Hd1 Hd2 Hd3 HLip x Hx)).
  (* the integral part *)
  assert (Hint : Rabs (RiemannInt pr_R) <= M4 * r ^ 5 / 60).
  { eapply Rle_trans; [ apply (RiemannInt_P17 pr_R pr_A Hab) | ].
    rewrite <- HQ.
    apply (RiemannInt_P19 pr_A pr_Q Hab).
    intros x Hx.
    assert (Hxc : c - r <= x <= c + r) by lra.
    pose proof (HT x Hxc) as H.
    unfold fct_cte, qrt.
    replace (f x + -1 * P3 f f1 f2 f3 c x) with (f x - P3 f f1 f2 f3 c x) by ring.
    lra. }
  (* the node part; the middle node vanishes because Q c = f c *)
  assert (HQc : P3 f f1 f2 f3 c c = f c) by (unfold P3; field).
  assert (Hlo : Rabs (f (c - r) - P3 f f1 f2 f3 c (c - r)) <= M4 * r ^ 4 / 24).
  { pose proof (HT (c - r) ltac:(lra)) as H.
    replace ((c - r - c) ^ 4) with (r ^ 4) in H by ring. exact H. }
  assert (Hhi : Rabs (f (c + r) - P3 f f1 f2 f3 c (c + r)) <= M4 * r ^ 4 / 24).
  { pose proof (HT (c + r) ltac:(lra)) as H.
    replace ((c + r - c) ^ 4) with (r ^ 4) in H by ring. exact H. }
  (* split the error into (integral of R) - (Simpson of R) *)
  set (E1 := f (c - r) - P3 f f1 f2 f3 c (c - r)).
  set (E2 := f (c + r) - P3 f f1 f2 f3 c (c + r)).
  assert (Esplit : RiemannInt prf - r / 3 * (f (c - r) + 4 * f c + f (c + r))
                   = RiemannInt pr_R - r / 3 * (E1 + E2)).
  { rewrite HR. unfold E1, E2.
    pose proof (simpson_P3_val f f1 f2 f3 c r) as HS.
    rewrite HQc in HS. lra. }
  rewrite Esplit.
  (* triangle *)
  replace (RiemannInt pr_R - r / 3 * (E1 + E2))
    with (RiemannInt pr_R + - (r / 3 * (E1 + E2))) by ring.
  eapply Rle_trans; [ apply Rabs_triang | ].
  rewrite Rabs_Ropp, Rabs_mult, (Rabs_pos_eq (r / 3)) by lra.
  assert (Hsum : Rabs (E1 + E2) <= 2 * (M4 * r ^ 4 / 24)).
  { eapply Rle_trans; [ apply Rabs_triang | ]. unfold E1, E2. lra. }
  assert (Hnode : r / 3 * Rabs (E1 + E2) <= r / 3 * (2 * (M4 * r ^ 4 / 24)))
    by (apply Rmult_le_compat_l; lra).
  assert (Efin : M4 * r ^ 5 / 60 + r / 3 * (2 * (M4 * r ^ 4 / 24))
               = 2 * M4 * r ^ 5 / 45) by field.
  lra.
Qed.

(* ----------------------------------------------------------------- *)
(*  F.  THE COMPOSITE RULE                                            *)
(*                                                                    *)
(*  Each panel is written SELF-CONTAINED -- its own two endpoints and  *)
(*  midpoint -- rather than in the classical odd/even-indexed form.    *)
(*  The classical form needs a parity side condition and an induction  *)
(*  that retroactively changes the coefficient of the previously       *)
(*  terminal node from 1 to 2, which a Fixpoint cannot do without an   *)
(*  accumulator and a reconciliation lemma.  The panel-local form has  *)
(*  S k |-> (previous) + (one panel), structurally identical to msum,  *)
(*  so CompositeQuad's skeleton transfers line for line.  The cost is  *)
(*  3n evaluations instead of 2n+1; shared nodes are computed twice.   *)
(* ----------------------------------------------------------------- *)
Fixpoint ssum (f : R -> R) (a h : R) (n : nat) : R :=
  match n with
  | O => 0
  | S k => ssum f a h k
           + h / 6 * (f (a + INR k * h)
                      + 4 * f (a + (INR k + / 2) * h)
                      + f (a + INR (S k) * h))
  end.

Theorem composite_simpson : forall (f f1 f2 f3 : R -> R) (a h M4 : R) (n : nat)
  (pr : Riemann_integrable f a (a + INR n * h)),
  0 <= h -> 0 <= M4 ->
  (forall y, a <= y <= a + INR n * h -> derivable_pt_lim f y (f1 y)) ->
  (forall y, a <= y <= a + INR n * h -> derivable_pt_lim f1 y (f2 y)) ->
  (forall y, a <= y <= a + INR n * h -> derivable_pt_lim f2 y (f3 y)) ->
  (forall y z, a <= y <= a + INR n * h -> a <= z <= a + INR n * h ->
     Rabs (f3 y - f3 z) <= M4 * Rabs (y - z)) ->
  Rabs (RiemannInt pr - ssum f a h n) <= INR n * (M4 * h ^ 5 / 720).
Proof.
  intros f f1 f2 f3 a h M4 n.
  induction n as [| n IH]; intros pr Hh HM Hd1 Hd2 Hd3 Hlip.
  - assert (Ez : a + INR 0 * h = a) by (simpl; ring).
    assert (pra : Riemann_integrable f a a).
    { apply continuity_implies_RiemannInt; [ apply Rle_refl | ].
      intros x Hx. apply (cont_of_deriv f f1 a (a + INR 0 * h) Hd1). lra. }
    rewrite (RI_endpoint f a (a + INR 0 * h) a pr pra Ez), (RiemannInt_P9 pra).
    simpl. replace (0 - 0) with 0 by ring. rewrite Rabs_R0. lra.
  - assert (HSn : INR (S n) = INR n + 1) by apply S_INR.
    assert (Hnh : 0 <= INR n * h)
      by (apply Rmult_le_pos; [ apply pos_INR | exact Hh ]).
    assert (Hgrow : a + INR n * h <= a + INR (S n) * h) by (rewrite HSn; nra).
    set (c := a + (INR n + / 2) * h).
    assert (Eb : c - h / 2 = a + INR n * h) by (unfold c; field).
    assert (Ec : c + h / 2 = a + INR (S n) * h) by (unfold c; rewrite HSn; field).
    assert (Hd1_n : forall y, a <= y <= a + INR n * h -> derivable_pt_lim f y (f1 y))
      by (intros y Hy; apply Hd1; lra).
    assert (Hd2_n : forall y, a <= y <= a + INR n * h -> derivable_pt_lim f1 y (f2 y))
      by (intros y Hy; apply Hd2; lra).
    assert (Hd3_n : forall y, a <= y <= a + INR n * h -> derivable_pt_lim f2 y (f3 y))
      by (intros y Hy; apply Hd3; lra).
    assert (Hlip_n : forall y z, a <= y <= a + INR n * h ->
                     a <= z <= a + INR n * h ->
                     Rabs (f3 y - f3 z) <= M4 * Rabs (y - z))
      by (intros y z Hy Hz; apply Hlip; lra).
    assert (prn : Riemann_integrable f a (a + INR n * h)).
    { apply continuity_implies_RiemannInt; [ lra | ].
      intros x Hx. apply (cont_of_deriv f f1 a (a + INR n * h) Hd1_n); exact Hx. }
    assert (prn' : Riemann_integrable f a (c - h / 2)) by (rewrite Eb; exact prn).
    assert (prs : Riemann_integrable f (c - h / 2) (c + h / 2)).
    { apply continuity_implies_RiemannInt; [ lra | ].
      intros x Hx. apply (cont_of_deriv f f1 a (a + INR (S n) * h) Hd1). lra. }
    assert (pr' : Riemann_integrable f a (c + h / 2)) by (rewrite Ec; exact pr).
    pose proof (RiemannInt_P26 prn' prs pr') as Hadd.
    assert (Esplit : RiemannInt pr = RiemannInt prn + RiemannInt prs).
    { rewrite (RI_endpoint f a (a + INR (S n) * h) (c + h / 2) pr pr' (eq_sym Ec)).
      rewrite <- Hadd.
      rewrite (RI_endpoint f a (c - h / 2) (a + INR n * h) prn' prn Eb).
      reflexivity. }
    assert (Hseg : Rabs (RiemannInt prs
                     - (h / 2) / 3 * (f (c - h / 2) + 4 * f c + f (c + h / 2)))
                   <= 2 * M4 * (h / 2) ^ 5 / 45).
    { apply (simpson_single f f1 f2 f3 c M4 (h / 2) prs); try lra.
      - intros y Hy. apply Hd1. lra.
      - intros y Hy. apply Hd2. lra.
      - intros y Hy. apply Hd3. lra.
      - intros y z Hy Hz. apply Hlip; lra. }
    (* move the NODE arguments only: c - h/2 also sits inside prs's TYPE, *)
    (* so a plain rewrite in Hseg would try to abstract it there and fail. *)
    replace (f (c - h / 2)) with (f (a + INR n * h)) in Hseg
      by (rewrite Eb; reflexivity).
    replace (f (c + h / 2)) with (f (a + INR (S n) * h)) in Hseg
      by (rewrite Ec; reflexivity).
    assert (Eseg : (h / 2) / 3 = h / 6) by field.
    assert (Erate : 2 * M4 * (h / 2) ^ 5 / 45 = M4 * h ^ 5 / 720) by field.
    rewrite Eseg, Erate in Hseg.
    pose proof (IH prn Hh HM Hd1_n Hd2_n Hd3_n Hlip_n) as HIH.
    cbn [ssum]. fold c.
    rewrite Esplit.
    replace (RiemannInt prn + RiemannInt prs
             - (ssum f a h n
                + h / 6 * (f (a + INR n * h) + 4 * f c + f (a + INR (S n) * h))))
      with ((RiemannInt prn - ssum f a h n)
            + (RiemannInt prs
               - h / 6 * (f (a + INR n * h) + 4 * f c + f (a + INR (S n) * h))))
      by ring.
    eapply Rle_trans; [ apply Rabs_triang | ].
    rewrite HSn. rewrite HSn in Hseg.
    replace ((INR n + 1) * (M4 * h ^ 5 / 720))
      with (INR n * (M4 * h ^ 5 / 720) + M4 * h ^ 5 / 720) by ring.
    lra.
Qed.

(* the form the quadrature consumes: n panels of width (b-a)/n, with pr *)
(* stated over [a,b] itself so no caller is left with b - a inside a    *)
(* Riemann_integrable TYPE, where it cannot be rewritten.               *)
Corollary composite_simpson_ab : forall (f f1 f2 f3 : R -> R) (a b M4 : R) (n : nat)
  (pr : Riemann_integrable f a b),
  (0 < n)%nat -> a <= b -> 0 <= M4 ->
  (forall y, a <= y <= b -> derivable_pt_lim f y (f1 y)) ->
  (forall y, a <= y <= b -> derivable_pt_lim f1 y (f2 y)) ->
  (forall y, a <= y <= b -> derivable_pt_lim f2 y (f3 y)) ->
  (forall y z, a <= y <= b -> a <= z <= b ->
     Rabs (f3 y - f3 z) <= M4 * Rabs (y - z)) ->
  Rabs (RiemannInt pr - ssum f a ((b - a) / INR n) n)
  <= M4 * (b - a) ^ 5 / (720 * INR n ^ 4).
Proof.
  intros f f1 f2 f3 a b M4 n pr Hn Hab HM Hd1 Hd2 Hd3 Hlip.
  assert (Hn0 : 0 < INR n) by (apply lt_0_INR; lia).
  assert (Hh : 0 <= (b - a) / INR n) by (apply Rle_mult_inv_pos; lra).
  assert (Etop : a + INR n * ((b - a) / INR n) = b) by (field; lra).
  assert (pr' : Riemann_integrable f a (a + INR n * ((b - a) / INR n)))
    by (rewrite Etop; exact pr).
  rewrite (RI_endpoint f a b (a + INR n * ((b - a) / INR n)) pr pr' (eq_sym Etop)).
  assert (Erate : INR n * (M4 * ((b - a) / INR n) ^ 5 / 720)
                = M4 * (b - a) ^ 5 / (720 * INR n ^ 4)) by (field; lra).
  rewrite <- Erate.
  apply (composite_simpson f f1 f2 f3 a ((b - a) / INR n) M4 n pr' Hh HM).
  - intros y Hy. apply Hd1. rewrite Etop in Hy. exact Hy.
  - intros y Hy. apply Hd2. rewrite Etop in Hy. exact Hy.
  - intros y Hy. apply Hd3. rewrite Etop in Hy. exact Hy.
  - intros y z Hy Hz. rewrite Etop in Hy, Hz. apply Hlip; assumption.
Qed.

Print Assumptions mvt_sandwich.
Print Assumptions climb2.
Print Assumptions taylor3_bound.
Print Assumptions int_qrt_val.
Print Assumptions simpson_single.
Print Assumptions composite_simpson_ab.
