(* ================================================================= *)
(*  MidpointQuad.v  --  the midpoint rule with an explicit error term. *)
(*                                                                    *)
(*    taylor1_bound   : |f x - f c - f' c (x-c)| <= M2 (x-c)^2         *)
(*    midpoint_single : |int_{c-r}^{c+r} f - 2 r f c| <= 2 M2 r^3 / 3  *)
(*                                                                    *)
(*  Stage 4b, second brick.  Taylor_Lagrange is NOT in this Stdlib, so *)
(*  the O(h^3) midpoint bound has to be built by hand.  Everything     *)
(*  below rests on MVT_cor2 alone.                                     *)
(*                                                                    *)
(*  The second-derivative hypothesis is stated as a LIPSCHITZ          *)
(*  condition on f' rather than as a bound on f''.  That is both       *)
(*  weaker (f'' need not exist) and easier to discharge for the        *)
(*  integrand at hand, and it is exactly what an application of the    *)
(*  mean value theorem to f' would produce anyway.                     *)
(*                                                                    *)
(*  The rate matters: the O(h) rectangle bound is far easier to prove  *)
(*  but would need ~670000 nodes on [0, ln 5] for 1e-6, against ~2100  *)
(*  for the midpoint rule.  Going through MVT twice instead of once    *)
(*  costs a factor 2 against the classical h^3/24 -- the constant here *)
(*  is 2 r^3/3 = h^3/12 -- which is irrelevant next to the change in   *)
(*  exponent.  Axiom-clean.                                           *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  the first-order Taylor bound, from MVT applied twice               *)
(* ----------------------------------------------------------------- *)
Theorem taylor1_bound : forall (f f' : R -> R) (c M2 r x : R),
  0 <= M2 ->
  (forall y, c - r <= y <= c + r -> derivable_pt_lim f y (f' y)) ->
  (forall y z, c - r <= y <= c + r -> c - r <= z <= c + r ->
     Rabs (f' y - f' z) <= M2 * Rabs (y - z)) ->
  c - r <= c <= c + r ->
  c - r <= x <= c + r ->
  Rabs (f x - f c - f' c * (x - c)) <= M2 * (x - c) ^ 2.
Proof.
  intros f f' c M2 r x HM Hder HLip Hc Hx.
  set (h := fun y => f y - f c - f' c * (y - c)).
  set (h' := fun y => f' y - f' c).
  assert (Hhd : forall y, c - r <= y <= c + r -> derivable_pt_lim h y (h' y)).
  { intros y Hy. unfold h, h'.
    apply (derivable_pt_lim_ext
             ((f - fct_cte (f c)) - mult_real_fct (f' c) (id - fct_cte c))%F).
    - intro z. unfold minus_fct, fct_cte, mult_real_fct, id. reflexivity.
    - replace (f' y - f' c) with ((f' y - 0) - f' c * (1 - 0)) by ring.
      apply derivable_pt_lim_minus.
      + apply derivable_pt_lim_minus;
          [ apply Hder; exact Hy | apply derivable_pt_lim_const ].
      + apply derivable_pt_lim_scal.
        apply derivable_pt_lim_minus;
          [ apply derivable_pt_lim_id | apply derivable_pt_lim_const ]. }
  assert (Hh0 : h c = 0) by (unfold h; ring).
  destruct (total_order_T x c) as [[Hlt | Heq] | Hgt].
  - (* x < c *)
    destruct (MVT_cor2 h h' x c Hlt
                (fun y Hy => Hhd y (conj (Rle_trans _ _ _ (proj1 Hx) (proj1 Hy))
                                         (Rle_trans _ _ _ (proj2 Hy) (proj2 Hc)))))
      as [xi [Hxi Hrange]].
    rewrite Hh0 in Hxi.
    assert (Hval : h x = - (h' xi * (c - x))) by (unfold h in *; lra).
    assert (Hb : Rabs (h' xi) <= M2 * Rabs (xi - c)).
    { unfold h'. apply HLip; [ split; lra | exact Hc ]. }
    assert (Hxic : Rabs (xi - c) <= Rabs (x - c))
      by (rewrite !Rabs_left1 by lra; lra).
    unfold h in Hval. rewrite Hval, Rabs_Ropp, Rabs_mult.
    assert (Hcx : Rabs (c - x) = Rabs (x - c)) by (rewrite <- Rabs_Ropp; f_equal; ring).
    rewrite Hcx.
    assert (Hpos : 0 <= Rabs (x - c)) by apply Rabs_pos.
    assert (Hsq : (x - c) ^ 2 = Rabs (x - c) * Rabs (x - c))
      by (rewrite <- Rabs_mult; rewrite Rabs_right by nra; ring).
    rewrite Hsq.
    assert (Hstep : Rabs (h' xi) <= M2 * Rabs (x - c)) by nra.
    assert (Hfin : Rabs (h' xi) * Rabs (x - c) <= M2 * Rabs (x - c) * Rabs (x - c))
      by (apply Rmult_le_compat_r; [ exact Hpos | exact Hstep ]).
    nra.
  - (* x = c *)
    subst x. replace (f c - f c - f' c * (c - c)) with 0 by ring.
    rewrite Rabs_R0. replace ((c - c) ^ 2) with 0 by ring. lra.
  - (* c < x *)
    destruct (MVT_cor2 h h' c x Hgt
                (fun y Hy => Hhd y (conj (Rle_trans _ _ _ (proj1 Hc) (proj1 Hy))
                                         (Rle_trans _ _ _ (proj2 Hy) (proj2 Hx)))))
      as [xi [Hxi Hrange]].
    rewrite Hh0 in Hxi.
    assert (Hval : h x = h' xi * (x - c)) by (unfold h in *; lra).
    assert (Hb : Rabs (h' xi) <= M2 * Rabs (xi - c))
      by (unfold h'; apply HLip; [ split; lra | exact Hc ]).
    assert (Hxic : Rabs (xi - c) <= Rabs (x - c))
      by (rewrite !Rabs_right by lra; lra).
    unfold h in Hval. rewrite Hval, Rabs_mult.
    assert (Hpos : 0 <= Rabs (x - c)) by apply Rabs_pos.
    assert (Hsq : (x - c) ^ 2 = Rabs (x - c) * Rabs (x - c))
      by (rewrite <- Rabs_mult; rewrite Rabs_right by nra; ring).
    rewrite Hsq.
    assert (Hstep : Rabs (h' xi) <= M2 * Rabs (x - c)) by nra.
    assert (Hfin : Rabs (h' xi) * Rabs (x - c) <= M2 * Rabs (x - c) * Rabs (x - c))
      by (apply Rmult_le_compat_r; [ exact Hpos | exact Hstep ]).
    nra.
Qed.

Print Assumptions taylor1_bound.
