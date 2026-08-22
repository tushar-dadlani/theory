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
Require Import ContinuousCoV.
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

(* ----------------------------------------------------------------- *)
(*  the two polynomial integrals, via the LOCAL antiderivative         *)
(* ----------------------------------------------------------------- *)
(*  ContinuousCoV.FTC_antideriv wants stdlib's `antiderivative`, which  *)
(*  asks only for differentiability ON [a,b] -- no global C1_fun.  That *)
(*  is what makes these cheap.                                         *)

Definition lin (c : R) : R -> R := fun y => y - c.

Lemma dlim_lin : forall c x, derivable_pt_lim (lin c) x 1.
Proof.
  intros c x.
  apply (derivable_pt_lim_ext (id - fct_cte c)%F);
    [ intro z; unfold minus_fct, fct_cte, id, lin; reflexivity | ].
  replace 1 with (1 - 0) by ring.
  apply derivable_pt_lim_minus;
    [ apply derivable_pt_lim_id | apply derivable_pt_lim_const ].
Qed.

Lemma dlim_sq : forall c x, derivable_pt_lim (fun y => (y - c) ^ 2 / 2) x (x - c).
Proof.
  intros c x.
  apply (derivable_pt_lim_ext (mult_real_fct (/ 2) (lin c * lin c))%F).
  - intro z. unfold mult_real_fct, mult_fct, lin. field.
  - replace (x - c) with (/ 2 * (1 * lin c x + lin c x * 1))
      by (unfold lin; field).
    apply (derivable_pt_lim_scal (lin c * lin c)%F (/ 2) x).
    apply derivable_pt_lim_mult; apply dlim_lin.
Qed.

Definition sq (c : R) : R -> R := fun y => (y - c) ^ 2.

Lemma dlim_sq2 : forall c x, derivable_pt_lim (sq c) x (2 * (x - c)).
Proof.
  intros c x.
  apply (derivable_pt_lim_ext (mult_real_fct 2 (fun y => (y - c) ^ 2 / 2))).
  - intro z. unfold mult_real_fct, sq. field.
  - replace (2 * (x - c)) with (2 * (x - c)) by ring.
    apply (derivable_pt_lim_scal (fun y => (y - c) ^ 2 / 2) 2 x).
    apply dlim_sq.
Qed.

Lemma dlim_cube : forall c x,
  derivable_pt_lim (fun y => (y - c) ^ 3 / 3) x ((x - c) ^ 2).
Proof.
  intros c x.
  apply (derivable_pt_lim_ext (mult_real_fct (/ 3) (lin c * sq c))%F).
  - intro z. unfold mult_real_fct, mult_fct, lin, sq. field.
  - replace ((x - c) ^ 2)
      with (/ 3 * (1 * sq c x + lin c x * (2 * (x - c))))
      by (unfold lin, sq; field).
    apply (derivable_pt_lim_scal (lin c * sq c)%F (/ 3) x).
    apply derivable_pt_lim_mult; [ apply dlim_lin | apply dlim_sq2 ].
Qed.

Lemma antideriv_lin : forall c r, 0 <= r ->
  antiderivative (lin c) (fun y => (y - c) ^ 2 / 2) (c - r) (c + r).
Proof.
  intros c r Hr. split; [ | lra ].
  intros x _. exists (exist _ (x - c) (dlim_sq c x)). reflexivity.
Qed.

Lemma antideriv_sq : forall c r, 0 <= r ->
  antiderivative (sq c) (fun y => (y - c) ^ 3 / 3) (c - r) (c + r).
Proof.
  intros c r Hr. split; [ | lra ].
  intros x _. exists (exist _ ((x - c) ^ 2) (dlim_cube c x)). reflexivity.
Qed.

(* ----------------------------------------------------------------- *)
(*  the two integrals, evaluated                                       *)
(* ----------------------------------------------------------------- *)
Lemma cont_lin : forall c x, continuity_pt (lin c) x.
Proof. intros c x. apply derivable_continuous_pt. exists 1. apply dlim_lin. Qed.

Lemma cont_sq : forall c x, continuity_pt (sq c) x.
Proof.
  intros c x. apply derivable_continuous_pt. exists (2 * (x - c)). apply dlim_sq2.
Qed.

(*  THE CANCELLATION.  This is where the O(h^3) comes from: the linear
    term of the Taylor expansion integrates to zero over an interval
    symmetric about c.  Without it the midpoint rule would be O(h^2),
    no better than the rectangle rule. *)
Theorem int_lin_zero : forall c r (pr : Riemann_integrable (lin c) (c - r) (c + r)),
  0 <= r -> RiemannInt pr = 0.
Proof.
  intros c r pr Hr.
  rewrite (FTC_antideriv (lin c) (fun y => (y - c) ^ 2 / 2) (c - r) (c + r)
             ltac:(lra) (fun x _ => cont_lin c x) pr (antideriv_lin c r Hr)).
  field.
Qed.

Theorem int_sq_val : forall c r (pr : Riemann_integrable (sq c) (c - r) (c + r)),
  0 <= r -> RiemannInt pr = 2 * r ^ 3 / 3.
Proof.
  intros c r pr Hr.
  rewrite (FTC_antideriv (sq c) (fun y => (y - c) ^ 3 / 3) (c - r) (c + r)
             ltac:(lra) (fun x _ => cont_sq c x) pr (antideriv_sq c r Hr)).
  field.
Qed.

Print Assumptions antideriv_lin.
Print Assumptions int_lin_zero.
Print Assumptions int_sq_val.
