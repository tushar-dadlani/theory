(* ================================================================= *)
(*  MidpointQuad.v  --  the midpoint rule with an explicit error term. *)
(*                                                                    *)
(*    taylor1_bound   : |f x - f c - f' c (x-c)| <= M2 (x-c)^2 / 2     *)
(*    midpoint_single : |int_{c-r}^{c+r} f - 2 r f c| <= M2 r^3 / 3    *)
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
(*  for the midpoint rule.  The constant here is the CLASSICAL one,    *)
(*  r^3/3 = h^3/24; an earlier version applied MVT twice to f and got  *)
(*  h^3/12, which costs a factor sqrt(2) in the node count.           *)
(*  Axiom-clean.                                                       *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra.
Require Import ContinuousCoV.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  the first-order Taylor bound, from MVT applied twice               *)
(* ----------------------------------------------------------------- *)
(* the two elementary derivatives the Taylor bound needs; they were   *)
(* below before, but taylor1_bound now uses the quadratic majorant.   *)
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


(* The SHARP first-order Taylor bound: M2 (x-c)^2 / 2, not M2 (x-c)^2. *)
(*                                                                    *)
(* The factor 2 is not cosmetic -- it is the whole difference between  *)
(* the classical composite-midpoint constant h^3/24 and the h^3/12     *)
(* an unrefined argument gives, hence a factor sqrt(2) in the node     *)
(* count.  It is recovered by NOT applying MVT to f directly.  Instead *)
(* consider                                                           *)
(*    G y = M2 (y-c)^2/2 - (f y - f c - f'c (y-c)),                    *)
(* whose derivative M2 (y-c) - (f' y - f' c) has a SIGN fixed by the   *)
(* Lipschitz hypothesis on each side of c.  One MVT on G then gives    *)
(* G x >= 0 in both directions at once, and the mirrored H = q + h     *)
(* gives the other side.  Applying MVT twice to f, as the obvious      *)
(* route does, throws the factor away because it bounds |f' xi - f' c| *)
(* by M2 |x - c| when the average of that over the segment is half as  *)
(* much.  Rests on MVT_cor2 alone, as before.                          *)
Theorem taylor1_bound : forall (f f' : R -> R) (c M2 r x : R),
  0 <= M2 ->
  (forall y, c - r <= y <= c + r -> derivable_pt_lim f y (f' y)) ->
  (forall y z, c - r <= y <= c + r -> c - r <= z <= c + r ->
     Rabs (f' y - f' z) <= M2 * Rabs (y - z)) ->
  c - r <= c <= c + r ->
  c - r <= x <= c + r ->
  Rabs (f x - f c - f' c * (x - c)) <= M2 * (x - c) ^ 2 / 2.
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
  (* the quadratic majorant and its derivative *)
  set (q := fun y => M2 * ((y - c) ^ 2 / 2)).
  set (q' := fun y => M2 * (y - c)).
  assert (Hqd : forall y, derivable_pt_lim q y (q' y)).
  { intro y. unfold q, q'.
    apply (derivable_pt_lim_scal (fun z => (z - c) ^ 2 / 2) M2 y (y - c)).
    apply dlim_sq. }
  assert (Hq0 : q c = 0) by (unfold q; field).
  (* the two auxiliary functions *)
  set (G := fun y => q y - h y).
  set (G' := fun y => q' y - h' y).
  set (H := fun y => q y + h y).
  set (H' := fun y => q' y + h' y).
  assert (HGd : forall y, c - r <= y <= c + r -> derivable_pt_lim G y (G' y))
    by (intros y Hy; unfold G, G';
        apply derivable_pt_lim_minus; [ apply Hqd | apply Hhd; exact Hy ]).
  assert (HHd : forall y, c - r <= y <= c + r -> derivable_pt_lim H y (H' y))
    by (intros y Hy; unfold H, H';
        apply derivable_pt_lim_plus; [ apply Hqd | apply Hhd; exact Hy ]).
  (* the Lipschitz hypothesis, two-sided, at any y between x and c *)
  assert (Hsign : forall y, c - r <= y <= c + r ->
            - (M2 * Rabs (y - c)) <= h' y <= M2 * Rabs (y - c)).
  { intros y Hy. unfold h'.
    pose proof (HLip y c Hy Hc) as HL.
    pose proof (Rle_abs (f' y - f' c)) as A1.
    pose proof (Rle_abs (- (f' y - f' c))) as A2.
    rewrite Rabs_Ropp in A2. lra. }
  assert (Hkey : 0 <= G x /\ 0 <= H x).
  { destruct (total_order_T x c) as [[Hlt | Heq] | Hgt].
    - (* x < c : both G' and H' are <= 0 on [x, c], and x - c < 0 *)
      assert (Hin : forall y, x <= y <= c -> c - r <= y <= c + r)
        by (intros y Hy; split; lra).
      destruct (MVT_cor2 G G' x c Hlt
                  (fun y Hy => HGd y (Hin y (conj (proj1 Hy) (proj2 Hy)))))
        as [xg [Hxg Hrg]].
      destruct (MVT_cor2 H H' x c Hlt
                  (fun y Hy => HHd y (Hin y (conj (proj1 Hy) (proj2 Hy)))))
        as [xh [Hxh Hrh]].
      assert (HG0 : G c = 0) by (unfold G; rewrite Hq0, Hh0; ring).
      assert (HH0 : H c = 0) by (unfold H; rewrite Hq0, Hh0; ring).
      (* on [x,c] every y has |y - c| = c - y *)
      assert (Hneg : forall y, x <= y <= c -> G' y <= 0 /\ H' y <= 0).
      { intros y Hy.
        assert (Hyr : c - r <= y <= c + r) by (apply Hin; exact Hy).
        destruct (Hsign y Hyr) as [S1 S2].
        assert (Ea : Rabs (y - c) = c - y)
          by (rewrite Rabs_left1 by lra; ring).
        rewrite Ea in S1, S2. unfold G', H', q'. lra. }
      split.
      + destruct (Hneg xg ltac:(lra)) as [S _]. rewrite HG0 in Hxg. nra.
      + destruct (Hneg xh ltac:(lra)) as [_ S]. rewrite HH0 in Hxh. nra.
    - (* x = c *)
      subst x. unfold G, H. rewrite Hq0, Hh0. split; lra.
    - (* c < x : both G' and H' are >= 0 on [c, x], and x - c > 0 *)
      assert (Hin : forall y, c <= y <= x -> c - r <= y <= c + r)
        by (intros y Hy; split; lra).
      destruct (MVT_cor2 G G' c x Hgt
                  (fun y Hy => HGd y (Hin y (conj (proj1 Hy) (proj2 Hy)))))
        as [xg [Hxg Hrg]].
      destruct (MVT_cor2 H H' c x Hgt
                  (fun y Hy => HHd y (Hin y (conj (proj1 Hy) (proj2 Hy)))))
        as [xh [Hxh Hrh]].
      assert (HG0 : G c = 0) by (unfold G; rewrite Hq0, Hh0; ring).
      assert (HH0 : H c = 0) by (unfold H; rewrite Hq0, Hh0; ring).
      assert (Hpos : forall y, c <= y <= x -> 0 <= G' y /\ 0 <= H' y).
      { intros y Hy.
        assert (Hyr : c - r <= y <= c + r) by (apply Hin; exact Hy).
        destruct (Hsign y Hyr) as [S1 S2].
        assert (Ea : Rabs (y - c) = y - c)
          by (rewrite Rabs_right by lra; ring).
        rewrite Ea in S1, S2. unfold G', H', q'. lra. }
      split.
      + destruct (Hpos xg ltac:(lra)) as [S _]. rewrite HG0 in Hxg. nra.
      + destruct (Hpos xh ltac:(lra)) as [_ S]. rewrite HH0 in Hxh. nra. }
  destruct Hkey as [HG HH].
  unfold G, H, q, h in HG, HH.
  apply Rabs_le. split; lra.
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

(* ----------------------------------------------------------------- *)
(*  THE MIDPOINT BOUND ON ONE SUBINTERVAL                              *)
(* ----------------------------------------------------------------- *)
Lemma cont_cte : forall k x, continuity_pt (fct_cte k) x.
Proof. intros k x. apply derivable_continuous_pt. exists 0. apply derivable_pt_lim_const. Qed.

Theorem midpoint_single : forall (f f' : R -> R) (c M2 r : R)
  (prf : Riemann_integrable f (c - r) (c + r)),
  0 <= r -> 0 <= M2 ->
  (forall y, c - r <= y <= c + r -> derivable_pt_lim f y (f' y)) ->
  (forall y z, c - r <= y <= c + r -> c - r <= z <= c + r ->
     Rabs (f' y - f' z) <= M2 * Rabs (y - z)) ->
  Rabs (RiemannInt prf - 2 * r * f c) <= M2 * r ^ 3 / 3.
Proof.
  intros f f' c M2 r prf Hr HM Hder HLip.
  assert (Hab : c - r <= c + r) by lra.
  assert (Hc : c - r <= c <= c + r) by lra.
  (* the pieces, all integrable because continuous *)
  assert (pr_cte : Riemann_integrable (fct_cte (f c)) (c - r) (c + r))
    by (apply continuity_implies_RiemannInt; [ exact Hab | intros x _; apply cont_cte ]).
  assert (pr_lin : Riemann_integrable (lin c) (c - r) (c + r))
    by (apply continuity_implies_RiemannInt; [ exact Hab | intros x _; apply cont_lin ]).
  assert (pr_sq : Riemann_integrable (sq c) (c - r) (c + r))
    by (apply continuity_implies_RiemannInt; [ exact Hab | intros x _; apply cont_sq ]).
  assert (pr_z : Riemann_integrable (fct_cte 0) (c - r) (c + r))
    by (apply continuity_implies_RiemannInt; [ exact Hab | intros x _; apply cont_cte ]).
  pose proof (RiemannInt_P10 (f' c) pr_cte pr_lin) as pr_g.
  pose proof (RiemannInt_P10 (-1) prf pr_g) as pr_R.
  pose proof (RiemannInt_P16 pr_R) as pr_A.
  pose proof (RiemannInt_P10 (M2 / 2) pr_z pr_sq) as pr_Q.
  (* the linear approximant integrates to 2 r f c : the cancellation *)
  assert (Hg : RiemannInt pr_g = 2 * r * f c).
  { rewrite (RiemannInt_P13 pr_cte pr_lin pr_g).
    rewrite (RiemannInt_P15 pr_cte).
    rewrite (int_lin_zero c r pr_lin Hr). ring. }
  (* so the remainder integral IS the quantity we are bounding *)
  assert (HR : RiemannInt pr_R = RiemannInt prf - 2 * r * f c).
  { rewrite (RiemannInt_P13 prf pr_g pr_R), Hg. ring. }
  (* and the majorant integrates to 2 M2 r^3 / 3 *)
  assert (HQ : RiemannInt pr_Q = M2 * r ^ 3 / 3).
  { rewrite (RiemannInt_P13 pr_z pr_sq pr_Q).
    rewrite (RiemannInt_P15 pr_z).
    rewrite (int_sq_val c r pr_sq Hr). field. }
  rewrite <- HR.
  eapply Rle_trans; [ apply (RiemannInt_P17 pr_R pr_A Hab) | ].
  rewrite <- HQ.
  apply (RiemannInt_P19 pr_A pr_Q Hab).
  intros x Hx.
  assert (Hxc : c - r <= x <= c + r) by lra.
  pose proof (taylor1_bound f f' c M2 r x HM Hder HLip Hc Hxc) as HT.
  unfold fct_cte, lin, sq.
  replace (f x + -1 * (f c + f' c * (x - c)))
    with (f x - f c - f' c * (x - c)) by ring.
  lra.
Qed.

Print Assumptions midpoint_single.
