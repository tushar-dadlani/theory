(* ================================================================= *)
(*  TintCoV.v  --  the u = e^t bridge between Newman's integrand and   *)
(*  the Tauberian one.                                                 *)
(*                                                                    *)
(*  Newman's contour argument delivers convergence of                  *)
(*      int_0^oo f(t) dt,      f(t) = psi(e^t) e^{-t} - 1              *)
(*  while TauberianSqueeze.TintCauchy is about                         *)
(*      int_x^y tint(u) du,    tint(u) = (psi(u) - u)/u^2.             *)
(*  Under u = e^t these are the same integral:                         *)
(*      f(t) dt = (psi(u)/u - 1) du/u = (psi(u) - u)/u^2 du.           *)
(*                                                                    *)
(*  Both integrands are discontinuous (psi is a step function), so the *)
(*  change of variables is done CELL BY CELL, where each side agrees   *)
(*  on the open cell with a continuous function, and the endpoints are *)
(*  absorbed by RiemannInt_P18 / PsiRIntegrable.Riemann_integrable_-   *)
(*  ext_open.  LocalCoV.cov_local does the continuous case.            *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia Arith.
Require Import ContinuousCoV LocalCoV Chebyshev ChebyshevPsiR PsiRIntegrable
        TauberianBlock TauberianSqueeze PrimePowerReindex.
Open Scope R_scope.

Lemma ln_mono_le : forall u v, 0 < u -> u <= v -> ln u <= ln v.
Proof.
  intros u v Hu Huv. destruct (Rle_lt_or_eq_dec u v Huv) as [Hlt | He];
    [ left; apply ln_increasing; assumption | rewrite He; apply Rle_refl ].
Qed.

(* Newman's integrand, in t-coordinates *)
Definition nf (t : R) : R := tint (exp t) * exp t.

(* the continuous comparison on the cell [N, N+1] *)
Definition hu (N : nat) (u : R) : R := (psi N - u) / (u * u).

Lemma hu_cont : forall N u, 0 < u -> continuity_pt (hu N) u.
Proof.
  intros N u Hu. unfold hu. apply continuity_pt_div.
  - apply continuity_pt_minus;
      [ apply continuity_pt_const; intros x y; reflexivity
      | apply derivable_continuous_pt; exists 1; apply derivable_pt_lim_id ].
  - apply continuity_pt_mult;
      apply derivable_continuous_pt; exists 1; apply derivable_pt_lim_id.
  - nra.
Qed.

Lemma cont_exp2 : forall x, continuity_pt exp x.
Proof.
  intro x; apply derivable_continuous_pt; exists (exp x); apply derivable_pt_lim_exp.
Qed.

(* on an open t-cell, nf agrees with a continuous function *)
Lemma nf_cell_eq : forall (N : nat) (a b t : R), (1 <= N)%nat ->
  ln (INR N) <= a -> b <= ln (INR (S N)) -> a < t < b ->
  nf t = hu N (exp t) * exp t.
Proof.
  intros N a b t HN Ha Hb Ht.
  assert (HN0 : 0 < INR N) by (apply lt_0_INR; lia).
  assert (HSN0 : 0 < INR (S N)) by (apply lt_0_INR; lia).
  assert (Hlo : INR N <= exp t).
  { rewrite <- (exp_ln (INR N) HN0). destruct Ht.
    destruct (Rle_lt_or_eq_dec (ln (INR N)) t ltac:(lra)) as [Hlt | He];
      [ left; apply exp_increasing; exact Hlt | rewrite He; apply Rle_refl ]. }
  assert (Hhi : exp t < INR (S N)).
  { rewrite <- (exp_ln (INR (S N)) HSN0). destruct Ht.
    apply exp_increasing. lra. }
  unfold nf, tint, hu. rewrite (psiR_step N (exp t) (conj Hlo Hhi)). reflexivity.
Qed.

Lemma nf_int_cell : forall (N : nat) (a b : R), (1 <= N)%nat ->
  ln (INR N) <= a -> a <= b -> b <= ln (INR (S N)) ->
  Riemann_integrable nf a b.
Proof.
  intros N a b HN Ha Hab Hb.
  apply (Riemann_integrable_ext_open nf (fun t => hu N (exp t) * exp t) a b Hab).
  - intros t Ht. exact (nf_cell_eq N a b t HN Ha Hb Ht).
  - destruct (Rle_lt_or_eq_dec a b Hab) as [Hlt | He];
      [ | rewrite <- He; apply RiemannInt_P7 ].
    apply RiemannInt_P6; [ exact Hlt | ].
    intros x Hx. apply continuity_pt_mult; [ | apply cont_exp2 ].
    apply (continuity_pt_comp exp (hu N));
      [ apply cont_exp2 | apply hu_cont; apply exp_pos ].
Qed.

(* ----------------------------------------------------------------- *)
(*  The change of variables, on one cell.                             *)
(* ----------------------------------------------------------------- *)

Lemma cov_cell : forall (N : nat) (a b : R), (1 <= N)%nat ->
  ln (INR N) <= a -> a <= b -> b <= ln (INR (S N)) ->
  forall (prL : Riemann_integrable nf a b)
         (prR : Riemann_integrable tint (exp a) (exp b)),
    RiemannInt prL = RiemannInt prR.
Proof.
  intros N a b HN Ha Hab Hb prL prR.
  assert (HN0 : 0 < INR N) by (apply lt_0_INR; lia).
  assert (HSN0 : 0 < INR (S N)) by (apply lt_0_INR; lia).
  assert (Hea : 0 < exp a) by apply exp_pos.
  assert (Heab : exp a <= exp b).
  { destruct (Rle_lt_or_eq_dec a b Hab) as [Hlt | He];
      [ left; apply exp_increasing; exact Hlt | rewrite He; apply Rle_refl ]. }
  (* left side: nf agrees with the continuous integrand on the open cell *)
  assert (prL' : Riemann_integrable (fun t => hu N (exp t) * exp t) a b).
  { destruct (Rle_lt_or_eq_dec a b Hab) as [Hlt | He];
      [ | rewrite <- He; apply RiemannInt_P7 ].
    apply RiemannInt_P6; [ exact Hlt | ].
    intros x Hx. apply continuity_pt_mult; [ | apply cont_exp2 ].
    apply (continuity_pt_comp exp (hu N));
      [ apply cont_exp2 | apply hu_cont; apply exp_pos ]. }
  rewrite (RiemannInt_P18 prL prL' Hab
             (fun t Ht => nf_cell_eq N a b t HN Ha Hb Ht)).
  (* right side: tint agrees with hu N on the open image cell *)
  assert (prR' : Riemann_integrable (hu N) (exp a) (exp b)).
  { destruct (Rle_lt_or_eq_dec (exp a) (exp b) Heab) as [Hlt | He];
      [ | rewrite <- He; apply RiemannInt_P7 ].
    apply RiemannInt_P6; [ exact Hlt | ].
    intros x Hx. apply hu_cont. lra. }
  rewrite (RiemannInt_P18 prR prR' Heab).
  - (* the continuous change of variables *)
    apply (cov_local exp exp (hu N) a b Hab).
    + intros t Ht. apply derivable_pt_lim_exp.
    + intros t Ht. apply cont_exp2.
    + intros t Ht. split.
      * destruct (Rle_lt_or_eq_dec a t (proj1 Ht)) as [Hlt | He];
          [ left; apply exp_increasing; exact Hlt | rewrite He; apply Rle_refl ].
      * destruct (Rle_lt_or_eq_dec t b (proj2 Ht)) as [Hlt | He];
          [ left; apply exp_increasing; exact Hlt | rewrite He; apply Rle_refl ].
    + intros u Hu. apply hu_cont. lra.
  - (* tint = hu N on the open image cell *)
    intros u Hu.
    assert (Hlo : INR N <= u).
    { apply Rle_trans with (exp a); [ | lra ].
      rewrite <- (exp_ln (INR N) HN0).
      destruct (Rle_lt_or_eq_dec (ln (INR N)) a Ha) as [Hlt | He];
        [ left; apply exp_increasing; exact Hlt | rewrite He; apply Rle_refl ]. }
    assert (Hhi : u < INR (S N)).
    { apply Rlt_le_trans with (exp b); [ lra | ].
      rewrite <- (exp_ln (INR (S N)) HSN0).
      destruct (Rle_lt_or_eq_dec b (ln (INR (S N))) Hb) as [Hlt | He];
        [ left; apply exp_increasing; exact Hlt | rewrite He; apply Rle_refl ]. }
    unfold tint, hu. rewrite (psiR_step N u (conj Hlo Hhi)). reflexivity.
Qed.

(* ----------------------------------------------------------------- *)
(*  Gluing across cells.  Breakpoints are ln (INR N), N >= 1.         *)
(* ----------------------------------------------------------------- *)

Lemma floor_exp_ge1 : forall a, 0 <= a -> (1 <= floorN (exp a))%nat.
Proof.
  intros a Ha.
  assert (H1 : 1 <= exp a) by (rewrite <- exp_0; destruct (Rle_lt_or_eq_dec 0 a Ha) as [H|H];
    [ left; apply exp_increasing; exact H | rewrite <- H; apply Rle_refl ]).
  destruct (floorN_spec (exp a) ltac:(pose proof (exp_pos a); lra)) as [Hf1 Hf2].
  destruct (Nat.eq_dec (floorN (exp a)) 0) as [Hz | Hz]; [ | lia ].
  rewrite Hz in Hf2. simpl in Hf2. lra.
Qed.

Lemma cell_lo : forall a, 0 <= a -> ln (INR (floorN (exp a))) <= a.
Proof.
  intros a Ha.
  assert (HN : (1 <= floorN (exp a))%nat) by (apply floor_exp_ge1; exact Ha).
  assert (HN0 : 0 < INR (floorN (exp a))) by (apply lt_0_INR; lia).
  destruct (floorN_spec (exp a) ltac:(pose proof (exp_pos a); lra)) as [Hf1 _].
  assert (H : ln (INR (floorN (exp a))) <= ln (exp a)).
  { destruct (Rle_lt_or_eq_dec _ _ Hf1) as [Hlt | He];
      [ left; apply ln_increasing; assumption | rewrite He; apply Rle_refl ]. }
  rewrite ln_exp in H. exact H.
Qed.

Lemma cell_hi : forall a b, 0 <= a -> a <= b ->
  (floorN (exp b) <= floorN (exp a))%nat ->
  b <= ln (INR (S (floorN (exp a)))).
Proof.
  intros a b Ha Hab Hk.
  assert (Hb0 : 0 <= b) by lra.
  assert (HSN0 : 0 < INR (S (floorN (exp a)))) by (apply lt_0_INR; lia).
  destruct (floorN_spec (exp b) ltac:(pose proof (exp_pos b); lra)) as [_ Hf2].
  assert (Hle : exp b < INR (S (floorN (exp a)))).
  { rewrite S_INR.
    assert (INR (floorN (exp b)) <= INR (floorN (exp a))) by (apply le_INR; lia).
    lra. }
  assert (H : ln (exp b) <= ln (INR (S (floorN (exp a)))))
    by (left; apply ln_increasing; [ apply exp_pos | exact Hle ]).
  rewrite ln_exp in H. exact H.
Qed.

Lemma nf_int_k : forall (k : nat) (a b : R), 0 <= a -> a <= b ->
  (floorN (exp b) <= floorN (exp a) + k)%nat -> Riemann_integrable nf a b.
Proof.
  induction k as [| k IH]; intros a b Ha Hab Hk.
  - apply (nf_int_cell (floorN (exp a)) a b (floor_exp_ge1 a Ha)
             (cell_lo a Ha) Hab).
    apply cell_hi; [ exact Ha | exact Hab | lia ].
  - destruct (le_gt_dec (floorN (exp b)) (floorN (exp a) + k)) as [Hle | Hgt].
    + exact (IH a b Ha Hab Hle).
    + set (c := ln (INR (S (floorN (exp a))))).
      assert (HN : (1 <= floorN (exp a))%nat) by (apply floor_exp_ge1; exact Ha).
      assert (HSN0 : 0 < INR (S (floorN (exp a)))) by (apply lt_0_INR; lia).
      assert (Hexpc : exp c = INR (S (floorN (exp a))))
        by (unfold c; apply exp_ln; exact HSN0).
      assert (Hac : a <= c).
      { destruct (floorN_spec (exp a) ltac:(pose proof (exp_pos a); lra)) as [_ Hf2].
        assert (H : ln (exp a) <= ln (INR (S (floorN (exp a)))))
          by (left; apply ln_increasing; [ apply exp_pos | rewrite S_INR; lra ]).
        rewrite ln_exp in H. unfold c. exact H. }
      assert (Hcb : c <= b).
      { destruct (floorN_spec (exp b) ltac:(pose proof (exp_pos b); lra)) as [Hf1 _].
        assert (Hle2 : INR (S (floorN (exp a))) <= INR (floorN (exp b)))
          by (apply le_INR; lia).
        assert (H : ln (INR (S (floorN (exp a)))) <= ln (exp b)).
        { destruct (Rle_lt_or_eq_dec (INR (S (floorN (exp a)))) (exp b) ltac:(lra))
            as [Hlt | He];
            [ left; apply ln_increasing; [ lra | exact Hlt ]
            | rewrite He; apply Rle_refl ]. }
        rewrite ln_exp in H. unfold c. exact H. }
      apply RiemannInt_P24 with (b := c).
      * apply (nf_int_cell (floorN (exp a)) a c HN (cell_lo a Ha) Hac).
        unfold c; apply Rle_refl.
      * assert (Hc0 : 0 <= c).
        { unfold c. rewrite <- ln_1. left. apply ln_increasing; [ lra | ].
          replace 1 with (INR 1) by (simpl; ring). apply lt_INR. lia. }
        apply (IH c b Hc0 Hcb).
        rewrite Hexpc, floorN_INR. lia.
Qed.

Theorem nf_integrable : forall a b, 0 <= a -> a <= b ->
  Riemann_integrable nf a b.
Proof.
  intros a b Ha Hab. apply (nf_int_k (floorN (exp b)) a b Ha Hab). lia.
Qed.

(* ----------------------------------------------------------------- *)
(*  The change of variables, glued across cells.                       *)
(* ----------------------------------------------------------------- *)

Lemma split_point : forall a b, 0 <= a -> a <= b ->
  (floorN (exp a) < floorN (exp b))%nat ->
  0 <= ln (INR (S (floorN (exp a))))
  /\ a <= ln (INR (S (floorN (exp a))))
  /\ ln (INR (S (floorN (exp a)))) <= b
  /\ exp (ln (INR (S (floorN (exp a))))) = INR (S (floorN (exp a))).
Proof.
  intros a b Ha Hab Hlt.
  assert (HN : (1 <= floorN (exp a))%nat) by (apply floor_exp_ge1; exact Ha).
  assert (HSN0 : 0 < INR (S (floorN (exp a)))) by (apply lt_0_INR; lia).
  assert (Hexpc : exp (ln (INR (S (floorN (exp a))))) = INR (S (floorN (exp a))))
    by (apply exp_ln; exact HSN0).
  destruct (floorN_spec (exp a) ltac:(pose proof (exp_pos a); lra)) as [_ Hf2].
  destruct (floorN_spec (exp b) ltac:(pose proof (exp_pos b); lra)) as [Hg1 _].
  repeat split.
  - rewrite <- ln_1. apply ln_mono_le; [ lra | ].
    replace 1 with (INR 1) by (simpl; ring). apply le_INR. lia.
  - assert (H : ln (exp a) <= ln (INR (S (floorN (exp a))))).
    { apply ln_mono_le; [ apply exp_pos | rewrite S_INR; lra ]. }
    rewrite ln_exp in H. exact H.
  - assert (Hle2 : INR (S (floorN (exp a))) <= INR (floorN (exp b)))
      by (apply le_INR; lia).
    assert (H : ln (INR (S (floorN (exp a)))) <= ln (exp b))
      by (apply ln_mono_le; lra).
    rewrite ln_exp in H. exact H.
  - exact Hexpc.
Qed.

Theorem cov_glue : forall (k : nat) (a b : R), 0 <= a -> a <= b ->
  (floorN (exp b) <= floorN (exp a) + k)%nat ->
  forall (prL : Riemann_integrable nf a b)
         (prR : Riemann_integrable tint (exp a) (exp b)),
    RiemannInt prL = RiemannInt prR.
Proof.
  induction k as [| k IH]; intros a b Ha Hab Hk prL prR.
  - apply (cov_cell (floorN (exp a)) a b (floor_exp_ge1 a Ha) (cell_lo a Ha) Hab).
    apply cell_hi; [ exact Ha | exact Hab | lia ].
  - destruct (le_gt_dec (floorN (exp b)) (floorN (exp a) + k)) as [Hle | Hgt].
    + exact (IH a b Ha Hab Hle prL prR).
    + destruct (split_point a b Ha Hab ltac:(lia)) as [Hc0 [Hac [Hcb Hexpc]]].
      set (c := ln (INR (S (floorN (exp a))))) in *.
      assert (Hea : 0 < exp a) by apply exp_pos.
      assert (Heac : exp a <= exp c)
        by (destruct (Rle_lt_or_eq_dec a c Hac) as [H | H];
            [ left; apply exp_increasing; exact H | rewrite H; apply Rle_refl ]).
      assert (Hecb : exp c <= exp b)
        by (destruct (Rle_lt_or_eq_dec c b Hcb) as [H|H];
            [ left; apply exp_increasing; exact H | rewrite H; apply Rle_refl ]).
      pose proof (nf_int_cell (floorN (exp a)) a c (floor_exp_ge1 a Ha)
                    (cell_lo a Ha) Hac ltac:(unfold c; apply Rle_refl)) as pL1.
      pose proof (nf_integrable c b Hc0 Hcb) as pL2.
      pose proof (tint_integrable (exp a) (exp c) Hea Heac) as pR1.
      pose proof (tint_integrable (exp c) (exp b) ltac:(apply exp_pos) Hecb) as pR2.
      rewrite <- (RiemannInt_P26 pL1 pL2 prL), <- (RiemannInt_P26 pR1 pR2 prR).
      f_equal.
      * apply (cov_cell (floorN (exp a)) a c (floor_exp_ge1 a Ha)
                 (cell_lo a Ha) Hac ltac:(unfold c; apply Rle_refl)).
      * apply (IH c b Hc0 Hcb).
        rewrite Hexpc, floorN_INR. lia.
Qed.

Corollary cov_exp : forall a b, 0 <= a -> a <= b ->
  forall (prL : Riemann_integrable nf a b)
         (prR : Riemann_integrable tint (exp a) (exp b)),
    RiemannInt prL = RiemannInt prR.
Proof.
  intros a b Ha Hab prL prR.
  apply (cov_glue (floorN (exp b)) a b Ha Hab ltac:(lia)).
Qed.

(* ----------------------------------------------------------------- *)
(*  The bridge: Newman's Cauchy tail gives TintCauchy, hence PNT.      *)
(* ----------------------------------------------------------------- *)

Definition NfCauchy : Prop :=
  forall eps, 0 < eps -> exists T0, 0 <= T0 /\
    forall a b (Ha : T0 <= a) (Hab : a <= b)
           (pr : Riemann_integrable nf a b),
      Rabs (RiemannInt pr) < eps.

Theorem nf_cauchy_tint : NfCauchy -> TintCauchy.
Proof.
  intros HN eps Heps.
  destruct (HN eps Heps) as [T0 [HT0 HB]].
  assert (HX1 : 1 <= exp T0)
    by (rewrite <- exp_0; destruct (Rle_lt_or_eq_dec 0 T0 HT0) as [H | H];
        [ left; apply exp_increasing; exact H | rewrite <- H; apply Rle_refl ]).
  exists (exp T0). split; [ exact HX1 | ].
  intros x y HX Hxy.
  assert (Hx1 : 1 <= x) by lra.
  assert (Hx0 : 0 < x) by lra.
  assert (Hy0 : 0 < y) by lra.
  assert (Ha0 : 0 <= ln x)
    by (rewrite <- ln_1; apply ln_mono_le; lra).
  assert (HTa : T0 <= ln x)
    by (rewrite <- (ln_exp T0); apply ln_mono_le; [ apply exp_pos | exact HX ]).
  assert (Hab : ln x <= ln y) by (apply ln_mono_le; lra).
  rewrite <- (exp_ln x Hx0), <- (exp_ln y Hy0).
  intro pr.
  pose proof (nf_integrable (ln x) (ln y) Ha0 Hab) as prL.
  rewrite <- (cov_exp (ln x) (ln y) Ha0 Hab prL pr).
  exact (HB (ln x) (ln y) HTa Hab prL).
Qed.

(* ================================================================= *)
(*  CAPSTONE: PNT, conditional only on Newman's Cauchy tail in         *)
(*  t-coordinates -- i.e. on exactly the contour argument's output.    *)
(* ================================================================= *)

Theorem pnt_of_nf_cauchy : NfCauchy ->
  Un_cv (fun N => pi_count N / (INR N / ln (INR N))) 1.
Proof. intro H. apply pnt_of_tint_cauchy, nf_cauchy_tint, H. Qed.

Print Assumptions pnt_of_nf_cauchy.
Print Assumptions cov_exp.
Print Assumptions nf_cauchy_tint.
