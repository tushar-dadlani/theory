(* ================================================================= *)
(*  XiHgrow.v  —  discharging Hgrow: Bxi (2^{k+1}) = O((k+1) 2^k).     *)
(*                                                                    *)
(*  XiZeroDensity.xi_sum_inv_sq was a REDUCTION: it derived            *)
(*  sum 1/|rho|^2 for xi from the dyadic machinery but kept the growth *)
(*  of the counting majorant as a hypothesis.  This file proves it, so *)
(*  the genus-1 convergence input becomes unconditional.               *)
(*                                                                    *)
(*    xi_Hgrow : forall k, Bxi (2 ^ (S k)) <= agrow * INR (S k) * 2^k  *)
(*                                                                    *)
(*  THE ESTIMATE.  With p := 2^k and u := 16 p + 9 (so that            *)
(*  8 (2^{k+1} + 1) + 1 = u), one has 4 . XiM = 2 + 4 u^2 Tgb u, and    *)
(*                                                                    *)
(*    Tgb u = Kc . (u/PI)^{u/2} . e^{-u/2}  <=  Kc . (u/PI)^{u/2}      *)
(*                                                                    *)
(*  since e^{-u/2} <= 1.  As u^2 (u/PI)^{u/2} >= 1 (u >= 9 > PI), the   *)
(*  additive 2 is absorbed and                                        *)
(*                                                                    *)
(*    ln (4 XiM) <= ln M0 + 2 ln u + (u/2) ln (u/PI).                  *)
(*                                                                    *)
(*  Then u <= 25 p and u/PI <= u give ln u, ln(u/PI) <= ln 25 + k ln 2, *)
(*  and (k+1) p >= 1 absorbs every constant, leaving a bound of the     *)
(*  shape Agrow . (k+1) . p.  Dividing by ln 3 gives agrow.            *)
(*                                                                    *)
(*  NO NUMERIC BOUND ON PI IS NEEDED beyond the Stdlib 2 < PI <= 4      *)
(*  (PI2_1, PI_4): the constant agrow is allowed to be any fixed real,  *)
(*  so PI can stay symbolic inside it.  That is what keeps this file    *)
(*  short -- chasing a numerically explicit constant would need         *)
(*  interval arithmetic on exp, ln and Rpower.  Axiom-clean.           *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia List.
Require Import ComplexField Cmodulus RiemannXiEntire XiGrowthBound
        XiZeroCount XiZeroDensity CDyadicSum.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  A.  elementary monotonicity helpers                                *)
(* ----------------------------------------------------------------- *)
Lemma exp_le_mono : forall x y, x <= y -> exp x <= exp y.
Proof.
  intros x y H. destruct (Rle_lt_or_eq_dec x y H) as [Hlt | Heq];
    [ left; apply exp_increasing; exact Hlt | rewrite Heq; apply Rle_refl ].
Qed.

Lemma ln_le_mono : forall x y, 0 < x -> x <= y -> ln x <= ln y.
Proof.
  intros x y Hx H. destruct (Rle_lt_or_eq_dec x y H) as [Hlt | Heq];
    [ left; apply ln_increasing; assumption | rewrite Heq; apply Rle_refl ].
Qed.

Lemma ln_Rpower : forall x y, ln (Rpower x y) = y * ln x.
Proof. intros x y. unfold Rpower. apply ln_exp. Qed.

Lemma Rpower_ge1 : forall x y, 1 <= x -> 0 <= y -> 1 <= Rpower x y.
Proof.
  intros x y Hx Hy. unfold Rpower.
  rewrite <- exp_0. apply exp_le_mono.
  assert (Hlx : 0 <= ln x) by (rewrite <- ln_1; apply ln_le_mono; lra).
  nra.
Qed.

Lemma PI_lb2 : 2 < PI.
Proof. pose proof PI2_1. lra. Qed.

(* ----------------------------------------------------------------- *)
(*  B.  the Tgb majorant, with the exponential factor dropped          *)
(* ----------------------------------------------------------------- *)
Definition Kc : R := / (1 - exp (- PI)) * (exp (- (PI / 2)) / (PI / 2)).

Lemma Kc_pos : 0 < Kc.
Proof.
  unfold Kc. pose proof PI_RGT_0 as HPI.
  assert (He : exp (- PI) < 1) by (rewrite <- exp_0; apply exp_increasing; lra).
  apply Rmult_lt_0_compat.
  - apply Rinv_0_lt_compat; lra.
  - apply Rdiv_lt_0_compat; [ apply exp_pos | lra ].
Qed.

Lemma Tgb_le_Kc : forall u, 0 <= u -> Tgb u <= Kc * Rpower (u / PI) (u / 2).
Proof.
  intros u Hu.
  assert (HRp : 0 < Rpower (u / PI) (u / 2)) by (unfold Rpower; apply exp_pos).
  assert (HE : exp (- (u / 2)) <= 1)
    by (rewrite <- exp_0; apply exp_le_mono; lra).
  assert (HE0 : 0 < exp (- (u / 2))) by apply exp_pos.
  pose proof Kc_pos as HK.
  assert (Heq : Tgb u = Kc * Rpower (u / PI) (u / 2) * exp (- (u / 2)))
    by (unfold Tgb, Kc; ring).
  rewrite Heq.
  assert (HKR : 0 < Kc * Rpower (u / PI) (u / 2))
    by (apply Rmult_lt_0_compat; assumption).
  nra.
Qed.

Lemma Tgb_pos : forall u, 0 < Tgb u.
Proof.
  intro u. pose proof Kc_pos as HK.
  assert (Heq : Tgb u = Kc * Rpower (u / PI) (u / 2) * exp (- (u / 2)))
    by (unfold Tgb, Kc; ring).
  rewrite Heq. apply Rmult_lt_0_compat;
    [ apply Rmult_lt_0_compat; [ exact HK | unfold Rpower; apply exp_pos ]
    | apply exp_pos ].
Qed.

Definition M0 : R := 2 + 4 * Kc.

Lemma M0_pos : 0 < M0.
Proof. unfold M0. pose proof Kc_pos. lra. Qed.

(* ----------------------------------------------------------------- *)
(*  C.  the logarithmic bound                                          *)
(* ----------------------------------------------------------------- *)
Lemma ln4XiM_bound : forall u, 9 <= u ->
  ln (2 + 4 * u ^ 2 * Tgb u) <= ln M0 + 2 * ln u + u / 2 * ln (u / PI).
Proof.
  intros u Hu.
  pose proof PI_RGT_0 as HPI0. pose proof PI_4 as HPI4. pose proof PI_lb2 as HPI2.
  pose proof Kc_pos as HK. pose proof M0_pos as HM0.
  set (Rp := Rpower (u / PI) (u / 2)).
  assert (HuPI : 1 <= u / PI).
  { apply (Rmult_le_reg_r PI); [ lra | ]. field_simplify; lra. }
  assert (HRp1 : 1 <= Rp) by (unfold Rp; apply Rpower_ge1; lra).
  assert (Hu2 : 1 <= u ^ 2) by nra.
  assert (Hprod : 1 <= u ^ 2 * Rp) by nra.
  assert (Htgb := Tgb_le_Kc u ltac:(lra)).
  fold Rp in Htgb.
  assert (Hpos : 0 < 2 + 4 * u ^ 2 * Tgb u).
  { pose proof (Tgb_pos u). nra. }
  assert (Hle : 2 + 4 * u ^ 2 * Tgb u <= M0 * (u ^ 2 * Rp)).
  { unfold M0. nra. }
  eapply Rle_trans; [ apply ln_le_mono; [ exact Hpos | exact Hle ] | ].
  assert (Hu2p : 0 < u ^ 2) by nra.
  assert (HRpp : 0 < Rp) by lra.
  rewrite (ln_mult M0 (u ^ 2 * Rp) HM0 ltac:(nra)).
  rewrite (ln_mult (u ^ 2) Rp Hu2p HRpp).
  rewrite (ln_pow u ltac:(lra) 2).
  unfold Rp. rewrite ln_Rpower.
  assert (HI2 : INR 2 = 2) by (simpl; lra). rewrite HI2. lra.
Qed.

Print Assumptions ln4XiM_bound.

(* ----------------------------------------------------------------- *)
(*  D.  plugging in u = 16 . 2^k + 9                                   *)
(* ----------------------------------------------------------------- *)
Definition Lc : R := ln 25 + ln 2.
Definition Agrow : R := Rabs (ln M0) + 2 * Lc + 25 / 2 * Lc.
Definition agrow : R := Agrow / ln 3.

Lemma ln2_pos : 0 < ln 2. Proof. pose proof ln_lt_2. lra. Qed.
Lemma ln3_pos : 0 < ln 3.
Proof. rewrite <- ln_1. apply ln_increasing; lra. Qed.
Lemma ln25_pos : 0 < ln 25.
Proof. rewrite <- ln_1. apply ln_increasing; lra. Qed.
Lemma Lc_pos : 0 < Lc.
Proof. unfold Lc. pose proof ln25_pos. pose proof ln2_pos. lra. Qed.

Lemma agrow_nonneg : 0 <= agrow.
Proof.
  unfold agrow, Agrow. pose proof Lc_pos. pose proof ln3_pos.
  pose proof (Rabs_pos (ln M0)).
  apply Rle_mult_inv_pos; lra.
Qed.

Theorem xi_Hgrow : forall k : nat, Bxi (2 ^ (S k)) <= agrow * INR (S k) * 2 ^ k.
Proof.
  intro k.
  pose proof PI_RGT_0 as HPI0. pose proof PI_4 as HPI4. pose proof PI_lb2 as HPI2.
  pose proof ln2_pos. pose proof ln3_pos. pose proof ln25_pos. pose proof Lc_pos.
  set (p := 2 ^ k).
  assert (Hp1 : 1 <= p) by (unfold p; apply pow_R1_Rle; lra).
  set (u := 16 * p + 9).
  assert (Hu9 : 9 <= u) by (unfold u; lra).
  assert (Hu25 : u <= 25 * p) by (unfold u; lra).
  (* Bxi's argument really is u - 1 *)
  assert (Harg : 8 * (2 ^ S k + 1) + 1 = u)
    by (unfold u, p; simpl (2 ^ S k); ring).
  assert (HX : 4 * XiM (8 * (2 ^ S k + 1)) = 2 + 4 * u ^ 2 * Tgb u).
  { unfold XiM. rewrite Harg. field. }
  pose proof (ln4XiM_bound u Hu9) as Hlnb.
  (* logarithms of u and u/PI, in terms of k *)
  assert (Hlnp : ln p = INR k * ln 2)
    by (unfold p; rewrite (ln_pow 2 ltac:(lra) k); reflexivity).
  assert (Hlnu : ln u <= ln 25 + INR k * ln 2).
  { rewrite <- Hlnp.
    replace (ln 25 + ln p) with (ln (25 * p))
      by (rewrite ln_mult; [ reflexivity | lra | lra ]).
    apply ln_le_mono; lra. }
  assert (HuPI1 : 1 <= u / PI).
  { apply (Rmult_le_reg_r PI); [ lra | ].
    replace (u / PI * PI) with u by (field; lra). lra. }
  assert (HlnuPI0 : 0 <= ln (u / PI))
    by (rewrite <- ln_1; apply ln_le_mono; lra).
  assert (HlnuPI : ln (u / PI) <= ln 25 + INR k * ln 2).
  { apply Rle_trans with (ln u); [ | exact Hlnu ].
    apply ln_le_mono; [ lra | ].
    assert (Hinv : / PI <= 1) by (rewrite <- Rinv_1; apply Rinv_le_contravar; lra).
    unfold Rdiv. nra. }
  (* assemble *)
  set (Sk := INR (S k)).
  assert (HSk : Sk = INR k + 1) by (unfold Sk; apply S_INR).
  assert (Hk0 : 0 <= INR k) by apply pos_INR.
  assert (HSk1 : 1 <= Sk) by lra.
  assert (HSkp : 1 <= Sk * p) by nra.
  assert (HLcSk : 0 <= Lc * Sk) by nra.
  assert (Hb : ln 25 + INR k * ln 2 <= Lc * Sk) by (unfold Lc; rewrite HSk; nra).
  assert (Hgrow : Lc * Sk <= Lc * Sk * p) by nra.
  assert (HA1 : ln M0 <= Rabs (ln M0) * (Sk * p)).
  { apply Rle_trans with (Rabs (ln M0)); [ apply Rle_abs | ].
    pose proof (Rabs_pos (ln M0)). nra. }
  assert (HA2 : 2 * ln u <= 2 * Lc * (Sk * p)) by nra.
  assert (HA3 : u / 2 * ln (u / PI) <= 25 / 2 * Lc * (Sk * p)).
  { apply Rle_trans with (25 * p / 2 * (Lc * Sk)).
    - apply Rmult_le_compat; [ lra | exact HlnuPI0 | lra | lra ].
    - apply Req_le. field. }
  (* divide by ln 3 *)
  unfold Bxi. rewrite HX. unfold agrow. fold Sk.
  apply (Rmult_le_reg_r (ln 3)); [ lra | ].
  replace (ln (2 + 4 * u ^ 2 * Tgb u) / ln 3 * ln 3)
    with (ln (2 + 4 * u ^ 2 * Tgb u)) by (field; lra).
  replace (Agrow / ln 3 * Sk * p * ln 3) with (Agrow * (Sk * p)) by (field; lra).
  unfold Agrow. lra.
Qed.

Print Assumptions xi_Hgrow.

(* ================================================================= *)
(*  THE GENUS-1 CONVERGENCE INPUT, now UNCONDITIONAL.                  *)
(* ================================================================= *)
Theorem xi_sum_inv_sq_uncond : forall s : list C,
  NoDup s ->
  (forall x, In x s -> XiC x = C0) ->
  (forall x, In x s -> 1 <= Cmod x) ->
  sumlist invsq s <= 4 * agrow.
Proof.
  intros s Hnd HP Hlow.
  exact (xi_sum_inv_sq agrow agrow_nonneg xi_Hgrow s Hnd HP Hlow).
Qed.

Print Assumptions xi_sum_inv_sq_uncond.

(* the same, counting each zero with its MULTIPLICITY -- which is what the
   Hadamard product actually needs.  Same majorant Bxi, so the same
   xi_Hgrow discharges it. *)
Theorem xi_sum_inv_sq_mult_uncond : forall s : list C,
  XiPeel s ->
  (forall x, In x s -> XiC x = C0) ->
  (forall x, In x s -> 1 <= Cmod x) ->
  sumlist invsq s <= 4 * agrow.
Proof.
  intros s Hpeel HP Hlow.
  exact (xi_sum_inv_sq_mult agrow agrow_nonneg xi_Hgrow s Hpeel HP Hlow).
Qed.

Print Assumptions xi_sum_inv_sq_mult_uncond.
