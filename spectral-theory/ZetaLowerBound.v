(* ================================================================= *)
(*  ZetaLowerBound.v  --  a QUANTITATIVE lower bound for zeta on Re>1. *)
(*                                                                    *)
(*    zeta_lower : 1 < a <= 2,  1 <= |b|  ==>                          *)
(*        (a - 1)^3  <=  5831 * |b| * |zeta(a + ib)|^4                 *)
(*                                                                    *)
(*  This is the first half of every proof of a zero-free region, and   *)
(*  it is exactly what the Mertens 3-4-1 inequality is FOR.  The repo  *)
(*  had 3-4-1 (ThreeFourOne.tfo_zeta) and used it only qualitatively,  *)
(*  to get zeta <> 0 on the line Re = 1.  With an upper bound on zeta  *)
(*  now available (ZetaStripBound.zetaC_bound) the same inequality     *)
(*  becomes quantitative: 3-4-1 reads                                  *)
(*                                                                    *)
(*      1 <= |zeta(a)|^3 |zeta(a+ib)|^4 |zeta(a+2ib)|,                 *)
(*                                                                    *)
(*  so an UPPER bound on the first and third factors is a LOWER bound  *)
(*  on the middle one.  |zeta(a)| <= 7/(a-1) captures the pole, and    *)
(*  |zeta(a+2ib)| <= 17|b| is the linear strip bound.                  *)
(*                                                                    *)
(*  Everything is stated multiplicatively -- (a-1)^3 <= C |b| X^4      *)
(*  rather than X >= ((a-1)^3/(C|b|))^{1/4} -- so no fourth roots ever *)
(*  appear.  Constants are not optimised; they are chosen to make the  *)
(*  arithmetic close by lra/nra.                                      *)
(*                                                                    *)
(*  WHAT THIS IS NOT.  It is a bound for a > 1 only, where zeta was    *)
(*  already known nonzero.  Turning it into a zero-free region DIPPING *)
(*  BELOW 1 needs a second ingredient -- a bound on zeta' and a mean   *)
(*  value estimate along the segment from a zero out to Re > 1.  That  *)
(*  is not in this file.  Axiom-clean.                                *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra.
Require Import ComplexField Cmodulus CSeries CZeta ZetaFn ThreeFourOne
        ZetaStripBound ZetaLogBound.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  A.  modulus of an explicit complex number                          *)
(* ----------------------------------------------------------------- *)
Lemma Cmod_mk : forall x y, Cmod (mkC x y) = sqrt (x * x + y * y).
Proof. intros x y; unfold Cmod, Cnorm2; cbn [Re Im]; reflexivity. Qed.

Lemma Cmod_mk_real : forall x, Cmod (mkC x 0) = Rabs x.
Proof.
  intro x. rewrite Cmod_mk.
  replace (x * x + 0 * 0) with (Rsqr x) by (unfold Rsqr; ring).
  apply sqrt_Rsqr_abs.
Qed.

Lemma Cmod_mk_im_le : forall x y, Rabs y <= Cmod (mkC x y).
Proof.
  intros x y. rewrite Cmod_mk, <- (sqrt_Rsqr_abs y).
  apply sqrt_le_1_alt. unfold Rsqr. nra.
Qed.

Lemma Cmod_mk_le : forall x y, Cmod (mkC x y) <= Rabs x + Rabs y.
Proof.
  intros x y. pose proof (Cmod_le_sum (mkC x y)) as H. cbn [Re Im] in H. exact H.
Qed.

Lemma ne1_gen : forall a b, 1 < a -> Cminus C1 (mkC a b) <> C0.
Proof.
  intros a b Ha Hc. apply (f_equal Re) in Hc.
  unfold Cminus, Cadd, Copp, C1, C0 in Hc; cbn [Re] in Hc; lra.
Qed.

Lemma sub_C1_mk : forall a b, Cminus (mkC a b) C1 = mkC (a - 1) b.
Proof.
  intros a b. apply Ceq; unfold Cminus, Cadd, Copp, C1; cbn [Re Im]; ring.
Qed.

(* the strip bound, on the proof-free wrapper *)
Lemma zF_bound : forall s (H0 : 0 < Re s) (H1 : Cminus C1 s <> C0),
  Cmod (zF s) <= / Cmod (Cminus s C1) + 2 * Cmod s * (1 + / Re s).
Proof. intros s H0 H1. rewrite (zF_eq s H0 H1). apply zetaC_bound. Qed.

(* ----------------------------------------------------------------- *)
(*  B.  the two upper bounds                                           *)
(* ----------------------------------------------------------------- *)
(* the pole at 1 *)
Theorem zF_upper_real : forall a, 1 < a -> a <= 2 ->
  Cmod (zF (mkC a 0)) <= 7 / (a - 1).
Proof.
  intros a Ha Ha2.
  assert (H0 : 0 < Re (mkC a 0)) by (cbn [Re]; lra).
  pose proof (zF_bound (mkC a 0) H0 (ne1_gen a 0 Ha)) as HB.
  rewrite sub_C1_mk, Cmod_mk_real, Cmod_mk_real in HB.
  cbn [Re] in HB.
  rewrite (Rabs_right (a - 1) ltac:(lra)), (Rabs_right a ltac:(lra)) in HB.
  replace (2 * a * (1 + / a)) with (2 * a + 2) in HB by (field; lra).
  assert (Hi1 : 1 <= / (a - 1))
    by (rewrite <- Rinv_1; apply Rinv_le_contravar; lra).
  unfold Rdiv. nra.
Qed.

(* the linear bound at height 2b *)
Theorem zF_upper_double : forall a b, 1 < a -> a <= 2 -> 1 <= Rabs b ->
  Cmod (zF (mkC a (2 * b))) <= 17 * Rabs b.
Proof.
  intros a b Ha Ha2 Hb.
  assert (H0 : 0 < Re (mkC a (2 * b))) by (cbn [Re]; lra).
  pose proof (zF_bound (mkC a (2 * b)) H0 (ne1_gen a (2 * b) Ha)) as HB.
  rewrite sub_C1_mk in HB. cbn [Re] in HB.
  (* |s - 1| >= 2|b| >= 2, so its inverse is at most 1/2 *)
  assert (Hlow : 2 * Rabs b <= Cmod (mkC (a - 1) (2 * b))).
  { pose proof (Cmod_mk_im_le (a - 1) (2 * b)) as H.
    rewrite (Rabs_mult 2 b), (Rabs_right 2 ltac:(lra)) in H. exact H. }
  assert (Hinv : / Cmod (mkC (a - 1) (2 * b)) <= / 2).
  { apply Rinv_le_contravar; [ lra | lra ]. }
  (* |s| <= a + 2|b| <= 4|b| *)
  assert (Hup : Cmod (mkC a (2 * b)) <= 4 * Rabs b).
  { pose proof (Cmod_mk_le a (2 * b)) as H.
    rewrite (Rabs_mult 2 b), (Rabs_right 2 ltac:(lra)), (Rabs_right a ltac:(lra)) in H.
    lra. }
  assert (Hia : / a <= 1) by (rewrite <- Rinv_1; apply Rinv_le_contravar; lra).
  assert (Hia0 : 0 < / a) by (apply Rinv_0_lt_compat; lra).
  nra.
Qed.

(* ----------------------------------------------------------------- *)
(*  C.  THE LOWER BOUND                                                *)
(* ----------------------------------------------------------------- *)
Theorem zeta_lower : forall a b, 1 < a -> a <= 2 -> 1 <= Rabs b ->
  (a - 1) ^ 3 <= 5831 * Rabs b * (Cmod (zF (mkC a b))) ^ 4.
Proof.
  intros a b Ha Ha2 Hb.
  assert (H00 : 0 < Re (mkC a 0)) by (cbn [Re]; lra).
  assert (H10 : 0 < Re (mkC a b)) by (cbn [Re]; lra).
  assert (H20 : 0 < Re (mkC a (2 * b))) by (cbn [Re]; lra).
  pose proof (tfo_zeta a b Ha H00 (ne1_gen a 0 Ha) H10 (ne1_gen a b Ha)
                H20 (ne1_gen a (2 * b) Ha)) as Htfo.
  rewrite <- (zF_eq (mkC a 0) H00 (ne1_gen a 0 Ha)) in Htfo.
  rewrite <- (zF_eq (mkC a b) H10 (ne1_gen a b Ha)) in Htfo.
  rewrite <- (zF_eq (mkC a (2 * b)) H20 (ne1_gen a (2 * b) Ha)) in Htfo.
  set (u := Cmod (zF (mkC a 0))) in *.
  set (v := Cmod (zF (mkC a b))) in *.
  set (w := Cmod (zF (mkC a (2 * b)))) in *.
  assert (Hu0 : 0 <= u) by apply Cmod_nonneg.
  assert (Hv0 : 0 <= v) by apply Cmod_nonneg.
  assert (Hw0 : 0 <= w) by apply Cmod_nonneg.
  pose proof (zF_upper_real a Ha Ha2) as Hu.
  pose proof (zF_upper_double a b Ha Ha2 Hb) as Hw.
  fold u in Hu. fold w in Hw.
  assert (HA : 0 < a - 1) by lra.
  assert (HA3 : 0 < (a - 1) ^ 3) by (apply pow_lt; lra).
  assert (Hv4 : 0 <= v ^ 4) by (apply pow_le; exact Hv0).
  (* cube the first bound *)
  assert (Hu3 : u ^ 3 <= (7 / (a - 1)) ^ 3)
    by (apply pow_incr; split; assumption).
  assert (Hu30 : 0 <= u ^ 3) by (apply pow_le; exact Hu0).
  assert (Hc3 : (7 / (a - 1)) ^ 3 = 343 / (a - 1) ^ 3) by (field; lra).
  rewrite Hc3 in Hu3.
  (* chain the two replacements through the product *)
  assert (Hstep1 : u ^ 3 * v ^ 4 * w <= 343 / (a - 1) ^ 3 * v ^ 4 * w).
  { apply Rmult_le_compat_r; [ exact Hw0 | ].
    apply Rmult_le_compat_r; [ exact Hv4 | exact Hu3 ]. }
  assert (Hpos : 0 <= 343 / (a - 1) ^ 3 * v ^ 4)
    by (apply Rmult_le_pos; [ apply Rle_mult_inv_pos; lra | exact Hv4 ]).
  assert (Hstep2 : 343 / (a - 1) ^ 3 * v ^ 4 * w
                <= 343 / (a - 1) ^ 3 * v ^ 4 * (17 * Rabs b))
    by (apply Rmult_le_compat_l; [ exact Hpos | exact Hw ]).
  assert (Hchain : 1 <= 343 / (a - 1) ^ 3 * v ^ 4 * (17 * Rabs b)) by lra.
  assert (Hfinal : (a - 1) ^ 3 * 1
                <= (a - 1) ^ 3 * (343 / (a - 1) ^ 3 * v ^ 4 * (17 * Rabs b)))
    by (apply Rmult_le_compat_l; [ lra | exact Hchain ]).
  rewrite Rmult_1_r in Hfinal.
  replace ((a - 1) ^ 3 * (343 / (a - 1) ^ 3 * v ^ 4 * (17 * Rabs b)))
    with (5831 * Rabs b * v ^ 4) in Hfinal by (field; lra).
  exact Hfinal.
Qed.

Print Assumptions zF_upper_real.
Print Assumptions zF_upper_double.
Print Assumptions zeta_lower.

(* ================================================================= *)
(*  D.  THE SAME BOUND, WITH THE CONSTANTS AS PARAMETERS               *)
(* ================================================================= *)
(*  The 7 and the 17 above are not structure, they are roundings of my *)
(*  own slack: the 7 is 1 + (2a+2) at the cap a <= 2, absorbed via     *)
(*  1/(a-1) >= 1, and the 17 is ceil(1/2 + 16|b|)/|b|.  Cap at a <= 3/2 *)
(*  instead and the first is 6.  Only the CUBE on the first is real -- *)
(*  it is the exponent 3 of Mertens 3-4-1.                             *)
(*                                                                    *)
(*  Parametrising them costs nothing and buys the splice below: the    *)
(*  second factor can then be supplied by ZetaLogBound.zeta_log_bound  *)
(*  instead of the O(|s|) bound, which is what keeps the zero-free     *)
(*  region logarithmic rather than polynomial.                         *)
(* ================================================================= *)
Theorem zeta_lower_gen : forall a b C1 C2, 1 < a -> a <= 2 -> 1 <= Rabs b ->
  0 <= C2 ->
  Cmod (zF (mkC a 0)) <= C1 / (a - 1) ->
  Cmod (zF (mkC a (2 * b))) <= C2 ->
  (a - 1) ^ 3 <= C1 ^ 3 * C2 * (Cmod (zF (mkC a b))) ^ 4.
Proof.
  intros a b C1 C2 Ha Ha2 Hb HC2 Hu Hw.
  assert (H00 : 0 < Re (mkC a 0)) by (cbn [Re]; lra).
  assert (H10 : 0 < Re (mkC a b)) by (cbn [Re]; lra).
  assert (H20 : 0 < Re (mkC a (2 * b))) by (cbn [Re]; lra).
  pose proof (tfo_zeta a b Ha H00 (ne1_gen a 0 Ha) H10 (ne1_gen a b Ha)
                H20 (ne1_gen a (2 * b) Ha)) as Htfo.
  rewrite <- (zF_eq (mkC a 0) H00 (ne1_gen a 0 Ha)) in Htfo.
  rewrite <- (zF_eq (mkC a b) H10 (ne1_gen a b Ha)) in Htfo.
  rewrite <- (zF_eq (mkC a (2 * b)) H20 (ne1_gen a (2 * b) Ha)) in Htfo.
  set (u := Cmod (zF (mkC a 0))) in *.
  set (v := Cmod (zF (mkC a b))) in *.
  set (w := Cmod (zF (mkC a (2 * b)))) in *.
  assert (Hu0 : 0 <= u) by apply Cmod_nonneg.
  assert (Hv0 : 0 <= v) by apply Cmod_nonneg.
  assert (Hw0 : 0 <= w) by apply Cmod_nonneg.
  assert (HA : 0 < a - 1) by lra.
  assert (HC1 : 0 <= C1)
    by (replace C1 with (C1 / (a - 1) * (a - 1)) by (field; lra); nra).
  assert (HA3 : 0 < (a - 1) ^ 3) by (apply pow_lt; lra).
  assert (Hv4 : 0 <= v ^ 4) by (apply pow_le; exact Hv0).
  assert (Hu3 : u ^ 3 <= (C1 / (a - 1)) ^ 3)
    by (apply pow_incr; split; assumption).
  assert (Hc3 : (C1 / (a - 1)) ^ 3 = C1 ^ 3 / (a - 1) ^ 3) by (field; lra).
  rewrite Hc3 in Hu3.
  assert (Hstep1 : u ^ 3 * v ^ 4 * w <= C1 ^ 3 / (a - 1) ^ 3 * v ^ 4 * w).
  { apply Rmult_le_compat_r; [ exact Hw0 | ].
    apply Rmult_le_compat_r; [ exact Hv4 | exact Hu3 ]. }
  assert (HC13 : 0 <= C1 ^ 3) by (apply pow_le; exact HC1).
  assert (Hpos : 0 <= C1 ^ 3 / (a - 1) ^ 3 * v ^ 4)
    by (apply Rmult_le_pos; [ apply Rle_mult_inv_pos; lra | exact Hv4 ]).
  assert (Hstep2 : C1 ^ 3 / (a - 1) ^ 3 * v ^ 4 * w
                <= C1 ^ 3 / (a - 1) ^ 3 * v ^ 4 * C2)
    by (apply Rmult_le_compat_l; [ exact Hpos | exact Hw ]).
  assert (Hchain : 1 <= C1 ^ 3 / (a - 1) ^ 3 * v ^ 4 * C2) by lra.
  assert (Hfinal : (a - 1) ^ 3 * 1
                <= (a - 1) ^ 3 * (C1 ^ 3 / (a - 1) ^ 3 * v ^ 4 * C2))
    by (apply Rmult_le_compat_l; [ lra | exact Hchain ]).
  rewrite Rmult_1_r in Hfinal.
  replace ((a - 1) ^ 3 * (C1 ^ 3 / (a - 1) ^ 3 * v ^ 4 * C2))
    with (C1 ^ 3 * C2 * v ^ 4) in Hfinal by (field; lra).
  exact Hfinal.
Qed.

(* ================================================================= *)
(*  E.  THE SPLICE: the same bound with a LOGARITHMIC second factor    *)
(* ================================================================= *)
(*  The point a + 2ib sits at Re = a > 1, so the PLAIN zeta_log_bound  *)
(*  applies -- no below-the-line extension is needed here.  Only the   *)
(*  mean value segment dips below 1.                                   *)
(*                                                                    *)
(*  This is the step that fixes the exponent of the zero-free region.  *)
(*  The constant here enters K = 16 A M^4 linearly and K enters the    *)
(*  region as 1/K, so the |b| carried by zeta_lower is a factor |t| in *)
(*  the region: it would turn c/ln^9 t into c/(t ln^8 t), polynomial   *)
(*  and vacuous.  With ln(2|b|) in its place the region stays          *)
(*  logarithmic.                                                      *)
(* ================================================================= *)
Theorem zeta_lower_log : forall a b, 1 < a -> a <= 2 -> 1 <= Rabs b ->
  (a - 1) ^ 3 <= 343 * (ln (2 * Rabs b) + 10) * (Cmod (zF (mkC a b))) ^ 4.
Proof.
  intros a b Ha Ha2 Hb.
  assert (Habs : Rabs (2 * b) = 2 * Rabs b)
    by (rewrite Rabs_mult, (Rabs_right 2 ltac:(lra)); reflexivity).
  assert (Hln : 0 <= ln (2 * Rabs b))
    by (apply ln_nonneg; lra).
  assert (Hlog : Cmod (zF (mkC a (2 * b))) <= ln (2 * Rabs b) + 10).
  { assert (Hre : Re (mkC a (2 * b)) = a) by reflexivity.
    assert (Him : Im (mkC a (2 * b)) = 2 * b) by reflexivity.
    pose proof (zeta_log_bound (mkC a (2 * b))
                  ltac:(rewrite Hre; lra) ltac:(rewrite Hre; lra)
                  ltac:(rewrite Him, Habs; lra)) as H.
    rewrite Him, Habs in H. exact H. }
  pose proof (zeta_lower_gen a b 7 (ln (2 * Rabs b) + 10) Ha Ha2 Hb
                ltac:(lra) (zF_upper_real a Ha Ha2) Hlog) as H.
  replace (7 ^ 3) with 343 in H by ring.
  exact H.
Qed.

Print Assumptions zeta_lower_gen.
Print Assumptions zeta_lower_log.
