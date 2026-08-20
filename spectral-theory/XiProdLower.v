(* ================================================================= *)
(*  XiProdLower.v  —  THE MINIMUM MODULUS of the Hadamard product.     *)
(*                                                                    *)
(*    xi_prod_lower : on a circle chosen to miss the zeros,            *)
(*                                                                    *)
(*        exp (LBexp rr del K)  <=  |P(w)|,                            *)
(*                                                                    *)
(*      P the Hadamard product over the enumerated zeros.              *)
(*                                                                    *)
(*  This is the estimate the whole SubQuadLog programme was built for. *)
(*  |H| = |xi|/|P| is useless pointwise because P vanishes at every    *)
(*  zero; on the good circle it is not, and this supplies the missing  *)
(*  denominator bound.                                                *)
(*                                                                    *)
(*  THE SPLIT IS DYADIC, at 2^K with 10 rr <= 2^K < 20 rr.  Both       *)
(*  thresholds matter and they pull in opposite directions:            *)
(*   * 2^K >= 10 rr is exactly Efac_lower_far's hypothesis, so every   *)
(*     far factor deviates from 1 only QUADRATICALLY;                  *)
(*   * 2^K < 20 rr keeps the near factors' denominators comparable to  *)
(*     the radius, so dividing by them costs only a constant.          *)
(*  Being a POWER OF TWO is the third constraint: xi_sum_inv1 and      *)
(*  xi_sum_tail are both stated at powers of two.  CDyadicBracket      *)
(*  supplies the K meeting all three.                                  *)
(*                                                                    *)
(*  THE NEAR BLOCK SPLITS AGAIN, into a constant and an exponential    *)
(*  (prodR_mult), because the two facts available about the zeros      *)
(*  answer different queries: how MANY there are (xi_count_peel) and   *)
(*  how big SUM 1/|rho| is (xi_sum_inv1).  The distance factor meets   *)
(*  the count, the exponential factor meets the sum.                   *)
(*                                                                    *)
(*  Everything is UNIFORM IN THE TRUNCATION -- the count and both sums *)
(*  are bounded over all prefixes at once -- which is what lets        *)
(*  CUn_cv_mod_ge carry the bound to the limit.  Same shape as         *)
(*  XiProdLimit.hadamard_prod_ne0.  Axiom-clean.                       *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia List Bool.
Require Import ComplexField Cmodulus Holomorphic CDeriv CSeries CInfProd
        JensenMultiZero CZeroListFactor CDyadicSum CDyadicSum2 CDyadicBracket
        CListProdBound CEfacLower
        RiemannXiEntire XiZeroCount XiZeroDensity XiHgrow XiZeroEnum
        XiHadamardProd XiProdFactor XiProdLimit XiGoodRadius XiSumBounds.
Open Scope R_scope.

(* the near/far predicate *)
Definition nearp (K : nat) : C -> bool :=
  fun x => if Rlt_dec (Cmod x) (2 ^ K) then true else false.

Lemma nearp_true : forall K x, nearp K x = true -> Cmod x < 2 ^ K.
Proof.
  intros K x H. unfold nearp in H.
  destruct (Rlt_dec (Cmod x) (2 ^ K)); [ assumption | discriminate ].
Qed.

Lemma nearp_false : forall K x, nearp K x = false -> 2 ^ K <= Cmod x.
Proof.
  intros K x H. unfold nearp in H.
  destruct (Rlt_dec (Cmod x) (2 ^ K)); [ discriminate | lra ].
Qed.

(* the exponent of the lower bound *)
Definition LBexp (rr del : R) (K : nat) : R :=
  Bxi (2 ^ K) * ln (del / 2 ^ K)
  - rr * (agrow * Aser K)
  - 2 * rr ^ 2 * (agrow * (2 * (INR K + 2) / 2 ^ K)).

Section ProdLower.

Variable rho : nat -> C.
Hypothesis Henum : ZeroEnum rho.
Hypothesis Hlow : forall n, 1 <= Cmod (rho n).

(* ----------------------------------------------------------------- *)
(*  A.  what every prefix list satisfies                               *)
(* ----------------------------------------------------------------- *)
Lemma take_peel : forall N, XiPeel (takeN rho N).
Proof. intro N. destruct Henum as [_ [_ [Hpre _]]]. apply Hpre. Qed.

Lemma take_zero : forall N x, In x (takeN rho N) -> XiC x = C0.
Proof. intros N x Hx. exact (enum_is_zero rho Henum x N Hx). Qed.

Lemma take_low : forall N x, In x (takeN rho N) -> 1 <= Cmod x.
Proof.
  intros N x Hx. unfold takeN in Hx. apply in_map_iff in Hx.
  destruct Hx as [n [Hn _]]. rewrite <- Hn. apply Hlow.
Qed.

Lemma take_ne0 : forall N x, In x (takeN rho N) -> x <> C0.
Proof.
  intros N x Hx Hc. pose proof (take_low N x Hx) as H.
  rewrite Hc, (proj2 (Cmod0 C0) eq_refl) in H. lra.
Qed.

(* the same, after a filter *)
Lemma filt_peel : forall (p : C -> bool) N, XiPeel (filter p (takeN rho N)).
Proof. intros p N. apply XiPeel_filter, take_peel. Qed.

Lemma filt_in : forall (p : C -> bool) N x,
  In x (filter p (takeN rho N)) -> In x (takeN rho N) /\ p x = true.
Proof. intros p N x Hx. exact (proj1 (filter_In p x (takeN rho N)) Hx). Qed.

(* ----------------------------------------------------------------- *)
(*  B.  the near block                                                 *)
(* ----------------------------------------------------------------- *)
Section Circle.

Variables r rr del : R.
Variable K : nat.
Variable w : C.
Hypothesis Hr : 1 <= r.
Hypothesis Hrr1 : 2 * r <= rr.
Hypothesis Hrr2 : rr <= 4 * r.
Hypothesis Hdel0 : 0 < del.
Hypothesis Hdelr : del <= r.
Hypothesis HK1 : 10 * rr <= 2 ^ K.
Hypothesis HK2 : 2 ^ K < 20 * rr.
Hypothesis Hw : Cmod w = rr.
Hypothesis Hgap : forall x, XiC x = C0 -> Cmod x < 80 * r ->
  del <= Cmod (Cminus w x).

Lemma Hrrpos : 0 < rr. Proof. lra. Qed.
Lemma H2K : 0 < 2 ^ K. Proof. apply pow2_pos. Qed.

Lemma Hq0 : 0 < del / 2 ^ K.
Proof. pose proof H2K. apply Rdiv_lt_0_compat; lra. Qed.

Lemma Hq1 : del / 2 ^ K <= 1.
Proof.
  pose proof H2K as H2. pose proof Hrrpos.
  apply (Rmult_le_reg_r (2 ^ K)); [ lra | ].
  unfold Rdiv. rewrite Rmult_assoc, Rinv_l by lra. lra.
Qed.

Lemma Hlnq : ln (del / 2 ^ K) <= 0.
Proof.
  rewrite <- ln_1. destruct (Rle_lt_or_eq_dec _ 1 Hq1) as [Hlt | Heq].
  - left. apply ln_increasing; [ apply Hq0 | exact Hlt ].
  - rewrite Heq. lra.
Qed.

(* every near zero contributes at least  q . e^{-rr/|x|}  *)
Lemma near_factor : forall N x, In x (filter (nearp K) (takeN rho N)) ->
  0 <= del / 2 ^ K * exp (- rr * invmod x)
  /\ del / 2 ^ K * exp (- rr * invmod x) <= Cmod (Efac w x).
Proof.
  intros N x Hx.
  destruct (filt_in (nearp K) N x Hx) as [Hin Hp].
  pose proof (nearp_true K x Hp) as Hsmall.
  pose proof (take_low N x Hin) as Hlow1.
  pose proof (take_ne0 N x Hin) as Hne.
  pose proof Hq0 as Hq0'. pose proof (exp_pos (- rr * invmod x)) as He.
  split; [ nra | ].
  pose proof (Efac_lower_near w x Hne) as Hlb.
  apply Rle_trans with (Cmod (Cminus x w) / Cmod x * exp (- (Cmod w / Cmod x)));
    [ | exact Hlb ].
  (* the distance factor *)
  assert (Hd : del <= Cmod (Cminus x w)).
  { rewrite <- (Cmod_opp (Cminus x w)).
    replace (Copp (Cminus x w)) with (Cminus w x) by ring.
    apply Hgap; [ exact (take_zero N x Hin) | lra ]. }
  assert (Hq2 : del / 2 ^ K <= Cmod (Cminus x w) / Cmod x).
  { unfold Rdiv. apply Rmult_le_compat; [ lra | | lra | ].
    - left. apply Rinv_0_lt_compat, H2K.
    - apply Rinv_le_contravar; lra. }
  (* the exponential factor is the same thing *)
  assert (Hex : exp (- rr * invmod x) = exp (- (Cmod w / Cmod x)))
    by (f_equal; unfold invmod; rewrite Hw; field; lra).
  rewrite Hex.
  apply Rmult_le_compat_r; [ left; apply exp_pos | exact Hq2 ].
Qed.

Lemma near_bound : forall N,
  exp (Bxi (2 ^ K) * ln (del / 2 ^ K) - rr * (agrow * Aser K))
  <= Cmod (Wlist (filter (nearp K) (takeN rho N)) w).
Proof.
  intro N. set (l := filter (nearp K) (takeN rho N)).
  pose proof Hq0 as Hq0'. pose proof Hlnq as Hlnq'. pose proof H2K as H2.
  (* the factorwise bound, transported *)
  assert (Hprod : prodR (fun x => del / 2 ^ K * exp (- rr * invmod x)) l
                  <= Cmod (Wlist l w))
    by (apply prodR_le_Wlist; intros x Hx; apply (near_factor N x Hx)).
  (* split constant from exponential *)
  rewrite (prodR_mult (fun _ => del / 2 ^ K)
             (fun x => exp (- rr * invmod x)) l) in Hprod.
  rewrite (prodR_exp (fun x => - rr * invmod x) l) in Hprod.
  rewrite (sumlist_scal (- rr) invmod l) in Hprod.
  (* the constant part meets the COUNT bound *)
  assert (Hcnt : INR (length l) <= Bxi (2 ^ K)).
  { apply xi_count_peel; [ lra | apply filt_peel | ].
    intros x Hx. destruct (filt_in (nearp K) N x Hx) as [_ Hp].
    exact (nearp_true K x Hp). }
  assert (Hcst : exp (Bxi (2 ^ K) * ln (del / 2 ^ K))
                 <= prodR (fun _ : C => del / 2 ^ K) l).
  { apply Rle_trans with ((del / 2 ^ K) ^ (length l)).
    - rewrite (pow_exp (del / 2 ^ K) (length l) Hq0'). apply exp_le. nra.
    - apply prodR_const_ge; [ exact Hq0' | intros x _; lra ]. }
  (* the exponential part meets the SUM bound *)
  assert (Hsum : sumlist invmod l <= agrow * Aser K).
  { apply xi_sum_inv1; [ apply filt_peel | | ].
    - intros x Hx. destruct (filt_in (nearp K) N x Hx) as [Hin _].
      exact (take_zero N x Hin).
    - intros x Hx. destruct (filt_in (nearp K) N x Hx) as [Hin Hp].
      split; [ exact (take_low N x Hin)
             | exact (nearp_true K x Hp) ]. }
  assert (Hexp : exp (- rr * (agrow * Aser K)) <= exp (- rr * sumlist invmod l))
    by (apply exp_le; pose proof Hrrpos; nra).
  (* multiply the two halves *)
  apply Rle_trans with (prodR (fun _ : C => del / 2 ^ K) l
                        * exp (- rr * sumlist invmod l));
    [ | exact Hprod ].
  replace (Bxi (2 ^ K) * ln (del / 2 ^ K) - rr * (agrow * Aser K))
    with (Bxi (2 ^ K) * ln (del / 2 ^ K) + (- rr * (agrow * Aser K))) by ring.
  rewrite exp_plus. apply Rmult_le_compat.
  - left; apply exp_pos.
  - left; apply exp_pos.
  - exact Hcst.
  - exact Hexp.
Qed.

(* ----------------------------------------------------------------- *)
(*  C.  the far block                                                  *)
(* ----------------------------------------------------------------- *)
Lemma far_factor : forall N x,
  In x (filter (fun y => negb (nearp K y)) (takeN rho N)) ->
  0 <= exp (- (2 * rr ^ 2) * invsq x)
  /\ exp (- (2 * rr ^ 2) * invsq x) <= Cmod (Efac w x).
Proof.
  intros N x Hx.
  destruct (filt_in _ N x Hx) as [Hin Hp].
  apply negb_true_iff in Hp.
  pose proof (nearp_false K x Hp) as Hbig.
  pose proof (take_ne0 N x Hin) as Hne.
  pose proof (take_low N x Hin) as Hlow1.
  split; [ left; apply exp_pos | ].
  assert (Hfar : 10 * Cmod w <= Cmod x) by (rewrite Hw; lra).
  pose proof (Efac_lower_far w x Hne Hfar) as Hlb.
  assert (Heq : - (2 * rr ^ 2) * invsq x = - (2 * Cmod w ^ 2 / Cmod x ^ 2))
    by (unfold invsq; rewrite Hw; field; lra).
  rewrite Heq. exact Hlb.
Qed.

Lemma far_bound : forall N,
  exp (- (2 * rr ^ 2) * (agrow * (2 * (INR K + 2) / 2 ^ K)))
  <= Cmod (Wlist (filter (fun y => negb (nearp K y)) (takeN rho N)) w).
Proof.
  intro N. set (l := filter (fun y => negb (nearp K y)) (takeN rho N)).
  assert (Hprod : prodR (fun x => exp (- (2 * rr ^ 2) * invsq x)) l
                  <= Cmod (Wlist l w))
    by (apply prodR_le_Wlist; intros x Hx; apply (far_factor N x Hx)).
  rewrite (prodR_exp (fun x => - (2 * rr ^ 2) * invsq x) l) in Hprod.
  rewrite (sumlist_scal (- (2 * rr ^ 2)) invsq l) in Hprod.
  (* the tail sum needs an OUTER dyadic cutoff too *)
  assert (Hsum : sumlist invsq l <= agrow * (2 * (INR K + 2) / 2 ^ K)).
  { assert (Habs2 : Rabs 2 > 1) by (rewrite Rabs_pos_eq; lra).
    destruct (Pow_x_infinity 2 Habs2 (maxmod l + 1)) as [M HM].
    pose proof (HM M (le_n M)) as HMm.
    rewrite Rabs_pos_eq in HMm by (apply pow_le; lra).
    assert (HKN2 : (K <= Nat.max K M)%nat) by lia.
    pose proof (pow2_mono M (Nat.max K M) ltac:(lia)) as Hmono.
    apply (xi_sum_tail K (Nat.max K M) HKN2); [ apply filt_peel | | ].
    - intros x Hx. destruct (filt_in _ N x Hx) as [Hin _].
      exact (take_zero N x Hin).
    - intros x Hx. destruct (filt_in _ N x Hx) as [Hin Hp].
      apply negb_true_iff in Hp.
      split; [ exact (nearp_false K x Hp) | ].
      pose proof (maxmod_ub l x Hx). lra. }
  apply Rle_trans with (exp (- (2 * rr ^ 2) * sumlist invsq l)); [ | exact Hprod ].
  apply exp_le. pose proof Hrrpos. nra.
Qed.

(* ----------------------------------------------------------------- *)
(*  D.  every truncation, then the limit                               *)
(* ----------------------------------------------------------------- *)
Lemma prod_lower_N : forall N,
  exp (LBexp rr del K) <= Cmod (Pprod (fun k => Efac w (rho k)) N).
Proof.
  intro N.
  rewrite <- (Wlist_takeN rho w N).
  rewrite (Wlist_filter_split (nearp K) (takeN rho (S N)) w), Cmod_mul.
  unfold LBexp.
  replace (Bxi (2 ^ K) * ln (del / 2 ^ K) - rr * (agrow * Aser K)
           - 2 * rr ^ 2 * (agrow * (2 * (INR K + 2) / 2 ^ K)))
    with ((Bxi (2 ^ K) * ln (del / 2 ^ K) - rr * (agrow * Aser K))
          + (- (2 * rr ^ 2) * (agrow * (2 * (INR K + 2) / 2 ^ K)))) by ring.
  rewrite exp_plus.
  apply Rmult_le_compat;
    [ left; apply exp_pos | left; apply exp_pos
    | exact (near_bound (S N)) | exact (far_bound (S N)) ].
Qed.

Theorem xi_prod_lower : forall Pw,
  CUn_cv (Pprod (fun k => Efac w (rho k))) Pw ->
  exp (LBexp rr del K) <= Cmod Pw.
Proof.
  intros Pw HP.
  apply (CUn_cv_mod_ge _ _ (exp (LBexp rr del K)) 0%nat HP).
  intros n _. apply prod_lower_N.
Qed.

End Circle.

End ProdLower.

Print Assumptions xi_prod_lower.

(* ================================================================= *)
(*  The packaged form: the caller supplies only the radius.            *)
(*                                                                    *)
(*  xi_good_radius picks the circle, CDyadicBracket picks the dyadic   *)
(*  cut, and the seven side conditions above are discharged here so    *)
(*  that a consumer sees one hypothesis (1 <= r) and one conclusion.   *)
(*  The covering radius 80 r is forced: the cut sits below 20 rr and   *)
(*  rr below 4 r, so the near zeros reach out to 80 r.                 *)
(* ================================================================= *)
Theorem xi_prod_lower_circle : forall rho, ZeroEnum rho ->
  (forall n, 1 <= Cmod (rho n)) ->
  forall r, 1 <= r ->
  exists (rr del : R) (K : nat),
    2 * r <= rr /\ rr <= 4 * r /\ 0 < del /\ del <= r /\
    r / (Bxi (80 * r) + 1) <= del /\
    10 * rr <= 2 ^ K /\ 2 ^ K < 20 * rr /\
    forall w, Cmod w = rr ->
      forall Pw, CUn_cv (Pprod (fun k => Efac w (rho k))) Pw ->
        exp (LBexp rr del K) <= Cmod Pw.
Proof.
  intros rho Henum Hlow r Hr.
  destruct (xi_good_radius r (80 * r) ltac:(lra) ltac:(lra))
    as [rr [del [Hlo [Hhi [Hd0 [Hdr [Hdb Hgap]]]]]]].
  destruct (dyadic_bracket (10 * rr) ltac:(lra)) as [K [HK1 HK2]].
  exists rr, del, K.
  repeat split; try assumption; try lra.
  intros w Hw Pw HP.
  apply (xi_prod_lower rho Henum Hlow r rr del K w
           Hr Hlo Hhi Hd0 Hdr HK1 ltac:(lra) Hw);
    [ intros x Hz Hm; exact (Hgap x Hz Hm w Hw) | exact HP ].
Qed.

Print Assumptions xi_prod_lower_circle.
