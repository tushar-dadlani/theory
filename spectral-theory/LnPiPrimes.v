(* ================================================================= *)
(*  LnPiPrimes.v  --  ln pi IS a prime object.                        *)
(*                                                                    *)
(*      2 * ln pi  =  ln 2 + ln 3 + sum_p  -ln(1 - 1/p^2)             *)
(*                                                                    *)
(*  read as a limit over the primes p <= B.  This is an IDENTITY, not  *)
(*  an asymptotic, and it is unconditional -- unlike Mertens' third    *)
(*  (MertensThird.MertensThird is a bare Prop; the e^gamma constant     *)
(*  there is still an unproved hypothesis, mertens_deep_input).        *)
(*                                                                    *)
(*  WHERE IT COMES FROM.  Both halves are already in the repository    *)
(*  and are already fused:                                            *)
(*                                                                    *)
(*    Ell2Euler.euler_product_operator_2                              *)
(*      : Un_cv (fun N => Zfactor (map (p |-> p^-2) (primes_upto ...)))*)
(*               (PI^2 / 6)                                           *)
(*                                                                    *)
(*  -- Basel (BaselZeta.basel) supplies the value pi^2/6, the Euler    *)
(*  product (EulerProductZeta.euler_product_zeta2) supplies the prime  *)
(*  side.  The ONLY thing missing was the logarithm, and that is what  *)
(*  this file adds: ln of a finite product (ln_Zfactor) and the        *)
(*  transfer of a limit through ln (Un_cv_ln).                        *)
(*                                                                    *)
(*  WHY IT IS WORTH RECORDING.  Everywhere else in this development    *)
(*  ln PI is an ARCHIMEDEAN constant: LnConstants.lnPI_bounds feeds    *)
(*  GammaArg.theta (the Riemann-Siegel theta, which carries the        *)
(*  pi^{-s/2} of the functional equation), hence ThetaEnclose and      *)
(*  every one of the nine certified zeros, and                        *)
(*  ExplicitFormulaXiZetaBridge.darchexp.  It has never appeared on    *)
(*  the PRIME side of an identity here.  This is the first place.      *)
(*                                                                    *)
(*  HONEST SCOPE.  No RH content, no PNT content.  This says nothing   *)
(*  about the critical strip; it is a statement about one constant.    *)
(*  Companion file LogBaseChange.v records the complementary negative  *)
(*  fact: log_10 pi, log_10 e and log_pi e add nothing to this -- they *)
(*  are change-of-base images of ln pi, and base 10 contributes only   *)
(*  the factorisation 10 = 2 * 5.                                     *)
(* ================================================================= *)

Require Import EulerProductR EulerProductZeta Ell2Euler CertifiedPi
        LnConstants LogBaseChange.
From Stdlib Require Import Reals Lra Lia List ZArith Znumtheory.
Import ListNotations.
Open Scope R_scope.

(* ================================================================= *)
(*  1.  ln IS 2-LIPSCHITZ-ish NEAR A POINT: the transfer lemma        *)
(* ================================================================= *)

(* NOTE.  The obvious route -- continuity_seq, the idiom used at
   GammaGaussLimit.v:448 and GaussSqrtStep.v:85 -- does NOT work for ln.
   continuity_seq demands GLOBAL continuity, and the standard library's
   ln is 0 on x <= 0, so `continuity ln` is false.  We go through the
   elementary two-sided bound instead. *)

Lemma ln_le_sub1 : forall y, 0 < y -> ln y <= y - 1.
Proof.
  intros y Hy. pose proof (exp_ineq1_le (ln y)) as H.
  rewrite exp_ln in H by exact Hy. lra.
Qed.

Lemma ln_ge_1_inv : forall y, 0 < y -> 1 - / y <= ln y.
Proof.
  intros y Hy.
  pose proof (ln_le_sub1 (/ y) (Rinv_0_lt_compat y Hy)) as H.
  rewrite ln_Rinv in H by exact Hy. lra.
Qed.

(* the only estimate we need: on y >= 1/2, |ln y| <= 2 |y - 1| *)
Lemma ln_close : forall y, / 2 <= y -> Rabs (ln y) <= 2 * Rabs (y - 1).
Proof.
  intros y Hy2. assert (Hy : 0 < y) by lra.
  pose proof (ln_le_sub1 y Hy) as H1.
  pose proof (ln_ge_1_inv y Hy) as H2.
  assert (Hinv2 : / y <= 2).
  { replace 2 with (/ (/ 2)) by field. apply Rinv_le_contravar; lra. }
  destruct (Rle_lt_dec 1 y) as [Hge | Hlt].
  - assert (Hinv1 : / y <= 1).
    { replace 1 with (/ 1) by field. apply Rinv_le_contravar; lra. }
    rewrite (Rabs_right (ln y)) by lra.
    rewrite (Rabs_right (y - 1)) by lra. lra.
  - rewrite (Rabs_left1 (ln y)) by lra.
    rewrite (Rabs_left1 (y - 1)) by lra.
    assert (E : / y - 1 = (1 - y) * / y) by (field; lra).
    assert (H3 : (1 - y) * / y <= (1 - y) * 2)
      by (apply Rmult_le_compat_l; lra).
    lra.
Qed.

Lemma Un_cv_ln : forall u L, Un_cv u L -> 0 < L -> (forall n, 0 < u n) ->
  Un_cv (fun n => ln (u n)) (ln L).
Proof.
  intros u L Hcv HL Hpos eps Heps.
  assert (Hd : 0 < Rmin (L / 2) (eps * L / 2)).
  { apply Rmin_glb_lt; [ lra | ]. apply Rmult_lt_0_compat; [ | lra ].
    apply Rmult_lt_0_compat; assumption. }
  destruct (Hcv _ Hd) as [N HN]. exists N. intros n Hn.
  specialize (HN n Hn). unfold R_dist in *.
  assert (Hb1 : Rabs (u n - L) < L / 2)
    by (eapply Rlt_le_trans; [ exact HN | apply Rmin_l ]).
  assert (Hb2 : Rabs (u n - L) < eps * L / 2)
    by (eapply Rlt_le_trans; [ exact HN | apply Rmin_r ]).
  destruct (Rabs_def2 _ _ Hb1) as [Hlt1 Hgt1].
  assert (Hun : L / 2 < u n) by lra.
  (* the ratio y = u n / L sits above 1/2 *)
  assert (Hy : / 2 <= u n / L).
  { unfold Rdiv. apply Rle_trans with ((L / 2) * / L);
      [ right; field; lra | apply Rmult_le_compat_r;
        [ left; apply Rinv_0_lt_compat; exact HL | lra ] ]. }
  (* ln (u n) - ln L = ln (u n / L) *)
  assert (Hsplit : ln (u n) - ln L = ln (u n / L)).
  { unfold Rdiv. rewrite ln_mult by (try exact (Hpos n); apply Rinv_0_lt_compat; exact HL).
    rewrite ln_Rinv by exact HL. ring. }
  rewrite Hsplit.
  eapply Rle_lt_trans; [ apply (ln_close _ Hy) | ].
  assert (Hrw : u n / L - 1 = (u n - L) / L) by (field; lra).
  rewrite Hrw. unfold Rdiv. rewrite Rabs_mult.
  rewrite (Rabs_right (/ L)) by (left; apply Rinv_0_lt_compat; exact HL).
  apply (Rmult_lt_reg_r L); [ exact HL | ].
  replace (2 * (Rabs (u n - L) * / L) * L) with (2 * Rabs (u n - L)) by (field; lra).
  lra.
Qed.

(* ================================================================= *)
(*  2.  ln OF A FINITE EULER PRODUCT                                  *)
(* ================================================================= *)

Definition Rsuml (l : list R) : R := fold_right Rplus 0 l.

Lemma Zfac_pos : forall xs, (forall x, In x xs -> x < 1) -> 0 < Zfactor xs.
Proof.
  intros xs; induction xs as [| x xs IH]; intro H;
    unfold Zfactor in *; cbn [map fold_right]; [ lra | ].
  apply Rmult_lt_0_compat.
  - apply Rinv_0_lt_compat; pose proof (H x (in_eq x xs)); lra.
  - apply IH; intros y Hy; apply H; right; exact Hy.
Qed.

Lemma ln_Zfactor : forall xs, (forall x, In x xs -> 0 <= x < 1) ->
  ln (Zfactor xs) = Rsuml (map (fun x => - ln (1 - x)) xs).
Proof.
  induction xs as [| x xs IH]; intro H.
  - unfold Zfactor, Rsuml; cbn [map fold_right]; rewrite ln_1; reflexivity.
  - assert (Hx : 0 <= x < 1) by (apply H; left; reflexivity).
    assert (Hxs : forall y, In y xs -> 0 <= y < 1)
      by (intros y Hy; apply H; right; exact Hy).
    assert (HZ : 0 < Zfactor xs)
      by (apply Zfac_pos; intros y Hy; apply (Hxs y Hy)).
    change (Zfactor (x :: xs)) with (/ (1 - x) * Zfactor xs).
    rewrite ln_mult by (try exact HZ; apply Rinv_0_lt_compat; lra).
    rewrite ln_Rinv by lra.
    rewrite (IH Hxs). unfold Rsuml. cbn [map fold_right]. ring.
Qed.

(* ================================================================= *)
(*  3.  THE PRIME SIDE                                                *)
(* ================================================================= *)

(* the local log-factor at p:  -ln(1 - p^{-2}) = ln (1 - p^{-2})^{-1} *)
Definition plog (p : Z) : R := - ln (1 - / (IZR p) ^ 2).

Definition PrimeLogSum (B : nat) : R := Rsuml (map plog (primes_upto (S B))).

(* the bound already used at EulerProductZeta.v:244-248 *)
Lemma prime_recipsq_range : forall p, prime p -> 0 <= / (IZR p) ^ 2 < 1.
Proof.
  intros p Hp. destruct Hp as [Hp1 _].
  assert (H2 : 2 <= IZR p) by (apply IZR_le; lia).
  split.
  - apply Rlt_le, Rinv_0_lt_compat, pow_lt; lra.
  - apply Rle_lt_trans with (/ 4); [ apply Rinv_le_contravar; [ lra | nra ] | lra ].
Qed.

Lemma PrimeLogSum_eq : forall N,
  PrimeLogSum N
  = ln (Zfactor (map (fun p => / (IZR p) ^ 2) (primes_upto (S N)))).
Proof.
  intro N. rewrite ln_Zfactor.
  - unfold PrimeLogSum, plog. rewrite map_map. reflexivity.
  - intros x Hx. apply in_map_iff in Hx. destruct Hx as [p [Hpx Hp]]; subst x.
    apply prime_recipsq_range, (primes_upto_prime (S N) p Hp).
Qed.

(* ================================================================= *)
(*  4.  THE LIMIT VALUE                                               *)
(* ================================================================= *)

Lemma ln_pi2_over_6 : ln (PI ^ 2 / 6) = 2 * ln PI - ln 2 - ln 3.
Proof.
  pose proof PI_RGT_0 as HP.
  assert (H6 : ln 6 = ln 2 + ln 3)
    by (replace 6 with (2 * 3) by ring; apply ln_mult; lra).
  replace (PI ^ 2) with (PI * PI) by ring.
  unfold Rdiv.
  rewrite ln_mult by (try nra; apply Rinv_0_lt_compat; lra).
  rewrite ln_Rinv by lra. rewrite H6.
  rewrite ln_mult by exact HP. ring.
Qed.

(* ================================================================= *)
(*  5.  THE IDENTITY                                                  *)
(* ================================================================= *)

Theorem lnPI_prime_sum : Un_cv PrimeLogSum (2 * ln PI - ln 2 - ln 3).
Proof.
  pose proof PI_RGT_0 as HP.
  assert (Hzp : forall N,
    0 < Zfactor (map (fun p => / (IZR p) ^ 2) (primes_upto (S N)))).
  { intro N. apply Zfac_pos. intros x Hx.
    apply in_map_iff in Hx. destruct Hx as [p [Hpx Hp]]; subst x.
    apply (prime_recipsq_range p (primes_upto_prime (S N) p Hp)). }
  assert (HL : 0 < PI ^ 2 / 6) by nra.
  pose proof (Un_cv_ln _ _ euler_product_operator_2 HL Hzp) as Hcv.
  rewrite ln_pi2_over_6 in Hcv.
  intros eps Heps. destruct (Hcv eps Heps) as [N HN]. exists N.
  intros n Hn. specialize (HN n Hn). unfold R_dist in *.
  rewrite PrimeLogSum_eq. exact HN.
Qed.

(* ================================================================= *)
(*  6.  NON-VACUITY                                                   *)
(* ================================================================= *)

(* (a) the limit is not the trivial 0.  ln 3 <= 2 ln 2 needs no new
       certification: 3 <= 4 = 2*2. *)
Lemma ln3_le_2ln2 : ln 3 <= 2 * ln 2.
Proof.
  assert (H4 : ln 4 = 2 * ln 2)
    by (replace 4 with (2 * 2) by ring; rewrite ln_mult by lra; ring).
  rewrite <- H4. apply ln_mono; lra.
Qed.

Theorem lnPI_prime_sum_pos : 0 < 2 * ln PI - ln 2 - ln 3.
Proof.
  pose proof lnPI_bounds as [Hlo _]. pose proof ln2_bounds as [_ Hhi].
  pose proof ln3_le_2ln2. lra.
Qed.

(* (b) the prime list is genuinely non-empty: 2 really is summed over. *)
Lemma two_in_primes_upto : forall B, In 2%Z (primes_upto (S (S B))).
Proof.
  intro B. apply primes_upto_complete; [ exact prime_2 | lia ].
Qed.

(* (c) every local factor is nonnegative, so the sum is a genuine
       increasing approximation from below, not a cancelling artefact. *)
Lemma plog_nonneg : forall p, prime p -> 0 <= plog p.
Proof.
  intros p Hp. destruct (prime_recipsq_range p Hp) as [H0 H1].
  unfold plog.
  assert (Hle : ln (1 - / (IZR p) ^ 2) <= ln 1) by (apply ln_mono; lra).
  rewrite ln_1 in Hle. lra.
Qed.

Theorem PrimeLogSum_nonneg : forall B, 0 <= PrimeLogSum B.
Proof.
  intro B. unfold PrimeLogSum, Rsuml.
  assert (Hall : forall p, In p (primes_upto (S B)) -> 0 <= plog p)
    by (intros p Hp; apply plog_nonneg, (primes_upto_prime (S B) p Hp)).
  revert Hall. generalize (primes_upto (S B)) as l. intro l.
  induction l as [| p l IH]; intro Hall; cbn [map fold_right]; [ lra | ].
  apply Rplus_le_le_0_compat.
  - apply Hall; left; reflexivity.
  - apply IH; intros q Hq; apply Hall; right; exact Hq.
Qed.

(* ================================================================= *)
(*  7.  THE PAYOFF: log_pi e, read off the primes                     *)
(* ================================================================= *)

(* log_pi e = 1 / ln pi, and ln pi is the prime sum above, so the      *)
(* fourth constant of the original question is itself a prime object   *)
(* -- a derived one, being a reciprocal.                              *)

Lemma Sfun_pos : forall B, 0 < PrimeLogSum B + ln 2 + ln 3.
Proof.
  intro B. pose proof (PrimeLogSum_nonneg B).
  assert (H2 : 0 < ln 2) by (apply ln_gt0; lra).
  assert (H3 : 0 < ln 3) by (apply ln_gt0; lra).
  lra.
Qed.

Theorem logPI_e_prime_sum :
  Un_cv (fun B => 2 / (PrimeLogSum B + ln 2 + ln 3)) (logb PI (exp 1)).
Proof.
  pose proof lnPI_gt0 as HlnP.
  assert (HS : Un_cv (fun B => PrimeLogSum B + ln 2 + ln 3) (2 * ln PI)).
  { intros eps Heps. destruct (lnPI_prime_sum eps Heps) as [N HN].
    exists N. intros n Hn. specialize (HN n Hn). unfold R_dist in *.
    replace (PrimeLogSum n + ln 2 + ln 3 - 2 * ln PI)
      with (PrimeLogSum n - (2 * ln PI - ln 2 - ln 3)) by ring.
    exact HN. }
  assert (H2P : 0 < 2 * ln PI) by lra.
  pose proof (Un_cv_ln _ _ HS H2P Sfun_pos) as Hln.
  assert (Hopp : Un_cv (fun B => - ln (PrimeLogSum B + ln 2 + ln 3))
                       (- ln (2 * ln PI)))
    by (apply CV_opp; exact Hln).
  assert (Hexp : Un_cv (fun B => exp (- ln (PrimeLogSum B + ln 2 + ln 3)))
                       (exp (- ln (2 * ln PI))))
    by (apply (continuity_seq exp); [ apply derivable_continuous, derivable_exp
                                    | exact Hopp ]).
  assert (Hmul : Un_cv (fun B => 2 * exp (- ln (PrimeLogSum B + ln 2 + ln 3)))
                       (2 * exp (- ln (2 * ln PI))))
    by (apply CV_mult; [ apply Un_cv_const | exact Hexp ]).
  (* rewrite exp(-ln y) = /y on both sides *)
  assert (Hlim : 2 * exp (- ln (2 * ln PI)) = logb PI (exp 1)).
  { rewrite exp_Ropp, exp_ln by exact H2P. rewrite logPI_e_inv.
    field; lra. }
  rewrite Hlim in Hmul.
  intros eps Heps. destruct (Hmul eps Heps) as [N HN]. exists N.
  intros n Hn. specialize (HN n Hn). unfold R_dist in *.
  assert (Hrw : 2 / (PrimeLogSum n + ln 2 + ln 3)
                = 2 * exp (- ln (PrimeLogSum n + ln 2 + ln 3))).
  { pose proof (Sfun_pos n). rewrite exp_Ropp, exp_ln by assumption.
    field; lra. }
  rewrite Hrw. exact HN.
Qed.

Print Assumptions lnPI_prime_sum.
Print Assumptions logPI_e_prime_sum.

(* ================================================================= *)
(*  END LnPiPrimes.v                                                  *)
(*                                                                    *)
(*  Numerically (outside Rocq, as a sanity check only): summing        *)
(*  -ln(1-p^-2) over primes p < 10^7 and adding ln 2 + ln 3, then      *)
(*  halving, gives 1.1447298829 against ln pi = 1.1447298858.          *)
(* ================================================================= *)
