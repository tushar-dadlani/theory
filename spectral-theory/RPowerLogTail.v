(* ================================================================= *)
(*  RPowerLogTail.v  --  the LOG-WEIGHTED p-series tail.               *)
(*                                                                    *)
(*    ln_le_pow  : 0 < d, 1 <= u  ==>  ln u <= (1/(d e)) u^d           *)
(*    logptail_ub : 0 < d <= 1/4, 1 <= N  ==>                          *)
(*      Sum_i ln(N+i+2) (N+i+1)^{-(2-d)}                               *)
(*        <= (4/(d e)) N^{-(1-2d)}                                     *)
(*                                                                    *)
(*  The SECOND missing brick.  RPowerTail.ptail_ub extends the plain   *)
(*  tail below Re s = 1, which is enough for the zeta bound (link [1]) *)
(*  but not for zeta' (link [3]): differentiating the Euler-Maclaurin  *)
(*  term termwise attaches a factor ln(n+2) to every summand, and      *)
(*  ZetaDerivBound.logtail_tele -- which handles exactly that -- again *)
(*  telescopes against 1/(n(n+1)) and so exists only at the integer    *)
(*  exponent 2.                                                       *)
(*                                                                    *)
(*  The trick is to spend the log ON the exponent rather than fight it.*)
(*  ln u <= (1/(d e)) u^d is sharp at u = e^{1/d} (that is where       *)
(*  v e^{-v} peaks, v = d ln u), and it is exactly exp_ineq1_le in     *)
(*  disguise: v <= e^{v-1}.  Absorbing u^d turns the exponent -(2-d)   *)
(*  into -(2-2d), still above -1, so ptail_ub applies and the sum      *)
(*  still decays like N^{-(1-2d)}.                                    *)
(*                                                                    *)
(*  The price is the constant 1/(d e), which at d = 1/ln T is          *)
(*  (ln T)/e -- i.e. ONE extra log.  That is affordable: the tail is   *)
(*  multiplied by |s| ~ T and N^{-(1-2d)} ~ 1/T at N ~ T, so the       *)
(*  product is O(ln T), which is the target order for zeta'.           *)
(*  Axiom-clean.                                                      *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import CPowBase CZetaTerm RPowerTail ZetaLogBound.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  A.  a logarithm is dominated by any positive power                 *)
(* ----------------------------------------------------------------- *)
Lemma ln_le_pow : forall d u, 0 < d -> 1 <= u -> ln u <= / (d * exp 1) * Rpower u d.
Proof.
  intros d u Hd Hu.
  assert (He : 0 < exp 1) by apply exp_pos.
  assert (HL : 0 <= ln u) by (apply ln_nonneg; exact Hu).
  assert (Hv : d * ln u <= exp (d * ln u - 1))
    by (pose proof (exp_ineq1_le (d * ln u - 1)); lra).
  assert (Hexp : exp (d * ln u - 1) * exp 1 = Rpower u d).
  { rewrite <- exp_plus.
    replace (d * ln u - 1 + 1) with (d * ln u) by ring.
    unfold Rpower. reflexivity. }
  assert (Hv2 : d * ln u * exp 1 <= Rpower u d)
    by (rewrite <- Hexp; apply Rmult_le_compat_r; lra).
  apply (Rmult_le_reg_r (d * exp 1)); [ nra | ].
  assert (E : / (d * exp 1) * Rpower u d * (d * exp 1) = Rpower u d) by (field; nra).
  rewrite E. nra.
Qed.

(* ----------------------------------------------------------------- *)
(*  B.  Rpower is monotone in the BASE                                 *)
(* ----------------------------------------------------------------- *)
Lemma Rpower_base_le : forall x y d, 0 < x -> x <= y -> 0 <= d ->
  Rpower x d <= Rpower y d.
Proof.
  intros x y d Hx Hxy Hd. unfold Rpower. apply exp_le.
  assert (Hln : ln x <= ln y) by (apply ln_le'; assumption).
  nra.
Qed.

(* ----------------------------------------------------------------- *)
(*  C.  THE LOG-WEIGHTED TAIL                                          *)
(* ----------------------------------------------------------------- *)
Theorem logptail_ub : forall d N K, 0 < d -> d <= / 4 -> (1 <= N)%nat ->
  sum_f_R0 (fun i => ln (INR (S (S (N + i))))
                     * Rpower (INR (S (N + i))) (- (2 - d))) K
  <= 4 / (d * exp 1) * Rpower (INR N) (- (1 - 2 * d)).
Proof.
  intros d N K Hd Hd4 HN.
  assert (He : 0 < exp 1) by apply exp_pos.
  assert (Hde : 0 < d * exp 1) by nra.
  eapply Rle_trans.
  - apply sum_Rle. intros i _.
    assert (H1 : 1 <= INR (S (N + i)))
      by (rewrite S_INR; pose proof (pos_INR (N + i)); lra).
    assert (H1' : 0 < INR (S (N + i))) by lra.
    assert (H2 : 1 <= INR (S (S (N + i))))
      by (rewrite !S_INR; pose proof (pos_INR (N + i)); lra).
    assert (Hle2 : INR (S (S (N + i))) <= 2 * INR (S (N + i)))
      by (rewrite !S_INR; pose proof (pos_INR (N + i)); lra).
    (* spend the log on the exponent *)
    assert (Hln : ln (INR (S (S (N + i))))
               <= / (d * exp 1) * Rpower (INR (S (S (N + i)))) d)
      by (apply ln_le_pow; assumption).
    assert (Hb : Rpower (INR (S (S (N + i)))) d <= Rpower (2 * INR (S (N + i))) d)
      by (apply Rpower_base_le; [ lra | exact Hle2 | lra ]).
    assert (Hsplit : Rpower (2 * INR (S (N + i))) d
                   = Rpower 2 d * Rpower (INR (S (N + i))) d)
      by (rewrite Rpower_mult_distr; [ reflexivity | lra | lra ]).
    assert (H2d : Rpower 2 d <= 2).
    { assert (E : (2:R) = Rpower 2 1) by (rewrite Rpower_1; lra).
      rewrite E at 2. apply Rpower_exp_le; lra. }
    assert (Hp0 : 0 < Rpower (INR (S (N + i))) d) by (unfold Rpower; apply exp_pos).
    assert (Hq0 : 0 < Rpower (INR (S (N + i))) (- (2 - d)))
      by (unfold Rpower; apply exp_pos).
    assert (Hln2 : ln (INR (S (S (N + i))))
                <= 2 / (d * exp 1) * Rpower (INR (S (N + i))) d).
    { assert (Hchain : / (d * exp 1) * Rpower (INR (S (S (N + i)))) d
                    <= / (d * exp 1) * (2 * Rpower (INR (S (N + i))) d)).
      { apply Rmult_le_compat_l; [ left; apply Rinv_0_lt_compat; exact Hde | ].
        rewrite Hsplit in Hb. nra. }
      assert (E : / (d * exp 1) * (2 * Rpower (INR (S (N + i))) d)
                = 2 / (d * exp 1) * Rpower (INR (S (N + i))) d)
        by (unfold Rdiv; ring).
      lra. }
    assert (Hcomb : ln (INR (S (S (N + i)))) * Rpower (INR (S (N + i))) (- (2 - d))
                 <= 2 / (d * exp 1) * Rpower (INR (S (N + i))) (- (2 - 2 * d))).
    { assert (Hmul : ln (INR (S (S (N + i)))) * Rpower (INR (S (N + i))) (- (2 - d))
                  <= 2 / (d * exp 1) * Rpower (INR (S (N + i))) d
                     * Rpower (INR (S (N + i))) (- (2 - d)))
        by (apply Rmult_le_compat_r; [ lra | exact Hln2 ]).
      assert (Eexp : Rpower (INR (S (N + i))) d * Rpower (INR (S (N + i))) (- (2 - d))
                   = Rpower (INR (S (N + i))) (- (2 - 2 * d))).
      { rewrite <- Rpower_plus. f_equal. ring. }
      rewrite Rmult_assoc, Eexp in Hmul. exact Hmul. }
    exact Hcomb.
  - (* pull the constant out and apply ptail_ub at p = 2 - 2d *)
    assert (E : sum_f_R0 (fun i => 2 / (d * exp 1)
                  * Rpower (INR (S (N + i))) (- (2 - 2 * d))) K
              = 2 / (d * exp 1)
                * sum_f_R0 (fun i => Rpower (INR (S (N + i))) (- (2 - 2 * d))) K).
    { rewrite (scal_sum (fun i => Rpower (INR (S (N + i))) (- (2 - 2 * d))) K
                (2 / (d * exp 1))).
      apply sum_eq; intros i _; ring. }
    rewrite E.
    pose proof (ptail_ub (2 - 2 * d) N K ltac:(lra) HN) as HT.
    replace (2 - 2 * d - 1) with (1 - 2 * d) in HT by ring.
    assert (Hpos : 0 <= Rpower (INR N) (- (1 - 2 * d)))
      by (left; unfold Rpower; apply exp_pos).
    assert (Hinv : / (1 - 2 * d) <= 2).
    { apply (Rmult_le_reg_r (1 - 2 * d)); [ lra | ].
      rewrite Rinv_l by lra. lra. }
    assert (Hi0 : 0 < / (1 - 2 * d)) by (apply Rinv_0_lt_compat; lra).
    assert (Hc0 : 0 < 2 / (d * exp 1))
      by (unfold Rdiv; apply Rmult_lt_0_compat;
          [ lra | apply Rinv_0_lt_compat; exact Hde ]).
    assert (Hstep : 2 / (d * exp 1)
                    * sum_f_R0 (fun i => Rpower (INR (S (N + i))) (- (2 - 2 * d))) K
                 <= 2 / (d * exp 1) * (/ (1 - 2 * d) * Rpower (INR N) (- (1 - 2 * d))))
      by (apply Rmult_le_compat_l; [ lra | exact HT ]).
    assert (Efin : 4 / (d * exp 1) * Rpower (INR N) (- (1 - 2 * d))
                 = 2 / (d * exp 1) * (2 * Rpower (INR N) (- (1 - 2 * d))))
      by (unfold Rdiv; ring).
    assert (Hfin : / (1 - 2 * d) * Rpower (INR N) (- (1 - 2 * d))
                <= 2 * Rpower (INR N) (- (1 - 2 * d)))
      by (apply Rmult_le_compat_r; [ exact Hpos | exact Hinv ]).
    assert (Hfin2 : 2 / (d * exp 1) * (/ (1 - 2 * d) * Rpower (INR N) (- (1 - 2 * d)))
                 <= 2 / (d * exp 1) * (2 * Rpower (INR N) (- (1 - 2 * d))))
      by (apply Rmult_le_compat_l; [ lra | exact Hfin ]).
    rewrite Efin. lra.
Qed.

Print Assumptions ln_le_pow.
Print Assumptions logptail_ub.
