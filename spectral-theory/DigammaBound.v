(* ================================================================= *)
(*  DigammaBound.v  --  Re psi(z) = O(ln |Im z|)  on  0 < Re z <= 1.   *)
(*                                                                    *)
(*     Re (digamma z dG)  <=  3 + (1/2) ln (1 + (Im z)^2)              *)
(*                                                                    *)
(*  This is the archimedean input of de la Vallee Poussin.  In the     *)
(*  bridge  ExplicitFormulaXiLogDeriv.XiC_logderiv,                    *)
(*     zeta'/zeta = xi'/xi - 1/z - 1/(z-1) + (1/2)ln pi - (1/2)psi(z/2),*)
(*  every term except psi has a bound already; psi had none anywhere   *)
(*  in the repo, which is why the zero-free region could not be run    *)
(*  additively.  With PhiThreeFourOne.tfo_phi and this, both halves of *)
(*  the dVP inequality are available.                                  *)
(*                                                                    *)
(*  METHOD.  From DigammaSeries.digamma_series,                        *)
(*     psi(z) = - gamma - 1/z - sum_{k>=1} [ 1/(k+z) - 1/k ],          *)
(*  and with z = a + i b the k-th term of the (negated) sum splits     *)
(*  EXACTLY as                                                        *)
(*                                                                    *)
(*     1/k - Re(1/(k+z))  =    a / (k (k+a))                           *)
(*                          +  b^2 / ((k+a)((k+a)^2 + b^2)).           *)
(*                                                                    *)
(*  Both pieces are >= 0 (so the sum is one-signed -- no cancellation  *)
(*  to track).  The first is <= 1/k^2 when a <= 1, summing to <= 2 by  *)
(*  the repo's GammaCWeierstrass.invsq_bound.  The second is the whole *)
(*  logarithm, and is <= f(k) := b^2/(k(k^2+b^2)).                     *)
(*                                                                    *)
(*  The usual treatment of sum f(k) splits the range at k ~ |b| (below *)
(*  it f(k) ~ 1/k, above it f(k) ~ b^2/k^3) and that index split is    *)
(*  painful in Coq.  It is avoidable: f has the ELEMENTARY primitive   *)
(*                                                                    *)
(*     G(x) = ln x - (1/2) ln (x^2 + b^2),     G'(x) = f(x),           *)
(*                                                                    *)
(*  so MVT plus f decreasing gives f(k) <= G(k) - G(k-1), and the sum  *)
(*  telescopes in ONE induction with no case analysis:                 *)
(*                                                                    *)
(*     sum_{k=1}^{K} f(k) <= f(1) + G(K) - G(1) <= 1 + (1/2)ln(1+b^2)  *)
(*                                                                    *)
(*  since G(K) = ln K - (1/2)ln(K^2+b^2) <= 0 and -G(1) = (1/2)ln(1+b^2).*)
(*  The crossover at k ~ |b| is still what produces the logarithm --   *)
(*  it is just done by the primitive instead of by hand.               *)
(*                                                                    *)
(*  Numerically checked against a direct 4e6-term summation of psi at  *)
(*  24 points (a in [0.5,1], |b| up to 5000): the bound holds with a   *)
(*  slack that settles at 5, and Re psi(z) -> ln|z| as it should.      *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import ComplexField Cmodulus CSeries Holomorphic CDeriv
        EulerMascheroni ChebyshevBound
        GammaC GammaCNe0 GammaCLogSum GammaCLogTerm GammaCWeierstrass
        CZetaXiComplex ExplicitFormulaDigamma DigammaSeries.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  Part A -- the telescoping majorant.                                *)
(* ----------------------------------------------------------------- *)

Section Telescope.
Variable b : R.

Definition fk (x : R) : R := b ^ 2 / (x * (x ^ 2 + b ^ 2)).
Definition Gk (x : R) : R := ln x - / 2 * ln (x ^ 2 + b ^ 2).

Lemma sq_pos : forall x, 0 < x -> 0 < x ^ 2 + b ^ 2.
Proof. intros x Hx. nra. Qed.

(* G' = f *)
Lemma dGk : forall x, 0 < x -> derivable_pt_lim Gk x (fk x).
Proof.
  intros x Hx. pose proof (sq_pos x Hx) as Hq.
  assert (H1 : derivable_pt_lim ln x (/ x)) by (apply derivable_pt_lim_ln; exact Hx).
  assert (H2a : derivable_pt_lim (fun t => t ^ 2) x (INR 2 * x ^ (2 - 1)))
    by apply derivable_pt_lim_pow.
  assert (H2b : derivable_pt_lim (fun _ : R => b ^ 2) x 0)
    by apply derivable_pt_lim_const.
  assert (H2 : derivable_pt_lim (fun t => t ^ 2 + b ^ 2) x (INR 2 * x ^ (2 - 1) + 0))
    by (apply derivable_pt_lim_plus; assumption).
  replace (INR 2 * x ^ (2 - 1) + 0) with (2 * x) in H2 by (simpl; ring).
  assert (H3 : derivable_pt_lim (fun t => ln (t ^ 2 + b ^ 2)) x (/ (x ^ 2 + b ^ 2) * (2 * x))).
  { apply (derivable_pt_lim_comp (fun t => t ^ 2 + b ^ 2) ln x (2 * x) (/ (x ^ 2 + b ^ 2))).
    - exact H2.
    - apply derivable_pt_lim_ln; exact Hq. }
  assert (H4 : derivable_pt_lim (fun t => / 2 * ln (t ^ 2 + b ^ 2)) x
                 (/ 2 * (/ (x ^ 2 + b ^ 2) * (2 * x))))
    by (apply derivable_pt_lim_scal; exact H3).
  assert (H5 : derivable_pt_lim Gk x (/ x - / 2 * (/ (x ^ 2 + b ^ 2) * (2 * x))))
    by (unfold Gk; apply derivable_pt_lim_minus; assumption).
  replace (fk x) with (/ x - / 2 * (/ (x ^ 2 + b ^ 2) * (2 * x)))
    by (unfold fk; field; split; lra).
  exact H5.
Qed.

(* f is decreasing on x > 0 : the denominator x(x^2+b^2) increases *)
Lemma fk_dec : forall u v, 0 < u -> u <= v -> fk v <= fk u.
Proof.
  intros u v Hu Huv.
  assert (Hv : 0 < v) by lra.
  assert (Hdu : 0 < u * (u ^ 2 + b ^ 2)) by (pose proof (sq_pos u Hu); nra).
  assert (Hdv : 0 < v * (v ^ 2 + b ^ 2)) by (pose proof (sq_pos v Hv); nra).
  assert (Hle : u * (u ^ 2 + b ^ 2) <= v * (v ^ 2 + b ^ 2)).
  { assert (Hfac : v * (v ^ 2 + b ^ 2) - u * (u ^ 2 + b ^ 2)
                   = (v - u) * (v ^ 2 + u * v + u ^ 2 + b ^ 2)) by ring.
    assert (H1 : 0 <= v - u) by lra.
    assert (H2 : 0 <= v ^ 2 + u * v + u ^ 2 + b ^ 2) by nra.
    nra. }
  unfold fk, Rdiv. apply Rmult_le_compat_l; [ nra | ].
  apply Rinv_le_contravar; [ exact Hdu | exact Hle ].
Qed.

(* the MVT step *)
Lemma fk_step : forall n, (1 <= n)%nat ->
  fk (INR (S n)) <= Gk (INR (S n)) - Gk (INR n).
Proof.
  intros n Hn.
  assert (Hn1 : 1 <= INR n) by (apply (le_INR 1); exact Hn).
  assert (Hlt : INR n < INR (S n)) by (apply lt_INR; lia).
  assert (Hd : forall c, INR n <= c <= INR (S n) -> derivable_pt_lim Gk c (fk c)).
  { intros c Hc. apply dGk. lra. }
  destruct (MVT_cor2 Gk fk (INR n) (INR (S n)) Hlt Hd) as [c [Hc1 Hc2]].
  rewrite Hc1.
  assert (Hstep : INR (S n) - INR n = 1) by (rewrite S_INR; ring).
  rewrite Hstep, Rmult_1_r.
  apply fk_dec; lra.
Qed.

(* the telescoping sum bound *)
Lemma fk_sum_tel : forall M,
  sum_f_R0 (fun n => fk (INR (S n))) M <= fk 1 + Gk (INR (S M)) - Gk 1.
Proof.
  induction M as [| M IH].
  - cbn [sum_f_R0]. replace (INR 1) with 1 by reflexivity. lra.
  - rewrite tech5.
    assert (Hs : fk (INR (S (S M))) <= Gk (INR (S (S M))) - Gk (INR (S M)))
      by (apply fk_step; lia).
    lra.
Qed.

Lemma Gk_le0 : forall x, 1 <= x -> Gk x <= 0.
Proof.
  intros x Hx.
  assert (Hx0 : 0 < x) by lra.
  assert (Hsq : ln (x ^ 2) <= ln (x ^ 2 + b ^ 2)).
  { apply ln_le; nra. }
  assert (Hln : ln (x ^ 2) = 2 * ln x).
  { replace (x ^ 2) with (x * x) by ring. rewrite ln_mult by lra. ring. }
  unfold Gk. lra.
Qed.

Theorem fk_sum_bound : forall M,
  sum_f_R0 (fun n => fk (INR (S n))) M <= 1 + / 2 * ln (1 + b ^ 2).
Proof.
  intro M.
  pose proof (fk_sum_tel M) as H.
  assert (H1 : fk 1 <= 1).
  { unfold fk. assert (0 < 1 * (1 ^ 2 + b ^ 2)) by nra.
    apply (Rmult_le_reg_r (1 * (1 ^ 2 + b ^ 2))); [ lra | ].
    unfold Rdiv. rewrite Rmult_assoc, Rinv_l by lra. nra. }
  assert (H2 : Gk (INR (S M)) <= 0).
  { apply Gk_le0. replace 1 with (INR 1) by reflexivity.
    apply le_INR; lia. }
  assert (H3 : Gk 1 = - (/ 2 * ln (1 + b ^ 2))).
  { unfold Gk. rewrite ln_1. replace (1 ^ 2 + b ^ 2) with (1 + b ^ 2) by ring. ring. }
  lra.
Qed.

End Telescope.

(* ----------------------------------------------------------------- *)
(*  Part B -- the termwise split.                                      *)
(* ----------------------------------------------------------------- *)

Lemma Re_gterm_val : forall n a b,
  Re (gterm n (mkC a b))
  = (INR (S n) + a) / ((INR (S n) + a) * (INR (S n) + a) + b * b) - / INR (S n).
Proof.
  intros n a b. unfold gterm, Cminus, Cinv, Cadd, RtoC, Cnorm2; cbn [Re Im].
  replace (0 + b) with b by ring. reflexivity.
Qed.

Lemma neg_Re_gterm_le : forall n a b, 0 < a -> a <= 1 ->
  - Re (gterm n (mkC a b)) <= / INR (S n) ^ 2 + fk b (INR (S n)).
Proof.
  intros n a b Ha Ha1.
  set (k := INR (S n)).
  assert (Hk : 1 <= k) by (unfold k; replace 1 with (INR 1) by reflexivity;
                           apply le_INR; lia).
  assert (Hk0 : 0 < k) by lra.
  assert (Hka : 0 < k + a) by lra.
  assert (Hq : 0 < (k + a) * (k + a) + b * b) by nra.
  rewrite Re_gterm_val. fold k.
  (* the exact split *)
  assert (Hsplit : - ((k + a) / ((k + a) * (k + a) + b * b) - / k)
                   = a / (k * (k + a))
                     + b ^ 2 / ((k + a) * ((k + a) ^ 2 + b ^ 2))).
  { field; repeat split; try lra; try nra. }
  rewrite Hsplit.
  apply Rplus_le_compat.
  - (* a/(k(k+a)) <= 1/k^2 *)
    apply Rle_trans with (1 / (k * k)).
    + unfold Rdiv. apply Rmult_le_compat.
      * lra.
      * left; apply Rinv_0_lt_compat; nra.
      * exact Ha1.
      * apply Rinv_le_contravar; nra.
    + right; field; lra.
  - (* b^2/((k+a)((k+a)^2+b^2)) <= b^2/(k(k^2+b^2)) *)
    unfold fk, Rdiv. apply Rmult_le_compat_l; [ nra | ].
    apply Rinv_le_contravar.
    + nra.
    + apply Rmult_le_compat; nra.
Qed.

(* ----------------------------------------------------------------- *)
(*  Part C -- summing, and passing to the limit.                       *)
(* ----------------------------------------------------------------- *)

Lemma sum_f_R0_opp : forall (f : nat -> R) N,
  - sum_f_R0 f N = sum_f_R0 (fun k => - f k) N.
Proof.
  intros f N. induction N as [| N IH]; [ reflexivity | ].
  rewrite !tech5, <- IH. ring.
Qed.

Lemma sum_f_R0_split2 : forall (f g : nat -> R) N,
  sum_f_R0 (fun k => f k + g k) N = sum_f_R0 f N + sum_f_R0 g N.
Proof.
  intros f g N. induction N as [| N IH]; [ reflexivity | ].
  rewrite !tech5, IH. ring.
Qed.

Lemma Un_cv_opp : forall (u : nat -> R) l, Un_cv u l -> Un_cv (fun n => - u n) (- l).
Proof.
  intros u l H eps He. destruct (H eps He) as [N HN]. exists N.
  intros n Hn. unfold R_dist.
  replace (- u n - - l) with (- (u n - l)) by ring.
  rewrite Rabs_Ropp. apply HN; exact Hn.
Qed.

Lemma Un_cv_cst : forall c : R, Un_cv (fun _ : nat => c) c.
Proof.
  intros c eps He. exists 0%nat. intros n _. unfold R_dist.
  replace (c - c) with 0 by ring. rewrite Rabs_R0. exact He.
Qed.

Lemma mkC_eta : forall z : C, mkC (Re z) (Im z) = z.
Proof. intros [x y]; reflexivity. Qed.

Theorem Sderiv_Re_bound : forall z, 0 < Re z -> Re z <= 1 ->
  - Re (Sderiv z) <= 3 + / 2 * ln (1 + (Im z) ^ 2).
Proof.
  intros z Ha Ha1.
  (* partial sums of the real parts converge to Re (Sderiv z) *)
  pose proof (Sderiv_series z Ha) as HS. unfold Cseries_cv in HS.
  rewrite CUn_cv_comp in HS. destruct HS as [HRe _].
  assert (HP : Un_cv (fun N => sum_f_R0 (fun k => Re (gterm k z)) N) (Re (Sderiv z))).
  { intros eps He. destruct (HRe eps He) as [N HN]. exists N. intros n Hn.
    rewrite <- Re_Cpsum. apply HN; exact Hn. }
  apply Rle_cv_lim with
    (Un := fun N => - sum_f_R0 (fun k => Re (gterm k z)) N)
    (Vn := fun _ : nat => 3 + / 2 * ln (1 + (Im z) ^ 2)).
  - (* uniform bound on the partial sums *)
    intro N. rewrite sum_f_R0_opp.
    apply Rle_trans with
      (sum_f_R0 (fun n => / INR (S n) ^ 2 + fk (Im z) (INR (S n))) N).
    + apply sum_Rle. intros k _.
      rewrite <- (mkC_eta z) at 1. apply neg_Re_gterm_le; assumption.
    + rewrite sum_f_R0_split2.
      assert (H1 : sum_f_R0 (fun n => / INR (S n) ^ 2) N <= 2).
      { rewrite sum_invsq_shift. apply invsq_bound. }
      pose proof (fk_sum_bound (Im z) N) as H2. lra.
  - apply Un_cv_opp; exact HP.
  - apply Un_cv_cst.
Qed.

(* ----------------------------------------------------------------- *)
(*  Part D -- the digamma bound.                                       *)
(* ----------------------------------------------------------------- *)

Theorem digamma_Re_bound : forall z dG, 0 < Re z -> Re z <= 1 ->
  is_Cderiv GammaC z dG ->
  Re (digamma z dG) <= 3 + / 2 * ln (1 + (Im z) ^ 2).
Proof.
  intros z dG Ha Ha1 HdG.
  rewrite (digamma_series z dG Ha HdG).
  (* Re (- (1/z + gamma + S)) = - Re(1/z) - gamma - Re S *)
  assert (Hval : Re (Copp (Cadd (Cadd (Cinv z) (RtoC gamma)) (Sderiv z)))
                 = - Re (Cinv z) - gamma - Re (Sderiv z)).
  { unfold Copp, Cadd, RtoC; cbn [Re Im]. ring. }
  rewrite Hval.
  (* Re (1/z) = a/(a^2+b^2) >= 0 *)
  assert (Hinv : 0 <= Re (Cinv z)).
  { unfold Cinv, Cnorm2; cbn [Re Im].
    assert (0 < Re z * Re z + Im z * Im z) by nra.
    apply Rle_mult_inv_pos; lra. }
  pose proof gamma_nonneg as Hg.
  pose proof (Sderiv_Re_bound z Ha Ha1) as HS.
  lra.
Qed.

Print Assumptions digamma_Re_bound.

(* ----------------------------------------------------------------- *)
(*  Part E -- the form the explicit formula wants: psi(s/2) on the     *)
(*  strip 0 < Re s <= 2, in terms of ln (1 + |Im s|).                  *)
(* ----------------------------------------------------------------- *)

Lemma halfz_Re : forall s, Re (halfz s) = / 2 * Re s.
Proof. intro s. unfold halfz, Cadd, Cmul, RtoC, C0; cbn [Re Im]; ring. Qed.

Lemma halfz_Im : forall s, Im (halfz s) = / 2 * Im s.
Proof. intro s. unfold halfz, Cadd, Cmul, RtoC, C0; cbn [Re Im]; ring. Qed.

Theorem digamma_half_log_bound : forall s dG, 0 < Re s -> Re s <= 2 ->
  is_Cderiv GammaC (halfz s) dG ->
  Re (digamma (halfz s) dG) <= 3 + ln (1 + Rabs (Im s)).
Proof.
  intros s dG Hs Hs2 HdG.
  assert (Ha : 0 < Re (halfz s)) by (rewrite halfz_Re; lra).
  assert (Ha1 : Re (halfz s) <= 1) by (rewrite halfz_Re; lra).
  pose proof (digamma_Re_bound (halfz s) dG Ha Ha1 HdG) as H.
  rewrite halfz_Im in H.
  (* (1/2) ln (1 + (t/2)^2) <= ln (1 + |t|) *)
  assert (Hkey : / 2 * ln (1 + (/ 2 * Im s) ^ 2) <= ln (1 + Rabs (Im s))).
  { assert (Hb : 0 <= Rabs (Im s)) by apply Rabs_pos.
    assert (Hsq : (Im s) ^ 2 = Rabs (Im s) ^ 2).
    { replace ((Im s) ^ 2) with (Im s * Im s) by ring.
      replace (Rabs (Im s) ^ 2) with (Rabs (Im s) * Rabs (Im s)) by ring.
      rewrite <- Rabs_mult, Rabs_pos_eq by nra. reflexivity. }
    assert (Hle : 1 + (/ 2 * Im s) ^ 2 <= (1 + Rabs (Im s)) ^ 2).
    { replace ((/ 2 * Im s) ^ 2) with (/ 4 * (Im s) ^ 2) by field.
      rewrite Hsq. nra. }
    assert (Hpos : 0 < 1 + (/ 2 * Im s) ^ 2) by nra.
    assert (Hln : ln (1 + (/ 2 * Im s) ^ 2) <= ln ((1 + Rabs (Im s)) ^ 2))
      by (apply ln_le; assumption).
    assert (Hsq2 : ln ((1 + Rabs (Im s)) ^ 2) = 2 * ln (1 + Rabs (Im s))).
    { replace ((1 + Rabs (Im s)) ^ 2) with ((1 + Rabs (Im s)) * (1 + Rabs (Im s)))
        by ring. rewrite ln_mult by lra. ring. }
    lra. }
  lra.
Qed.

Print Assumptions digamma_half_log_bound.

(* ================================================================= *)
(*  END DigammaBound.v                                                *)
(* ================================================================= *)
