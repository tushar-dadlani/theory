(* ================================================================= *)
(*  CLDeriv.v  --  -L'(s,chi) = sum chi(n) ln n n^{-s} on Re s > 1.   *)
(*                                                                    *)
(*  CZetaDerivDirichlet gets the same statement for zeta by            *)
(*  differentiating the Euler-Maclaurin telescoping, which is what     *)
(*  gives zeta its continuation.  L has no such decomposition in this  *)
(*  repo, so that route does not transfer.  Instead this is proved     *)
(*  DIRECTLY from the definition of is_Cderiv, by a second-order       *)
(*  estimate on each term:                                            *)
(*                                                                    *)
(*    n^{-(s+h)} - n^{-s} + h ln n  n^{-s} = n^{-s} (e^w - 1 - w)      *)
(*                                          with w = -h ln n          *)
(*                                                                    *)
(*  and CexpRemainder.Cexpf_remainder_w bounds |e^w - 1 - w| by        *)
(*  3|w|^2 e^{|w|}.  Summing gives an error <= 3|h|^2 sum (ln n)^2     *)
(*  n^{-(Re s - |h|)}, quadratic in h with a constant that is UNIFORM  *)
(*  once |h| <= (Re s - 1)/2 -- which is exactly is_Cderiv.            *)
(*                                                                    *)
(*  Part A is the (ln n)^2 majorant, the analogue of                   *)
(*  CVonMangoldtSeries.blam_sum_cv with ln x <= (1/c) x^c squared.     *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia ZArith Znumtheory FunctionalExtensionality.
Require Import ComplexField Cmodulus Holomorphic CDeriv CexpFull CexpRemainder
        CSeries CZetaTerm CZetaTerm2 CDirichlet CVonMangoldtSeries CharModulus
        RootsOfUnity ZmodOrder DirichletModP CTwistedCoeff CLSeries CLHolo1
        CTwist341 CZetaDerivDirichlet CEulerProductZeta.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  Part A -- the (ln n)^2 majorant.                                   *)
(* ----------------------------------------------------------------- *)

Definition bl2 (a : R) (n : nat) : R :=
  (ln (INR (S n)))^2 * Rpower (INR (S n)) (- a).

Lemma lnS_nonneg : forall n, 0 <= ln (INR (S n)).
Proof.
  intro n. rewrite <- ln_1. apply ln_le'; [ lra | ].
  rewrite <- INR_1. apply le_INR. lia.
Qed.

Lemma bl2_nonneg : forall a n, 0 <= bl2 a n.
Proof.
  intros a n. unfold bl2. apply Rmult_le_pos.
  - apply pow2_ge_0.
  - apply Rlt_le. unfold Rpower. apply exp_pos.
Qed.

Lemma bl2_sum_cv : forall a, 1 < a -> { T | Un_cv (sum_f_R0 (bl2 a)) T }.
Proof.
  intros a Ha. set (c := (a - 1) / 4). assert (Hc : 0 < c) by (unfold c; lra).
  assert (Hci : 0 <= (/ c)^2) by apply pow2_ge_0.
  destruct (pseries_cv (a - 2 * c) ltac:(unfold c; lra)) as [T' HT'].
  set (term := fun n => Rpower (INR (S n)) (- (a - 2 * c))).
  assert (Ht0 : forall n, 0 <= term n)
    by (intro n; unfold term; apply Rlt_le; unfold Rpower; apply exp_pos).
  assert (Hbound : forall n, bl2 a n <= (/ c)^2 * term n).
  { intro n. unfold bl2, term.
    assert (Hb1 : 1 <= INR (S n)) by (rewrite <- INR_1; apply le_INR; lia).
    assert (Hln : ln (INR (S n)) <= / c * Rpower (INR (S n)) c)
      by (apply ln_le_rpow; [ exact Hc | exact Hb1 ]).
    assert (Hsq : (ln (INR (S n)))^2 <= (/ c)^2 * Rpower (INR (S n)) (2 * c)).
    { replace ((/ c)^2 * Rpower (INR (S n)) (2 * c))
        with ((/ c * Rpower (INR (S n)) c)^2).
      2:{ replace (2 * c) with (c + c) by ring. rewrite Rpower_plus. ring. }
      apply pow_incr. split; [ apply lnS_nonneg | exact Hln ]. }
    apply Rle_trans
      with ((/ c)^2 * Rpower (INR (S n)) (2 * c) * Rpower (INR (S n)) (- a)).
    - apply Rmult_le_compat_r;
        [ apply Rlt_le; unfold Rpower; apply exp_pos | exact Hsq ].
    - rewrite Rmult_assoc, <- Rpower_plus.
      replace (2 * c + - a) with (- (a - 2 * c)) by ring. apply Req_le; reflexivity. }
  apply growing_cv.
  - intro N; rewrite tech5; pose proof (bl2_nonneg a (S N)); lra.
  - unfold has_ub, bound, is_upper_bound, EUn.
    exists ((/ c)^2 * T'); intros y [N Hy]; rewrite Hy; clear Hy y.
    apply Rle_trans with (sum_f_R0 (fun m => (/ c)^2 * term m) N).
    + apply sum_Rle; intros i _; apply Hbound.
    + replace (fun m => (/ c)^2 * term m) with (fun m => term m * (/ c)^2)
        by (apply functional_extensionality; intro m; ring).
      rewrite <- scal_sum; apply Rmult_le_compat_l; [ exact Hci | ].
      apply (growing_ineq (sum_f_R0 term) T'); [ | exact HT' ].
      intro M; rewrite tech5; pose proof (Ht0 (S M)); lra.
Qed.

(* ----------------------------------------------------------------- *)
(*  Part B -- the per-term second-order estimate.                      *)
(* ----------------------------------------------------------------- *)

Lemma Lterm_second_order : forall p g A,
  (1 <= g <= p - 1)%nat -> ord p g = (p - 1)%nat ->
  forall s h k,
  Cmod (Cminus (Cminus (Lterm p g A (Cadd s h) k) (Lterm p g A s k))
               (Cmul (Ldterm p g A s k) h))
  <= 3 * (Cmod h)^2 * bl2 (Re s - Cmod h) k.
Proof.
  intros p g A Hg Hord s h k.
  set (x := INR (S k)).
  assert (Hx1 : 1 <= x) by (unfold x; rewrite <- INR_1; apply le_INR; lia).
  assert (Hx0 : 0 < x) by lra.
  assert (HLx0 : 0 <= ln x) by (unfold x; apply lnS_nonneg).
  set (w := Cmul (Copp h) (RtoC (ln x))).
  assert (Hmw : Cmod w = Cmod h * ln x).
  { unfold w. rewrite Cmod_mul, Cmod_opp, Cmod_RtoC, (Rabs_pos_eq _ HLx0).
    reflexivity. }
  assert (Hpw : Cpw x (Copp h) = Cexpf w) by (unfold Cpw, w; reflexivity).
  assert (Hkey : Cminus (Cminus (Lterm p g A (Cadd s h) k) (Lterm p g A s k))
                        (Cmul (Ldterm p g A s k) h)
                 = Cmul (dchar p g A (S k))
                        (Cmul (Cpw x (Copp s))
                              (Cminus (Cminus (Cexpf w) C1) w))).
  { unfold Lterm, Gchi, Ldterm. fold x.
    replace (Copp (Cadd s h)) with (Cadd (Copp s) (Copp h)) by ring.
    rewrite Cpw_split, Hpw. unfold w.
    apply Ceq; unfold Cmul, Cminus, Cadd, Copp, C1, RtoC; cbn [Re Im]; ring. }
  rewrite Hkey, !Cmod_mul.
  assert (Hc1 : Cmod (dchar p g A (S k)) <= 1) by (apply Cmod_dchar_le; assumption).
  assert (Hc0 : 0 <= Cmod (dchar p g A (S k))) by apply Cmod_nonneg.
  assert (HP : Cmod (Cpw x (Copp s)) = Rpower x (- Re s))
    by (rewrite Cpw_mod; f_equal; unfold Copp; cbn [Re]; ring).
  assert (HP0 : 0 <= Rpower x (- Re s)) by (apply Rlt_le; unfold Rpower; apply exp_pos).
  assert (HR : Cmod (Cminus (Cminus (Cexpf w) C1) w) <= 3 * (Cmod w)^2 * exp (Cmod w))
    by apply Cexpf_remainder_w.
  assert (HR0 : 0 <= Cmod (Cminus (Cminus (Cexpf w) C1) w)) by apply Cmod_nonneg.
  assert (Hexp : exp (Cmod w) = Rpower x (Cmod h)).
  { rewrite Hmw. unfold Rpower. reflexivity. }
  assert (Hfin : 3 * (Cmod w)^2 * exp (Cmod w)
                 = 3 * (Cmod h)^2 * ((ln x)^2 * Rpower x (Cmod h))).
  { rewrite Hexp, Hmw. ring. }
  rewrite HP.
  assert (Hstep : Cmod (dchar p g A (S k))
                  * (Rpower x (- Re s) * Cmod (Cminus (Cminus (Cexpf w) C1) w))
                  <= 1 * (Rpower x (- Re s) * (3 * (Cmod w)^2 * exp (Cmod w)))).
  { apply Rmult_le_compat; [ exact Hc0 | | exact Hc1 | ].
    - apply Rmult_le_pos; [ exact HP0 | exact HR0 ].
    - apply Rmult_le_compat_l; [ exact HP0 | exact HR ]. }
  eapply Rle_trans; [ exact Hstep | ].
  rewrite Hfin. unfold bl2. fold x.
  replace (- (Re s - Cmod h)) with (- Re s + Cmod h) by ring.
  rewrite Rpower_plus. apply Req_le. ring.
Qed.

(* ----------------------------------------------------------------- *)
(*  Part C -- assembly: LFun' = sum of the termwise derivatives.        *)
(* ----------------------------------------------------------------- *)

Lemma Cpsum_minus : forall F G N,
  Cpsum (fun k => Cminus (F k) (G k)) N = Cminus (Cpsum F N) (Cpsum G N).
Proof.
  intros F G N. induction N as [| N IH]; [ reflexivity | ].
  replace (Cpsum (fun k => Cminus (F k) (G k)) (S N))
    with (Cadd (Cpsum (fun k => Cminus (F k) (G k)) N) (Cminus (F (S N)) (G (S N))))
    by reflexivity.
  replace (Cpsum F (S N)) with (Cadd (Cpsum F N) (F (S N))) by reflexivity.
  replace (Cpsum G (S N)) with (Cadd (Cpsum G N) (G (S N))) by reflexivity.
  rewrite IH. apply Ceq; unfold Cadd, Cminus, Copp; cbn [Re Im]; ring.
Qed.

Lemma Cpsum_scal_r : forall F c N,
  Cpsum (fun k => Cmul (F k) c) N = Cmul (Cpsum F N) c.
Proof.
  intros F c N. induction N as [| N IH].
  - reflexivity.
  - replace (Cpsum (fun k => Cmul (F k) c) (S N))
      with (Cadd (Cpsum (fun k => Cmul (F k) c) N) (Cmul (F (S N)) c)) by reflexivity.
    replace (Cpsum F (S N)) with (Cadd (Cpsum F N) (F (S N))) by reflexivity.
    rewrite IH. apply Ceq; unfold Cadd, Cmul; cbn [Re Im]; ring.
Qed.

Lemma CUn_cv_scal_r : forall u l c, CUn_cv u l -> CUn_cv (fun n => Cmul (u n) c) (Cmul l c).
Proof.
  intros u l c H eps He.
  destruct (Rle_lt_dec (Cmod c) 0) as [Hc | Hc].
  - assert (Hc0 : c = C0).
    { apply (proj1 (Cmod0 c)). pose proof (Cmod_nonneg c). lra. }
    exists 0%nat. intros n _. rewrite Hc0.
    replace (Cminus (Cmul (u n) C0) (Cmul l C0)) with C0
      by (apply Ceq; unfold Cmul, Cminus, Cadd, Copp, C0; cbn [Re Im]; ring).
    rewrite (proj2 (Cmod0 C0) eq_refl). exact He.
  - destruct (H (eps / Cmod c) ltac:(apply Rdiv_lt_0_compat; lra)) as [N HN].
    exists N. intros n Hn.
    replace (Cminus (Cmul (u n) c) (Cmul l c)) with (Cmul (Cminus (u n) l) c)
      by (apply Ceq; unfold Cmul, Cminus, Cadd, Copp; cbn [Re Im]; ring).
    rewrite Cmod_mul.
    apply Rlt_le_trans with (eps / Cmod c * Cmod c).
    + apply Rmult_lt_compat_r; [ lra | apply HN; exact Hn ].
    + apply Req_le. field. lra.
Qed.

Lemma Rpower_exp_mono : forall x a b, 1 <= x -> a <= b -> Rpower x a <= Rpower x b.
Proof.
  intros x a b Hx Hab. unfold Rpower. apply exp_le.
  assert (Hl : 0 <= ln x) by (rewrite <- ln_1; apply ln_le'; lra).
  nra.
Qed.

Theorem LFun_deriv : forall p g A
  (Hp : prime (Z.of_nat p)) (Hg : (1 <= g <= p - 1)%nat)
  (Hord : ord p g = (p - 1)%nat) (HA : (0 < A < p - 1)%nat)
  s (Hs : 1 < Re s) D,
  Cseries_cv (Ldterm p g A s) D ->
  is_Cderiv (LFun p g A Hp Hg Hord HA) s D.
Proof.
  intros p g A Hp Hg Hord HA s Hs D HD.
  set (a0 := (Re s + 1) / 2). assert (Ha0 : 1 < a0) by (unfold a0; lra).
  destruct (bl2_sum_cv a0 Ha0) as [K HK].
  assert (HKub : forall N, sum_f_R0 (bl2 a0) N <= K).
  { intro N. apply (growing_ineq (sum_f_R0 (bl2 a0)) K); [ | exact HK ].
    intro M; rewrite tech5; pose proof (bl2_nonneg a0 (S M)); lra. }
  assert (HK0 : 0 <= K)
    by (eapply Rle_trans; [ apply (bl2_nonneg a0 0%nat) | apply (HKub 0%nat) ]).
  intros eps Heps.
  exists (Rmin ((Re s - 1) / 2) (eps / (3 * K + 1))). split.
  { apply Rmin_pos; [ lra | apply Rdiv_lt_0_compat; lra ]. }
  intros h Hh.
  assert (Hh1 : Cmod h < (Re s - 1) / 2)
    by (eapply Rlt_le_trans; [ exact Hh | apply Rmin_l ]).
  assert (Hh2 : Cmod h < eps / (3 * K + 1))
    by (eapply Rlt_le_trans; [ exact Hh | apply Rmin_r ]).
  assert (Hh0 : 0 <= Cmod h) by apply Cmod_nonneg.
  assert (Ha : a0 <= Re s - Cmod h) by (unfold a0; lra).
  (* the shifted point is still in the half-plane *)
  assert (HRe : 0 < Re (Cadd s h)).
  { pose proof (Re_le_Cmod h) as Hre.
    pose proof (Cmod_nonneg h) as Hcn.
    assert (Hl : - Cmod h <= Re h).
    { destruct (Rle_lt_dec 0 (Re h)) as [Hn | Hn]; [ lra | ].
      rewrite Rabs_left in Hre by exact Hn. lra. }
    unfold Cadd; cbn [Re]; lra. }
  assert (HRe0 : 0 < Re s) by lra.
  (* the three series *)
  pose proof (LFun_series p g A Hp Hg Hord HA (Cadd s h) HRe) as Hsh.
  pose proof (LFun_series p g A Hp Hg Hord HA s HRe0) as Hss.
  (* the error sequence *)
  set (E := fun N => Cpsum (fun k => Cminus (Cminus (Lterm p g A (Cadd s h) k)
                                                    (Lterm p g A s k))
                                            (Cmul (Ldterm p g A s k) h)) N).
  assert (HEeq : forall N, E N = Cminus (Cminus (Cpsum (Lterm p g A (Cadd s h)) N)
                                                (Cpsum (Lterm p g A s) N))
                                        (Cmul (Cpsum (Ldterm p g A s) N) h)).
  { intro N. unfold E. rewrite Cpsum_minus, Cpsum_minus, Cpsum_scal_r. reflexivity. }
  assert (HEcv : CUn_cv E (Cminus (Cminus (LFun p g A Hp Hg Hord HA (Cadd s h))
                                          (LFun p g A Hp Hg Hord HA s))
                                  (Cmul D h))).
  { apply (CUn_cv_ext (fun N => Cminus (Cminus (Cpsum (Lterm p g A (Cadd s h)) N)
                                               (Cpsum (Lterm p g A s) N))
                                       (Cmul (Cpsum (Ldterm p g A s) N) h)));
      [ intro N; symmetry; apply HEeq | ].
    apply CUn_cv_minus; [ apply CUn_cv_minus; [ exact Hsh | exact Hss ] | ].
    apply CUn_cv_scal_r. exact HD. }
  (* uniform bound on the error sequence *)
  assert (HEb : forall N, Cmod (E N) <= 3 * (Cmod h)^2 * K).
  { intro N. eapply Rle_trans; [ apply Cmod_Cpsum_le | ].
    eapply Rle_trans with (sum_f_R0 (fun k => 3 * (Cmod h)^2 * bl2 a0 k) N).
    - apply sum_Rle. intros k _.
      eapply Rle_trans; [ apply (Lterm_second_order p g A Hg Hord s h k) | ].
      apply Rmult_le_compat_l; [ nra | ].
      unfold bl2. apply Rmult_le_compat_l; [ apply pow2_ge_0 | ].
      apply Rpower_exp_mono; [ rewrite <- INR_1; apply le_INR; lia | lra ].
    - replace (fun k => 3 * (Cmod h)^2 * bl2 a0 k)
        with (fun k => bl2 a0 k * (3 * (Cmod h)^2))
        by (apply functional_extensionality; intro k; ring).
      rewrite <- scal_sum.
      replace (3 * (Cmod h)^2 * K) with (3 * (Cmod h)^2 * K) by ring.
      apply Rmult_le_compat_l; [ nra | apply HKub ]. }
  (* pass to the limit *)
  assert (Hlim : Cmod (Cminus (Cminus (LFun p g A Hp Hg Hord HA (Cadd s h))
                                      (LFun p g A Hp Hg Hord HA s))
                              (Cmul D h))
                 <= 3 * (Cmod h)^2 * K).
  { apply Rle_cv_lim with (Un := fun N => Cmod (E N))
                          (Vn := fun _ : nat => 3 * (Cmod h)^2 * K).
    - exact HEb.
    - apply CUn_cv_Cmod. exact HEcv.
    - intros e He. exists 0%nat. intros n _. unfold R_dist.
      replace (3 * (Cmod h)^2 * K - 3 * (Cmod h)^2 * K) with 0 by ring.
      rewrite Rabs_R0. exact He. }
  eapply Rle_trans; [ exact Hlim | ].
  assert (Hfin : 3 * K * Cmod h <= eps).
  { apply Rle_trans with (3 * K * (eps / (3 * K + 1))).
    - apply Rmult_le_compat_l; [ nra | lra ].
    - apply (Rmult_le_reg_r (3 * K + 1)); [ lra | ].
      replace (3 * K * (eps / (3 * K + 1)) * (3 * K + 1))
        with (3 * K * eps * (/ (3 * K + 1) * (3 * K + 1))) by (unfold Rdiv; ring).
      rewrite Rinv_l by lra. nra. }
  nra.
Qed.

Print Assumptions bl2_sum_cv.
Print Assumptions Lterm_second_order.
Print Assumptions LFun_deriv.

(* ================================================================= *)
(*  END CLDeriv.v                                                     *)
(* ================================================================= *)
