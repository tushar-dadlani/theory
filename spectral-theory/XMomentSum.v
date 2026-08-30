(* ================================================================= *)
(*  XMomentSum.v  --  the x-space moment sums, and their calculus.     *)
(*                                                                    *)
(*    Sig i x  =  sum_{k>=1} (pi k^2 e^x)^i exp(-pi k^2 e^x)           *)
(*                                                                    *)
(*  and the ONE recursion that generates the whole derivative tower:   *)
(*                                                                    *)
(*    Sig i ' = i . Sig i - Sig (i+1)                                  *)
(*                                                                    *)
(*  WHY MOMENT SUMS RATHER THAN ONE SERIES PER ORDER.  The derivative  *)
(*  polynomials P3 = -w^3 + 3w^2 - w and P4 are SIGN-INDEFINITE (P3    *)
(*  changes sign at w = (3+sqrt 5)/2 = 2.618, and pi e^x drops below   *)
(*  that on the part of the CVU ball with x < 0).  A series with       *)
(*  sign-indefinite terms is not monotone, so growing_cv does not      *)
(*  apply and one would need Cauchy completeness instead.              *)
(*                                                                    *)
(*  Every moment sum, by contrast, has NONNEGATIVE terms, so each is   *)
(*  built by growing_cv and an Rle_dec guard exactly as ThetaDeriv.v   *)
(*  builds DPsi.  The derivatives are then FIXED INTEGER COMBINATIONS  *)
(*  of them --                                                        *)
(*    GPsi = Sig 0,  GPsi' = -Sig 1,  GPsi'' = Sig 2 - Sig 1,          *)
(*    GPsi''' = -Sig 3 + 3 Sig 2 - Sig 1                               *)
(*  -- so identifying them is `ring`, not analysis.  And because the   *)
(*  recursion above is uniform in i, ONE derivable_pt_lim_CVU proof    *)
(*  instantiated three times replaces three separate CVU passes.       *)
(*                                                                    *)
(*  DOMAIN.  derivable_pt_lim_CVU needs a Boule around x, which dips   *)
(*  BELOW x, so the guard must sit strictly under the interval of      *)
(*  interest.  Guard at -1/2, ball radius 1/4; and 1/2 <= exp y for    *)
(*  y >= -1/2 is one line from exp_ineq1_le, which is exactly the      *)
(*  hypothesis exp_half_geo already wants.  No numeric bound on e.     *)
(*  Axiom-clean.                                                       *)
(* ================================================================= *)

From Stdlib Require Import Reals Ranalysis5 PSeries_reg Compare_dec Lra Lia.
From Stdlib Require Import FunctionalExtensionality.
Require Import JacobiTheta RiemannPsi ThetaTailSharp CertifiedPi PsiXDeriv
        ThetaDerivMajorant ThetaDeriv XMomentMajorant.
Open Scope R_scope.

Definition mterm (i : nat) (x : R) (n : nat) : R :=
  (PI * INR (S n) ^ 2 * exp x) ^ i * exp (- (PI * INR (S n) ^ 2 * exp x)).
Definition mpartial (i : nat) (x : R) (N : nat) : R := sum_f_R0 (mterm i x) N.
Definition KMu (i : nat) : R := Cm i / (1 - exp (- (PI / 4))).

(* the guard threshold: exp y >= 1/2 there, which is exp_half_geo's need *)
Lemma exp_ge_half : forall x, - / 2 <= x -> / 2 <= exp x.
Proof.
  intros x Hx. pose proof (exp_ineq1_le x) as H. lra.
Qed.

Lemma mterm_nonneg : forall i x n, 0 <= mterm i x n.
Proof.
  intros i x n. unfold mterm. apply Rmult_le_pos; [ | left; apply exp_pos ].
  apply pow_le. pose proof PI_RGT_0.
  apply Rmult_le_pos; [ | left; apply exp_pos ].
  apply Rmult_le_pos; [ lra | apply pow_le; apply pos_INR ].
Qed.

Lemma mpartial_growing : forall i x, Un_growing (mpartial i x).
Proof.
  intros i x N. unfold mpartial. cbn [sum_f_R0].
  pose proof (mterm_nonneg i x (S N)). lra.
Qed.

Lemma mpartial_bound : forall i x N,
  (i <= 4)%nat -> - / 2 <= x -> mpartial i x N <= KMu i.
Proof.
  intros i x N Hi Hx.
  assert (Hu : / 2 <= exp x) by (apply exp_ge_half; exact Hx).
  pose proof qd_bounds as [Hq0 Hq1].
  unfold mpartial, KMu.
  apply Rle_trans with (sum_f_R0 (fun k => Cm i * exp (- (PI / 4)) ^ k) N).
  - apply sum_f_R0_le. intro k. unfold mterm.
    apply mterm_geo_bound; assumption.
  - assert (E : sum_f_R0 (fun k => Cm i * exp (- (PI / 4)) ^ k) N
              = Cm i * sum_f_R0 (fun k => exp (- (PI / 4)) ^ k) N).
    { rewrite (scal_sum (fun k => exp (- (PI / 4)) ^ k) N (Cm i)).
      apply sum_eq; intros k _; ring. }
    rewrite E. unfold Rdiv.
    apply Rmult_le_compat_l; [ left; apply Cm_pos | ].
    apply geom_partial_bound; unfold qd in *; lra.
Qed.

Lemma msum_converges : forall i x, (i <= 4)%nat -> - / 2 <= x ->
  { L : R | Un_cv (mpartial i x) L }.
Proof.
  intros i x Hi Hx. apply growing_cv; [ apply mpartial_growing | ].
  unfold has_ub, EUn, bound, is_upper_bound.
  exists (KMu i). intros r [n ->]. apply mpartial_bound; assumption.
Qed.

(* TOTAL, by two guards, so it can be fed to RiemannInt downstream *)
Definition Sig (i : nat) (x : R) : R :=
  match le_gt_dec i 4 with
  | left Hi => match Rle_dec (- / 2) x with
               | left Hx => proj1_sig (msum_converges i x Hi Hx)
               | right _ => 0
               end
  | right _ => 0
  end.

Lemma Sig_spec : forall i x, (i <= 4)%nat -> - / 2 <= x ->
  Un_cv (mpartial i x) (Sig i x).
Proof.
  intros i x Hi Hx. unfold Sig.
  destruct (le_gt_dec i 4) as [Hi' | Hi']; [ | exfalso; lia ].
  destruct (Rle_dec (- / 2) x) as [Hx' | Hx']; [ | exfalso; lra ].
  destruct (msum_converges i x Hi' Hx') as [L HL]. simpl. exact HL.
Qed.

Lemma Sig_nonneg : forall i x, (i <= 4)%nat -> - / 2 <= x -> 0 <= Sig i x.
Proof.
  intros i x Hi Hx.
  apply Rle_trans with (mpartial i x 0).
  - unfold mpartial; cbn [sum_f_R0]. apply mterm_nonneg.
  - apply (growing_ineq (mpartial i x));
      [ apply mpartial_growing | apply Sig_spec; assumption ].
Qed.

Lemma Sig_bound : forall i x, (i <= 4)%nat -> - / 2 <= x -> Sig i x <= KMu i.
Proof.
  intros i x Hi Hx.
  eapply Rle_cv_lim.
  2: apply Sig_spec; assumption.
  2: apply Un_cv_const'.
  intro N. apply mpartial_bound; assumption.
Qed.

(* ----------------------------------------------------------------- *)
(*  THE CALCULUS LEMMA.  d/dx (w^i e^{-w}) with w = a e^x:              *)
(*  since dw/dx = w, the product rule gives i w^i e^{-w} - w^{i+1}e^{-w}. *)
(*  Uniform in i -- this single recursion is what replaces a separate   *)
(*  differentiation argument at every order.                           *)
(* ----------------------------------------------------------------- *)
Lemma mterm_deriv : forall i x n,
  derivable_pt_lim (fun s => mterm i s n) x
                   (INR i * mterm i x n - mterm (S i) x n).
Proof.
  intros i x n. unfold mterm.
  set (a := PI * INR (S n) ^ 2).
  (* the inner function w = a e^x, with w' = w *)
  assert (Hw : derivable_pt_lim (fun s => a * exp s) x (a * exp x))
    by (apply derivable_pt_lim_scal; apply derivable_pt_lim_exp).
  (* the power factor *)
  assert (Hp : derivable_pt_lim (fun s => (a * exp s) ^ i) x
                 (INR i * (a * exp x) ^ Init.Nat.pred i * (a * exp x))).
  { apply (derivable_pt_lim_comp (fun s => a * exp s) (fun z => z ^ i) x
             (a * exp x) (INR i * (a * exp x) ^ Init.Nat.pred i)).
    - exact Hw.
    - apply derivable_pt_lim_pow. }
  (* the exponential factor *)
  assert (He : derivable_pt_lim (fun s => exp (- (a * exp s))) x
                 (exp (- (a * exp x)) * - (a * exp x))).
  { apply (derivable_pt_lim_comp (fun s => - (a * exp s)) exp x
             (- (a * exp x)) (exp (- (a * exp x)))).
    - apply derivable_pt_lim_opp; exact Hw.
    - apply derivable_pt_lim_exp. }
  pose proof (derivable_pt_lim_mult (fun s => (a * exp s) ^ i)
                (fun s => exp (- (a * exp s))) x
                (INR i * (a * exp x) ^ Init.Nat.pred i * (a * exp x))
                (exp (- (a * exp x)) * - (a * exp x)) Hp He) as Hm.
  (* reconcile: i w^(i-1) . w = i w^i, and the second term is -w^(i+1). *)
  (* The product rule leaves beta-redexes (f2 x etc.), so reduce first. *)
  cbv beta in Hm.
  replace (INR i * ((a * exp x) ^ i * exp (- (a * exp x)))
           - (a * exp x) ^ S i * exp (- (a * exp x)))
    with (INR i * (a * exp x) ^ Init.Nat.pred i * (a * exp x)
            * exp (- (a * exp x))
          + (a * exp x) ^ i * (exp (- (a * exp x)) * - (a * exp x)))
    by (destruct i as [| i'];
        [ simpl; ring | cbn [Init.Nat.pred pow]; ring ]).
  exact Hm.
Qed.

Lemma mpartial_deriv : forall i N x,
  derivable_pt_lim (fun s => mpartial i s N) x
                   (INR i * mpartial i x N - mpartial (S i) x N).
Proof.
  intros i N x. unfold mpartial.
  induction N as [| N IH]; cbn [sum_f_R0].
  - apply mterm_deriv.
  - assert (E : INR i * (sum_f_R0 (mterm i x) N + mterm i x (S N))
                - (sum_f_R0 (mterm (S i) x) N + mterm (S i) x (S N))
              = (INR i * sum_f_R0 (mterm i x) N - sum_f_R0 (mterm (S i) x) N)
                + (INR i * mterm i x (S N) - mterm (S i) x (S N))) by ring.
    rewrite E.
    apply derivable_pt_lim_plus; [ exact IH | apply mterm_deriv ].
Qed.

(* ----------------------------------------------------------------- *)
(*  UNIFORM CONVERGENCE, once, for every order at once                 *)
(* ----------------------------------------------------------------- *)
Definition mfn (i N : nat) (x : R) : R := mpartial i x N.

Lemma mpartial_tail : forall i x N M, (i <= 4)%nat -> - / 2 <= x ->
  mpartial i x M
  <= mpartial i x N
     + Cm i * exp (- (PI / 4)) ^ (S N) / (1 - exp (- (PI / 4))).
Proof.
  intros i x N M Hi Hx. pose proof qd_bounds as [Hq0 Hq1].
  assert (Hu : / 2 <= exp x) by (apply exp_ge_half; exact Hx).
  set (q := exp (- (PI / 4))) in *.
  assert (HqN : 0 < q ^ (S N)) by (apply pow_lt; unfold q, qd in *; lra).
  assert (Htail : 0 <= Cm i * q ^ (S N) / (1 - q)).
  { unfold Rdiv. apply Rmult_le_pos.
    - pose proof (Cm_pos i). nra.
    - left; apply Rinv_0_lt_compat. unfold q, qd in *; lra. }
  destruct (Nat.le_gt_cases M N) as [Hle | Hgt].
  - assert (mpartial i x M <= mpartial i x N)
      by (apply tech9; [ apply mpartial_growing | exact Hle ]).
    lra.
  - unfold mpartial. rewrite (tech2 (mterm i x) N M Hgt).
    apply Rplus_le_compat_l.
    apply Rle_trans with
      (sum_f_R0 (fun k => Cm i * q ^ (S N) * q ^ k) (M - S N)).
    + apply sum_f_R0_le. intro k. unfold mterm.
      eapply Rle_trans; [ apply (mterm_geo_bound i (exp x) (S N + k) Hi Hu) | ].
      unfold q. rewrite pow_add. right; ring.
    + assert (E : sum_f_R0 (fun k => Cm i * q ^ (S N) * q ^ k) (M - S N)
                = Cm i * q ^ (S N) * sum_f_R0 (fun k => q ^ k) (M - S N)).
      { rewrite (scal_sum (fun k => q ^ k) (M - S N) (Cm i * q ^ (S N))).
        apply sum_eq; intros k _; ring. }
      rewrite E.
      assert (Hgp : sum_f_R0 (fun k => q ^ k) (M - S N) <= / (1 - q))
        by (apply geom_partial_bound; unfold q, qd in *; lra).
      unfold Rdiv. apply Rmult_le_compat_l; [ pose proof (Cm_pos i); nra | ].
      exact Hgp.
Qed.

Lemma Sig_tail : forall i x N, (i <= 4)%nat -> - / 2 <= x ->
  Sig i x <= mpartial i x N
             + Cm i * exp (- (PI / 4)) ^ (S N) / (1 - exp (- (PI / 4))).
Proof.
  intros i x N Hi Hx. eapply Rle_cv_lim.
  2: apply Sig_spec; assumption.
  2: apply Un_cv_const'.
  intro M. apply mpartial_tail; assumption.
Qed.

Theorem mpartial_CVU : forall i c (r : posreal), (i <= 4)%nat ->
  (forall y : R, Boule c r y -> - / 2 <= y) -> CVU (mfn i) (Sig i) c r.
Proof.
  intros i c r Hi Hdom eps Heps. pose proof qd_bounds as [Hq0 Hq1].
  set (q := exp (- (PI / 4))) in *.
  assert (Habs : Rabs q < 1) by (rewrite Rabs_pos_eq; unfold q, qd in *; lra).
  assert (HC : 0 < Cm i) by apply Cm_pos.
  assert (Hy : 0 < eps * (1 - q) / Cm i)
    by (unfold Rdiv; unfold q, qd in *;
        repeat apply Rmult_lt_0_compat; try lra;
        apply Rinv_0_lt_compat; lra).
  destruct (pow_lt_1_zero q Habs _ Hy) as [N HN].
  exists N. intros n y Hn Hby.
  assert (Hx : - / 2 <= y) by (apply Hdom; exact Hby).
  pose proof (Sig_tail i y n Hi Hx) as Hup. fold q in Hup.
  pose proof (growing_ineq (mpartial i y) (Sig i y)
                (mpartial_growing i y) (Sig_spec i y Hi Hx) n) as Hlo.
  assert (Hsm : Rabs (q ^ (S n)) < eps * (1 - q) / Cm i) by (apply HN; lia).
  rewrite Rabs_pos_eq in Hsm by (apply pow_le; unfold q, qd in *; lra).
  unfold mfn.
  replace (Sig i y - mpartial i y n) with (- (mpartial i y n - Sig i y)) by ring.
  rewrite Rabs_Ropp, Rabs_left1 by lra.
  assert (Hfin : Cm i * q ^ (S n) / (1 - q) < eps).
  { apply (Rmult_lt_reg_r ((1 - q) / Cm i)).
    - unfold Rdiv; unfold q, qd in *. apply Rmult_lt_0_compat;
        [ lra | apply Rinv_0_lt_compat; lra ].
    - assert (E2 : Cm i * q ^ (S n) / (1 - q) * ((1 - q) / Cm i) = q ^ (S n))
        by (field; unfold q, qd in *; lra).
      rewrite E2.
      assert (Eassoc : eps * ((1 - q) / Cm i) = eps * (1 - q) / Cm i)
        by (field; lra).
      rewrite Eassoc. exact Hsm. }
  lra.
Qed.

Lemma cont_mfn : forall i N y, continuity_pt (mfn i N) y.
Proof.
  intros i N y. apply derivable_continuous_pt.
  exists (INR i * mpartial i y N - mpartial (S i) y N).
  unfold mfn. apply mpartial_deriv.
Qed.

(* ----------------------------------------------------------------- *)
(*  THE DERIVATIVE, uniformly in i                                     *)
(*                                                                    *)
(*  Ball radius 1/4 around x >= -1/4 keeps the whole Boule above -1/2, *)
(*  which is the guard threshold; the CVU limit function must be       *)
(*  continuous there, and it is, by CVU_continuity on the SAME         *)
(*  uniform convergence.  The derivative of the partials is a LINEAR   *)
(*  COMBINATION of two moment partials, so its uniform convergence     *)
(*  follows from mpartial_CVU at i and at S i.                        *)
(* ----------------------------------------------------------------- *)
Lemma Hr4' : 0 < / 4. Proof. lra. Qed.
Definition rq : posreal := mkposreal (/ 4) Hr4'.

(* Stdlib has no CVU_minus; this is the combination actually needed *)
Lemma CVU_lin : forall (f g : nat -> R -> R) (F G : R -> R) c r a b,
  CVU f F c r -> CVU g G c r ->
  CVU (fun N y => a * f N y + b * g N y) (fun y => a * F y + b * G y) c r.
Proof.
  intros f g F G c r a b Hf Hg eps Heps.
  set (m := Rmax (Rabs a) (Rabs b) + 1).
  assert (Hm : 0 < m).
  { unfold m. pose proof (Rabs_pos a).
    pose proof (Rmax_l (Rabs a) (Rabs b)). lra. }
  (* 4m, not 2m: the two halves must sum STRICTLY below eps *)
  assert (He2 : 0 < eps / (4 * m))
    by (apply Rdiv_lt_0_compat; lra).
  destruct (Hf _ He2) as [N1 H1]. destruct (Hg _ He2) as [N2 H2].
  exists (Nat.max N1 N2). intros n y Hn Hby.
  assert (Hn1 : (N1 <= n)%nat) by lia.
  assert (Hn2 : (N2 <= n)%nat) by lia.
  pose proof (H1 n y Hn1 Hby) as G1. pose proof (H2 n y Hn2 Hby) as G2.
  replace (a * F y + b * G y - (a * f n y + b * g n y))
    with (a * (F y - f n y) + b * (G y - g n y)) by ring.
  eapply Rle_lt_trans; [ apply Rabs_triang | ].
  rewrite !Rabs_mult.
  assert (Ha : Rabs a <= m)
    by (unfold m; pose proof (Rmax_l (Rabs a) (Rabs b)); lra).
  assert (Hb : Rabs b <= m)
    by (unfold m; pose proof (Rmax_r (Rabs a) (Rabs b)); lra).
  assert (P1 : Rabs a * Rabs (F y - f n y) <= m * (eps / (4 * m))).
  { apply Rmult_le_compat; try apply Rabs_pos; [ exact Ha | lra ]. }
  assert (P2 : Rabs b * Rabs (G y - g n y) <= m * (eps / (4 * m))).
  { apply Rmult_le_compat; try apply Rabs_pos; [ exact Hb | lra ]. }
  assert (E : m * (eps / (4 * m)) = eps / 4) by (field; lra).
  lra.
Qed.

Theorem Sig_deriv : forall i x, (S i <= 4)%nat -> - / 4 <= x ->
  derivable_pt_lim (Sig i) x (INR i * Sig i x - Sig (S i) x).
Proof.
  intros i x HSi Hx.
  assert (Hi : (i <= 4)%nat) by lia.
  assert (Hdom : forall y : R, Boule x rq y -> - / 2 <= y).
  { intros y Hy. unfold Boule, rq in Hy; simpl in Hy.
    destruct (Rabs_def2 _ _ Hy) as [H1 H2]. lra. }
  assert (Hc1 : CVU (mfn i) (Sig i) x rq)
    by (apply mpartial_CVU; assumption).
  assert (Hc2 : CVU (mfn (S i)) (Sig (S i)) x rq)
    by (apply mpartial_CVU; assumption).
  assert (Hcomb : CVU (fun N y => INR i * mfn i N y + (-1) * mfn (S i) N y)
                    (fun y => INR i * Sig i y + (-1) * Sig (S i) y) x rq)
    by (apply CVU_lin; assumption).
  replace (INR i * Sig i x - Sig (S i) x)
    with (INR i * Sig i x + (-1) * Sig (S i) x) by ring.
  apply (derivable_pt_lim_CVU (mfn i)
           (fun N y => INR i * mfn i N y + (-1) * mfn (S i) N y)
           (Sig i) (fun y => INR i * Sig i y + (-1) * Sig (S i) y) x x rq).
  - unfold Boule, rq; simpl.
    replace (x - x) with 0 by ring; rewrite Rabs_R0; lra.
  - intros y n Hy. unfold mfn.
    replace (INR i * mpartial i y n + (-1) * mpartial (S i) y n)
      with (INR i * mpartial i y n - mpartial (S i) y n) by ring.
    apply mpartial_deriv.
  - intros y Hy. apply Sig_spec; [ exact Hi | apply Hdom; exact Hy ].
  - exact Hcomb.
  - apply (CVU_continuity
             (fun N y => INR i * mfn i N y + (-1) * mfn (S i) N y)
             (fun y => INR i * Sig i y + (-1) * Sig (S i) y) x rq Hcomb).
    intros n y _.
    apply continuity_pt_plus.
    + apply (continuity_pt_scal (mfn i n) (INR i) y). apply cont_mfn.
    + apply (continuity_pt_scal (mfn (S i) n) (-1) y). apply cont_mfn.
Qed.

(* ----------------------------------------------------------------- *)
(*  BRIDGES to the existing tree.  These are regression tests: if the  *)
(*  new construction disagreed with the already-verified GPsi and DG,  *)
(*  one of the two would be wrong.                                     *)
(* ----------------------------------------------------------------- *)
Lemma mterm0_eq : forall x n, mterm 0 x n = theta_term (exp x) n.
Proof.
  intros x n. unfold mterm, theta_term. simpl. ring.
Qed.

Lemma Sig0_eq_GPsi : forall x, - / 2 <= x -> Sig 0 x = GPsi x.
Proof.
  intros x Hx.
  assert (Hu : 0 < exp x) by apply exp_pos.
  assert (Hcv1 : Un_cv (mpartial 0 x) (Sig 0 x))
    by (apply Sig_spec; [ lia | exact Hx ]).
  assert (Hcv2 : Un_cv (mpartial 0 x) (GPsi x)).
  { unfold GPsi.
    assert (E : mpartial 0 x = theta_partial (exp x)).
    { apply functional_extensionality. intro N.
      unfold mpartial, theta_partial. apply sum_eq. intros k Hk.
      apply mterm0_eq. }
    rewrite E. apply (Psi_is_limit (exp x) Hu). }
  apply (UL_sequence (mpartial 0 x)); assumption.
Qed.

Lemma mterm1_eq : forall x n, mterm 1 x n = gterm x n.
Proof.
  intros x n. unfold mterm, gterm. simpl. ring.
Qed.

Lemma Sig1_eq_DG : forall x, 0 <= x -> Sig 1 x = - DG x.
Proof.
  intros x Hx.
  assert (Hx2 : - / 2 <= x) by lra.
  assert (Hcv1 : Un_cv (mpartial 1 x) (Sig 1 x))
    by (apply Sig_spec; [ lia | exact Hx2 ]).
  assert (Hcv2 : Un_cv (mpartial 1 x) (- DG x)).
  { assert (E : mpartial 1 x = gpartial x).
    { apply functional_extensionality. intro N.
      unfold mpartial, gpartial. apply sum_eq. intros k Hk.
      apply mterm1_eq. }
    rewrite E. apply gpartial_cv; exact Hx. }
  apply (UL_sequence (mpartial 1 x)); assumption.
Qed.

Print Assumptions Sig_spec.
Print Assumptions mterm_deriv.
Print Assumptions mpartial_CVU.
Print Assumptions Sig_deriv.
Print Assumptions Sig0_eq_GPsi.
Print Assumptions Sig1_eq_DG.
