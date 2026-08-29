(* ================================================================= *)
(*  PsiXDeriv.v  --  the x-space derivative of Psi(e^x).               *)
(*                                                                    *)
(*    GPsi x := Psi (exp x)      DG x := DPsi (exp x) * exp x          *)
(*                                                                    *)
(*    GPsi_deriv     : 0 <= x -> derivable_pt_lim GPsi x (DG x)        *)
(*    DG_bound       : 0 <= x -> |DG x| <= 2/(1-q)                     *)
(*    DG_lipschitz   : 0 <= x -> 0 <= y ->                             *)
(*                       |DG x - DG y| <= 18/(1-q) * |x - y|           *)
(*                                                                    *)
(*  Why not just compose DPsi_bound / DPsi_lipschitz with the chain    *)
(*  rule?  Because the composition is where all the sharpness dies.    *)
(*  |DG| <= |DPsi(u)| . u would use sup|DPsi| (attained near u = 1/2)  *)
(*  times sup u = e^L = 5, and the Lipschitz constant would pick up    *)
(*  e^{2L} = 25 -- multiplying the worst case of Psi'' by the largest  *)
(*  u, when in fact Psi'' is ~10^{-6} there.  For the t = 16 sign      *)
(*  change that route inflates the midpoint constant by 2200x: 44000   *)
(*  quadrature nodes instead of 940.                                   *)
(*                                                                    *)
(*  Bounding a u e^{-a u} and (a u)^2 e^{-a u} DIRECTLY (majorants     *)
(*  xterm_bound / xterm2_bound) keeps u inside the exponent where it   *)
(*  belongs and costs nothing: the same half-split works, with u       *)
(*  simply riding along inside v = a u.                                *)
(*                                                                    *)
(*  As in ThetaDeriv2, the Lipschitz bound needs no third CVU pass:    *)
(*  the finite partials are Lipschitz with an N-free constant by       *)
(*  MVT_cor2, and the constant survives the limit.  Axiom-clean.       *)
(* ================================================================= *)

From Stdlib Require Import Reals Ranalysis5 Lra Lia.
Require Import JacobiTheta RiemannPsi ThetaTailSharp CertifiedPi ThetaDerivMajorant ThetaDeriv ThetaDeriv2.
Open Scope R_scope.

Definition GPsi (x : R) : R := Psi (exp x).
Definition DG (x : R) : R := DPsi (exp x) * exp x.

Definition gterm (x : R) (n : nat) : R :=
  PI * INR (S n) ^ 2 * exp x * exp (- (PI * INR (S n) ^ 2 * exp x)).
Definition gpartial (x : R) (N : nat) : R := sum_f_R0 (gterm x) N.

Definition gterm' (x : R) (n : nat) : R :=
  (PI * INR (S n) ^ 2 * exp x - (PI * INR (S n) ^ 2 * exp x) ^ 2)
    * exp (- (PI * INR (S n) ^ 2 * exp x)).
Definition g2partial (x : R) (N : nat) : R := sum_f_R0 (gterm' x) N.

(* --- the SHARP constants: k = 1, 2 exact, k >= 3 geometric --- *)
(* The uniform majorant gives 2/(1-q) = 3.68 and 18/(1-q) = 33.1,     *)
(* against true values 0.1358 and 0.5623 -- factors of 27 and 59, all *)
(* of it slack in the FIRST term (2 q^0 = 2 vs pi e^{-pi} = 0.136).   *)
(* Evaluating k = 1, 2 exactly removes essentially all of it: the     *)
(* residual tail below is 1.5e-6 and 1.4e-5 respectively.  Since the  *)
(* quadrature node count scales as sqrt(Mfin), this is what takes the *)
(* t = 16 run from 8192 panels to 2048.                                *)
Definition qt : R := exp (- PI).
Definition Ktail : R := exp (- (9 * PI / 2)) / (1 - qt).

Definition Kg1 : R :=
  PI * exp (- PI) + 4 * PI * exp (- (4 * PI)) + 2 * Ktail.
Definition Kg2 : R :=
  (PI ^ 2 + PI) * exp (- PI)
  + (16 * PI ^ 2 + 4 * PI) * exp (- (4 * PI))
  + 18 * Ktail.

Lemma qt_bounds : 0 < qt < 1.
Proof.
  split; [ apply exp_pos | ].
  unfold qt. rewrite <- exp_0. apply exp_increasing. pose proof PI_RGT_0; lra.
Qed.

Lemma Ktail_nonneg : 0 <= Ktail.
Proof.
  pose proof qt_bounds as [H0 H1]. unfold Ktail.
  apply Rle_mult_inv_pos; [ left; apply exp_pos | lra ].
Qed.

(* INR at the two exact indices *)
Lemma INR_S0 : INR 1 = 1. Proof. simpl; ring. Qed.
Lemma INR_S1 : INR 2 = 2. Proof. simpl; ring. Qed.

Lemma exp_ge_1 : forall x, 0 <= x -> 1 <= exp x.
Proof. intros x Hx. rewrite <- exp_0. apply exp_le_compat; exact Hx. Qed.

Lemma Kg1_nonneg : 0 <= Kg1.
Proof.
  unfold Kg1. pose proof PI_RGT_0. pose proof Ktail_nonneg.
  pose proof (exp_pos (- PI)). pose proof (exp_pos (- (4 * PI))). nra.
Qed.

Lemma Kg2_nonneg : 0 <= Kg2.
Proof.
  unfold Kg2. pose proof PI_RGT_0. pose proof Ktail_nonneg.
  pose proof (exp_pos (- PI)). pose proof (exp_pos (- (4 * PI))). nra.
Qed.

(* the head terms, at their maxima u = 1 *)
Lemma gterm_at1 : forall x n, 0 <= x ->
  gterm x n <= PI * INR (S n) ^ 2 * exp (- (PI * INR (S n) ^ 2)).
Proof.
  intros x n Hx. unfold gterm. apply xterm_at1. apply exp_ge_1; exact Hx.
Qed.

Lemma gterm_head0 : forall x, 0 <= x -> gterm x 0 <= PI * exp (- PI).
Proof.
  intros x Hx. eapply Rle_trans; [ apply gterm_at1; exact Hx | ].
  rewrite INR_S0. replace (PI * 1 ^ 2) with PI by ring. right; reflexivity.
Qed.

Lemma gterm_head1 : forall x, 0 <= x -> gterm x 1 <= 4 * PI * exp (- (4 * PI)).
Proof.
  intros x Hx. eapply Rle_trans; [ apply gterm_at1; exact Hx | ].
  rewrite INR_S1. replace (PI * 2 ^ 2) with (4 * PI) by ring. right; reflexivity.
Qed.

Lemma gterm_tail : forall x i, 0 <= x ->
  gterm x (2 + i) <= 2 * exp (- (9 * PI / 2)) * qt ^ i.
Proof.
  intros x i Hx.
  eapply Rle_trans; [ apply gterm_at1; exact Hx | ].
  assert (Hk : INR (S (2 + i)) = INR i + 3)
    by (rewrite !S_INR, plus_INR; simpl; ring).
  rewrite Hk. unfold qt. apply sharp_tail1.
Qed.

(* ----------------------------------------------------------------- *)
(*  A.  the partials, and their limit                                 *)
(* ----------------------------------------------------------------- *)
Lemma gpartial_eq : forall x N, gpartial x N = dtheta_partial (exp x) N * exp x.
Proof.
  intros x N. unfold gpartial, dtheta_partial.
  induction N; cbn [sum_f_R0].
  - unfold gterm, dtheta_term. ring.
  - rewrite IHN.
    assert (E : gterm x (S N) = dtheta_term (exp x) (S N) * exp x)
      by (unfold gterm, dtheta_term; ring).
    rewrite E. ring.
Qed.

Lemma gpartial_cv : forall x, 0 <= x -> Un_cv (gpartial x) (- DG x).
Proof.
  intros x Hx.
  assert (Hu : / 2 <= exp x) by (pose proof (exp_ge_1 x Hx); lra).
  assert (Hcv : Un_cv (fun N => dtheta_partial (exp x) N * exp x)
                  (- DPsi (exp x) * exp x))
    by (apply CV_mult; [ apply DPsi_spec; exact Hu | apply Un_cv_const' ]).
  assert (E : - DG x = - DPsi (exp x) * exp x) by (unfold DG; ring).
  rewrite E.
  intros eps He. destruct (Hcv eps He) as [N HN]. exists N. intros n Hn.
  rewrite gpartial_eq. apply HN; exact Hn.
Qed.

Lemma gterm_nonneg : forall x n, 0 <= gterm x n.
Proof.
  intros x n. unfold gterm. pose proof PI_RGT_0.
  apply Rmult_le_pos; [ | left; apply exp_pos ].
  apply Rmult_le_pos; [ | left; apply exp_pos ].
  apply Rmult_le_pos; [ lra | apply pow_le; apply pos_INR ].
Qed.

Lemma gpartial_nonneg : forall x N, 0 <= gpartial x N.
Proof.
  intros x N. unfold gpartial. induction N; cbn [sum_f_R0].
  - apply gterm_nonneg.
  - pose proof (gterm_nonneg x (S N)). lra.
Qed.

(* the split: two exact head terms, then a geometric tail.             *)
(* Stated for an ARBITRARY termwise-dominated sequence, so that the    *)
(* same argument serves both the plain sum and the e^{x/4}-weighted    *)
(* one below without being written twice.                              *)
Lemma sharp_sum_bound : forall (f : nat -> R) N,
  (forall n, 0 <= f n) ->
  (forall n, f n <= PI * INR (S n) ^ 2 * exp (- (PI * INR (S n) ^ 2))) ->
  sum_f_R0 f N <= Kg1.
Proof.
  intros f N Hpos Hdom. pose proof qt_bounds as [Hq0 Hq1].
  assert (H0 : f 0%nat <= PI * exp (- PI)).
  { eapply Rle_trans; [ apply Hdom | ].
    rewrite INR_S0. replace (PI * 1 ^ 2) with PI by ring. right; reflexivity. }
  assert (H1 : f 1%nat <= 4 * PI * exp (- (4 * PI))).
  { eapply Rle_trans; [ apply Hdom | ].
    rewrite INR_S1. replace (PI * 2 ^ 2) with (4 * PI) by ring.
    right; reflexivity. }
  assert (Htl0 : forall i, f (2 + i)%nat <= 2 * exp (- (9 * PI / 2)) * qt ^ i).
  { intro i. eapply Rle_trans; [ apply Hdom | ].
    assert (Hk : INR (S (2 + i)) = INR i + 3)
      by (rewrite !S_INR, plus_INR; simpl; ring).
    rewrite Hk. unfold qt. apply sharp_tail1. }
  pose proof (Hpos 1%nat) as Hn1.
  assert (Htail : 0 <= 2 * Ktail) by (pose proof Ktail_nonneg; lra).
  unfold Kg1.
  destruct (Nat.le_gt_cases N 1) as [Hle | Hgt].
  - assert (Hmono : sum_f_R0 f N <= f 0%nat + f 1%nat).
    { destruct N as [| [| N]].
      - cbn [sum_f_R0]. lra.
      - cbn [sum_f_R0]. lra.
      - exfalso; lia. }
    lra.
  - rewrite (tech2 f 1 N Hgt).
    assert (Hhead : sum_f_R0 f 1
                    <= PI * exp (- PI) + 4 * PI * exp (- (4 * PI)))
      by (cbn [sum_f_R0]; lra).
    assert (Htl : sum_f_R0 (fun i => f (S 1 + i)%nat) (N - S 1) <= 2 * Ktail).
    { eapply Rle_trans.
      - apply sum_f_R0_le. intro i.
        change (S 1 + i)%nat with (2 + i)%nat. apply Htl0.
      - assert (E : sum_f_R0 (fun i => 2 * exp (- (9 * PI / 2)) * qt ^ i) (N - S 1)
                  = 2 * exp (- (9 * PI / 2))
                    * sum_f_R0 (fun i => qt ^ i) (N - S 1)).
        { rewrite (scal_sum (fun i => qt ^ i) (N - S 1)
                     (2 * exp (- (9 * PI / 2)))).
          apply sum_eq; intros i _; ring. }
        rewrite E. unfold Ktail, Rdiv.
        assert (Hgp : sum_f_R0 (fun i => qt ^ i) (N - S 1) <= / (1 - qt))
          by (apply geom_partial_bound; lra).
        assert (Hc : 0 <= 2 * exp (- (9 * PI / 2)))
          by (pose proof (exp_pos (- (9 * PI / 2))); lra).
        assert (Hstep : 2 * exp (- (9 * PI / 2))
                          * sum_f_R0 (fun i => qt ^ i) (N - S 1)
                     <= 2 * exp (- (9 * PI / 2)) * / (1 - qt))
          by (apply Rmult_le_compat_l; assumption).
        lra. }
    lra.
Qed.

Lemma gpartial_bound : forall x N, 0 <= x -> gpartial x N <= Kg1.
Proof.
  intros x N Hx. unfold gpartial.
  apply sharp_sum_bound; [ intro n; apply gterm_nonneg | ].
  intro n; apply gterm_at1; exact Hx.
Qed.

(* ----------------------------------------------------------------- *)
(*  The JOINT bound.  |DG(x)| . e^{x/4} <= Kg1 -- the same constant    *)
(*  as |DG| alone, because the e^{x/4} growth is dominated by the      *)
(*  e^{-pi k^2 e^x} decay many times over, so the product still peaks  *)
(*  at x = 0.  Bounding the two factors SEPARATELY would cost a factor *)
(*  e^{L/4} = 1.5 for nothing: sup|DG| and sup e^{x/4} are attained at *)
(*  opposite ends of [0, L].                                           *)
(* ----------------------------------------------------------------- *)
Lemma gterm_Qe_at1 : forall x n, 0 <= x ->
  gterm x n * exp (/ 4 * x)
  <= PI * INR (S n) ^ 2 * exp (- (PI * INR (S n) ^ 2)).
Proof.
  intros x n Hx. pose proof PI_lower as HP3.
  set (k := INR (S n)).
  assert (Hk1 : 1 <= k) by (unfold k; rewrite S_INR; pose proof (pos_INR n); lra).
  assert (Hk2 : 1 <= k ^ 2) by nra.
  set (a := PI * k ^ 2).
  assert (Ha : 3 <= a) by (unfold a; nra).
  assert (Hex : 1 + x <= exp x) by apply exp_ineq1_le.
  unfold gterm. fold k. fold a.
  (* a e^x e^{-a e^x} e^{x/4} = a . exp (x - a e^x + x/4) <= a e^{-a} *)
  assert (E : exp x * exp (- (a * exp x)) * exp (/ 4 * x)
            = exp (x + - (a * exp x) + / 4 * x))
    by (rewrite <- !exp_plus; reflexivity).
  assert (Hle : x + - (a * exp x) + / 4 * x <= - a).
  { assert (Hgap : 5 * x / 4 <= a * (exp x - 1)).
    { assert (H3x : 3 * x <= a * (exp x - 1)).
      { apply Rle_trans with (a * x); [ nra | ].
        apply Rmult_le_compat_l; lra. }
      lra. }
    lra. }
  assert (Hmono : exp (x + - (a * exp x) + / 4 * x) <= exp (- a))
    by (apply exp_le_compat; exact Hle).
  assert (Hchain : a * exp x * exp (- (a * exp x)) * exp (/ 4 * x)
                 = a * (exp x * exp (- (a * exp x)) * exp (/ 4 * x))) by ring.
  rewrite Hchain, E. nra.
Qed.

Lemma gpartial_Qe_bound : forall x N, 0 <= x ->
  gpartial x N * exp (/ 4 * x) <= Kg1.
Proof.
  intros x N Hx.
  assert (E : gpartial x N * exp (/ 4 * x)
            = sum_f_R0 (fun n => gterm x n * exp (/ 4 * x)) N).
  { unfold gpartial.
    assert (Ec : sum_f_R0 (gterm x) N * exp (/ 4 * x)
               = exp (/ 4 * x) * sum_f_R0 (gterm x) N) by ring.
    rewrite Ec, (scal_sum (gterm x) N (exp (/ 4 * x))).
    apply sum_eq; intros i _; ring. }
  rewrite E. apply sharp_sum_bound.
  - intro n. apply Rmult_le_pos; [ apply gterm_nonneg | left; apply exp_pos ].
  - intro n. apply gterm_Qe_at1; exact Hx.
Qed.

Lemma DG_nonpos : forall x, 0 <= x -> DG x <= 0.
Proof.
  intros x Hx. pose proof (gpartial_cv x Hx) as Hcv.
  assert (Hlo : 0 <= - DG x).
  { apply Rle_trans with (gpartial x 0); [ apply gpartial_nonneg | ].
    apply (growing_ineq (gpartial x)); [ | exact Hcv ].
    intro N. unfold gpartial. cbn [sum_f_R0].
    pose proof (gterm_nonneg x (S N)). lra. }
  lra.
Qed.

Theorem DG_bound : forall x, 0 <= x -> Rabs (DG x) <= Kg1.
Proof.
  intros x Hx. pose proof (gpartial_cv x Hx) as Hcv.
  assert (Hlo : 0 <= - DG x) by (pose proof (DG_nonpos x Hx); lra).
  assert (Hhi : - DG x <= Kg1).
  { eapply Rle_cv_lim.
    2: exact Hcv.
    2: apply Un_cv_const'.
    intro N. apply gpartial_bound; exact Hx. }
  rewrite Rabs_left1 by lra. lra.
Qed.

Theorem DG_Qe_bound : forall x, 0 <= x -> Rabs (DG x * exp (/ 4 * x)) <= Kg1.
Proof.
  intros x Hx. pose proof (gpartial_cv x Hx) as Hcv.
  assert (Hq : 0 < exp (/ 4 * x)) by apply exp_pos.
  assert (Hcv2 : Un_cv (fun N => gpartial x N * exp (/ 4 * x))
                   (- DG x * exp (/ 4 * x)))
    by (apply CV_mult; [ exact Hcv | apply Un_cv_const' ]).
  assert (Hlo : 0 <= - DG x * exp (/ 4 * x)).
  { apply Rmult_le_pos; [ pose proof (DG_nonpos x Hx); lra | lra ]. }
  assert (Hhi : - DG x * exp (/ 4 * x) <= Kg1).
  { eapply Rle_cv_lim.
    2: exact Hcv2.
    2: apply Un_cv_const'.
    intro N. apply gpartial_Qe_bound; exact Hx. }
  rewrite Rabs_left1 by nra. lra.
Qed.


(* ----------------------------------------------------------------- *)
(*  B.  differentiating the partials in x                             *)
(* ----------------------------------------------------------------- *)
Lemma gterm_deriv : forall n x, derivable_pt_lim (fun s => gterm s n) x (gterm' x n).
Proof.
  intros n x. unfold gterm, gterm'. set (c := PI * INR (S n) ^ 2).
  assert (H1 : derivable_pt_lim (fun s => c * exp s) x (c * exp x))
    by (apply derivable_pt_lim_scal; apply derivable_pt_lim_exp).
  assert (H2 : derivable_pt_lim (fun s => exp (- (c * exp s))) x
                 (exp (- (c * exp x)) * - (c * exp x))).
  { apply (derivable_pt_lim_comp (fun s => - (c * exp s)) exp x
             (- (c * exp x)) (exp (- (c * exp x)))).
    - apply derivable_pt_lim_opp; exact H1.
    - apply derivable_pt_lim_exp. }
  pose proof (derivable_pt_lim_mult (fun s => c * exp s)
                (fun s => exp (- (c * exp s))) x
                (c * exp x) (exp (- (c * exp x)) * - (c * exp x)) H1 H2) as Hm.
  replace ((c * exp x - (c * exp x) ^ 2) * exp (- (c * exp x)))
    with (c * exp x * exp (- (c * exp x))
          + c * exp x * (exp (- (c * exp x)) * - (c * exp x))) by ring.
  exact Hm.
Qed.

Lemma gpartial_deriv : forall N x,
  derivable_pt_lim (fun s => gpartial s N) x (g2partial x N).
Proof.
  intros N x. unfold gpartial, g2partial.
  apply (deriv_sum (fun k s => gterm s k) (fun k s => gterm' s k) N x).
  intro k. apply gterm_deriv.
Qed.

Lemma sum_f_R0_abs : forall (A : nat -> R) N,
  Rabs (sum_f_R0 A N) <= sum_f_R0 (fun i => Rabs (A i)) N.
Proof.
  intros A N. induction N; cbn [sum_f_R0].
  - apply Rle_refl.
  - eapply Rle_trans; [ apply Rabs_triang | ]. lra.
Qed.

(* |gterm'| <= ((au)^2 + au) e^{-au}, then both pieces at u = 1 *)
Lemma gterm'_abs_at1 : forall x n, 0 <= x ->
  Rabs (gterm' x n)
  <= (PI * INR (S n) ^ 2) ^ 2 * exp (- (PI * INR (S n) ^ 2))
     + PI * INR (S n) ^ 2 * exp (- (PI * INR (S n) ^ 2)).
Proof.
  intros x n Hx.
  assert (He1 : 1 <= exp x) by (apply exp_ge_1; exact Hx).
  pose proof (xterm_at1 (exp x) n He1) as A1.
  pose proof (xterm2_at1 (exp x) n He1) as A2.
  set (w := PI * INR (S n) ^ 2 * exp x) in *.
  assert (Hw : 0 <= w).
  { unfold w. pose proof PI_RGT_0.
    apply Rmult_le_pos; [ | left; apply exp_pos ].
    apply Rmult_le_pos; [ lra | apply pow_le; apply pos_INR ]. }
  assert (He : 0 < exp (- w)) by apply exp_pos.
  unfold gterm'. fold w.
  apply Rabs_le. split; nra.
Qed.

Lemma gterm'_head0 : forall x, 0 <= x ->
  Rabs (gterm' x 0) <= (PI ^ 2 + PI) * exp (- PI).
Proof.
  intros x Hx. eapply Rle_trans; [ apply gterm'_abs_at1; exact Hx | ].
  rewrite INR_S0. replace (PI * 1 ^ 2) with PI by ring. right; ring.
Qed.

Lemma gterm'_head1 : forall x, 0 <= x ->
  Rabs (gterm' x 1) <= (16 * PI ^ 2 + 4 * PI) * exp (- (4 * PI)).
Proof.
  intros x Hx. eapply Rle_trans; [ apply gterm'_abs_at1; exact Hx | ].
  rewrite INR_S1. replace (PI * 2 ^ 2) with (4 * PI) by ring. right; ring.
Qed.

Lemma gterm'_tail : forall x i, 0 <= x ->
  Rabs (gterm' x (2 + i)) <= 18 * exp (- (9 * PI / 2)) * qt ^ i.
Proof.
  intros x i Hx.
  eapply Rle_trans; [ apply gterm'_abs_at1; exact Hx | ].
  assert (Hk : INR (S (2 + i)) = INR i + 3)
    by (rewrite !S_INR, plus_INR; simpl; ring).
  rewrite Hk. unfold qt.
  eapply Rle_trans; [ | apply (sharp_tail2 i) ]. right; ring.
Qed.

Lemma g2partial_abs_bound : forall x N, 0 <= x -> Rabs (g2partial x N) <= Kg2.
Proof.
  intros x N Hx. pose proof qt_bounds as [Hq0 Hq1].
  pose proof (gterm'_head0 x Hx) as H0.
  pose proof (gterm'_head1 x Hx) as H1.
  pose proof (Rabs_pos (gterm' x 1)) as Hn1.
  assert (Htail : 0 <= 18 * Ktail) by (pose proof Ktail_nonneg; lra).
  unfold Kg2, g2partial.
  eapply Rle_trans; [ apply sum_f_R0_abs | ].
  destruct (Nat.le_gt_cases N 1) as [Hle | Hgt].
  - assert (Hmono : sum_f_R0 (fun i => Rabs (gterm' x i)) N
                    <= Rabs (gterm' x 0) + Rabs (gterm' x 1)).
    { destruct N as [| [| N]].
      - cbn [sum_f_R0]. lra.
      - cbn [sum_f_R0]. lra.
      - exfalso; lia. }
    lra.
  - rewrite (tech2 (fun i => Rabs (gterm' x i)) 1 N Hgt).
    assert (Hhead : sum_f_R0 (fun i => Rabs (gterm' x i)) 1
                    <= (PI ^ 2 + PI) * exp (- PI)
                       + (16 * PI ^ 2 + 4 * PI) * exp (- (4 * PI)))
      by (cbn [sum_f_R0]; lra).
    assert (Htl : sum_f_R0 (fun i => Rabs (gterm' x (S 1 + i))) (N - S 1)
                  <= 18 * Ktail).
    { eapply Rle_trans.
      - apply sum_f_R0_le. intro i.
        change (S 1 + i)%nat with (2 + i)%nat. apply gterm'_tail; exact Hx.
      - assert (E : sum_f_R0 (fun i => 18 * exp (- (9 * PI / 2)) * qt ^ i) (N - S 1)
                  = 18 * exp (- (9 * PI / 2))
                    * sum_f_R0 (fun i => qt ^ i) (N - S 1)).
        { rewrite (scal_sum (fun i => qt ^ i) (N - S 1)
                     (18 * exp (- (9 * PI / 2)))).
          apply sum_eq; intros i _; ring. }
        rewrite E. unfold Ktail, Rdiv.
        assert (Hgp : sum_f_R0 (fun i => qt ^ i) (N - S 1) <= / (1 - qt))
          by (apply geom_partial_bound; lra).
        assert (Hc : 0 <= 18 * exp (- (9 * PI / 2)))
          by (pose proof (exp_pos (- (9 * PI / 2))); lra).
        assert (Hstep : 18 * exp (- (9 * PI / 2))
                          * sum_f_R0 (fun i => qt ^ i) (N - S 1)
                     <= 18 * exp (- (9 * PI / 2)) * / (1 - qt))
          by (apply Rmult_le_compat_l; assumption).
        lra. }
    lra.
Qed.

(* ----------------------------------------------------------------- *)
(*  C.  Lipschitz, uniformly in N, then in the limit                  *)
(* ----------------------------------------------------------------- *)
Lemma gpartial_lip : forall N x y, 0 <= x -> 0 <= y ->
  Rabs (gpartial x N - gpartial y N) <= Kg2 * Rabs (x - y).
Proof.
  intros N x y Hx Hy.
  assert (Hgen : forall p q, 0 <= p -> 0 <= q -> p < q ->
    Rabs (gpartial p N - gpartial q N) <= Kg2 * Rabs (p - q)).
  { intros p q Hp Hq Hpq.
    destruct (MVT_cor2 (fun s => gpartial s N) (fun s => g2partial s N) p q Hpq
                (fun c _ => gpartial_deriv N c)) as [c [Hc Hcr]].
    assert (Hc0 : 0 <= c) by lra.
    replace (gpartial p N - gpartial q N)
      with (- (gpartial q N - gpartial p N)) by ring.
    rewrite Rabs_Ropp, Hc, Rabs_mult.
    replace (Rabs (p - q)) with (Rabs (q - p))
      by (rewrite <- (Rabs_Ropp (q - p)); f_equal; ring).
    apply Rmult_le_compat_r;
      [ apply Rabs_pos | apply g2partial_abs_bound; exact Hc0 ]. }
  destruct (Rtotal_order x y) as [H | [H | H]].
  - apply Hgen; assumption.
  - subst y. replace (gpartial x N - gpartial x N) with 0 by ring.
    rewrite Rabs_R0. apply Rmult_le_pos; [ apply Kg2_nonneg | apply Rabs_pos ].
  - replace (gpartial x N - gpartial y N)
      with (- (gpartial y N - gpartial x N)) by ring.
    rewrite Rabs_Ropp.
    replace (Rabs (x - y)) with (Rabs (y - x))
      by (rewrite <- (Rabs_Ropp (y - x)); f_equal; ring).
    apply Hgen; assumption.
Qed.

Theorem DG_lipschitz : forall x y, 0 <= x -> 0 <= y ->
  Rabs (DG x - DG y) <= Kg2 * Rabs (x - y).
Proof.
  intros x y Hx Hy.
  pose proof (CV_minus (gpartial x) (gpartial y) (- DG x) (- DG y)
                (gpartial_cv x Hx) (gpartial_cv y Hy)) as Hcv.
  assert (Hup : - DG x - - DG y <= Kg2 * Rabs (x - y)).
  { eapply Rle_cv_lim.
    2: exact Hcv.
    2: apply Un_cv_const'.
    intro N. pose proof (gpartial_lip N x y Hx Hy) as HL.
    apply abs_le_inv in HL. destruct HL as [_ H2]. exact H2. }
  assert (Hlo : - (Kg2 * Rabs (x - y)) <= - DG x - - DG y).
  { eapply Rle_cv_lim.
    2: apply Un_cv_const'.
    2: exact Hcv.
    intro N. pose proof (gpartial_lip N x y Hx Hy) as HL.
    apply abs_le_inv in HL. destruct HL as [H1 _]. exact H1. }
  apply Rabs_le. lra.
Qed.

(* ----------------------------------------------------------------- *)
(*  D.  the chain rule                                                *)
(* ----------------------------------------------------------------- *)
Theorem GPsi_deriv : forall x, 0 <= x -> derivable_pt_lim GPsi x (DG x).
Proof.
  intros x Hx. unfold GPsi, DG.
  apply (derivable_pt_lim_comp exp Psi x (exp x) (DPsi (exp x))).
  - apply derivable_pt_lim_exp.
  - apply Psi_derivable. apply exp_ge_1; exact Hx.
Qed.

Print Assumptions DG_bound.
Print Assumptions DG_lipschitz.
Print Assumptions GPsi_deriv.
