(* ================================================================= *)
(*  LogGeomSeries.v  —  the log-series  Sum_{k>=1} r^k cos(k theta)/k   *)
(*  = -1/2 ln(1 - 2 r cos theta + r^2)  for 0 <= r < 1.                *)
(*                                                                    *)
(*  The analytic centerpiece of the Prime Number Theorem zero-free     *)
(*  line.  Partial sums f_N differentiable with derivative fp_N(t) =    *)
(*  Sum t^k cos((k+1)theta) = Re of a complex geometric partial sum;    *)
(*  fp_N -> gp uniformly on a ball (geometric tail), so CVU_derivable   *)
(*  makes the pointwise limit F differentiable with F' = gp; the closed *)
(*  form G(t) = -1/2 ln(1-2t cos theta+t^2) has the same derivative and *)
(*  F(0)=G(0)=0, so F = G (MVT).  Axiom-clean.                         *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia FunctionalExtensionality.
Require Import ComplexField Cmodulus CSeries CDeriv EulerFormula RootsOfUnity
        CEulerProductZeta EulerFactorR.
Open Scope R_scope.

(* ================================================================= *)
(*  1.  partial sums and their derivatives                            *)
(* ================================================================= *)

Definition lterm (θ : R) (k : nat) (t : R) : R :=
  cos (INR (S k) * θ) / INR (S k) * t ^ (S k).
Definition ldterm (θ : R) (k : nat) (t : R) : R :=
  cos (INR (S k) * θ) * t ^ k.

Definition lsum  (θ : R) (N : nat) (t : R) : R := sum_f_R0 (fun k => lterm θ k t) N.
Definition ldsum (θ : R) (N : nat) (t : R) : R := sum_f_R0 (fun k => ldterm θ k t) N.

Lemma lterm_deriv : forall θ k t, derivable_pt_lim (fun u => lterm θ k u) t (ldterm θ k t).
Proof.
  intros θ k t; unfold lterm, ldterm.
  replace (cos (INR (S k) * θ) * t ^ k)
    with (cos (INR (S k) * θ) / INR (S k) * (INR (S k) * t ^ k))
    by (field; apply not_0_INR; lia).
  apply derivable_pt_lim_scal.
  apply (derivable_pt_lim_pow t (S k)).
Qed.

Lemma lsum_deriv : forall θ N t, derivable_pt_lim (fun u => lsum θ N u) t (ldsum θ N t).
Proof.
  intros θ N t; induction N as [|N IH].
  - unfold lsum, ldsum; simpl; apply lterm_deriv.
  - unfold lsum, ldsum; simpl.
    apply (derivable_pt_lim_plus
             (fun u => sum_f_R0 (fun k => lterm θ k u) N) (fun u => lterm θ (S N) u)
             t (ldsum θ N t) (ldterm θ (S N) t)); [ exact IH | apply lterm_deriv ].
Qed.

(* ================================================================= *)
(*  2.  complex closed form of the derivative partial sum             *)
(* ================================================================= *)

Definition cw (t θ : R) : C := Cmul (RtoC t) (Cexp θ).
Definition gp (θ t : R) : R := (cos θ - t) / (1 - 2 * t * cos θ + t ^ 2).

Lemma Re_Cadd : forall a b, Re (Cadd a b) = Re a + Re b.
Proof. intros; unfold Cadd; reflexivity. Qed.
Lemma Re_Cminus : forall a b, Re (Cminus a b) = Re a - Re b.
Proof. intros; unfold Cminus; reflexivity. Qed.
Lemma Cmod_Cexp : forall θ, Cmod (Cexp θ) = 1.
Proof. intro θ; unfold Cmod; rewrite Cnorm2_Cexp; apply sqrt_1. Qed.

Lemma Cmod_cw : forall t θ, Cmod (cw t θ) = Rabs t.
Proof. intros; unfold cw; rewrite Cmod_mul, Cmod_RtoC, Cmod_Cexp; ring. Qed.

Lemma cw_ne_C1 : forall t θ, Rabs t < 1 -> cw t θ <> C1.
Proof.
  intros t θ Ht He; assert (H : Cmod (cw t θ) = Cmod C1) by (rewrite He; reflexivity).
  rewrite Cmod_cw, Cmod_C1 in H; lra.
Qed.

Lemma cw_pow : forall t θ k, Cpow (cw t θ) k = Cmul (RtoC (t ^ k)) (Cexp (INR k * θ)).
Proof.
  intros t θ k; induction k as [|k IH]; cbn [Cpow].
  - replace (t ^ 0) with 1 by (simpl; ring).
    replace (INR 0 * θ) with 0 by (simpl; ring).
    rewrite Cexp_0; unfold RtoC, C1; apply Ceq; cbn [Re Im Cmul]; ring.
  - unfold cw in *; rewrite IH.
    replace (INR (S k) * θ) with (θ + INR k * θ) by (rewrite S_INR; ring).
    rewrite Cexp_add.
    replace (t ^ S k) with (t * t ^ k) by (simpl; ring).
    rewrite RtoC_mul; ring.
Qed.

Lemma ldterm_Re : forall θ k t, ldterm θ k t = Re (Cmul (Cexp θ) (Cpow (cw t θ) k)).
Proof.
  intros θ k t; unfold ldterm; rewrite cw_pow.
  replace (Cmul (Cexp θ) (Cmul (RtoC (t ^ k)) (Cexp (INR k * θ))))
    with (Cmul (RtoC (t ^ k)) (Cexp (INR (S k) * θ))).
  2:{ replace (INR (S k) * θ) with (θ + INR k * θ) by (rewrite S_INR; ring).
      rewrite Cexp_add; ring. }
  unfold Cexp, Cmul, RtoC; cbn [Re Im]; ring.
Qed.

Lemma Re_Csum_S : forall (f : nat -> C) N,
  Re (Csum f (S N)) = sum_f_R0 (fun k => Re (f k)) N.
Proof.
  intros f N; induction N as [|N IH].
  - cbn [Csum]; rewrite Re_Cadd; unfold C0; cbn [Re sum_f_R0]; ring.
  - change (Csum f (S (S N))) with (Cadd (Csum f (S N)) (f (S N))).
    rewrite Re_Cadd, IH, tech5; reflexivity.
Qed.

Lemma Cmul_Csum : forall c (f : nat -> C) N, Cmul c (Csum f N) = Csum (fun k => Cmul c (f k)) N.
Proof.
  intros c f N; induction N as [|N IH]; cbn [Csum]; [ ring | rewrite <- IH; ring ].
Qed.

Lemma ldsum_closed : forall θ N t,
  ldsum θ N t = Re (Cmul (Cexp θ) (Csum (fun k => Cpow (cw t θ) k) (S N))).
Proof.
  intros θ N t; unfold ldsum.
  rewrite Cmul_Csum, Re_Csum_S.
  apply sum_eq; intros k _; rewrite <- ldterm_Re; reflexivity.
Qed.

(* the closed form of the derivative limit *)
Lemma gp_eq : forall θ t, Rabs t < 1 ->
  Re (Cmul (Cexp θ) (Cinv (Cminus C1 (cw t θ)))) = gp θ t.
Proof.
  intros θ t Ht.
  assert (HD : 0 < 1 - 2 * t * cos θ + t ^ 2).
  { pose proof (Rabs_pos t); pose proof (Rabs_pos (cos θ)).
    pose proof (Rle_abs (t * cos θ)) as Ha; pose proof (Rabs_mult t (cos θ)) as Hm.
    pose proof (COS_bound θ) as [Hc1 Hc2].
    assert (Hcabs : Rabs (cos θ) <= 1) by (apply Rabs_le; lra).
    pose proof (Rsqr_abs t) as Hsq; unfold Rsqr in Hsq.
    nra. }
  set (d := Cminus C1 (cw t θ)).
  assert (HRd : Re d = 1 - t * cos θ)
    by (unfold d, Cminus, cw, Cmul, Cexp, Cadd, Copp, RtoC, C1; cbn [Re Im]; ring).
  assert (HId : Im d = - (t * sin θ))
    by (unfold d, Cminus, cw, Cmul, Cexp, Cadd, Copp, RtoC, C1; cbn [Re Im]; ring).
  assert (HN : Cnorm2 d = 1 - 2 * t * cos θ + t ^ 2).
  { unfold d, Cnorm2, Cminus, cw, Cmul, Cexp, Cadd, Copp, RtoC, C1; cbn [Re Im].
    pose proof (sin2_cos2 θ) as Hcs; unfold Rsqr in Hcs; nra. }
  unfold gp, Cmul, Cinv, Cexp; cbn [Re Im].
  rewrite HRd, HId, HN.
  assert (HDne : 1 - 2 * t * cos θ + t ^ 2 <> 0) by (apply Rgt_not_eq; exact HD).
  field_simplify_eq; [ | exact HDne ].
  pose proof (sin2_cos2 θ) as Hcs; unfold Rsqr in Hcs.
  replace (sin θ ^ 2) with (1 - cos θ * cos θ) by nra; ring.
Qed.

Lemma remainder_C : forall θ t N, Rabs t < 1 ->
  Cminus (Cmul (Cexp θ) (Csum (fun k => Cpow (cw t θ) k) (S N)))
         (Cmul (Cexp θ) (Cinv (Cminus C1 (cw t θ))))
  = Cmul (Cmul (Cexp θ) (Cpow (cw t θ) (S N))) (Cinv (Cminus (cw t θ) C1)).
Proof.
  intros θ t N Ht.
  assert (Hne : cw t θ <> C1) by (apply cw_ne_C1; exact Ht).
  assert (Hw1 : Cminus (cw t θ) C1 <> C0)
    by (intro He; apply Hne; replace (cw t θ) with (Cadd (Cminus (cw t θ) C1) C1) by ring;
        rewrite He; ring).
  assert (H1w : Cminus C1 (cw t θ) <> C0)
    by (intro He; apply Hne; replace (cw t θ) with (Cminus C1 (Cminus C1 (cw t θ))) by ring;
        rewrite He; ring).
  rewrite (geom_sum_value (cw t θ) (S N) Hne); unfold Cdiv.
  field; split; assumption.
Qed.

Lemma ldsum_minus_gp : forall θ t N, Rabs t < 1 ->
  ldsum θ N t - gp θ t
  = Re (Cmul (Cmul (Cexp θ) (Cpow (cw t θ) (S N))) (Cinv (Cminus (cw t θ) C1))).
Proof.
  intros θ t N Ht.
  rewrite (ldsum_closed θ N t), <- (gp_eq θ t Ht), <- Re_Cminus, (remainder_C θ t N Ht).
  reflexivity.
Qed.

Lemma remainder_bound : forall θ t N, Rabs t < 1 ->
  Rabs (ldsum θ N t - gp θ t) <= (Rabs t) ^ (S N) / (1 - Rabs t).
Proof.
  intros θ t N Ht.
  assert (Hw1 : Cminus (cw t θ) C1 <> C0).
  { intro He; assert (H : Cmod (cw t θ) = Cmod C1).
    { replace (cw t θ) with (Cadd (Cminus (cw t θ) C1) C1) by ring; rewrite He; f_equal; ring. }
    rewrite Cmod_cw, Cmod_C1 in H; lra. }
  assert (Hden : 1 - Rabs t <= Cmod (Cminus (cw t θ) C1)).
  { pose proof (Cmod_diff_le (cw t θ) C1) as HD; rewrite Cmod_cw, Cmod_C1 in HD.
    rewrite Rabs_minus_sym in HD; pose proof (Rle_abs (1 - Rabs t)); lra. }
  assert (Hdpos : 0 < Cmod (Cminus (cw t θ) C1)) by (apply Cmod_pos_ne0; exact Hw1).
  rewrite (ldsum_minus_gp θ t N Ht).
  eapply Rle_trans; [ apply Cmod_Re_le | ].
  rewrite Cmod_mul, Cmod_mul, Cmod_Cexp, Cmod_Cpow, Cmod_cw, (Cmod_inv _ Hw1).
  rewrite Rmult_1_l.
  apply Rmult_le_compat.
  - apply pow_le, Rabs_pos.
  - apply Rlt_le, Rinv_0_lt_compat; exact Hdpos.
  - apply Rle_refl.
  - apply Rinv_le_contravar; [ | exact Hden ].
    assert (0 <= Rabs t) by apply Rabs_pos; lra.
Qed.

(* ================================================================= *)
(*  3.  uniform convergence and the CVU-derivable assembly            *)
(* ================================================================= *)


Lemma Un_cv_const : forall c : R, Un_cv (fun _ => c) c.
Proof. intros c eps He; exists 0%nat; intros n _; unfold R_dist; replace (c - c) with 0 by ring; rewrite Rabs_R0; exact He. Qed.

Lemma Un_cv_ext : forall u v L, (forall n, u n = v n) -> Un_cv u L -> Un_cv v L.
Proof. intros u v L He H eps Heps; destruct (H eps Heps) as [N HN]; exists N; intros n Hn; unfold R_dist; rewrite <- He; apply HN; exact Hn. Qed.

Lemma geomS_cv : forall q, Rabs q < 1 -> { T | Un_cv (fun N => sum_f_R0 (fun k => q ^ (S k)) N) T }.
Proof.
  intros q Hq; exists (q * / (1 - q)).
  apply (Un_cv_ext (fun N => q * sum_f_R0 (fun k => q ^ k) N)).
  - intro N; rewrite scal_sum; apply sum_eq; intros k _; simpl; ring.
  - apply (CV_mult (fun _ => q) (fun N => sum_f_R0 (fun k => q ^ k) N) q (/ (1 - q)));
      [ apply Un_cv_const | apply (geom_limit q Hq) ].
Qed.

(* pointwise convergence of the antiderivative series (dominated by geometric) *)
Lemma lsum_cv : forall θ t, Rabs t < 1 -> { L | Un_cv (fun N => lsum θ N t) L }.
Proof.
  intros θ t Ht; unfold lsum.
  apply (Rseries_abs_cv (fun k => lterm θ k t) (fun k => (Rabs t) ^ (S k))).
  - intro k.
    assert (Hpos : 1 <= INR (S k)) by (rewrite <- INR_1; apply le_INR; lia).
    assert (Hinv0 : 0 < / INR (S k)) by (apply Rinv_0_lt_compat; lra).
    unfold lterm, Rdiv; rewrite Rabs_mult, Rabs_mult, <- RPow_abs.
    apply Rle_trans with (1 * 1 * (Rabs t) ^ (S k)); [ | lra ].
    apply Rmult_le_compat_r; [ apply pow_le, Rabs_pos | ].
    apply Rmult_le_compat.
    + apply Rabs_pos.
    + apply Rabs_pos.
    + apply Rabs_le; apply COS_bound.
    + rewrite (Rabs_right (/ INR (S k))) by (apply Rle_ge; lra).
      rewrite <- Rinv_1; apply Rinv_le_contravar; lra.
  - apply (geomS_cv (Rabs t)); rewrite Rabs_pos_eq by apply Rabs_pos; exact Ht.
Qed.

(* ================================================================= *)
(*  4.  CVU, the closed-form derivative, and MVT                      *)
(* ================================================================= *)

Lemma lsum_0 : forall θ N, lsum θ N 0 = 0.
Proof.
  intros θ N; unfold lsum; induction N as [|N IH]; simpl.
  - unfold lterm; simpl; ring.
  - rewrite IH; unfold lterm; simpl; ring.
Qed.

Definition Flim (θ y : R) : R :=
  match Rlt_dec (Rabs y) 1 with
  | left H => proj1_sig (lsum_cv θ y H)
  | right _ => 0
  end.

Lemma Flim_cv : forall θ y, Rabs y < 1 -> Un_cv (fun N => lsum θ N y) (Flim θ y).
Proof.
  intros θ y H; unfold Flim; destruct (Rlt_dec (Rabs y) 1) as [Hl | Hr];
    [ exact (proj2_sig (lsum_cv θ y Hl)) | lra ].
Qed.

Lemma pow_cv0 : forall x, Rabs x < 1 -> Un_cv (fun n => x ^ n) 0.
Proof.
  intros x Hx eps Heps; destruct (pow_lt_1_zero x Hx eps Heps) as [N HN].
  exists N; intros n Hn; unfold R_dist; rewrite Rminus_0_r; apply HN; exact Hn.
Qed.

Lemma logCVU : forall θ (rho : posreal), (rho < 1)%R ->
  CVU (fun N => ldsum θ N) (gp θ) 0 rho.
Proof.
  intros θ rho Hrho eps Heps.
  assert (Hr0 : 0 <= rho) by (apply Rlt_le, cond_pos).
  assert (Hcv : Un_cv (fun n => rho ^ (S n) / (1 - rho)) 0).
  { apply (Un_cv_ext (fun n => rho ^ (S n) * / (1 - rho)));
      [ intro n; unfold Rdiv; ring | ].
    replace 0 with (0 * / (1 - rho)) by ring.
    apply CV_mult; [ | apply Un_cv_const ].
    apply (Un_cv_ext (fun n => rho * rho ^ n)); [ intro n; simpl; ring | ].
    replace 0 with (rho * 0) by ring.
    apply CV_mult; [ apply Un_cv_const | ].
    apply pow_cv0; rewrite Rabs_pos_eq by exact Hr0; exact Hrho. }
  destruct (Hcv eps Heps) as [N HN]; exists N; intros n y Hn Hy.
  unfold Boule in Hy; rewrite Rminus_0_r in Hy.
  assert (Hy1 : Rabs y < 1) by lra.
  rewrite Rabs_minus_sym.
  eapply Rle_lt_trans; [ apply (remainder_bound θ y n Hy1) | ].
  specialize (HN n Hn); unfold R_dist in HN; rewrite Rminus_0_r in HN.
  rewrite Rabs_right in HN
    by (apply Rle_ge; apply Rmult_le_pos;
        [ apply pow_le | apply Rlt_le, Rinv_0_lt_compat ]; lra).
  eapply Rle_lt_trans; [ | exact HN ].
  apply Rmult_le_compat.
  - apply pow_le, Rabs_pos.
  - apply Rlt_le, Rinv_0_lt_compat; lra.
  - apply pow_incr; split; [ apply Rabs_pos | lra ].
  - apply Rinv_le_contravar; lra.
Qed.

Lemma G_deriv : forall θ y, Rabs y < 1 ->
  derivable_pt_lim (fun t => - (/2) * ln (1 - 2 * t * cos θ + t ^ 2)) y (gp θ y).
Proof.
  intros θ y Hy.
  assert (HD : 0 < 1 - 2 * y * cos θ + y ^ 2).
  { pose proof (Rabs_pos y); pose proof (Rabs_pos (cos θ)).
    pose proof (Rle_abs (y * cos θ)) as Ha; pose proof (Rabs_mult y (cos θ)) as Hm.
    pose proof (COS_bound θ) as [Hc1 Hc2].
    assert (Hcabs : Rabs (cos θ) <= 1) by (apply Rabs_le; lra).
    pose proof (Rsqr_abs y) as Hsq; unfold Rsqr in Hsq. nra. }
  assert (HDne : 1 - 2 * y * cos θ + y ^ 2 <> 0) by (apply Rgt_not_eq; exact HD).
  assert (HDd : derivable_pt_lim (fun t => 1 - 2 * t * cos θ + t ^ 2) y (2 * y - 2 * cos θ)).
  { replace (fun t => 1 - 2 * t * cos θ + t ^ 2)
      with (fun t => (1 + - (2 * cos θ) * t) + t ^ 2)
      by (apply functional_extensionality; intro; ring).
    replace (2 * y - 2 * cos θ)
      with ((0 + - (2 * cos θ) * 1) + INR 2 * y ^ (Init.Nat.pred 2)) by (simpl; ring).
    apply derivable_pt_lim_plus.
    - apply derivable_pt_lim_plus.
      + apply derivable_pt_lim_const.
      + apply (derivable_pt_lim_scal (fun t => t) (- (2 * cos θ)) y 1 (derivable_pt_lim_id y)).
    - apply (derivable_pt_lim_pow y 2). }
  pose proof (derivable_pt_lim_comp (fun t => 1 - 2 * t * cos θ + t ^ 2) ln y
                (2 * y - 2 * cos θ) (/ (1 - 2 * y * cos θ + y ^ 2)) HDd
                (derivable_pt_lim_ln _ HD)) as Hcomp.
  replace (gp θ y)
    with (- (/2) * (/ (1 - 2 * y * cos θ + y ^ 2) * (2 * y - 2 * cos θ)))
    by (unfold gp; field; exact HDne).
  apply (derivable_pt_lim_scal (comp ln (fun t => 1 - 2 * t * cos θ + t ^ 2))
           (- (/2)) y (/ (1 - 2 * y * cos θ + y ^ 2) * (2 * y - 2 * cos θ)) Hcomp).
Qed.

(* ================================================================= *)
(*  5.  the log-series                                               *)
(* ================================================================= *)

Theorem log_geom_series : forall θ r, 0 <= r < 1 ->
  Un_cv (fun N => lsum θ N r) (- (/2) * ln (1 - 2 * r * cos θ + r ^ 2)).
Proof.
  intros θ r [Hr0 Hr1].
  set (rho := mkposreal ((1 + r) / 2) ltac:(lra)).
  assert (Hrho1 : (rho < 1)%R) by (simpl; lra).
  assert (Hbnd : forall y, Rabs y < rho -> Rabs y < 1) by (intros; lra).
  assert (HFd : forall y, Boule 0 rho y -> derivable_pt_lim (Flim θ) y (gp θ y)).
  { apply (CVU_derivable (fun N => lsum θ N) (fun N => ldsum θ N) (Flim θ) (gp θ) 0 rho).
    - apply logCVU; exact Hrho1.
    - intros y Hy; unfold Boule in Hy; rewrite Rminus_0_r in Hy.
      apply Flim_cv, Hbnd; exact Hy.
    - intros n y _; apply lsum_deriv. }
  assert (HGd : forall y, Boule 0 rho y ->
    derivable_pt_lim (fun t => - (/2) * ln (1 - 2 * t * cos θ + t ^ 2)) y (gp θ y)).
  { intros y Hy; unfold Boule in Hy; rewrite Rminus_0_r in Hy.
    apply G_deriv, Hbnd; exact Hy. }
  (* h := F - G has zero derivative on [0,r] ⇒ h r = h 0 *)
  set (G := fun t => - (/2) * ln (1 - 2 * t * cos θ + t ^ 2)).
  set (h := fun t => Flim θ t - G t).
  assert (Hh0 : h 0 = 0).
  { unfold h, G; assert (HF0 : Flim θ 0 = 0).
    { apply (UL_sequence (fun N => lsum θ N 0)); [ apply Flim_cv; rewrite Rabs_R0; lra | ].
      apply (Un_cv_ext (fun _ => 0)); [ intro; symmetry; apply lsum_0 | apply Un_cv_const ]. }
    rewrite HF0; replace (1 - 2 * 0 * cos θ + 0 ^ 2) with 1 by ring; rewrite ln_1; ring. }
  assert (Hhr : h r = 0).
  { destruct (Rle_lt_or_eq_dec 0 r Hr0) as [Hlt | Heq].
    - destruct (MVT_cor2 h (fun _ => 0) 0 r Hlt) as [c [Hc _]].
      + intros c Hc; unfold h.
        assert (Hbc : Boule 0 rho c).
        { unfold Boule; rewrite Rminus_0_r, Rabs_right by lra; simpl; lra. }
        replace 0 with (gp θ c - gp θ c) by ring.
        apply derivable_pt_lim_minus; [ apply HFd | apply HGd ]; exact Hbc.
      + rewrite Hh0, Rmult_0_l in Hc; lra.
    - rewrite <- Heq; exact Hh0. }
  assert (HFr : Flim θ r = G r) by (unfold h in Hhr; lra).
  unfold G in HFr; cbv beta in HFr.
  rewrite <- HFr.
  apply Flim_cv; rewrite Rabs_right by lra; lra.
Qed.

Print Assumptions log_geom_series.
