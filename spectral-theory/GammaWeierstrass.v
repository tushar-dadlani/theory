(* ================================================================= *)
(*  GammaWeierstrass.v   (the real Weierstrass identity Gam(s)*P(s)=1)   *)
(*                                                                    *)
(*  Using the Gauss limit  Gam s = lim N^s N!/(s(s+1)...(s+N))          *)
(*  (GammaGaussLimit.gauss_limit_fact), regroup the reciprocal          *)
(*                                                                    *)
(*     1/G_N(s) = s * Wprod_N(s) * exp(s (H_N - ln N))                  *)
(*                                                                    *)
(*  where  Wprod_N(s) = prod_{k=1}^N (1+s/k) e^{-s/k}.  The product      *)
(*  converges (log-sum telescopes, O(1/k^2)), H_N - ln N -> gamma        *)
(*  (EulerMascheroni), so  1/G_N -> P(s) = s e^{gamma s} prod(...),       *)
(*  and  G_N (1/G_N) = 1  forces  Gam(s) P(s) = 1  (hence Gam s > 0).     *)
(*                                                                    *)
(*  Axioms: standard classical-Reals only.                            *)
(* ================================================================= *)

From Stdlib Require Import Reals Rpower Lra Lia Factorial.
Require Import GammaReal GammaExtend GammaGaussLimit HarmonicSum EulerMascheroni
        ImproperCv1.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  the calculus input :  x - x^2/2 <= ln(1+x)  for x >= 0            *)
(* ----------------------------------------------------------------- *)

Lemma affine_d : forall c, derivable_pt_lim (fun t => 1 + t) c 1.
Proof.
  intros c eps Heps. exists (mkposreal eps Heps). intros h Hh0 _.
  replace ((1 + (c + h) - (1 + c)) / h - 1) with 0 by (field; exact Hh0).
  rewrite Rabs_R0. exact Heps.
Qed.

Lemma lnd : forall c, 0 < 1 + c -> derivable_pt_lim (fun t => ln (1 + t)) c (/ (1 + c)).
Proof.
  intros c Hc.
  replace (/ (1 + c)) with (/ (1 + c) * 1) by ring.
  change (fun t => ln (1 + t)) with (comp ln (fun t => 1 + t)).
  apply (derivable_pt_lim_comp (fun t => 1 + t) ln c 1 (/ (1 + c)));
    [ apply affine_d | apply derivable_pt_lim_ln; lra ].
Qed.

Lemma sq_d : forall c, derivable_pt_lim (fun t => t * t) c (1 * c + c * 1).
Proof.
  intro c. apply (derivable_pt_lim_mult (fun t => t) (fun t => t) c 1 1);
    apply derivable_pt_lim_id.
Qed.

Lemma ln_lower_bound : forall x, 0 <= x -> x - x * x / 2 <= ln (1 + x).
Proof.
  intros x Hx. destruct (Rle_lt_or_eq_dec 0 x Hx) as [Hlt | Heq].
  2:{ rewrite <- Heq. rewrite Rplus_0_r, ln_1. lra. }
  set (phi := fun t => (ln (1 + t) - t) + / 2 * (t * t)).
  assert (Hderiv : forall c, 0 <= c <= x -> derivable_pt_lim phi c (c * c / (1 + c))).
  { intros c [Hc0 Hcx]. unfold phi.
    replace (c * c / (1 + c)) with ((/ (1 + c) - 1) + / 2 * (1 * c + c * 1))
      by (field; lra).
    apply derivable_pt_lim_plus.
    - apply derivable_pt_lim_minus; [ apply lnd; lra | apply derivable_pt_lim_id ].
    - apply (derivable_pt_lim_scal (fun t => t * t) (/ 2) c (1 * c + c * 1)). apply sq_d. }
  destruct (MVT_cor2 phi (fun c => c * c / (1 + c)) 0 x Hlt Hderiv) as [c [Hc Hcin]].
  assert (Hphi0 : phi 0 = 0) by (unfold phi; rewrite Rplus_0_r, ln_1; ring).
  assert (Hpos : 0 <= (c * c / (1 + c)) * (x - 0)).
  { apply Rmult_le_pos; [ | lra ].
    unfold Rdiv; apply Rmult_le_pos; [ apply Rle_0_sqr | left; apply Rinv_0_lt_compat; lra ]. }
  rewrite <- Hc, Hphi0 in Hpos. unfold phi in Hpos. lra.
Qed.

(* ----------------------------------------------------------------- *)
Section RealWeierstrass.
Variable s : R.
Hypothesis Hs : 0 < s.

Definition wq (k : nat) : R := (1 + s / INR k) * exp (- (s / INR k)).
Definition rq (k : nat) : R := 1 + s / INR k.
Definition Lg (k : nat) : R := ln (1 + s / INR k) - s / INR k.

Fixpoint Wprod (N : nat) : R := match N with O => 1 | S M => Wprod M * wq (S M) end.
Fixpoint RQ (N : nat) : R := match N with O => 1 | S M => RQ M * rq (S M) end.
Fixpoint LW (N : nat) : R := match N with O => 0 | S M => LW M + Lg (S M) end.
Fixpoint MW (N : nat) : R := match N with O => 0 | S M => MW M + / 2 * (s / INR (S M)) ^ 2 end.

Lemma Snpos : forall n, 0 < INR (S n).
Proof. intro n; apply lt_0_INR; lia. Qed.

Lemma rq_pos : forall n, 0 < rq (S n).
Proof.
  intro n; unfold rq. pose proof (Snpos n).
  assert (0 < s / INR (S n)) by (apply Rdiv_lt_0_compat; [ exact Hs | exact H ]). lra.
Qed.

Lemma wq_expLg : forall n, wq (S n) = exp (Lg (S n)).
Proof.
  intro n. unfold wq, Lg.
  replace (ln (1 + s / INR (S n)) - s / INR (S n))
    with (ln (1 + s / INR (S n)) + (- (s / INR (S n)))) by ring.
  rewrite exp_plus, exp_ln by (pose proof (rq_pos n); unfold rq in *; lra).
  reflexivity.
Qed.

Lemma Wprod_expLW : forall N, Wprod N = exp (LW N).
Proof.
  induction N as [| N IH].
  - simpl. rewrite exp_0. reflexivity.
  - simpl Wprod; simpl LW. rewrite IH, wq_expLg, <- exp_plus. reflexivity.
Qed.

Lemma Wprod_pos : forall N, 0 < Wprod N.
Proof. intro N. rewrite Wprod_expLW. apply exp_pos. Qed.

(* --- bounds on the log-term  Lg (S n) --- *)

Lemma Lg_nonpos : forall n, Lg (S n) <= 0.
Proof.
  intro n. unfold Lg.
  pose proof (Snpos n) as HN.
  assert (Hx : 0 < 1 + s / INR (S n)) by (pose proof (rq_pos n); unfold rq in *; lra).
  pose proof (ln_le_x1 (1 + s / INR (S n)) Hx) as H. lra.
Qed.

Lemma Lg_lower : forall n, - (/ 2 * (s / INR (S n)) ^ 2) <= Lg (S n).
Proof.
  intro n. unfold Lg.
  pose proof (Snpos n) as HN.
  assert (Hx : 0 <= s / INR (S n))
    by (apply Rlt_le, Rdiv_lt_0_compat; [ exact Hs | exact HN ]).
  pose proof (ln_lower_bound (s / INR (S n)) Hx) as H.
  replace ((s / INR (S n)) ^ 2) with (s / INR (S n) * (s / INR (S n))) by ring.
  lra.
Qed.

(* --- the majorant sum  MW N <= s^2 --- *)

Lemma MW_bound : forall N, MW N <= s * s - s * s / INR (S N).
Proof.
  induction N as [| N IH].
  - simpl MW. replace (INR 1) with 1 by (simpl; ring).
    replace (s * s - s * s / 1) with 0 by (field). apply Rle_refl.
  - change (MW (S N)) with (MW N + / 2 * (s / INR (S N)) ^ 2).
    set (a := INR (S N)) in *. assert (Ha1 : 1 <= a) by (unfold a; apply (le_INR 1); lia).
    assert (Ha0 : 0 < a) by lra.
    assert (Hb : INR (S (S N)) = a + 1) by (unfold a; rewrite (S_INR (S N)); ring).
    rewrite Hb.
    assert (Hstep : / 2 * (s / a) ^ 2 <= s * s / a - s * s / (a + 1)).
    { replace (/ 2 * (s / a) ^ 2) with (s * s / (2 * a * a)) by (field; lra).
      replace (s * s / a - s * s / (a + 1)) with (s * s / (a * (a + 1))) by (field; lra).
      unfold Rdiv. apply Rmult_le_compat_l; [ apply Rle_0_sqr | ].
      apply Rinv_le_contravar; [ apply Rmult_lt_0_compat; lra | ].
      replace (2 * a * a) with (a * (2 * a)) by ring.
      apply Rmult_le_compat_l; lra. }
    lra.
Qed.

Lemma MW_le : forall N, MW N <= s * s.
Proof.
  intro N. pose proof (MW_bound N) as H.
  assert (0 <= s * s / INR (S N))
    by (apply Rle_mult_inv_pos; [ apply Rle_0_sqr | apply Snpos ]). lra.
Qed.

(* --- LW is bounded below and decreasing --- *)

Lemma LW_lower : forall N, - MW N <= LW N.
Proof.
  induction N as [| N IH].
  - simpl. lra.
  - change (LW (S N)) with (LW N + Lg (S N)).
    change (MW (S N)) with (MW N + / 2 * (s / INR (S N)) ^ 2).
    pose proof (Lg_lower N) as H. lra.
Qed.

Lemma LW_ge : forall N, - (s * s) <= LW N.
Proof.
  intro N. pose proof (LW_lower N) as H1. pose proof (MW_le N) as H2. lra.
Qed.

(* --- convergence of  LW  (decreasing, bounded below) and of Wprod --- *)

Lemma LW_cv : { L : R | Un_cv LW L }.
Proof.
  destruct (growing_cv (fun N => - LW N)) as [L HL].
  - intro N. simpl LW. pose proof (Lg_nonpos N) as H. lra.
  - exists (s * s). intros r [N ->]. pose proof (LW_ge N) as H. lra.
  - exists (0 - L). apply (Un_cv_ext (fun N => 0 - - LW N) LW (0 - L)).
    + intro N; ring.
    + apply (CV_minus (fun _ => 0) (fun N => - LW N) 0 L (Un_cv_const 0) HL).
Qed.

Definition Winf : R := proj1_sig LW_cv.

Lemma Wprod_cv : Un_cv Wprod (exp Winf).
Proof.
  unfold Winf. destruct LW_cv as [L HL]; simpl.
  apply (Un_cv_ext (fun N => exp (LW N))); [ intro N; symmetry; apply Wprod_expLW | ].
  apply (continuity_seq exp LW L); [ apply derivable_continuous, derivable_exp | exact HL ].
Qed.

(* ----------------------------------------------------------------- *)
(*  the regrouping :  1/G_N = s * Wprod_N * exp(s (H_N - ln N))         *)
(* ----------------------------------------------------------------- *)

(* prodshift s (S N) = s(s+1)...(s+N) = s * N! * prod_{k=1}^N (1+s/k) *)
Lemma prodshift_RQ : forall N, prodshift s (S N) = s * INR (fact N) * RQ N.
Proof.
  induction N as [| N IH].
  - simpl. ring.
  - change (prodshift s (S (S N))) with ((s + INR (S N)) * prodshift s (S N)).
    rewrite IH. change (RQ (S N)) with (RQ N * rq (S N)). unfold rq.
    replace (fact (S N)) with (S N * fact N)%nat by reflexivity.
    rewrite mult_INR. field. apply Rgt_not_eq, Snpos.
Qed.

(* the e^{-s/k} convergence factors regroup against exp(s H_N) *)
Lemma wq_rq_exp : forall n, wq (S n) * exp (s / INR (S n)) = rq (S n).
Proof.
  intro n. unfold wq, rq. rewrite Rmult_assoc, <- exp_plus.
  replace (- (s / INR (S n)) + s / INR (S n)) with 0 by ring.
  rewrite exp_0. ring.
Qed.

(* prod_{k=1}^N (1+s/k) = Wprod_N * exp(s H_N) *)
Lemma RQ_Wprod : forall N, RQ N = Wprod N * exp (s * Harm N).
Proof.
  induction N as [| N IH].
  - change (RQ 0) with 1. change (Wprod 0) with 1.
    assert (Harm 0 = 0) by reflexivity. rewrite H, Rmult_0_r, exp_0. ring.
  - change (RQ (S N)) with (RQ N * rq (S N)).
    change (Wprod (S N)) with (Wprod N * wq (S N)).
    rewrite IH, Harm_rec.
    replace (s * (Harm N + / INR (S N))) with (s * Harm N + s / INR (S N))
      by (unfold Rdiv; ring).
    rewrite exp_plus, <- (wq_rq_exp N). ring.
Qed.

Definition G (N : nat) : R := Rpower (INR N) s * (INR (fact N) / prodshift s (S N)).
Definition recipG (N : nat) : R := prodshift s (S N) / (Rpower (INR N) s * INR (fact N)).

Lemma recip_G_eq : forall N, (1 <= N)%nat ->
  recipG N = s * Wprod N * exp (s * gseq N).
Proof.
  intros N HN. assert (HNN : 0 < INR N) by (apply lt_0_INR; lia).
  unfold recipG. rewrite (prodshift_RQ N), (RQ_Wprod N). unfold gseq.
  replace (s * (Harm N - ln (INR N))) with (s * Harm N + - (s * ln (INR N))) by ring.
  rewrite exp_plus, exp_Ropp.
  assert (HRp : Rpower (INR N) s = exp (s * ln (INR N))) by reflexivity.
  rewrite HRp. field.
  split; [ apply Rgt_not_eq, exp_pos | apply INR_fact_neq_0 ].
Qed.

Lemma GtimesRecip : forall N, G N * recipG N = 1.
Proof.
  intro N. unfold G, recipG. field.
  repeat split;
    solve [ apply Rgt_not_eq, prodshift_pos; exact Hs
          | apply INR_fact_neq_0
          | apply Rgt_not_eq, Rpower_pos ].
Qed.

Lemma Un_cv_shiftS : forall (u : nat -> R) l, Un_cv u l -> Un_cv (fun n => u (S n)) l.
Proof.
  intros u l H eps He. destruct (H eps He) as [N HN]. exists N. intros n Hn.
  apply HN. lia.
Qed.

(* ----------------------------------------------------------------- *)
(*  the real Weierstrass identity  Gam(s) * P(s) = 1                   *)
(* ----------------------------------------------------------------- *)

Definition Pval : R := s * exp Winf * exp (s * gamma).

Theorem real_weierstrass : Gam s Hs * Pval = 1.
Proof.
  (* along the subsequence N = S n *)
  assert (HG : Un_cv (fun n => G (S n)) (Gam s Hs)).
  { apply Un_cv_shiftS. exact (gauss_limit_fact s Hs). }
  assert (HsW : Un_cv (fun n => s * Wprod (S n)) (s * exp Winf)).
  { apply (CV_mult (fun _ => s) (fun n => Wprod (S n)) s (exp Winf)
             (Un_cv_const s) (Un_cv_shiftS Wprod (exp Winf) Wprod_cv)). }
  assert (Hg : Un_cv (fun n => s * gseq (S n)) (s * gamma)).
  { apply (CV_mult (fun _ => s) (fun n => gseq (S n)) s gamma
             (Un_cv_const s) gamma_is_limit). }
  assert (Hexpg : Un_cv (fun n => exp (s * gseq (S n))) (exp (s * gamma))).
  { apply (continuity_seq exp (fun n => s * gseq (S n)) (s * gamma)
             (derivable_continuous exp derivable_exp (s * gamma)) Hg). }
  assert (Hrecip : Un_cv (fun n => recipG (S n)) Pval).
  { unfold Pval. apply (Un_cv_ext (fun n => s * Wprod (S n) * exp (s * gseq (S n)))).
    - intro n; symmetry; apply recip_G_eq; lia.
    - apply (CV_mult (fun n => s * Wprod (S n)) (fun n => exp (s * gseq (S n)))
               (s * exp Winf) (exp (s * gamma)) HsW Hexpg). }
  (* G (S n) * recipG (S n) converges to  Gam s * Pval  and is constantly 1 *)
  assert (Hprod : Un_cv (fun n => G (S n) * recipG (S n)) (Gam s Hs * Pval)).
  { apply (CV_mult (fun n => G (S n)) (fun n => recipG (S n))
             (Gam s Hs) Pval HG Hrecip). }
  assert (Hone : Un_cv (fun n => G (S n) * recipG (S n)) 1).
  { apply (Un_cv_ext (fun _ => 1)); [ intro n; symmetry; apply GtimesRecip | apply Un_cv_const ]. }
  exact (UL_sequence _ _ _ Hprod Hone).
Qed.

Theorem Gam_ne0 : Gam s Hs <> 0.
Proof.
  intro Hc. pose proof real_weierstrass as H. rewrite Hc, Rmult_0_l in H. lra.
Qed.

Theorem Gam_pos : 0 < Gam s Hs.
Proof.
  pose proof (Gam_nonneg s Hs) as Hge. pose proof Gam_ne0 as Hne. lra.
Qed.

Print Assumptions real_weierstrass.

End RealWeierstrass.
