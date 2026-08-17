(* ================================================================= *)
(*  ExpTailIntegral.v  —  Stage 2, brick 4: the exponential dominator.  *)
(*                                                                    *)
(*  The closed-form improper integral of edk u = e^{-pi u} on [1,inf):  *)
(*                                                                    *)
(*    edk_improper : ImproperCv1 edk edk_int (e^{-pi} / pi)            *)
(*    edk_pint     : int_1^A edk = -1/pi e^{-pi A} + 1/pi e^{-pi}      *)
(*                                                                    *)
(*  With Psi_upper1 (Stage 1), wker(1/2) u = u^{-3/4} Psi(u) <=         *)
(*  Psi(u) <= e^{-pi u}/(1-e^{-pi}) for u>=1, so a constant multiple of *)
(*  edk dominates |Re(wkerC(1/2+it) .)|.  Feeding that + edk_improper   *)
(*  into MellinTailBound.improper_tail_le turns the truncation error of *)
(*  Re TC(1/2+it) at cutoff X into the CLOSED FORM  C . e^{-pi X}/pi.   *)
(*                                                                    *)
(*  Proof mirrors MellinElem.eker (FTC via antiderivative, then the     *)
(*  n = INR(S k) limit).  Axioms: standard classical-Reals only.       *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra.
Require Import ImproperCv1 MellinElem CImproperIntegral ContinuousCoV LogGeomSeries.
Open Scope R_scope.

Definition edk (u : R) : R := exp (- (PI * u)).

Lemma edk_pos : forall u, 0 < edk u.
Proof. intro u; unfold edk; apply exp_pos. Qed.

(* derivative of the antiderivative F u = -1/pi e^{-pi u} is edk *)
Lemma edk_deriv : forall x,
  derivable_pt_lim (fun y => - / PI * exp (- (PI * y))) x (edk x).
Proof.
  intro x. pose proof PI_RGT_0 as HPI.
  assert (Hin : derivable_pt_lim (fun y => - (PI * y)) x (- PI)).
  { replace (- PI) with (- (PI * 1)) by ring.
    apply derivable_pt_lim_opp.
    apply (derivable_pt_lim_scal (fun y => y) PI x 1 (derivable_pt_lim_id x)). }
  assert (Hexp : derivable_pt_lim (fun y => exp (- (PI * y))) x
                   (exp (- (PI * x)) * (- PI))).
  { apply (derivable_pt_lim_comp (fun y => - (PI * y)) exp x (- PI) (exp (- (PI * x))));
      [ exact Hin | apply derivable_pt_lim_exp ]. }
  apply (derivable_pt_lim_scal (fun y => exp (- (PI * y))) (- / PI) x
           (exp (- (PI * x)) * (- PI))) in Hexp.
  replace (edk x) with (- / PI * (exp (- (PI * x)) * - PI))
    by (unfold edk; field; lra).
  exact Hexp.
Qed.

Lemma edk_deriv_self : forall x, derivable_pt_lim edk x (edk x * - PI).
Proof.
  intro x. unfold edk.
  assert (Hin : derivable_pt_lim (fun y => - (PI * y)) x (- PI)).
  { replace (- PI) with (- (PI * 1)) by ring.
    apply derivable_pt_lim_opp.
    apply (derivable_pt_lim_scal (fun y => y) PI x 1 (derivable_pt_lim_id x)). }
  apply (derivable_pt_lim_comp (fun y => - (PI * y)) exp x (- PI) (exp (- (PI * x))));
    [ exact Hin | apply derivable_pt_lim_exp ].
Qed.

Lemma cont_edk : continuity edk.
Proof.
  intro x. apply (derivable_continuous_pt edk x).
  exists (edk x * - PI). apply edk_deriv_self.
Qed.

Lemma edk_int : forall x y, Riemann_integrable edk x y.
Proof.
  intros x y; destruct (Rle_dec x y) as [H | H].
  - apply continuity_implies_RiemannInt; [ exact H | intros u _; apply cont_edk ].
  - apply RiemannInt_P1; apply continuity_implies_RiemannInt;
      [ lra | intros u _; apply cont_edk ].
Qed.

Lemma edk_pint : forall A, 1 <= A ->
  pint1 edk edk_int A = (- / PI * exp (- (PI * A))) - (- / PI * exp (- (PI * 1))).
Proof.
  intros A HA; unfold pint1.
  set (F := fun x => - / PI * exp (- (PI * x))).
  assert (Hanti : antiderivative edk F 1 A).
  { split; [ | exact HA ]. intros x [Hx1 HxA].
    exists (exist (fun l => derivable_pt_lim F x l) (edk x) (edk_deriv x)).
    reflexivity. }
  rewrite (FTC_antideriv edk F 1 A HA (fun x _ => cont_edk x) (edk_int 1 A) Hanti).
  unfold F; reflexivity.
Qed.

(* e^{-pi n} = (e^{-pi})^n *)
Lemma exp_neg_pow : forall n, exp (- (PI * INR n)) = (exp (- PI)) ^ n.
Proof.
  induction n as [| n IH].
  - simpl; rewrite Rmult_0_r, Ropp_0, exp_0; reflexivity.
  - rewrite S_INR.
    replace (- (PI * (INR n + 1))) with ((- (PI * INR n)) + (- PI)) by ring.
    rewrite exp_plus, IH; simpl; ring.
Qed.

Lemma exp_neg_PI_lt1 : exp (- PI) < 1.
Proof. rewrite <- exp_0; apply exp_increasing; pose proof PI_RGT_0; lra. Qed.

Lemma edk_seq_cv0 : Un_cv (fun k => exp (- (PI * INR (S k)))) 0.
Proof.
  apply (Un_cv_ext (fun k => exp (- PI) * (exp (- PI)) ^ k)).
  - intro k; rewrite exp_neg_pow; simpl; ring.
  - replace 0 with (exp (- PI) * 0) by ring.
    apply CV_mult; [ apply Un_cv_const | ].
    apply pow_cv0. rewrite Rabs_right;
      [ apply exp_neg_PI_lt1 | apply Rle_ge; apply Rlt_le; apply exp_pos ].
Qed.

Theorem edk_improper : ImproperCv1 edk edk_int (exp (- PI) / PI).
Proof.
  pose proof PI_RGT_0 as HPI.
  apply (improper_welldef1 edk edk_int (fun x _ => Rlt_le _ _ (edk_pos x))
           (fun k => INR (S k)) (exp (- PI) / PI)).
  - intro k; rewrite S_INR; pose proof (pos_INR k); lra.
  - apply cv_infty_Sn.
  - apply (Un_cv_ext (fun k => (- / PI * exp (- (PI * INR (S k))))
                             - (- / PI * exp (- (PI * 1))))).
    + intro k; symmetry; apply edk_pint; rewrite S_INR; pose proof (pos_INR k); lra.
    + replace (exp (- PI) / PI) with (- / PI * 0 - (- / PI * exp (- (PI * 1))))
        by (rewrite Rmult_1_r; field; lra).
      apply CV_minus; [ | apply Un_cv_const ].
      apply (CV_mult (fun _ => - / PI) (fun k => exp (- (PI * INR (S k)))) (- / PI) 0);
        [ apply Un_cv_const | apply edk_seq_cv0 ].
Qed.

Print Assumptions edk_improper.
