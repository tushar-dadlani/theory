(* ================================================================= *)
(*  ThetaTailSharp.v  --  a SHARP two-sided enclosure of Psi.           *)
(*                                                                    *)
(*    Psi_sharp : 0 < t ->                                            *)
(*      e^{-pi t} + e^{-4 pi t}                                        *)
(*        <= Psi t <=                                                  *)
(*      e^{-pi t} + e^{-4 pi t} + e^{-9 pi t} / (1 - e^{-pi t})        *)
(*                                                                    *)
(*  ThetaTailBounds.Psi_enclosure traps Psi between e^{-pi t} and      *)
(*  e^{-pi t}/(1 - e^{-pi}), a band of RELATIVE width                  *)
(*  1/(1 - e^{-pi}) - 1 = 4.52% at every t.  That is about 20x too     *)
(*  coarse for the sign change of xir: the (1/4 + t^2) ~ 196           *)
(*  amplification in XirIntegralReduction.xir_reduction' means Re TC   *)
(*  must be pinned to roughly 0.2% relative.                           *)
(*                                                                    *)
(*  Keeping ONE more term fixes it outright.  The residual             *)
(*  sum_{n>=3} e^{-pi n^2 t} is bounded using n^2 >= 9 + (n-3), giving *)
(*  e^{-9 pi t}/(1 - e^{-pi t}); at t = 1 that is 5.4e-13 against a    *)
(*  value of 4.3e-2, i.e. a relative width of 1.3e-11 -- eleven orders *)
(*  better than needed, from one extra term.  The gain is so large     *)
(*  because the exponents are QUADRATIC: the first neglected term      *)
(*  drops from e^{-4 pi t} to e^{-9 pi t}, not by a constant factor.   *)
(*                                                                    *)
(*  Axiom-clean.                                                      *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import JacobiTheta RiemannPsi ThetaTailBounds.
Open Scope R_scope.

Lemma Un_cv_const' : forall c : R, Un_cv (fun _ => c) c.
Proof.
  intros c eps Heps. exists 0%nat. intros n _. unfold R_dist.
  replace (c - c) with 0 by ring. rewrite Rabs_R0. exact Heps.
Qed.

Section Sharp.
Variable t : R.
Hypothesis Ht : 0 < t.

(* ----------------------------------------------------------------- *)
(*  A.  the tail terms, dominated by e^{-9 pi t} times a geometric     *)
(* ----------------------------------------------------------------- *)
Lemma theta_term_tail_le : forall k,
  theta_term t (2 + k) <= exp (- (9 * (PI * t))) * exp (- (PI * t)) ^ k.
Proof.
  intro k. unfold theta_term.
  assert (HPI : 0 < PI) by apply PI_RGT_0.
  assert (Hk : INR (S (2 + k)) = INR k + 3)
    by (rewrite !S_INR, plus_INR; simpl; ring).
  rewrite Hk.
  assert (Hk0 : 0 <= INR k) by apply pos_INR.
  (* (k+3)^2 >= 9 + k *)
  assert (Hsq : 9 + INR k <= (INR k + 3) ^ 2) by nra.
  apply Rle_trans with (exp (- (PI * (9 + INR k) * t))).
  - apply exp_le_mono. apply Ropp_le_contravar.
    apply Rmult_le_compat_r; [ lra | ].
    apply Rmult_le_compat_l; [ lra | exact Hsq ].
  - (* e^{-pi(9+k)t} = e^{-9 pi t} * (e^{-pi t})^k *)
    replace (- (PI * (9 + INR k) * t))
      with (- (9 * (PI * t)) + INR k * (- (PI * t))) by ring.
    rewrite exp_plus, <- exp_INR_pow. apply Rle_refl.
Qed.

(* ----------------------------------------------------------------- *)
(*  B.  the partial sums, sharply                                      *)
(* ----------------------------------------------------------------- *)
Lemma theta_partial_sharp : forall N,
  theta_partial t N
  <= theta_partial t 1 + exp (- (9 * (PI * t))) / (1 - exp (- (PI * t))).
Proof.
  intro N.
  assert (Hq1 : exp (- (PI * t)) < 1) by (apply theta_ratio_lt1; exact Ht).
  assert (Hq0 : 0 <= exp (- (PI * t))) by (left; apply exp_pos).
  assert (Hgeo : 0 <= exp (- (9 * (PI * t))) / (1 - exp (- (PI * t)))).
  { apply Rle_mult_inv_pos; [ left; apply exp_pos | lra ]. }
  destruct (Nat.le_gt_cases N 1) as [Hle | Hgt].
  - (* N <= 1 : monotonicity of the partial sums *)
    assert (Hmono : theta_partial t N <= theta_partial t 1).
    { destruct N as [| [| N]].
      - unfold theta_partial; cbn [sum_f_R0].
        pose proof (exp_pos (- (PI * INR 2 ^ 2 * t))); unfold theta_term; lra.
      - apply Rle_refl.
      - exfalso; lia. }
    lra.
  - (* N >= 2 : split off the first two terms *)
    unfold theta_partial.
    rewrite (tech2 (theta_term t) 1 N Hgt).
    apply Rplus_le_compat_l.
    eapply Rle_trans.
    + apply sum_f_R0_le. intro i. apply theta_term_tail_le.
    + assert (E : sum_f_R0 (fun k => exp (- (9 * (PI * t)))
                    * exp (- (PI * t)) ^ k) (N - 2)
                = exp (- (9 * (PI * t)))
                  * sum_f_R0 (fun k => exp (- (PI * t)) ^ k) (N - 2)).
      { rewrite (scal_sum (fun k => exp (- (PI * t)) ^ k) (N - 2)
                   (exp (- (9 * (PI * t))))).
        apply sum_eq; intros i _; ring. }
      rewrite E.
      assert (Hgp : sum_f_R0 (fun k => exp (- (PI * t)) ^ k) (N - 2)
                 <= / (1 - exp (- (PI * t))))
        by (apply geom_partial_bound; assumption).
      unfold Rdiv.
      apply Rmult_le_compat_l; [ left; apply exp_pos | exact Hgp ].
Qed.

End Sharp.

(* ----------------------------------------------------------------- *)
(*  C.  THE SHARP ENCLOSURE                                            *)
(* ----------------------------------------------------------------- *)
Theorem Psi_sharp : forall t (Ht : 0 < t),
  exp (- (PI * t)) + exp (- (PI * 4 * t)) <= Psi t
  <= exp (- (PI * t)) + exp (- (PI * 4 * t))
     + exp (- (9 * (PI * t))) / (1 - exp (- (PI * t))).
Proof.
  intros t Ht.
  assert (Etp : theta_partial t 1 = exp (- (PI * t)) + exp (- (PI * 4 * t))).
  { unfold theta_partial, theta_term; cbn [sum_f_R0].
    f_equal; f_equal; simpl INR; ring. }
  rewrite (Psi_val t Ht). unfold theta.
  destruct (theta_half_converges t Ht) as [L HL]; simpl.
  split.
  - assert (Hle : theta_partial t 1 <= L)
      by (apply (growing_ineq (theta_partial t));
          [ apply theta_partial_growing | exact HL ]).
    rewrite Etp in Hle. lra.
  - assert (Hub : L <= theta_partial t 1
                   + exp (- (9 * (PI * t))) / (1 - exp (- (PI * t)))).
    { eapply Rle_cv_lim.
      - intro n. apply theta_partial_sharp; exact Ht.
      - exact HL.
      - apply Un_cv_const'. }
    rewrite Etp in Hub. lra.
Qed.

Print Assumptions theta_term_tail_le.
Print Assumptions theta_partial_sharp.
Print Assumptions Psi_sharp.
