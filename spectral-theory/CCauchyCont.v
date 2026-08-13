(* ================================================================= *)
(*  CCauchyCont.v  (identity-theorem plan, FE chain brick 2 — core)    *)
(*                                                                    *)
(*  Global continuity of the clamped Cauchy power integral in the       *)
(*  pole parameter.  This file: the reusable algebraic core -- a        *)
(*  Lipschitz bound on complex powers,                                 *)
(*     |a^{n} - b^{n}| <= n . M^{n-1} . |a - b|   (|a|,|b| <= M),        *)
(*  and the induced Lipschitz bound on the inverse-power kernel         *)
(*     |1/a^n - 1/b^n| <= n . M^{n-1} / d^{2n} . |a - b|                *)
(*  (|a|,|b| in [d, M]), which drives the ML continuity estimate.       *)
(*                                                                    *)
(*  Axioms: standard classical-Reals only.                            *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import ComplexField Cmodulus CDeriv RootsOfUnity CTaylor CWindingOffCenter.
Open Scope R_scope.

(* Cmod of a power (local) *)
Lemma Cmod_Cpow : forall a k, Cmod (Cpow a k) = (Cmod a) ^ k.
Proof.
  intros a k; induction k as [|k IH]; cbn [Cpow pow];
    [ apply Cmod_C1 | rewrite Cmod_mul, IH; reflexivity ].
Qed.

Lemma cpow_step : forall (a b P Q : C),
  Cminus (Cmul a P) (Cmul b Q) = Cadd (Cmul a (Cminus P Q)) (Cmul (Cminus a b) Q).
Proof. intros; ring. Qed.

Lemma rstep : forall M Mm I C : R,
  M * (I * Mm * C) + C * (M * Mm) = (I + 1) * (M * Mm) * C.
Proof. intros; ring. Qed.

Lemma rcomm : forall X C iD : R, X * C * iD = X * iD * C.
Proof. intros; ring. Qed.

(* the power Lipschitz bound *)
Lemma Cpow_diff_bound : forall (a b : C) (M : R) (m : nat),
  Cmod a <= M -> Cmod b <= M ->
  Cmod (Cminus (Cpow a (S m)) (Cpow b (S m))) <= INR (S m) * M ^ m * Cmod (Cminus a b).
Proof.
  intros a b M m Ha Hb.
  assert (HM : 0 <= M) by (eapply Rle_trans; [ apply Cmod_nonneg | exact Ha ]).
  induction m as [|m IH].
  - cbn [Cpow]. replace (Cminus (Cmul a C1) (Cmul b C1)) with (Cminus a b) by ring.
    simpl. rewrite Rmult_1_r, Rmult_1_l. lra.
  - assert (Hstep : Cminus (Cpow a (S (S m))) (Cpow b (S (S m)))
      = Cadd (Cmul a (Cminus (Cpow a (S m)) (Cpow b (S m))))
             (Cmul (Cminus a b) (Cpow b (S m)))).
    { change (Cpow a (S (S m))) with (Cmul a (Cpow a (S m))).
      change (Cpow b (S (S m))) with (Cmul b (Cpow b (S m))).
      apply cpow_step. }
    rewrite Hstep.
    eapply Rle_trans; [ apply Cmod_triangle | ].
    rewrite Cmod_mul, Cmod_mul, Cmod_Cpow.
    (* Cmod a * Cmod(diff) + Cmod(a-b) * Cmod b ^ (S m)
         <= M * (INR(S m) M^m |a-b|) + |a-b| * M^(S m) *)
    apply Rle_trans with
      (M * (INR (S m) * M ^ m * Cmod (Cminus a b)) + Cmod (Cminus a b) * M ^ S m).
    + apply Rplus_le_compat.
      * apply Rmult_le_compat; [ apply Cmod_nonneg | apply Cmod_nonneg | exact Ha | exact IH ].
      * apply Rmult_le_compat_l; [ apply Cmod_nonneg | ].
        apply pow_incr; split; [ apply Cmod_nonneg | exact Hb ].
    + (* = INR(S(S m)) M^(S m) |a-b| *)
      rewrite (S_INR (S m)). simpl (M ^ S m). apply Req_le. apply rstep.
Qed.

(* the inverse-power kernel is Lipschitz where the base is bounded below *)
Lemma Cinv_pow_diff_bound : forall (a b : C) (d M : R) (m : nat),
  0 < d -> d <= Cmod a -> d <= Cmod b -> Cmod a <= M -> Cmod b <= M ->
  Cmod (Cminus (Cinv (Cpow a (S m))) (Cinv (Cpow b (S m))))
  <= INR (S m) * M ^ m / (d ^ S m * d ^ S m) * Cmod (Cminus a b).
Proof.
  intros a b d M m Hd Hda Hdb HaM HbM.
  assert (Hane : a <> C0)
    by (intro Hc; rewrite Hc, (proj2 (Cmod0 C0) eq_refl) in Hda; lra).
  assert (Hbne : b <> C0)
    by (intro Hc; rewrite Hc, (proj2 (Cmod0 C0) eq_refl) in Hdb; lra).
  assert (Hapow : Cpow a (S m) <> C0) by (apply Cpow_ne0; exact Hane).
  assert (Hbpow : Cpow b (S m) <> C0) by (apply Cpow_ne0; exact Hbne).
  (* 1/a^n - 1/b^n = (b^n - a^n)/(a^n b^n) *)
  assert (Heq : Cminus (Cinv (Cpow a (S m))) (Cinv (Cpow b (S m)))
    = Cmul (Cminus (Cpow b (S m)) (Cpow a (S m)))
           (Cinv (Cmul (Cpow a (S m)) (Cpow b (S m))))).
  { field; split; assumption. }
  rewrite Heq, Cmod_mul.
  assert (HXne : Cmul (Cpow a (S m)) (Cpow b (S m)) <> C0)
    by (apply Cmul_ne0; assumption).
  rewrite (Cmod_inv _ HXne), Cmod_mul, !Cmod_Cpow.
  (* Cmod(b^n - a^n) * / (|a|^{Sm} |b|^{Sm}) <= (n M^{m} |a-b|) / (d^{Sm} d^{Sm}) *)
  assert (Hdiff : Cmod (Cminus (Cpow b (S m)) (Cpow a (S m)))
                  <= INR (S m) * M ^ m * Cmod (Cminus a b)).
  { replace (Cmod (Cminus a b)) with (Cmod (Cminus b a))
      by (rewrite <- Cmod_opp; f_equal; ring).
    apply Cpow_diff_bound; assumption. }
  assert (Hdpos : 0 < d ^ S m) by (apply pow_lt; exact Hd).
  assert (Hden : 0 < Cmod a ^ S m * Cmod b ^ S m)
    by (apply Rmult_lt_0_compat; apply pow_lt; lra).
  apply Rle_trans with
    (INR (S m) * M ^ m * Cmod (Cminus a b) * / (d ^ S m * d ^ S m)).
  - apply Rmult_le_compat.
    + apply Cmod_nonneg.
    + left; apply Rinv_0_lt_compat; exact Hden.
    + exact Hdiff.
    + apply Rinv_le_contravar; [ apply Rmult_lt_0_compat; exact Hdpos | ].
      apply Rmult_le_compat;
        [ left; exact Hdpos | left; exact Hdpos
        | apply pow_incr; split; [ lra | exact Hda ]
        | apply pow_incr; split; [ lra | exact Hdb ] ].
  - unfold Rdiv. apply Req_le. apply rcomm.
Qed.

Print Assumptions Cpow_diff_bound.
Print Assumptions Cinv_pow_diff_bound.
