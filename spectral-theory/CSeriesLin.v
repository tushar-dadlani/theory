(* ================================================================= *)
(*  CSeriesLin.v  —  linearity of the complex series limit.            *)
(*                                                                    *)
(*  Cseries_cv_add / _minus / _cscal, the Sigma-analogue of the CImp   *)
(*  linearity lemmas, all componentwise via stdlib CV_plus/CV_minus/   *)
(*  CV_mult and plus_sum/minus_sum/scal_sum.  These package the series  *)
(*  algebra needed to assemble S(s+h)-S(s)-D*h as a single series for   *)
(*  the differentiation-under-the-sum.  Axiom-clean.                   *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra FunctionalExtensionality.
Require Import ComplexField Cmodulus CSeries.
Open Scope R_scope.

Lemma Un_cv_const : forall c : R, Un_cv (fun _ => c) c.
Proof.
  intros c eps Heps; exists 0%nat; intros n _; unfold R_dist.
  replace (c - c) with 0 by ring; rewrite Rabs_R0; exact Heps.
Qed.

Lemma Cseries_cv_add : forall a b A B,
  Cseries_cv a A -> Cseries_cv b B ->
  Cseries_cv (fun n => Cadd (a n) (b n)) (Cadd A B).
Proof.
  intros a b A B HA HB.
  rewrite Cseries_cv_comp in HA, HB.
  destruct HA as [HAr HAi], HB as [HBr HBi].
  apply Cseries_cv_comp; split.
  - replace (Re (Cadd A B)) with (Re A + Re B) by (unfold Cadd; cbn [Re]; reflexivity).
    replace (sum_f_R0 (fun n => Re (Cadd (a n) (b n))))
      with (fun N => sum_f_R0 (fun n => Re (a n)) N + sum_f_R0 (fun n => Re (b n)) N).
    + apply CV_plus; assumption.
    + apply functional_extensionality; intro N; rewrite <- plus_sum;
        apply sum_eq; intros i _; unfold Cadd; cbn [Re]; reflexivity.
  - replace (Im (Cadd A B)) with (Im A + Im B) by (unfold Cadd; cbn [Im]; reflexivity).
    replace (sum_f_R0 (fun n => Im (Cadd (a n) (b n))))
      with (fun N => sum_f_R0 (fun n => Im (a n)) N + sum_f_R0 (fun n => Im (b n)) N).
    + apply CV_plus; assumption.
    + apply functional_extensionality; intro N; rewrite <- plus_sum;
        apply sum_eq; intros i _; unfold Cadd; cbn [Im]; reflexivity.
Qed.

Lemma Cseries_cv_minus : forall a b A B,
  Cseries_cv a A -> Cseries_cv b B ->
  Cseries_cv (fun n => Cminus (a n) (b n)) (Cminus A B).
Proof.
  intros a b A B HA HB.
  rewrite Cseries_cv_comp in HA, HB.
  destruct HA as [HAr HAi], HB as [HBr HBi].
  apply Cseries_cv_comp; split.
  - replace (Re (Cminus A B)) with (Re A - Re B) by (unfold Cminus; cbn [Re]; reflexivity).
    replace (sum_f_R0 (fun n => Re (Cminus (a n) (b n))))
      with (fun N => sum_f_R0 (fun n => Re (a n)) N - sum_f_R0 (fun n => Re (b n)) N).
    + apply CV_minus; assumption.
    + apply functional_extensionality; intro N; rewrite <- minus_sum;
        apply sum_eq; intros i _; unfold Cminus; cbn [Re]; reflexivity.
  - replace (Im (Cminus A B)) with (Im A - Im B) by (unfold Cminus; cbn [Im]; reflexivity).
    replace (sum_f_R0 (fun n => Im (Cminus (a n) (b n))))
      with (fun N => sum_f_R0 (fun n => Im (a n)) N - sum_f_R0 (fun n => Im (b n)) N).
    + apply CV_minus; assumption.
    + apply functional_extensionality; intro N; rewrite <- minus_sum;
        apply sum_eq; intros i _; unfold Cminus; cbn [Im]; reflexivity.
Qed.

Lemma Cseries_cv_cscal : forall c a A,
  Cseries_cv a A -> Cseries_cv (fun n => Cmul c (a n)) (Cmul c A).
Proof.
  intros c a A HA.
  rewrite Cseries_cv_comp in HA; destruct HA as [HAr HAi].
  apply Cseries_cv_comp; split.
  - replace (Re (Cmul c A)) with (Re c * Re A - Im c * Im A)
      by (unfold Cmul; cbn [Re]; reflexivity).
    replace (sum_f_R0 (fun n => Re (Cmul c (a n))))
      with (fun N => Re c * sum_f_R0 (fun n => Re (a n)) N
                     - Im c * sum_f_R0 (fun n => Im (a n)) N).
    + apply CV_minus; apply CV_mult; try apply Un_cv_const; assumption.
    + apply functional_extensionality; intro N.
      rewrite (scal_sum (fun n => Re (a n)) N (Re c)),
              (scal_sum (fun n => Im (a n)) N (Im c)), <- minus_sum.
      apply sum_eq; intros i _; unfold Cmul; cbn [Re]; ring.
  - replace (Im (Cmul c A)) with (Re c * Im A + Im c * Re A)
      by (unfold Cmul; cbn [Im]; reflexivity).
    replace (sum_f_R0 (fun n => Im (Cmul c (a n))))
      with (fun N => Re c * sum_f_R0 (fun n => Im (a n)) N
                     + Im c * sum_f_R0 (fun n => Re (a n)) N).
    + apply CV_plus; apply CV_mult; try apply Un_cv_const; assumption.
    + apply functional_extensionality; intro N.
      rewrite (scal_sum (fun n => Im (a n)) N (Re c)),
              (scal_sum (fun n => Re (a n)) N (Im c)), <- plus_sum.
      apply sum_eq; intros i _; unfold Cmul; cbn [Im]; ring.
Qed.

Print Assumptions Cseries_cv_add.
Print Assumptions Cseries_cv_cscal.

(* ================================================================= *)
(*  END CSeriesLin.v.                                                  *)
(* ================================================================= *)
