(* ================================================================= *)
(*  CSine.v   (complex sine, for the Gamma reflection formula)          *)
(*                                                                    *)
(*  Csin w = (Cexpf(i w) - Cexpf(-i w)) / (2i),  the entire complex     *)
(*  sine.  Agreement Csin(RtoC t) = RtoC(sin t), and the nonvanishing   *)
(*  Csin(pi w) <> 0 for 0 < Re w < 1 (needed so pi/sin(pi z) is a       *)
(*  legitimate nonzero value in the reflection formula).                *)
(*                                                                    *)
(*  Axioms: standard classical-Reals only.                            *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import ComplexField Cmodulus CexpFull EulerFormula.
Open Scope R_scope.

Definition Ci : C := mkC 0 1.

Definition Csin (w : C) : C :=
  Cmul (Cinv (Cmul (RtoC 2) Ci)) (Cminus (Cexpf (Cmul Ci w)) (Cexpf (Cmul (Copp Ci) w))).

Lemma twoCi_ne0 : Cmul (RtoC 2) Ci <> C0.
Proof.
  intro Hc. apply (f_equal Im) in Hc.
  unfold Cmul, RtoC, Ci, C0 in Hc; cbn [Re Im] in Hc; lra.
Qed.

Lemma Ci_ne0 : Ci <> C0.
Proof. intro Hc. apply (f_equal Im) in Hc. unfold Ci, C0 in Hc; cbn [Im] in Hc; lra. Qed.

Lemma RtoC2_ne0 : RtoC 2 <> C0.
Proof. intro Hc. apply (f_equal Re) in Hc. unfold RtoC, C0 in Hc; cbn [Re] in Hc; lra. Qed.

Lemma Cexpf_C0 : Cexpf C0 = C1.
Proof.
  unfold Cexpf, C0; cbn [Re Im]. rewrite exp_0, Cexp_0.
  unfold RtoC, C1, Cmul; apply Ceq; cbn [Re Im]; ring.
Qed.

Lemma Csin_RtoC : forall t, Csin (RtoC t) = RtoC (sin t).
Proof.
  intro t. unfold Csin.
  assert (H1 : Cexpf (Cmul Ci (RtoC t)) = mkC (cos t) (sin t)).
  { replace (Cmul Ci (RtoC t)) with (mkC 0 t)
      by (apply Ceq; unfold Cmul, Ci, RtoC; cbn [Re Im]; ring).
    unfold Cexpf; cbn [Re Im]. rewrite exp_0.
    unfold Cexp, RtoC, Cmul; apply Ceq; cbn [Re Im]; ring. }
  assert (H2 : Cexpf (Cmul (Copp Ci) (RtoC t)) = mkC (cos t) (- sin t)).
  { replace (Cmul (Copp Ci) (RtoC t)) with (mkC 0 (- t))
      by (apply Ceq; unfold Cmul, Copp, Ci, RtoC; cbn [Re Im]; ring).
    unfold Cexpf; cbn [Re Im]. rewrite exp_0.
    unfold Cexp, RtoC, Cmul; apply Ceq; cbn [Re Im];
      rewrite ?cos_neg, ?sin_neg; ring. }
  rewrite H1, H2.
  replace (Cminus (mkC (cos t) (sin t)) (mkC (cos t) (- sin t)))
     with (Cmul (Cmul (RtoC 2) Ci) (RtoC (sin t)))
     by (apply Ceq; unfold Cmul, Cminus, Cadd, Copp, RtoC, Ci; cbn [Re Im]; ring).
  field. split; [ apply Ci_ne0 | apply RtoC2_ne0 ].
Qed.

(* Cexpf w = C1  ==>  Re w = 0  (from the modulus) *)
Lemma Cexpf_eq1_Re : forall w, Cexpf w = C1 -> Re w = 0.
Proof.
  intros w Hw.
  pose proof (Cmod_Cexpf w) as HM. rewrite Hw in HM.
  assert (HC1 : Cmod C1 = 1)
    by (replace C1 with (RtoC 1) by reflexivity; rewrite Cmod_RtoC; apply Rabs_R1).
  rewrite HC1 in HM. symmetry in HM.
  (* exp (Re w) = 1  ->  Re w = 0 *)
  destruct (Rle_lt_dec (Re w) 0) as [Hle | Hgt].
  - destruct (Rle_lt_or_eq_dec (Re w) 0 Hle) as [Hlt | Heq]; [ | exact Heq ].
    exfalso. pose proof (exp_increasing (Re w) 0 Hlt) as Hei. rewrite exp_0 in Hei. lra.
  - exfalso. pose proof (exp_increasing 0 (Re w) Hgt) as Hei. rewrite exp_0 in Hei. lra.
Qed.

Lemma Csin_pi_ne0 : forall w, 0 < Re w -> Re w < 1 ->
  Csin (Cmul (RtoC PI) w) <> C0.
Proof.
  intros w Hw0 Hw1 Hc.
  set (v := Cmul (RtoC PI) w) in *.
  (* Csin v = 0  ->  Cexpf(i v) = Cexpf(-i v) *)
  assert (Heq : Cexpf (Cmul Ci v) = Cexpf (Cmul (Copp Ci) v)).
  { assert (Hdiff : Cminus (Cexpf (Cmul Ci v)) (Cexpf (Cmul (Copp Ci) v)) = C0).
    { unfold Csin in Hc.
      transitivity (Cmul (Cmul (RtoC 2) Ci)
        (Cmul (Cinv (Cmul (RtoC 2) Ci))
              (Cminus (Cexpf (Cmul Ci v)) (Cexpf (Cmul (Copp Ci) v))))).
      - field. split; [ apply Ci_ne0 | apply RtoC2_ne0 ].
      - rewrite Hc. ring. }
    transitivity (Cadd (Cminus (Cexpf (Cmul Ci v)) (Cexpf (Cmul (Copp Ci) v)))
                       (Cexpf (Cmul (Copp Ci) v))); [ ring | rewrite Hdiff; ring ]. }
  (* Cexpf(2 i v) = 1 *)
  assert (Hsq : Cexpf (Cmul (RtoC 2) (Cmul Ci v)) = C1).
  { replace (Cmul (RtoC 2) (Cmul Ci v)) with (Cadd (Cmul Ci v) (Cmul Ci v))
      by (apply Ceq; unfold Cmul, Cadd, RtoC, Ci; cbn [Re Im]; ring).
    rewrite Cexpf_add. rewrite Heq at 2.
    replace (Cmul (Cexpf (Cmul Ci v)) (Cexpf (Cmul (Copp Ci) v)))
       with (Cexpf (Cadd (Cmul Ci v) (Cmul (Copp Ci) v))) by (rewrite Cexpf_add; reflexivity).
    replace (Cadd (Cmul Ci v) (Cmul (Copp Ci) v)) with C0
      by (apply Ceq; unfold Cmul, Cadd, Copp, C0, Ci; cbn [Re Im]; ring).
    apply Cexpf_C0. }
  (* Re(2 i v) = 0  ->  Im w = 0 *)
  apply Cexpf_eq1_Re in Hsq.
  assert (HIm : Im w = 0).
  { revert Hsq. unfold v, Cmul, RtoC, Ci; cbn [Re Im]. intro H.
    (* Re(2 i (pi w)) = - 2 * PI * Im w = 0 *)
    pose proof PI_RGT_0. nra. }
  (* w = RtoC (Re w), so Csin(pi w) = RtoC(sin(pi Re w)) <> 0 *)
  assert (Hwr : w = RtoC (Re w))
    by (apply Ceq; unfold RtoC; cbn [Re Im]; [ reflexivity | exact HIm ]).
  unfold v in Hc. rewrite Hwr in Hc.
  replace (Cmul (RtoC PI) (RtoC (Re w))) with (RtoC (PI * Re w)) in Hc
    by (rewrite RtoC_mul; reflexivity).
  rewrite Csin_RtoC in Hc.
  apply (f_equal Re) in Hc. unfold RtoC, C0 in Hc; cbn [Re] in Hc.
  assert (0 < sin (PI * Re w)).
  { apply sin_gt_0; [ pose proof PI_RGT_0; nra | ].
    pose proof PI_RGT_0. nra. }
  lra.
Qed.

Print Assumptions Csin_pi_ne0.
