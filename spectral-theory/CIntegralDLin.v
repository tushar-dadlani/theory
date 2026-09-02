(* ================================================================= *)
(*  CIntegralDLin.v  --  linearity for CintfD.                         *)
(*                                                                    *)
(*  Deferred from E1 because its exact shape was unclear.  E5 fixes    *)
(*  it: proving g_T holomorphic IN z needs the increment identity      *)
(*      lint(z+h) - lint z - h*ldint z                                 *)
(*  under the integral, i.e. additivity plus complex-scalar multiples. *)
(*                                                                    *)
(*  Everything reduces to one real lemma, RI_lincomb_val, since the    *)
(*  real and imaginary parts of  c * f  are each 2-term real linear    *)
(*  combinations of  Re f  and  Im f.                                  *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import ComplexField Cmodulus CIntegral2 PsiRIntegrable CIntegralD.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  Real scalar multiples and 2-term combinations.                    *)
(* ----------------------------------------------------------------- *)

Lemma RI_scal_int : forall (g : R -> R) a b (l : R),
  Riemann_integrable g a b -> a <= b ->
  Riemann_integrable (fun x => l * g x) a b.
Proof.
  intros g a b l pr Hab.
  apply (Riemann_integrable_ext_open (fun x => l * g x)
           (fun x => fct_cte 0 x + l * g x) a b Hab).
  - intros t Ht. unfold fct_cte. ring.
  - apply RiemannInt_P10. apply RiemannInt_P14. exact pr.
Qed.

Lemma RI_scal_val : forall (g : R -> R) a b (l : R)
  (pr : Riemann_integrable g a b)
  (pr' : Riemann_integrable (fun x => l * g x) a b), a <= b ->
  RiemannInt pr' = l * RiemannInt pr.
Proof.
  intros g a b l pr pr' Hab.
  assert (pr3 : Riemann_integrable (fun x => fct_cte 0 x + l * g x) a b)
    by (apply RiemannInt_P10; [ apply RiemannInt_P14 | exact pr ]).
  assert (Heq : RiemannInt pr' = RiemannInt pr3).
  { apply (RiemannInt_P18 pr' pr3 Hab).
    intros x Hx. unfold fct_cte. ring. }
  rewrite Heq, (RiemannInt_P13 (RiemannInt_P14 a b 0) pr pr3),
          (RiemannInt_P15 (RiemannInt_P14 a b 0)).
  ring.
Qed.

Lemma RI_lincomb_val : forall (u v : R -> R) a b (l1 l2 : R)
  (pr1 : Riemann_integrable u a b) (pr2 : Riemann_integrable v a b)
  (pr : Riemann_integrable (fun x => l1 * u x + l2 * v x) a b), a <= b ->
  RiemannInt pr = l1 * RiemannInt pr1 + l2 * RiemannInt pr2.
Proof.
  intros u v a b l1 l2 pr1 pr2 pr Hab.
  assert (pru : Riemann_integrable (fun x => l1 * u x) a b)
    by (apply RI_scal_int; assumption).
  assert (pr3 : Riemann_integrable (fun x => l1 * u x + l2 * v x) a b)
    by (apply RiemannInt_P10; [ exact pru | exact pr2 ]).
  assert (Heq : RiemannInt pr = RiemannInt pr3) by apply RiemannInt_P5.
  rewrite Heq, (RiemannInt_P13 pru pr2 pr3), (RI_scal_val u a b l1 pr1 pru Hab).
  reflexivity.
Qed.

(* ----------------------------------------------------------------- *)
(*  CintfD linearity.                                                 *)
(* ----------------------------------------------------------------- *)

Theorem CintfD_add : forall (f g : R -> C) a b prFRe prFIm prGRe prGIm prSRe prSIm,
  a <= b ->
  CintfD (fun t => Cadd (f t) (g t)) a b prSRe prSIm
  = Cadd (CintfD f a b prFRe prFIm) (CintfD g a b prGRe prGIm).
Proof.
  intros f g a b prFRe prFIm prGRe prGIm prSRe prSIm Hab.
  assert (HRe : RiemannInt prSRe = RiemannInt prFRe + RiemannInt prGRe).
  { assert (pr : Riemann_integrable (fun x => 1 * Re (f x) + 1 * Re (g x)) a b)
      by (apply (Riemann_integrable_ext_open _ (fun x => Re (Cadd (f x) (g x)))
                   a b Hab); [ intros t Ht; cbn [Re Cadd]; ring | exact prSRe ]).
    transitivity (RiemannInt pr).
    - apply (RiemannInt_P18 prSRe pr Hab). intros x Hx; cbn [Re Cadd]; ring.
    - rewrite (RI_lincomb_val _ _ a b 1 1 prFRe prGRe pr Hab); ring. }
  assert (HIm : RiemannInt prSIm = RiemannInt prFIm + RiemannInt prGIm).
  { assert (pr : Riemann_integrable (fun x => 1 * Im (f x) + 1 * Im (g x)) a b)
      by (apply (Riemann_integrable_ext_open _ (fun x => Im (Cadd (f x) (g x)))
                   a b Hab); [ intros t Ht; cbn [Im Cadd]; ring | exact prSIm ]).
    transitivity (RiemannInt pr).
    - apply (RiemannInt_P18 prSIm pr Hab). intros x Hx; cbn [Im Cadd]; ring.
    - rewrite (RI_lincomb_val _ _ a b 1 1 prFIm prGIm pr Hab); ring. }
  unfold CintfD, Cadd; apply Ceq; cbn [Re Im]; assumption.
Qed.

Theorem CintfD_sub : forall (f g : R -> C) a b prFRe prFIm prGRe prGIm prSRe prSIm,
  a <= b ->
  CintfD (fun t => Cminus (f t) (g t)) a b prSRe prSIm
  = Cminus (CintfD f a b prFRe prFIm) (CintfD g a b prGRe prGIm).
Proof.
  intros f g a b prFRe prFIm prGRe prGIm prSRe prSIm Hab.
  assert (HRe : RiemannInt prSRe = RiemannInt prFRe - RiemannInt prGRe).
  { assert (pr : Riemann_integrable (fun x => 1 * Re (f x) + (-1) * Re (g x)) a b)
      by (apply (Riemann_integrable_ext_open _ (fun x => Re (Cminus (f x) (g x)))
                   a b Hab); [ intros t Ht; cbn [Re Cminus]; ring | exact prSRe ]).
    transitivity (RiemannInt pr).
    - apply (RiemannInt_P18 prSRe pr Hab). intros x Hx; cbn [Re Cminus]; ring.
    - rewrite (RI_lincomb_val _ _ a b 1 (-1) prFRe prGRe pr Hab); ring. }
  assert (HIm : RiemannInt prSIm = RiemannInt prFIm - RiemannInt prGIm).
  { assert (pr : Riemann_integrable (fun x => 1 * Im (f x) + (-1) * Im (g x)) a b)
      by (apply (Riemann_integrable_ext_open _ (fun x => Im (Cminus (f x) (g x)))
                   a b Hab); [ intros t Ht; cbn [Im Cminus]; ring | exact prSIm ]).
    transitivity (RiemannInt pr).
    - apply (RiemannInt_P18 prSIm pr Hab). intros x Hx; cbn [Im Cminus]; ring.
    - rewrite (RI_lincomb_val _ _ a b 1 (-1) prFIm prGIm pr Hab); ring. }
  unfold CintfD, Cminus; apply Ceq; cbn [Re Im]; assumption.
Qed.

Theorem CintfD_cmul_l : forall (c : C) (f : R -> C) a b prFRe prFIm prSRe prSIm,
  a <= b ->
  CintfD (fun t => Cmul c (f t)) a b prSRe prSIm
  = Cmul c (CintfD f a b prFRe prFIm).
Proof.
  intros c f a b prFRe prFIm prSRe prSIm Hab.
  assert (HRe : RiemannInt prSRe
                = Re c * RiemannInt prFRe - Im c * RiemannInt prFIm).
  { assert (pr : Riemann_integrable
                   (fun x => Re c * Re (f x) + (- Im c) * Im (f x)) a b)
      by (apply (Riemann_integrable_ext_open _ (fun x => Re (Cmul c (f x)))
                   a b Hab); [ intros t Ht; cbn [Re Im Cmul]; ring | exact prSRe ]).
    transitivity (RiemannInt pr).
    - apply (RiemannInt_P18 prSRe pr Hab). intros x Hx; cbn [Re Im Cmul]; ring.
    - rewrite (RI_lincomb_val _ _ a b (Re c) (- Im c) prFRe prFIm pr Hab); ring. }
  assert (HIm : RiemannInt prSIm
                = Re c * RiemannInt prFIm + Im c * RiemannInt prFRe).
  { assert (pr : Riemann_integrable
                   (fun x => Re c * Im (f x) + Im c * Re (f x)) a b)
      by (apply (Riemann_integrable_ext_open _ (fun x => Im (Cmul c (f x)))
                   a b Hab); [ intros t Ht; cbn [Re Im Cmul]; ring | exact prSIm ]).
    transitivity (RiemannInt pr).
    - apply (RiemannInt_P18 prSIm pr Hab). intros x Hx; cbn [Re Im Cmul]; ring.
    - rewrite (RI_lincomb_val _ _ a b (Re c) (Im c) prFIm prFRe pr Hab); ring. }
  unfold CintfD, Cmul; apply Ceq; cbn [Re Im]; assumption.
Qed.

Print Assumptions CintfD_add.
Print Assumptions CintfD_cmul_l.
Print Assumptions CintfD_sub.
