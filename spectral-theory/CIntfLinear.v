(* ================================================================= *)
(*  CIntfLinear.v  —  linearity of the complex path integral Cintf.    *)
(*                                                                    *)
(*    Cintf_scal : INT (c . f) = c . INT f                             *)
(*    Cintf_add  : INT (f + g) = INT f + INT g                         *)
(*                                                                    *)
(*  CIntegral2 ships Ccont_add and Ccont_scal -- the CONTINUITY halves *)
(*  -- but never the corresponding facts about the integral itself.    *)
(*  Both are needed by the Borel-Caratheodory assembly (pulling the    *)
(*  factor Ci out of the Cauchy kernel, and rewriting the integrand    *)
(*  as 2 Re G - 2 M against the weight).                               *)
(*                                                                    *)
(*  Underneath sit the real-level facts, which Coq's Reals also do not *)
(*  provide directly: RiemannInt_P13 gives INT (f + l g) in the        *)
(*  SYNTACTIC shape "f x + l * g x", so every use needs the integrand  *)
(*  massaged and the integrability proof transported along an          *)
(*  extensional equality.  RiemannInt_ext_fun does that transport once *)
(*  and for all (via functional extensionality, already in the axiom   *)
(*  set), which is what makes RInt_scal and RInt_lin2 short.           *)
(*  Axiom-clean.                                                       *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra FunctionalExtensionality.
Require Import ComplexField Cmodulus CImproperIntegral CIntegral2.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  A.  transport an integral across an extensional equality          *)
(* ----------------------------------------------------------------- *)
Lemma RiemannInt_ext_fun : forall (f g : R -> R) (a b : R)
  (prf : Riemann_integrable f a b) (prg : Riemann_integrable g a b),
  f = g -> RiemannInt prf = RiemannInt prg.
Proof.
  intros f g a b prf prg E. revert prf. rewrite E. intro p. apply RiemannInt_P5.
Qed.

(* component algebra, to keep the assembly free of cbn guesswork *)
Lemma Re_Cmul : forall c w, Re (Cmul c w) = Re c * Re w - Im c * Im w.
Proof. intros [cr ci] [wr wi]; reflexivity. Qed.
Lemma Im_Cmul : forall c w, Im (Cmul c w) = Re c * Im w + Im c * Re w.
Proof. intros [cr ci] [wr wi]; reflexivity. Qed.
Lemma Re_Cadd : forall x w, Re (Cadd x w) = Re x + Re w.
Proof. intros [xr xi] [wr wi]; reflexivity. Qed.
Lemma Im_Cadd : forall x w, Im (Cadd x w) = Im x + Im w.
Proof. intros [xr xi] [wr wi]; reflexivity. Qed.

(* ----------------------------------------------------------------- *)
(*  B.  real scaling and two-term linearity                           *)
(* ----------------------------------------------------------------- *)
Lemma RInt_scal : forall (c : R) (h : R -> R) (a b : R)
  (prh : Riemann_integrable h a b)
  (pr : Riemann_integrable (fun x => c * h x) a b),
  RiemannInt pr = c * RiemannInt prh.
Proof.
  intros c h a b prh pr.
  pose proof (RiemannInt_P14 a b 0) as pr0.
  assert (Heq : (fun x : R => fct_cte 0 x + c * h x) = (fun x : R => c * h x))
    by (apply functional_extensionality; intro x; unfold fct_cte; ring).
  pose proof (RiemannInt_P10 c pr0 prh) as pr3.
  rewrite <- (RiemannInt_ext_fun _ _ a b pr3 pr Heq).
  assert (H13 : RiemannInt pr3 = RiemannInt pr0 + c * RiemannInt prh)
    by apply RiemannInt_P13.
  assert (H15 : RiemannInt pr0 = 0 * (b - a)) by apply RiemannInt_P15.
  rewrite H13, H15. ring.
Qed.

Lemma RInt_lin2 : forall (c1 c2 : R) (h1 h2 : R -> R) (a b : R)
  (pr1 : Riemann_integrable h1 a b) (pr2 : Riemann_integrable h2 a b)
  (pr : Riemann_integrable (fun x => c1 * h1 x + c2 * h2 x) a b),
  RiemannInt pr = c1 * RiemannInt pr1 + c2 * RiemannInt pr2.
Proof.
  intros c1 c2 h1 h2 a b pr1 pr2 pr.
  assert (prs : Riemann_integrable (fun x => c1 * h1 x) a b).
  { assert (Heq : (fun x : R => fct_cte 0 x + c1 * h1 x) = (fun x : R => c1 * h1 x))
      by (apply functional_extensionality; intro x; unfold fct_cte; ring).
    rewrite <- Heq. exact (RiemannInt_P10 c1 (RiemannInt_P14 a b 0) pr1). }
  pose proof (RiemannInt_P10 c2 prs pr2) as pr3.
  assert (Hpp : RiemannInt pr = RiemannInt pr3) by apply RiemannInt_P5.
  rewrite Hpp.
  assert (H13 : RiemannInt pr3 = RiemannInt prs + c2 * RiemannInt pr2)
    by apply RiemannInt_P13.
  rewrite H13, (RInt_scal c1 h1 a b pr1 prs). reflexivity.
Qed.

(* ----------------------------------------------------------------- *)
(*  C.  complex scaling                                               *)
(* ----------------------------------------------------------------- *)
Theorem Cintf_scal : forall (c : C) (f : R -> C) (Hf : Ccont f)
  (Hcf : Ccont (fun u => Cmul c (f u))) (a b : R),
  Cintf (fun u => Cmul c (f u)) Hcf a b = Cmul c (Cintf f Hf a b).
Proof.
  intros c f Hf Hcf a b.
  assert (HRe : Re (Cintf (fun u => Cmul c (f u)) Hcf a b)
                = Re c * Re (Cintf f Hf a b) + - Im c * Im (Cintf f Hf a b)).
  { rewrite !Re_Cintf, !Im_Cintf.
    assert (Heq : (fun u => Re (Cmul c (f u)))
                = (fun x => Re c * (fun u => Re (f u)) x
                            + - Im c * (fun u => Im (f u)) x))
      by (apply functional_extensionality; intro u; cbn [Re Im Cmul]; ring).
    assert (prx : Riemann_integrable
                    (fun x => Re c * (fun u => Re (f u)) x
                              + - Im c * (fun u => Im (f u)) x) a b)
      by (rewrite <- Heq; exact (cont_RI _ (proj1 Hcf) a b)).
    rewrite (RiemannInt_ext_fun _ _ a b (cont_RI _ (proj1 Hcf) a b) prx Heq).
    apply RInt_lin2. }
  assert (HIm : Im (Cintf (fun u => Cmul c (f u)) Hcf a b)
                = Re c * Im (Cintf f Hf a b) + Im c * Re (Cintf f Hf a b)).
  { rewrite !Re_Cintf, !Im_Cintf.
    assert (Heq : (fun u => Im (Cmul c (f u)))
                = (fun x => Re c * (fun u => Im (f u)) x
                            + Im c * (fun u => Re (f u)) x))
      by (apply functional_extensionality; intro u; cbn [Re Im Cmul]; ring).
    assert (prx : Riemann_integrable
                    (fun x => Re c * (fun u => Im (f u)) x
                              + Im c * (fun u => Re (f u)) x) a b)
      by (rewrite <- Heq; exact (cont_RI _ (proj2 Hcf) a b)).
    rewrite (RiemannInt_ext_fun _ _ a b (cont_RI _ (proj2 Hcf) a b) prx Heq).
    apply RInt_lin2. }
  apply Ceq; [ rewrite HRe, Re_Cmul | rewrite HIm, Im_Cmul ]; ring.
Qed.

(* ----------------------------------------------------------------- *)
(*  D.  complex addition                                              *)
(* ----------------------------------------------------------------- *)
Theorem Cintf_add : forall (f g : R -> C) (Hf : Ccont f) (Hg : Ccont g)
  (Hfg : Ccont (fun u => Cadd (f u) (g u))) (a b : R),
  Cintf (fun u => Cadd (f u) (g u)) Hfg a b
  = Cadd (Cintf f Hf a b) (Cintf g Hg a b).
Proof.
  intros f g Hf Hg Hfg a b.
  assert (HRe : Re (Cintf (fun u => Cadd (f u) (g u)) Hfg a b)
                = 1 * Re (Cintf f Hf a b) + 1 * Re (Cintf g Hg a b)).
  { rewrite !Re_Cintf.
    assert (Heq : (fun u => Re (Cadd (f u) (g u)))
                = (fun x => 1 * (fun u => Re (f u)) x + 1 * (fun u => Re (g u)) x))
      by (apply functional_extensionality; intro u; cbn [Re Im Cadd]; ring).
    assert (prx : Riemann_integrable
                    (fun x => 1 * (fun u => Re (f u)) x
                              + 1 * (fun u => Re (g u)) x) a b)
      by (rewrite <- Heq; exact (cont_RI _ (proj1 Hfg) a b)).
    rewrite (RiemannInt_ext_fun _ _ a b (cont_RI _ (proj1 Hfg) a b) prx Heq).
    apply RInt_lin2. }
  assert (HIm : Im (Cintf (fun u => Cadd (f u) (g u)) Hfg a b)
                = 1 * Im (Cintf f Hf a b) + 1 * Im (Cintf g Hg a b)).
  { rewrite !Im_Cintf.
    assert (Heq : (fun u => Im (Cadd (f u) (g u)))
                = (fun x => 1 * (fun u => Im (f u)) x + 1 * (fun u => Im (g u)) x))
      by (apply functional_extensionality; intro u; cbn [Re Im Cadd]; ring).
    assert (prx : Riemann_integrable
                    (fun x => 1 * (fun u => Im (f u)) x
                              + 1 * (fun u => Im (g u)) x) a b)
      by (rewrite <- Heq; exact (cont_RI _ (proj2 Hfg) a b)).
    rewrite (RiemannInt_ext_fun _ _ a b (cont_RI _ (proj2 Hfg) a b) prx Heq).
    apply RInt_lin2. }
  apply Ceq; [ rewrite HRe, Re_Cadd | rewrite HIm, Im_Cadd ]; ring.
Qed.

Print Assumptions Cintf_scal.
Print Assumptions Cintf_add.
