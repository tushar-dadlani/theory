(* ================================================================= *)
(*  CConjIntegral.v  —  the CONJUGATE-INTEGRAL identity: the one       *)
(*  ingredient Borel-Caratheodory was missing.                         *)
(*                                                                    *)
(*    Cintf_conj : INT conj(f) = conj (INT f).                         *)
(*                                                                    *)
(*  COrderOne isolated the order-1 step down to a single named Prop,   *)
(*  BorelCaratheodory, whose classical proof runs through              *)
(*                                                                    *)
(*    G^{(n)}(0)/n! = (1/(pi R^n)) INT_0^{2PI} Re G(R e^{it}) e^{-int} dt *)
(*                                                                    *)
(*  and that in turn rests on the CONJUGATE HALF vanishing:            *)
(*    INT conj(G) e^{-int} dt = conj (INT G e^{int} dt) = conj 0 = 0,   *)
(*  the last step by Cauchy.  Every other piece it needs -- Cauchy loop *)
(*  vanishing, the mean value at the centre, the ML bound -- was        *)
(*  already in the repo; the transfer of conjugation THROUGH the        *)
(*  integral was not.  This file supplies it.                          *)
(*                                                                    *)
(*  THE ACTUAL OBSTACLE was smaller and more annoying than the complex *)
(*  analysis: Cintf is built from two real Riemann integrals, and       *)
(*  conjugation negates the imaginary one -- but Coq's Reals ship no    *)
(*  lemma  INT (-g) = - INT g.  (RiemannInt_P8 negates by SWAPPING THE  *)
(*  BOUNDS, which is a different statement.)  RiemannInt_opp below      *)
(*  fills that hole, via RiemannInt_P13's linearity with f := 0 and     *)
(*  l := -1, transporting the integrability proof across the            *)
(*  extensional equality (fun x => 0 + -1 * g x) = (fun x => - g x).    *)
(*  Once that exists, Cintf_conj is one Ceq and two component facts.    *)
(*  Axiom-clean.                                                       *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra FunctionalExtensionality.
Require Import ComplexField Cmodulus CIntegral2 CSegInt.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  A.  the missing real lemma:  INT (-g) = - INT g                    *)
(* ----------------------------------------------------------------- *)
Lemma RiemannInt_opp : forall (g : R -> R) (a b : R)
  (pr : Riemann_integrable g a b)
  (pr' : Riemann_integrable (fun x => - g x) a b),
  RiemannInt pr' = - RiemannInt pr.
Proof.
  intros g a b pr pr'.
  pose proof (RiemannInt_P14 a b 0) as pr0.
  assert (Heq : (fun x : R => fct_cte 0 x + -1 * g x) = (fun x : R => - g x))
    by (apply functional_extensionality; intro x; unfold fct_cte; ring).
  assert (Hkey : forall pr3 : Riemann_integrable
                     (fun x : R => fct_cte 0 x + -1 * g x) a b,
                 RiemannInt pr3 = RiemannInt pr').
  { rewrite Heq. intro p. apply RiemannInt_P5. }
  pose proof (RiemannInt_P10 (-1) pr0 pr) as pr3.
  rewrite <- (Hkey pr3).
  assert (H13 : RiemannInt pr3 = RiemannInt pr0 + -1 * RiemannInt pr)
    by apply RiemannInt_P13.
  assert (H15 : RiemannInt pr0 = 0 * (b - a)) by apply RiemannInt_P15.
  rewrite H13, H15. ring.
Qed.

(* ----------------------------------------------------------------- *)
(*  B.  conjugation preserves continuity                              *)
(* ----------------------------------------------------------------- *)
Lemma Ccont_conj : forall f, Ccont f -> Ccont (fun t => Cconj (f t)).
Proof.
  intros f [HR HI]. split; cbn [Re Im Cconj].
  - exact HR.
  - apply (continuity_opp (fun u => Im (f u))). exact HI.
Qed.

(* ----------------------------------------------------------------- *)
(*  C.  THE CONJUGATE-INTEGRAL IDENTITY                                *)
(* ----------------------------------------------------------------- *)
Theorem Cintf_conj : forall f (Hf : Ccont f)
  (Hcf : Ccont (fun t => Cconj (f t))) (a b : R),
  Cintf (fun t => Cconj (f t)) Hcf a b = Cconj (Cintf f Hf a b).
Proof.
  intros f Hf Hcf a b. apply Ceq.
  - (* real parts: the same integrand, different proof term *)
    unfold Cintf, Cconj; cbn [Re Im]. apply RiemannInt_P5.
  - (* imaginary parts: the negated integrand *)
    unfold Cintf, Cconj; cbn [Re Im]. apply RiemannInt_opp.
Qed.

Corollary Cintf_conj_zero : forall f (Hf : Ccont f)
  (Hcf : Ccont (fun t => Cconj (f t))) (a b : R),
  Cintf f Hf a b = C0 ->
  Cintf (fun t => Cconj (f t)) Hcf a b = C0.
Proof.
  intros f Hf Hcf a b Hz.
  rewrite (Cintf_conj f Hf Hcf a b), Hz.
  apply Ceq; simpl; ring.
Qed.

(* ----------------------------------------------------------------- *)
(*  D.  the real part as a half-sum -- how Re G enters the integral    *)
(* ----------------------------------------------------------------- *)
Lemma Re_half_sum : forall w : C,
  RtoC (Re w) = Cmul (RtoC (/ 2)) (Cadd w (Cconj w)).
Proof.
  intro w. apply Ceq; destruct w as [wr wi]; cbn [Re Im RtoC Cmul Cadd Cconj]; lra.
Qed.

(* ----------------------------------------------------------------- *)
(*  E.  the conjugate half of a WEIGHTED (Fourier-type) integral       *)
(*                                                                    *)
(*  This is the shape Borel-Caratheodory consumes: with v t = e^{int}, *)
(*  conj(g) . e^{-int} = conj (g . e^{int}), so the conjugate half of   *)
(*  INT Re(g) e^{-int} dt is conj (INT g e^{int} dt) -- and THAT is 0   *)
(*  by Cauchy for n >= 1.                                             *)
(* ----------------------------------------------------------------- *)
Theorem Cintf_conj_weighted : forall (g v : R -> C)
  (Hgv : Ccont (fun t => Cmul (g t) (v t)))
  (Hcgv : Ccont (fun t => Cmul (Cconj (g t)) (Cconj (v t)))) (a b : R),
  Cintf (fun t => Cmul (Cconj (g t)) (Cconj (v t))) Hcgv a b
  = Cconj (Cintf (fun t => Cmul (g t) (v t)) Hgv a b).
Proof.
  intros g v Hgv Hcgv a b.
  assert (Hconj : Ccont (fun t => Cconj (Cmul (g t) (v t))))
    by (apply Ccont_conj; exact Hgv).
  rewrite <- (Cintf_conj (fun t => Cmul (g t) (v t)) Hgv Hconj a b).
  apply Cintf_ext. intro t. symmetry. apply Cconj_mul.
Qed.

Corollary Cintf_conj_weighted_zero : forall (g v : R -> C)
  (Hgv : Ccont (fun t => Cmul (g t) (v t)))
  (Hcgv : Ccont (fun t => Cmul (Cconj (g t)) (Cconj (v t)))) (a b : R),
  Cintf (fun t => Cmul (g t) (v t)) Hgv a b = C0 ->
  Cintf (fun t => Cmul (Cconj (g t)) (Cconj (v t))) Hcgv a b = C0.
Proof.
  intros g v Hgv Hcgv a b Hz.
  rewrite (Cintf_conj_weighted g v Hgv Hcgv a b), Hz.
  apply Ceq; simpl; ring.
Qed.

Print Assumptions Cintf_conj.
Print Assumptions Cintf_conj_weighted.
