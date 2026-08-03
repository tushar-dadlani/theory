(* ================================================================= *)
(*  CPowBase.v  —  the complex power c^w as a function of its real     *)
(*  base: explicit real/imaginary components and their x-derivative.   *)
(*                                                                    *)
(*  Re (Cpw x w) = x^{Re w}·cos(Im w·ln x),                            *)
(*  Im (Cpw x w) = x^{Re w}·sin(Im w·ln x),                            *)
(*  and d/dx (Cpw x w) = w·x^{w-1} (componentwise).  These feed the    *)
(*  double-MVT bound on the Euler–Maclaurin term gtermC.  Axiom-clean. *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra FunctionalExtensionality.
Require Import ComplexField Cmodulus CexpFull EulerFormula.
Open Scope R_scope.

(* derivative of the real power in its base *)
Lemma Rpow_deriv : forall c x, 0 < x ->
  derivable_pt_lim (fun y => Rpower y c) x (c * Rpower x (c - 1)).
Proof.
  intros c x Hx.
  assert (Hval : c * Rpower x (c - 1) = exp (c * ln x) * (c * / x)).
  { unfold Rpower.
    replace ((c - 1) * ln x) with (c * ln x + - ln x) by ring.
    rewrite exp_plus, exp_Ropp, exp_ln by exact Hx. ring. }
  rewrite Hval.
  assert (Heq : (fun y => Rpower y c) = (fun y => exp (c * ln y)))
    by (apply functional_extensionality; intro y; reflexivity).
  rewrite Heq.
  apply (derivable_pt_lim_comp (fun y => c * ln y) exp x (c * / x) (exp (c * ln x))).
  - apply (derivable_pt_lim_scal ln c x (/ x)); apply derivable_pt_lim_ln; exact Hx.
  - apply derivable_pt_lim_exp.
Qed.

Lemma Re_Cpw : forall x w, Re (Cpw x w) = Rpower x (Re w) * cos (Im w * ln x).
Proof.
  intros x w; unfold Cpw, Cexpf, Cexp, Cmul, RtoC; simpl; unfold Rpower.
  replace (Re w * ln x - Im w * 0) with (Re w * ln x) by ring.
  replace (Re w * 0 + Im w * ln x) with (Im w * ln x) by ring.
  ring.
Qed.

Lemma Im_Cpw : forall x w, Im (Cpw x w) = Rpower x (Re w) * sin (Im w * ln x).
Proof.
  intros x w; unfold Cpw, Cexpf, Cexp, Cmul, RtoC; simpl; unfold Rpower.
  replace (Re w * ln x - Im w * 0) with (Re w * ln x) by ring.
  replace (Re w * 0 + Im w * ln x) with (Im w * ln x) by ring.
  ring.
Qed.

(* helper: x^{a}/x = x^{a-1} *)
Lemma Rpower_pred : forall x a, 0 < x -> Rpower x a * / x = Rpower x (a - 1).
Proof.
  intros x a Hx.
  replace (a - 1) with (a + - 1) by ring; rewrite Rpower_plus; f_equal.
  unfold Rpower; replace (-1 * ln x) with (- ln x) by ring.
  rewrite exp_Ropp, exp_ln by exact Hx; reflexivity.
Qed.

(* base derivative:  d/dx (c^w) = w · c^{w-1}, componentwise *)
Lemma Re_Cpw_deriv : forall x w, 0 < x ->
  derivable_pt_lim (fun t => Re (Cpw t w)) x (Re (Cmul w (Cpw x (Cminus w C1)))).
Proof.
  intros x w Hx.
  assert (Heq : (fun t => Re (Cpw t w)) = (fun t => Rpower t (Re w) * cos (Im w * ln t)))
    by (apply functional_extensionality; intro t; apply Re_Cpw).
  rewrite Heq.
  replace (Re (Cmul w (Cpw x (Cminus w C1))))
    with (Re w * Rpower x (Re w - 1) * cos (Im w * ln x)
          + Rpower x (Re w) * (- sin (Im w * ln x) * (Im w * / x))).
  - apply (derivable_pt_lim_mult (fun t => Rpower t (Re w)) (fun t => cos (Im w * ln t))
             x (Re w * Rpower x (Re w - 1)) (- sin (Im w * ln x) * (Im w * / x))).
    + apply Rpow_deriv; exact Hx.
    + apply (derivable_pt_lim_comp (fun t => Im w * ln t) cos x (Im w * / x)
               (- sin (Im w * ln x))).
      * apply (derivable_pt_lim_scal ln (Im w) x (/ x)); apply derivable_pt_lim_ln; exact Hx.
      * apply derivable_pt_lim_cos.
  - unfold Cmul; cbn [Re]; rewrite Re_Cpw, Im_Cpw.
    replace (Re (Cminus w C1)) with (Re w - 1)
      by (unfold Cminus, Cadd, Copp, C1; simpl; ring).
    replace (Im (Cminus w C1)) with (Im w)
      by (unfold Cminus, Cadd, Copp, C1; simpl; ring).
    rewrite <- (Rpower_pred x (Re w) Hx); field; apply Rgt_not_eq; exact Hx.
Qed.

Lemma Im_Cpw_deriv : forall x w, 0 < x ->
  derivable_pt_lim (fun t => Im (Cpw t w)) x (Im (Cmul w (Cpw x (Cminus w C1)))).
Proof.
  intros x w Hx.
  assert (Heq : (fun t => Im (Cpw t w)) = (fun t => Rpower t (Re w) * sin (Im w * ln t)))
    by (apply functional_extensionality; intro t; apply Im_Cpw).
  rewrite Heq.
  replace (Im (Cmul w (Cpw x (Cminus w C1))))
    with (Re w * Rpower x (Re w - 1) * sin (Im w * ln x)
          + Rpower x (Re w) * (cos (Im w * ln x) * (Im w * / x))).
  - apply (derivable_pt_lim_mult (fun t => Rpower t (Re w)) (fun t => sin (Im w * ln t))
             x (Re w * Rpower x (Re w - 1)) (cos (Im w * ln x) * (Im w * / x))).
    + apply Rpow_deriv; exact Hx.
    + apply (derivable_pt_lim_comp (fun t => Im w * ln t) sin x (Im w * / x)
               (cos (Im w * ln x))).
      * apply (derivable_pt_lim_scal ln (Im w) x (/ x)); apply derivable_pt_lim_ln; exact Hx.
      * apply derivable_pt_lim_sin.
  - unfold Cmul; cbn [Im]; rewrite Re_Cpw, Im_Cpw.
    replace (Re (Cminus w C1)) with (Re w - 1)
      by (unfold Cminus, Cadd, Copp, C1; simpl; ring).
    replace (Im (Cminus w C1)) with (Im w)
      by (unfold Cminus, Cadd, Copp, C1; simpl; ring).
    rewrite <- (Rpower_pred x (Re w) Hx); field; apply Rgt_not_eq; exact Hx.
Qed.

Print Assumptions Re_Cpw.
Print Assumptions Re_Cpw_deriv.

(* ================================================================= *)
(*  END CPowBase.v (part 1).                                          *)
(* ================================================================= *)
