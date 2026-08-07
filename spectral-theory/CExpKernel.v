(* ================================================================= *)
(*  CExpKernel.v  —  Milestone C, brick C3: the exponential kernel      *)
(*  e^{zt} (z : C, t : R) with its t-derivative z·e^{zt}, modulus        *)
(*  e^{Re z·t}, and continuity.  Cexpf has no derivative lemma in the    *)
(*  repo; we build it from the explicit components exp(a t)cos(b t),     *)
(*  exp(a t)sin(b t) (a=Re z, b=Im z).  Feeds the Laplace integrand      *)
(*  f(t)e^{−zt} and the Newman contour kernel.                          *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia FunctionalExtensionality.
Require Import ComplexField Cmodulus CexpFull EulerFormula CIntegral2.
Open Scope R_scope.

(* ---- linear-argument derivative helpers ---- *)
Lemma dexp_lin : forall a t, derivable_pt_lim (fun u => exp (a * u)) t (a * exp (a * t)).
Proof.
  intros a t.
  assert (H : derivable_pt_lim (comp exp (mult_real_fct a (fun u => u))) t
                (exp (a * t) * (a * 1))).
  { apply derivable_pt_lim_comp.
    - apply derivable_pt_lim_scal, derivable_pt_lim_id.
    - apply derivable_pt_lim_exp. }
  replace (fun u => exp (a * u)) with (comp exp (mult_real_fct a (fun u => u)))
    by (apply functional_extensionality; intro u; reflexivity).
  replace (a * exp (a * t)) with (exp (a * t) * (a * 1)) by ring; exact H.
Qed.

Lemma dcos_lin : forall b t, derivable_pt_lim (fun u => cos (b * u)) t (- sin (b * t) * b).
Proof.
  intros b t.
  assert (H : derivable_pt_lim (comp cos (mult_real_fct b (fun u => u))) t
                (- sin (b * t) * (b * 1))).
  { apply derivable_pt_lim_comp.
    - apply derivable_pt_lim_scal, derivable_pt_lim_id.
    - apply derivable_pt_lim_cos. }
  replace (fun u => cos (b * u)) with (comp cos (mult_real_fct b (fun u => u)))
    by (apply functional_extensionality; intro u; reflexivity).
  replace (- sin (b * t) * b) with (- sin (b * t) * (b * 1)) by ring; exact H.
Qed.

Lemma dsin_lin : forall b t, derivable_pt_lim (fun u => sin (b * u)) t (cos (b * t) * b).
Proof.
  intros b t.
  assert (H : derivable_pt_lim (comp sin (mult_real_fct b (fun u => u))) t
                (cos (b * t) * (b * 1))).
  { apply derivable_pt_lim_comp.
    - apply derivable_pt_lim_scal, derivable_pt_lim_id.
    - apply derivable_pt_lim_sin. }
  replace (fun u => sin (b * u)) with (comp sin (mult_real_fct b (fun u => u)))
    by (apply functional_extensionality; intro u; reflexivity).
  replace (cos (b * t) * b) with (cos (b * t) * (b * 1)) by ring; exact H.
Qed.

(* ---- the kernel e^{z t} ---- *)
Definition cexpzt (z : C) (t : R) : C := Cexpf (Cmul z (RtoC t)).

Lemma Cexpf_mkC : forall a b, Cexpf (mkC a b) = mkC (exp a * cos b) (exp a * sin b).
Proof. intros a b; unfold Cexpf, Cexp, Cmul, RtoC; apply Ceq; cbn; ring. Qed.

Lemma cexpzt_mkC : forall z t, cexpzt z t = mkC (exp (Re z * t) * cos (Im z * t))
                                               (exp (Re z * t) * sin (Im z * t)).
Proof.
  intros z t; unfold cexpzt.
  assert (Hm : Cmul z (RtoC t) = mkC (Re z * t) (Im z * t))
    by (unfold Cmul, RtoC; apply Ceq; cbn; ring).
  rewrite Hm, Cexpf_mkC; reflexivity.
Qed.

Lemma Re_cexpzt : forall z t, Re (cexpzt z t) = exp (Re z * t) * cos (Im z * t).
Proof. intros z t; rewrite cexpzt_mkC; reflexivity. Qed.

Lemma Im_cexpzt : forall z t, Im (cexpzt z t) = exp (Re z * t) * sin (Im z * t).
Proof. intros z t; rewrite cexpzt_mkC; reflexivity. Qed.

(* ---- modulus:  |e^{zt}| = e^{Re z · t} ---- *)
Lemma Cmod_cexpzt : forall z t, Cmod (cexpzt z t) = exp (Re z * t).
Proof.
  intros z t; unfold cexpzt; rewrite Cmod_Cexpf.
  assert (Hm : Re (Cmul z (RtoC t)) = Re z * t) by (unfold Cmul, RtoC; cbn; ring).
  rewrite Hm; reflexivity.
Qed.

(* ---- the t-derivative:  d/dt e^{zt} = z e^{zt} ---- *)
Lemma Re_cexpzt_deriv : forall z t,
  derivable_pt_lim (fun u => Re (cexpzt z u)) t (Re (Cmul z (cexpzt z t))).
Proof.
  intros z t.
  set (V := Re z * exp (Re z * t) * cos (Im z * t)
           + exp (Re z * t) * (- sin (Im z * t) * Im z)).
  assert (Htgt : Re (Cmul z (cexpzt z t)) = V)
    by (unfold V, Cmul; cbn [Re]; rewrite Re_cexpzt, Im_cexpzt; ring).
  rewrite Htgt.
  assert (Hf : (fun u => Re (cexpzt z u)) = (fun u => exp (Re z * u) * cos (Im z * u)))
    by (apply functional_extensionality; intro u; apply Re_cexpzt).
  rewrite Hf; unfold V.
  apply (derivable_pt_lim_mult (fun u => exp (Re z * u)) (fun u => cos (Im z * u)) t
           (Re z * exp (Re z * t)) (- sin (Im z * t) * Im z)).
  - apply dexp_lin.
  - apply dcos_lin.
Qed.

Lemma Im_cexpzt_deriv : forall z t,
  derivable_pt_lim (fun u => Im (cexpzt z u)) t (Im (Cmul z (cexpzt z t))).
Proof.
  intros z t.
  set (V := Re z * exp (Re z * t) * sin (Im z * t)
           + exp (Re z * t) * (cos (Im z * t) * Im z)).
  assert (Htgt : Im (Cmul z (cexpzt z t)) = V)
    by (unfold V, Cmul; cbn [Im]; rewrite Re_cexpzt, Im_cexpzt; ring).
  rewrite Htgt.
  assert (Hf : (fun u => Im (cexpzt z u)) = (fun u => exp (Re z * u) * sin (Im z * u)))
    by (apply functional_extensionality; intro u; apply Im_cexpzt).
  rewrite Hf; unfold V.
  apply (derivable_pt_lim_mult (fun u => exp (Re z * u)) (fun u => sin (Im z * u)) t
           (Re z * exp (Re z * t)) (cos (Im z * t) * Im z)).
  - apply dexp_lin.
  - apply dsin_lin.
Qed.

(* ---- continuity in t ---- *)
Lemma Ccont_cexpzt : forall z, Ccont (fun u => cexpzt z u).
Proof.
  intro z; split; intro x.
  - apply derivable_continuous_pt; exists (Re (Cmul z (cexpzt z x))); apply Re_cexpzt_deriv.
  - apply derivable_continuous_pt; exists (Im (Cmul z (cexpzt z x))); apply Im_cexpzt_deriv.
Qed.

Print Assumptions Re_cexpzt_deriv.
Print Assumptions Cmod_cexpzt.

(* ================================================================= *)
(*  END CExpKernel.v  —  the kernel e^{zt}, its t-derivative & modulus. *)
(* ================================================================= *)
