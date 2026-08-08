(* ================================================================= *)
(*  CMeanValue.v  —  Milestone C, brick C2d (mean-value route),         *)
(*  Blocks 2 & 3: the loop integral of a derivative vanishes, and the    *)
(*  radial chain rule d/dr F(arc r θ) = F'(arc r θ)·(cosθ, sinθ).         *)
(*                                                                    *)
(*  These are near-verbatim reuse of C2b (pathint_primitive_loop) and    *)
(*  C1c (Cderiv_path_Re/Im); they feed the Leibniz step (Block 4) that    *)
(*  proves the mean value M(r)=∫₀^{2π}F(arc r θ)dθ is constant, hence     *)
(*  Cauchy's integral formula ∮_{|z|=R} F/z = 2πi·F(0).                   *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import ComplexField Cmodulus CIntegral2 CPathIntegral CPathFTC
        CSegInt Holomorphic CHoloCalculus CWinding.
Open Scope R_scope.

(* d/dr (r·c) = c *)
Lemma dmul_const : forall c r0, derivable_pt_lim (fun r => r * c) r0 c.
Proof.
  intros c r0.
  assert (H := derivable_pt_lim_mult (fun x => x) (fun _ => c) r0 1 0
                 (derivable_pt_lim_id r0) (derivable_pt_lim_const c r0)).
  unfold mult_fct in H;
  replace (1 * c + r0 * 0) with c in H by ring; exact H.
Qed.

(* the arc's θ-derivative is arc' *)
Lemma dRe_arc_theta : forall r s, derivable_pt_lim (fun t => Re (arc r t)) s (Re (arc' r s)).
Proof.
  intros r s; unfold arc, arc'; cbn [Re].
  replace (- (r * sin s)) with (r * (- sin s)) by ring.
  apply (derivable_pt_lim_scal cos r s), derivable_pt_lim_cos.
Qed.

Lemma dIm_arc_theta : forall r s, derivable_pt_lim (fun t => Im (arc r t)) s (Im (arc' r s)).
Proof.
  intros r s; unfold arc, arc'; cbn [Im].
  apply (derivable_pt_lim_scal sin r s), derivable_pt_lim_sin.
Qed.

Section MeanValue.
Variable F Fp : C -> C.
Variable HF : CcontC F.
Variable HFp : CcontC Fp.
Hypothesis HFhol : forall z, is_Cderiv F z (Fp z).

(* ---- Block 2: the loop integral of a derivative around a circle is 0 ---- *)
(* F is a primitive of Fp, so pathint_primitive_loop applies directly. *)
Theorem circint_Fp_zero : forall r
  (Hf : Ccont (fun u => Cmul (Fp (arc r u)) (arc' r u))),
  pathint (arc r) (arc' r) Fp Hf 0 (2 * PI) = C0.
Proof.
  intros r Hf.
  apply (pathint_primitive_loop F Fp (arc r) (arc' r) Hf 0 (2 * PI)).
  - generalize PI_RGT_0; lra.
  - unfold arc; apply Ceq; cbn;
      rewrite ?cos_0, ?sin_0, ?cos_2PI, ?sin_2PI; ring.
  - intros s _; apply HFhol.
  - intros s _; apply dRe_arc_theta.
  - intros s _; apply dIm_arc_theta.
Qed.

(* ---- Block 3: the radial chain rule d/dr F(arc r θ) ---- *)
(* the r-derivative of the path r ↦ arc r θ is the constant (cosθ, sinθ) *)
Theorem Farc_r_deriv : forall r0 t,
  derivable_pt_lim (fun r => Re (F (arc r t))) r0
    (Re (Cmul (Fp (arc r0 t)) (mkC (cos t) (sin t))))
  /\ derivable_pt_lim (fun r => Im (F (arc r t))) r0
    (Im (Cmul (Fp (arc r0 t)) (mkC (cos t) (sin t)))).
Proof.
  intros r0 t; split.
  - apply (Cderiv_path_Re F (fun r => arc r t) (fun _ => mkC (cos t) (sin t)) r0
             (Fp (arc r0 t))).
    + apply HFhol.
    + change (Re (mkC (cos t) (sin t))) with (cos t); unfold arc; cbn [Re];
        apply dmul_const.
    + change (Im (mkC (cos t) (sin t))) with (sin t); unfold arc; cbn [Im];
        apply dmul_const.
  - apply (Cderiv_path_Im F (fun r => arc r t) (fun _ => mkC (cos t) (sin t)) r0
             (Fp (arc r0 t))).
    + apply HFhol.
    + change (Re (mkC (cos t) (sin t))) with (cos t); unfold arc; cbn [Re];
        apply dmul_const.
    + change (Im (mkC (cos t) (sin t))) with (sin t); unfold arc; cbn [Im];
        apply dmul_const.
Qed.

End MeanValue.

Print Assumptions circint_Fp_zero.
Print Assumptions Farc_r_deriv.

(* ================================================================= *)
(*  END CMeanValue.v  —  ∮F'=0 (C2d Block 2) + radial chain rule (Block 3). *)
(* ================================================================= *)
