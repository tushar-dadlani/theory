(* ================================================================= *)
(*  CCauchyInterior.v  (identity-theorem plan, brick B1)               *)
(*                                                                    *)
(*  The CAUCHY INTEGRAL FORMULA AT AN INTERIOR POINT, on the full      *)
(*  circle:                                                            *)
(*     oint_{|z|=R} F(z)/(z-w) dz = 2 pi i . F(w)   for |w| < R,        *)
(*  the interior-point analogue of CTruncCauchy.trunc_cauchy (which is  *)
(*  the centre case w = 0 on a truncated contour).                     *)
(*                                                                    *)
(*  Split F(z)/(z-w) = phi(z) + F(w)/(z-w) with the removable quotient  *)
(*  phi(z) = (F(z)-F(w))/(z-w).  The phi-loop integral is 0 (Cauchy's   *)
(*  theorem for a function holomorphic off w and continuous through it, *)
(*  CGoursatExcept.pathint_loop_except); the second gives                *)
(*  F(w).oint dz/(z-w) = F(w).2 pi i (CWindingOffCenter.winding_interior).*)
(*                                                                    *)
(*  Like trunc_cauchy, the removable properties of phi (continuity      *)
(*  through w, holomorphy off w, local boundedness) are HYPOTHESES      *)
(*  here; deriving them from F's differentiability at w (the removable  *)
(*  singularity theorem, under the path-composition CcontC) is the      *)
(*  remaining step toward a fully unconditional formula.               *)
(*                                                                    *)
(*  Axioms: standard classical-Reals only.                            *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra.
Require Import ComplexField Cmodulus CIntegral2 CSegInt CPathIntegral Holomorphic
        CGoursatLin CGoursatExcept CPrimConv CWinding CLeibniz CWindingOffCenter.
Open Scope R_scope.

Section CauchyInterior.
Variable R2 Rr : R.
Variable w : C.
Variable F phi : C -> C.
Hypothesis HR : 0 < Rr.
Hypothesis HRR2 : Rr < R2.
Hypothesis HwR : Cmod w < Rr.
(* phi is the removable quotient, with the trunc_cauchy-style properties *)
Hypothesis Hphi_cc : CcontC phi.
Hypothesis Hphi_arc : forall u,
  phi (arc Rr u) = Cmul (Cminus (F (arc Rr u)) (F w)) (Cinv (Cminus (arc Rr u) w)).
Hypothesis Hphi_hol : forall z, Cmod z < R2 -> z <> w -> exists d, is_Cderiv phi z d.
Hypothesis Hphi_bd : exists M eta, 0 < eta /\
  forall z, Cmod (Cminus z w) < eta -> Cmod (phi z) <= M.
Hypothesis Hphi_cont : forall z, Cmod z < R2 -> forall eps, 0 < eps -> exists del, 0 < del /\
  forall z', Cmod (Cminus z' z) < del -> Cmod (Cminus (phi z') (phi z)) < eps.

(* ---- the disk U = { |z| < R2 } is convex and open, contains everything ---- *)
Definition disk (z : C) : Prop := Cmod z < R2.

Lemma disk_convex : Convex disk.
Proof.
  intros a b Ha Hb s Hs. unfold disk in *.
  assert (Hseg : seg a b s = Cadd (Cmul (RtoC (1 - s)) a) (Cmul (RtoC s) b))
    by (unfold seg, Cadd, Cmul, RtoC, Cminus; apply Ceq; cbn; ring).
  rewrite Hseg. eapply Rle_lt_trans; [ apply Cmod_triangle | ].
  rewrite !Cmod_mul, !Cmod_RtoC.
  rewrite (Rabs_pos_eq (1 - s)) by lra. rewrite (Rabs_pos_eq s) by lra.
  apply Rle_lt_trans with (Rmax (Cmod a) (Cmod b)).
  - apply Rle_trans with ((1 - s) * Rmax (Cmod a) (Cmod b) + s * Rmax (Cmod a) (Cmod b)).
    + apply Rplus_le_compat; apply Rmult_le_compat_l;
        solve [ lra | apply Rmax_l | apply Rmax_r ].
    + apply Req_le; ring.
  - apply Rmax_lub_lt; lra.
Qed.

Lemma disk_open : Open disk.
Proof.
  intros z Hz. unfold disk in *. exists (R2 - Cmod z). split; [ lra | ].
  intros z' Hz'. unfold disk. pose proof (Cmod_rev_triangle z' z). lra.
Qed.

Lemma arc_in_disk : forall u, disk (arc Rr u).
Proof. intro u; unfold disk; rewrite (Cmod_arc Rr u) by lra; exact HRR2. Qed.

Lemma w_in_disk : disk w.
Proof. unfold disk; lra. Qed.

Lemma c0_in_disk : disk C0.
Proof. unfold disk; rewrite (proj2 (Cmod0 C0) eq_refl); lra. Qed.

(* the denominator on the circle never vanishes *)
Lemma arc_minus_w_ne : forall u, Cminus (arc Rr u) w <> C0.
Proof.
  intros u Hc.
  assert (Hle : Rr - Cmod w <= Cmod (Cminus (arc Rr u) w)).
  { eapply Rle_trans; [ | apply Cmod_rev_triangle ].
    rewrite (Cmod_arc Rr u) by lra. lra. }
  rewrite Hc, (proj2 (Cmod0 C0) eq_refl) in Hle. lra.
Qed.

(* ---- the removable-quotient loop integral is 0 ---- *)
Lemma phi_loop_zero :
  forall (Hf : Ccont (fun u => Cmul (phi (arc Rr u)) (arc' Rr u))),
  pathint (arc Rr) (arc' Rr) phi Hf 0 (2 * PI) = C0.
Proof.
  intro Hf.
  apply (pathint_loop_except disk disk_convex disk_open phi Hphi_cc w w_in_disk
           Hphi_hol Hphi_bd Hphi_cont C0 c0_in_disk (arc Rr) (arc' Rr) Hf 0 (2 * PI)).
  - generalize PI_RGT_0; lra.
  - symmetry; apply arc_closed.
  - intros s _; apply arc_in_disk.
  - intros s _; apply arc_Re_deriv.
  - intros s _; apply arc_Im_deriv.
Qed.

(* ---- Cauchy's integral formula at the interior point w ---- *)
Theorem cauchy_interior_cond :
  forall (Hf : Ccont (fun u => Cmul (Cmul (F (arc Rr u)) (Cinv (Cminus (arc Rr u) w)))
                                    (arc' Rr u))),
  pathint (arc Rr) (arc' Rr) (fun z => Cmul (F z) (Cinv (Cminus z w))) Hf 0 (2 * PI)
  = Cmul (mkC 0 (2 * PI)) (F w).
Proof.
  intro Hf.
  assert (HcP : Ccont (fun u => Cmul (phi (arc Rr u)) (arc' Rr u)))
    by (apply Ccont_mul; [ apply Hphi_cc, Ccont_arc | apply Ccont_arc' ]).
  assert (HcW : Ccont (fun u => Cmul (Cinv (Cminus (arc Rr u) w)) (arc' Rr u)))
    by (apply Ccont_mul; [ apply Ccont_inv;
          [ apply Ccont_minus; [ apply Ccont_arc | apply Ccont_const ]
          | apply arc_minus_w_ne ] | apply Ccont_arc' ]).
  assert (HcFW : Ccont (fun u => Cmul (F w) (Cmul (Cinv (Cminus (arc Rr u) w)) (arc' Rr u))))
    by (apply Ccont_scal; exact HcW).
  assert (Hsum : Ccont (fun u => Cadd (Cmul (phi (arc Rr u)) (arc' Rr u))
                          (Cmul (F w) (Cmul (Cinv (Cminus (arc Rr u) w)) (arc' Rr u)))))
    by (apply Ccont_add; [ exact HcP | exact HcFW ]).
  (* rewrite the integrand as phi + F(w)/(z-w), then split *)
  unfold pathint.
  rewrite (Cintf_ext
             (fun u => Cmul (Cmul (F (arc Rr u)) (Cinv (Cminus (arc Rr u) w))) (arc' Rr u))
             (fun u => Cadd (Cmul (phi (arc Rr u)) (arc' Rr u))
                            (Cmul (F w) (Cmul (Cinv (Cminus (arc Rr u) w)) (arc' Rr u))))
             Hf Hsum 0 (2 * PI)).
  2:{ intro u. rewrite Hphi_arc.
      unfold Cmul, Cadd, Cminus, Cinv; apply Ceq; cbn [Re Im]; ring. }
  rewrite (Cintf_add (fun u => Cmul (phi (arc Rr u)) (arc' Rr u))
             (fun u => Cmul (F w) (Cmul (Cinv (Cminus (arc Rr u) w)) (arc' Rr u)))
             HcP HcFW Hsum 0 (2 * PI) ltac:(generalize PI_RGT_0; lra)).
  rewrite (Cintf_cmul_l (F w) (fun u => Cmul (Cinv (Cminus (arc Rr u) w)) (arc' Rr u))
             HcW HcFW 0 (2 * PI) ltac:(generalize PI_RGT_0; lra)).
  (* first summand = 0 (phi_loop_zero), second = F(w) * 2 pi i (winding_interior) *)
  change (Cintf (fun u => Cmul (phi (arc Rr u)) (arc' Rr u)) HcP 0 (2 * PI))
    with (pathint (arc Rr) (arc' Rr) phi HcP 0 (2 * PI)).
  rewrite (phi_loop_zero HcP).
  change (Cintf (fun u => Cmul (Cinv (Cminus (arc Rr u) w)) (arc' Rr u)) HcW 0 (2 * PI))
    with (pathint (arc Rr) (arc' Rr) (fun z => Cinv (Cminus z w)) HcW 0 (2 * PI)).
  rewrite (winding_interior Rr w HR HwR HcW).
  apply Ceq; simpl; ring.
Qed.

End CauchyInterior.

Print Assumptions cauchy_interior_cond.
