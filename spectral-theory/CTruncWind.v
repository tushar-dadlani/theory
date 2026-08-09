(* ================================================================= *)
(*  CTruncWind.v  —  Milestone C, brick C4-4: the truncated winding     *)
(*  integral  ∮_C dz/z = 2πi.                                           *)
(*                                                                    *)
(*  C = (arc |z|=R over [−α,α], through 0) + (chord from arc R α to      *)
(*  arc R (−α)), α∈(π/2,π).  Arc part = mkC 0 (2α) (integrand ≡ i,        *)
(*  arc_over_id); chord part = mkC 0 (−2·atan(y/a)), a=R cos α, y=R sin α *)
(*  (FTC with ½·ln N and −atan antiderivatives); and 2α − 2·atan(y/a) =  *)
(*  2π since atan(tan α) = α−π (atan_tan on α−π, tan(α−π)=tan α).         *)
(* ================================================================= *)

From Stdlib Require Import Reals Ratan Lra Lia.
Require Import ComplexField Cmodulus CImproperIntegral CIntegral2
        CPathIntegral CSegInt CWinding ContinuousCoV.
Open Scope R_scope.

(* ---- the arc part: integrand collapses to the constant i ---- *)
Lemma arc_winding : forall (R alpha : R), 0 < R ->
  forall (Hf : Ccont (fun u => Cmul (Cinv (arc R u)) (arc' R u))),
  pathint (arc R) (arc' R) Cinv Hf (- alpha) alpha = mkC 0 (2 * alpha).
Proof.
  intros R alpha HR Hf; unfold pathint.
  transitivity (Cintf (fun _ => Ci) (Ccont_const Ci) (- alpha) alpha).
  - apply Cintf_ext; intro u; apply arc_over_id; exact HR.
  - rewrite Cintf_const_ab; unfold Cmul, RtoC, Ci; apply Ceq; cbn; ring.
Qed.

(* ---- the chord integrand denominator N(s) = a² + y²(1−2s)² ---- *)
Definition Nfun (a y s : R) : R := a * a + y * y * (1 - 2 * s) * (1 - 2 * s).

Lemma Nfun_pos : forall a y s, a <> 0 -> 0 < Nfun a y s.
Proof.
  intros a y s Ha; unfold Nfun.
  assert (Ha2 : 0 < a * a) by (destruct (Rdichotomy a 0 Ha); nra).
  pose proof (Rle_0_sqr y) as Hy; unfold Rsqr in Hy.
  pose proof (Rle_0_sqr (1 - 2 * s)) as Hs; unfold Rsqr in Hs.
  nra.
Qed.

(* Nfun's derivative, proved directly: the difference quotient is
   -4 y² (1-2s) + 4 y² h, off the limit by exactly 4 y² h. *)
Lemma Nfun_deriv : forall a y s,
  derivable_pt_lim (Nfun a y) s (- 4 * (y * y) * (1 - 2 * s)).
Proof.
  intros a y s eps Heps.
  set (K := 4 * (y * y) + 1).
  assert (HK : 0 < K).
  { unfold K; pose proof (Rle_0_sqr y) as Hy; unfold Rsqr in Hy; nra. }
  exists (mkposreal (eps / K) (Rdiv_lt_0_compat eps K Heps HK)).
  intros h Hh0 Hlt. unfold Nfun.
  replace ((a * a + y * y * (1 - 2 * (s + h)) * (1 - 2 * (s + h)) -
            (a * a + y * y * (1 - 2 * s) * (1 - 2 * s))) / h -
           - 4 * (y * y) * (1 - 2 * s))
     with (4 * (y * y) * h) by (field; exact Hh0).
  rewrite Rabs_mult.
  rewrite (Rabs_pos_eq (4 * (y * y)));
    [ | pose proof (Rle_0_sqr y) as Hy; unfold Rsqr in Hy; nra ].
  apply Rle_lt_trans with (K * Rabs h).
  - apply Rmult_le_compat_r; [ apply Rabs_pos | unfold K; nra ].
  - replace eps with (K * (eps / K)) by (field; lra).
    apply Rmult_lt_compat_l; [ exact HK | exact Hlt ].
Qed.

(* ---- Re antiderivative:  G_Re(s) = ½·ln N(s),  G_Re' = Re-integrand ---- *)
Definition GRe (a y s : R) : R := / 2 * ln (Nfun a y s).

Lemma GRe_deriv : forall a y s, a <> 0 ->
  derivable_pt_lim (GRe a y) s (- 2 * (y * y) * (1 - 2 * s) / Nfun a y s).
Proof.
  intros a y s Ha.
  assert (Hcomp : derivable_pt_lim (fun s => ln (Nfun a y s)) s
                    (/ Nfun a y s * (- 4 * (y * y) * (1 - 2 * s)))).
  { apply (derivable_pt_lim_comp (Nfun a y) ln s
             (- 4 * (y * y) * (1 - 2 * s)) (/ Nfun a y s)).
    - apply Nfun_deriv.
    - apply derivable_pt_lim_ln, Nfun_pos; exact Ha. }
  unfold GRe.
  replace (- 2 * (y * y) * (1 - 2 * s) / Nfun a y s)
     with (/ 2 * (/ Nfun a y s * (- 4 * (y * y) * (1 - 2 * s))))
     by (field; apply Rgt_not_eq, Nfun_pos; exact Ha).
  exact (derivable_pt_lim_scal (fun s => ln (Nfun a y s)) (/ 2) s
           (/ Nfun a y s * (- 4 * (y * y) * (1 - 2 * s))) Hcomp).
Qed.

(* ---- Im antiderivative:  G_Im(s) = −atan(y(1−2s)/(−a)) ---- *)
Definition Ginn (a y s : R) : R := y * (1 - 2 * s) / (- a).

Lemma Ginn_deriv : forall a y s, a <> 0 ->
  derivable_pt_lim (Ginn a y) s (y * (- 2) / (- a)).
Proof.
  intros a y s Ha eps Heps. exists (mkposreal 1 Rlt_0_1). intros h Hh0 _.
  unfold Ginn.
  assert (Hna : - a <> 0) by (intro Hc; apply Ha; lra).
  replace ((y * (1 - 2 * (s + h)) / (- a) - y * (1 - 2 * s) / (- a)) / h -
           y * (- 2) / (- a)) with 0 by (field; split; assumption).
  rewrite Rabs_R0; exact Heps.
Qed.

Lemma one_plus_inner : forall a y s, a <> 0 ->
  1 + (Ginn a y s) ^ 2 = Nfun a y s / (a * a).
Proof.
  intros a y s Ha. unfold Ginn, Nfun.
  field; exact Ha.
Qed.

Definition GIm (a y s : R) : R := - atan (Ginn a y s).

Lemma GIm_deriv : forall a y s, a <> 0 ->
  derivable_pt_lim (GIm a y) s (- 2 * a * y / Nfun a y s).
Proof.
  intros a y s Ha.
  assert (Hcomp : derivable_pt_lim (fun s => atan (Ginn a y s)) s
                    (/ (1 + (Ginn a y s) ^ 2) * (y * (- 2) / (- a)))).
  { apply (derivable_pt_lim_comp (Ginn a y) atan s
             (y * (- 2) / (- a)) (/ (1 + (Ginn a y s) ^ 2))).
    - apply Ginn_deriv; exact Ha.
    - apply derivable_pt_lim_atan. }
  unfold GIm.
  assert (Hna : - a <> 0) by (intro Hc; apply Ha; lra).
  assert (HN : Nfun a y s <> 0) by (apply Rgt_not_eq, Nfun_pos; exact Ha).
  assert (Ha2 : a * a <> 0) by (apply Rmult_integral_contrapositive_currified; exact Ha).
  replace (- 2 * a * y / Nfun a y s)
     with (- (/ (1 + (Ginn a y s) ^ 2) * (y * (- 2) / (- a)))).
  2:{ rewrite (one_plus_inner a y s Ha). field; repeat split; assumption. }
  exact (derivable_pt_lim_opp (fun s => atan (Ginn a y s)) s
           (/ (1 + (Ginn a y s) ^ 2) * (y * (- 2) / (- a))) Hcomp).
Qed.

(* ---- the chord geometry, in clean mkC form ---- *)
Lemma seg_chord : forall a y s,
  seg (mkC a y) (mkC a (- y)) s = mkC a (y * (1 - 2 * s)).
Proof. intros; unfold seg, Cadd, Cmul, Cminus, RtoC; apply Ceq; cbn; ring. Qed.

Lemma seg'_chord : forall a y s,
  seg' (mkC a y) (mkC a (- y)) s = mkC 0 (- 2 * y).
Proof. intros; unfold seg', Cminus; apply Ceq; cbn; ring. Qed.

Lemma Cnorm2_chord : forall a y s,
  Cnorm2 (mkC a (y * (1 - 2 * s))) = Nfun a y s.
Proof. intros; unfold Cnorm2, Nfun; cbn [Re Im]; ring. Qed.

(* ---- the chord integrand, componentwise ---- *)
Lemma chord_Re : forall a y s, a <> 0 ->
  Re (Cmul (Cinv (seg (mkC a y) (mkC a (- y)) s))
           (seg' (mkC a y) (mkC a (- y)) s))
  = - 2 * (y * y) * (1 - 2 * s) / Nfun a y s.
Proof.
  intros a y s Ha.
  rewrite seg_chord, seg'_chord.
  unfold Cmul, Cinv; cbn [Re Im]; rewrite !Cnorm2_chord.
  field; apply Rgt_not_eq, Nfun_pos; exact Ha.
Qed.

Lemma chord_Im : forall a y s, a <> 0 ->
  Im (Cmul (Cinv (seg (mkC a y) (mkC a (- y)) s))
           (seg' (mkC a y) (mkC a (- y)) s))
  = - 2 * a * y / Nfun a y s.
Proof.
  intros a y s Ha.
  rewrite seg_chord, seg'_chord.
  unfold Cmul, Cinv; cbn [Re Im]; rewrite !Cnorm2_chord.
  field; apply Rgt_not_eq, Nfun_pos; exact Ha.
Qed.

(* ---- the chord winding contribution:  ∫chord dz/z = mkC 0 (−2 atan(y/a)) ---- *)
Lemma chord_winding : forall (a y : R) (Ha : a <> 0)
  (Hf : Ccont (fun u => Cmul (Cinv (seg (mkC a y) (mkC a (- y)) u))
                             (seg' (mkC a y) (mkC a (- y)) u))),
  pathint (seg (mkC a y) (mkC a (- y))) (seg' (mkC a y) (mkC a (- y))) Cinv Hf 0 1
  = mkC 0 (- 2 * atan (y / a)).
Proof.
  intros a y Ha Hf. unfold pathint. apply Ceq.
  - (* Re part = 0 *)
    rewrite Re_Cintf.
    rewrite (FTC_antideriv _ (GRe a y) 0 1 Rle_0_1
               (fun x _ => proj1 Hf x) (cont_RI _ (proj1 Hf) 0 1)).
    + unfold GRe.
      assert (HN : Nfun a y 1 = Nfun a y 0) by (unfold Nfun; ring).
      rewrite HN; cbn [Re Im]; ring.
    + split; [ | lra ]. intros x _.
      exists (exist (fun l => derivable_pt_lim (GRe a y) x l)
                (- 2 * (y * y) * (1 - 2 * x) / Nfun a y x) (GRe_deriv a y x Ha)).
      unfold derive_pt; simpl; apply chord_Re; exact Ha.
  - (* Im part = -2 atan(y/a) *)
    rewrite Im_Cintf.
    rewrite (FTC_antideriv _ (GIm a y) 0 1 Rle_0_1
               (fun x _ => proj2 Hf x) (cont_RI _ (proj2 Hf) 0 1)).
    + unfold GIm, Ginn.
      assert (Hna : - a <> 0) by (intro Hc; apply Ha; lra).
      replace (y * (1 - 2 * 1) / (- a)) with (y / a) by (field; assumption).
      replace (y * (1 - 2 * 0) / (- a)) with (- (y / a)) by (field; assumption).
      rewrite atan_opp; cbn [Re Im]; ring.
    + split; [ | lra ]. intros x _.
      exists (exist (fun l => derivable_pt_lim (GIm a y) x l)
                (- 2 * a * y / Nfun a y x) (GIm_deriv a y x Ha)).
      unfold derive_pt; simpl; apply chord_Im; exact Ha.
Qed.

(* ---- for α∈(π/2,π):  cos α < 0,  and  atan(tan α) = α − π ---- *)
Lemma cos_neg_on_quad2 : forall alpha, PI / 2 < alpha < PI -> cos alpha < 0.
Proof.
  intros alpha [H1 H2]. assert (HPI := PI_RGT_0).
  assert (Hpa : cos (PI - alpha) = - cos alpha)
    by (rewrite cos_minus, sin_PI, cos_PI; ring).
  assert (Hpos : 0 < cos (PI - alpha)) by (apply cos_gt_0; lra).
  lra.
Qed.

Lemma atan_ratio : forall (R alpha : R), 0 < R -> PI / 2 < alpha < PI ->
  atan (R * sin alpha / (R * cos alpha)) = alpha - PI.
Proof.
  intros R alpha HR Ha. assert (HPI := PI_RGT_0).
  assert (Hcos : cos alpha < 0) by (apply cos_neg_on_quad2; exact Ha).
  replace (R * sin alpha / (R * cos alpha)) with (tan (alpha - PI)).
  - apply atan_tan; split; lra.
  - unfold tan. rewrite sin_minus, cos_minus, sin_PI, cos_PI.
    field; split; [ | apply Rgt_not_eq; exact HR ]; lra.
Qed.

(* ================================================================= *)
(*  THE TRUNCATED WINDING NUMBER:   ∮_C dz/z = 2πi.                     *)
(*  C = arc |z|=R over [−α,α] (through 0), then chord back.             *)
(* ================================================================= *)
Theorem trunc_winding : forall (R alpha : R), 0 < R -> PI / 2 < alpha < PI ->
  forall (HfA : Ccont (fun u => Cmul (Cinv (arc R u)) (arc' R u)))
         (HfC : Ccont (fun u =>
                  Cmul (Cinv (seg (mkC (R * cos alpha) (R * sin alpha))
                                  (mkC (R * cos alpha) (- (R * sin alpha))) u))
                       (seg' (mkC (R * cos alpha) (R * sin alpha))
                             (mkC (R * cos alpha) (- (R * sin alpha))) u))),
  Cadd (pathint (arc R) (arc' R) Cinv HfA (- alpha) alpha)
       (pathint (seg (mkC (R * cos alpha) (R * sin alpha))
                     (mkC (R * cos alpha) (- (R * sin alpha))))
                (seg' (mkC (R * cos alpha) (R * sin alpha))
                     (mkC (R * cos alpha) (- (R * sin alpha)))) Cinv HfC 0 1)
  = mkC 0 (2 * PI).
Proof.
  intros R alpha HR Ha HfA HfC.
  assert (Hcos : cos alpha < 0) by (apply cos_neg_on_quad2; exact Ha).
  assert (Hane : R * cos alpha <> 0)
    by (apply Rmult_integral_contrapositive_currified;
        [ apply Rgt_not_eq; exact HR | apply Rlt_not_eq; exact Hcos ]).
  rewrite (arc_winding R alpha HR HfA).
  rewrite (chord_winding (R * cos alpha) (R * sin alpha) Hane HfC).
  unfold Cadd; cbn [Re Im]. apply Ceq; cbn [Re Im].
  - ring.
  - rewrite (atan_ratio R alpha HR Ha). ring.
Qed.

Print Assumptions trunc_winding.

(* ================================================================= *)
(*  END — brick C4-4 complete:  ∮_C dz/z = 2πi.                         *)
(* ================================================================= *)
