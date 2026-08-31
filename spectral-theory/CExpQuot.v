(* ================================================================= *)
(*  CExpQuot.v  --  E(u) = (e^u - 1)/u, as an ENTIRE function.         *)
(*                                                                    *)
(*  The first brick of the analytic continuation.  The repo's zeta is  *)
(*     zetaC s = 1/(s-1) + sum_n gtermC s n,                           *)
(*     gtermC s n = a^{-s} - [b^w - a^w]/w,   w = 1-s, a = n+1, b = n+2 *)
(*  and the bracket carries a 1/(1-s), so EVERY term is singular at    *)
(*  s = 1 in the Coq encoding -- even though the singularity is        *)
(*  removable, the numerator vanishing there.  Worse, ZetaFn.zF is     *)
(*  DEFINED to be C0 at s = 1, so the encoded function has the wrong   *)
(*  value, not merely a missing derivative.                            *)
(*                                                                    *)
(*  The fix is algebraic rather than analytic.  Writing r = b/a and    *)
(*  L = ln r,                                                          *)
(*     [b^w - a^w]/w = a^w . L . E(w L),    E(u) = (e^u - 1)/u,        *)
(*  and E is entire, with E(0) = 1.  Every factor is then entire in s, *)
(*  so the term is regular at s = 1 and the sum is the true analytic   *)
(*  continuation.                                                      *)
(*                                                                    *)
(*  Holomorphy of E away from 0 is the quotient rule.  AT 0 it needs   *)
(*  a SECOND-order remainder for Cexpf, |e^u - 1 - u - u^2/2| = O(u^3),*)
(*  whereas CexpRemainder supplies only the first-order O(u^2).  The   *)
(*  second follows from the first along the segment: the t-derivative  *)
(*  of Re(e^{tu} - 1 - tu - (tu)^2/2) is exactly Re(u . (e^{tu} - 1 -  *)
(*  tu)), which the existing bound controls.  One MVT per component.   *)
(*  Axiom-clean.                                                       *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra.
Require Import ComplexField Cmodulus EulerFormula CexpFull CexpfDeriv CexpRemainder
        Holomorphic CDeriv.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  A.  a one-MVT bound (order2_bound's little brother)                *)
(* ----------------------------------------------------------------- *)
Lemma exp_mono_le : forall a b, a <= b -> exp a <= exp b.
Proof.
  intros a b H. destruct (Rle_lt_or_eq_dec a b H) as [Hlt | Heq];
    [ left; apply exp_increasing; exact Hlt | rewrite Heq; apply Rle_refl ].
Qed.

Lemma mvt_bound : forall (f df : R -> R) (M : R), 0 <= M ->
  (forall t, 0 <= t <= 1 -> derivable_pt_lim f t (df t)) ->
  (forall t, 0 <= t <= 1 -> Rabs (df t) <= M) ->
  Rabs (f 1 - f 0) <= M.
Proof.
  intros f df M HM Hf Hbd.
  destruct (MVT_cor2 f df 0 1 Rlt_0_1 (fun c Hc => Hf c Hc)) as [c [Hfc Hc]].
  rewrite Hfc. replace (1 - 0) with 1 by ring. rewrite Rmult_1_r.
  apply Hbd. lra.
Qed.

Lemma Cmod_split : forall z, Cmod z <= Rabs (Re z) + Rabs (Im z).
Proof.
  intro z.
  assert (Ea : Cmod (mkC (Re z) 0) = Rabs (Re z)).
  { unfold Cmod, Cnorm2; cbn [Re Im].
    replace (Re z * Re z + 0 * 0) with (Rsqr (Re z)) by (unfold Rsqr; ring).
    apply sqrt_Rsqr_abs. }
  assert (Eb : Cmod (mkC 0 (Im z)) = Rabs (Im z)).
  { unfold Cmod, Cnorm2; cbn [Re Im].
    replace (0 * 0 + Im z * Im z) with (Rsqr (Im z)) by (unfold Rsqr; ring).
    apply sqrt_Rsqr_abs. }
  assert (Ez : z = Cadd (mkC (Re z) 0) (mkC 0 (Im z)))
    by (apply Ceq; unfold Cadd; cbn [Re Im]; ring).
  rewrite Ez at 1.
  eapply Rle_trans; [ apply Cmod_triangle | ].
  rewrite Ea, Eb. apply Rle_refl.
Qed.

Lemma Re_le_Cmod' : forall z, Rabs (Re z) <= Cmod z.
Proof.
  intro z. unfold Cmod. rewrite <- (sqrt_Rsqr_abs (Re z)).
  apply sqrt_le_1_alt. unfold Rsqr, Cnorm2.
  pose proof (Rle_0_sqr (Im z)) as H; unfold Rsqr in H; nra.
Qed.

Lemma Im_le_Cmod' : forall z, Rabs (Im z) <= Cmod z.
Proof.
  intro z. unfold Cmod. rewrite <- (sqrt_Rsqr_abs (Im z)).
  apply sqrt_le_1_alt. unfold Rsqr, Cnorm2.
  pose proof (Rle_0_sqr (Re z)) as H; unfold Rsqr in H; nra.
Qed.

(* ----------------------------------------------------------------- *)
(*  B.  the second-order remainder for Cexpf                          *)
(* ----------------------------------------------------------------- *)
Section Rem2.
Variable w : C.

Let s := Re w.
Let r := Im w.
Let Rf := fun t : R => exp (t * s) * cos (t * r).
Let If := fun t : R => exp (t * s) * sin (t * r).
Let dRf := fun t : R => exp (t * s) * (s * cos (t * r) - r * sin (t * r)).
Let dIf := fun t : R => exp (t * s) * (s * sin (t * r) + r * cos (t * r)).

Lemma dRf_ok' : forall t, derivable_pt_lim Rf t (dRf t).
Proof.
  intro t; unfold Rf, dRf.
  assert (H := derivable_pt_lim_mult _ _ _ _ _ (dexpts s t) (dcosts r t)).
  replace (exp (t * s) * (s * cos (t * r) - r * sin (t * r)))
    with (exp (t * s) * s * cos (t * r) + exp (t * s) * (- sin (t * r) * r)) by ring.
  exact H.
Qed.

Lemma dIf_ok' : forall t, derivable_pt_lim If t (dIf t).
Proof.
  intro t; unfold If, dIf.
  assert (H := derivable_pt_lim_mult _ _ _ _ _ (dexpts s t) (dsints r t)).
  replace (exp (t * s) * (s * sin (t * r) + r * cos (t * r)))
    with (exp (t * s) * s * sin (t * r) + exp (t * s) * (cos (t * r) * r)) by ring.
  exact H.
Qed.

(* Cexpf (t w) has real part Rf t and imaginary part If t *)
Lemma Cexpf_tw : forall t : R,
  Cexpf (Cmul (RtoC t) w) = mkC (Rf t) (If t).
Proof.
  intro t. unfold Cexpf, Rf, If.
  apply Ceq; unfold Cmul, RtoC, Cexp; cbn [Re Im];
    fold s; fold r;
    [ replace (t * s - 0 * r) with (t * s) by ring;
      replace (t * r + 0 * s) with (t * r) by ring; ring
    | replace (t * s - 0 * r) with (t * s) by ring;
      replace (t * r + 0 * s) with (t * r) by ring; ring ].
Qed.

(* the t-derivative of Re(e^{tw}) is Re(w e^{tw}) -- and likewise for Im *)
Lemma dRf_eq : forall t : R,
  dRf t = Re (Cmul w (Cexpf (Cmul (RtoC t) w))).
Proof.
  intro t. rewrite Cexpf_tw. unfold dRf, Rf, If, Cmul; cbn [Re Im].
  fold s; fold r. ring.
Qed.

Lemma dIf_eq : forall t : R,
  dIf t = Im (Cmul w (Cexpf (Cmul (RtoC t) w))).
Proof.
  intro t. rewrite Cexpf_tw. unfold dIf, Rf, If, Cmul; cbn [Re Im].
  fold s; fold r. ring.
Qed.

(* the two component remainders, each by one MVT.  Coefficients are    *)
(* written IN FRONT so that mult_real_fct matches definitionally.      *)
Let Gr := fun t : R => Rf t - (1 + s * t + (s * s - r * r) / 2 * t ^ 2).
Let dGr := fun t : R => dRf t - (s + (s * s - r * r) * t).
Let Gi := fun t : R => If t - (r * t + s * r * t ^ 2).
Let dGi := fun t : R => dIf t - (r + 2 * (s * r) * t).

Lemma Gr_deriv : forall t, derivable_pt_lim Gr t (dGr t).
Proof.
  intro t. unfold Gr, dGr.
  apply derivable_pt_lim_minus; [ apply dRf_ok' | ].
  replace (s + (s * s - r * r) * t)
    with (0 + s * 1 + (s * s - r * r) / 2 * (INR 2 * t ^ Init.Nat.pred 2))
    by (simpl; field).
  apply derivable_pt_lim_plus.
  - apply derivable_pt_lim_plus.
    + apply derivable_pt_lim_const.
    + apply (derivable_pt_lim_scal (fun x => x) s t 1). apply derivable_pt_lim_id.
  - apply (derivable_pt_lim_scal (fun x => x ^ 2) ((s * s - r * r) / 2) t
             (INR 2 * t ^ Init.Nat.pred 2)).
    apply derivable_pt_lim_pow.
Qed.

Lemma Gi_deriv : forall t, derivable_pt_lim Gi t (dGi t).
Proof.
  intro t. unfold Gi, dGi.
  apply derivable_pt_lim_minus; [ apply dIf_ok' | ].
  replace (r + 2 * (s * r) * t)
    with (r * 1 + s * r * (INR 2 * t ^ Init.Nat.pred 2))
    by (simpl; field).
  apply derivable_pt_lim_plus.
  - apply (derivable_pt_lim_scal (fun x => x) r t 1). apply derivable_pt_lim_id.
  - apply (derivable_pt_lim_scal (fun x => x ^ 2) (s * r) t
             (INR 2 * t ^ Init.Nat.pred 2)).
    apply derivable_pt_lim_pow.
Qed.

(* dGr t and dGi t are the components of w . (e^{tw} - 1 - tw), which  *)
(* the EXISTING first-order remainder already bounds.                  *)
Lemma dG_eq : forall t : R,
  dGr t = Re (Cmul w (Cminus (Cminus (Cexpf (Cmul (RtoC t) w)) C1)
                         (Cmul (RtoC t) w)))
  /\ dGi t = Im (Cmul w (Cminus (Cminus (Cexpf (Cmul (RtoC t) w)) C1)
                            (Cmul (RtoC t) w))).
Proof.
  intro t. rewrite Cexpf_tw.
  unfold dGr, dGi, dRf, dIf, Rf, If, Cmul, Cminus, Cadd, Copp, C1, RtoC;
    cbn [Re Im]. fold s; fold r. split; ring.
Qed.

Lemma dG_bound : forall t, 0 <= t <= 1 ->
  Rabs (dGr t) <= 3 * Cmod w ^ 3 * exp (Cmod w)
  /\ Rabs (dGi t) <= 3 * Cmod w ^ 3 * exp (Cmod w).
Proof.
  intros t Ht.
  set (u := Cmul (RtoC t) w).
  assert (Hmu : Cmod u = t * Cmod w).
  { unfold u. rewrite Cmod_mul, Cmod_RtoC, Rabs_right by lra. reflexivity. }
  assert (Hle : Cmod u <= Cmod w).
  { rewrite Hmu. pose proof (Cmod_nonneg w). nra. }
  pose proof (Cexpf_remainder_w u) as HR.
  set (D := Cminus (Cminus (Cexpf u) C1) u) in *.
  assert (HD : Cmod D <= 3 * Cmod w ^ 2 * exp (Cmod w)).
  { eapply Rle_trans; [ exact HR | ].
    assert (H1 : Cmod u ^ 2 <= Cmod w ^ 2)
      by (apply pow_incr; split; [ apply Cmod_nonneg | exact Hle ]).
    assert (H2 : exp (Cmod u) <= exp (Cmod w)) by (apply exp_mono_le; exact Hle).
    assert (H3 : 0 < exp (Cmod u)) by apply exp_pos.
    assert (H4 : 0 <= Cmod u ^ 2) by (apply pow_le; apply Cmod_nonneg).
    nra. }
  assert (Hprod : Cmod (Cmul w D) <= 3 * Cmod w ^ 3 * exp (Cmod w)).
  { rewrite Cmod_mul.
    assert (Hw : 0 <= Cmod w) by apply Cmod_nonneg.
    assert (Hstep : Cmod w * Cmod D <= Cmod w * (3 * Cmod w ^ 2 * exp (Cmod w)))
      by (apply Rmult_le_compat_l; assumption).
    nra. }
  destruct (dG_eq t) as [Er Ei]. fold u in Er, Ei. fold D in Er, Ei.
  split.
  - rewrite Er. eapply Rle_trans; [ apply Re_le_Cmod' | exact Hprod ].
  - rewrite Ei. eapply Rle_trans; [ apply Im_le_Cmod' | exact Hprod ].
Qed.

Theorem Cexpf_remainder2 :
  Cmod (Cminus (Cminus (Cminus (Cexpf w) C1) w)
          (Cmul (RtoC (/ 2)) (Cmul w w)))
  <= 6 * Cmod w ^ 3 * exp (Cmod w).
Proof.
  assert (HM : 0 <= 3 * Cmod w ^ 3 * exp (Cmod w)).
  { pose proof (Cmod_nonneg w). pose proof (exp_pos (Cmod w)).
    assert (0 <= Cmod w ^ 3) by (apply pow_le; assumption). nra. }
  assert (Hr : Rabs (Gr 1 - Gr 0) <= 3 * Cmod w ^ 3 * exp (Cmod w)).
  { apply (mvt_bound Gr dGr _ HM).
    - intros t _. apply Gr_deriv.
    - intros t Ht. apply (proj1 (dG_bound t Ht)). }
  assert (Hi : Rabs (Gi 1 - Gi 0) <= 3 * Cmod w ^ 3 * exp (Cmod w)).
  { apply (mvt_bound Gi dGi _ HM).
    - intros t _. apply Gi_deriv.
    - intros t Ht. apply (proj2 (dG_bound t Ht)). }
  (* Gr 0 = Gi 0 = 0, and (Gr 1, Gi 1) are the components of the target *)
  assert (Er0 : Gr 0 = 0)
    by (unfold Gr, Rf; simpl; rewrite Rmult_0_l, exp_0, Rmult_0_l, cos_0; ring).
  assert (Ei0 : Gi 0 = 0)
    by (unfold Gi, If; simpl; rewrite Rmult_0_l, exp_0, Rmult_0_l, sin_0; ring).
  set (T := Cminus (Cminus (Cminus (Cexpf w) C1) w)
              (Cmul (RtoC (/ 2)) (Cmul w w))).
  assert (ETr : Re T = Gr 1).
  { assert (E1 : Cmul (RtoC 1) w = w)
      by (apply Ceq; unfold Cmul, RtoC; cbn [Re Im]; ring).
    unfold T, Gr, Rf.
    assert (Hc : Cexpf w = mkC (exp (1 * s) * cos (1 * r)) (exp (1 * s) * sin (1 * r))).
    { rewrite <- E1 at 1. rewrite Cexpf_tw. reflexivity. }
    rewrite Hc. unfold Cminus, Cadd, Copp, Cmul, C1, RtoC; cbn [Re Im].
    fold s; fold r. field. }
  assert (ETi : Im T = Gi 1).
  { assert (E1 : Cmul (RtoC 1) w = w)
      by (apply Ceq; unfold Cmul, RtoC; cbn [Re Im]; ring).
    unfold T, Gi, If.
    assert (Hc : Cexpf w = mkC (exp (1 * s) * cos (1 * r)) (exp (1 * s) * sin (1 * r))).
    { rewrite <- E1 at 1. rewrite Cexpf_tw. reflexivity. }
    rewrite Hc. unfold Cminus, Cadd, Copp, Cmul, C1, RtoC; cbn [Re Im].
    fold s; fold r. field. }
  eapply Rle_trans; [ apply Cmod_split | ].
  rewrite ETr, ETi. rewrite Er0 in Hr. rewrite Ei0 in Hi.
  replace (Gr 1 - 0) with (Gr 1) in Hr by ring.
  replace (Gi 1 - 0) with (Gi 1) in Hi by ring.
  lra.
Qed.

End Rem2.

Print Assumptions mvt_bound.
Print Assumptions Cexpf_remainder2.
