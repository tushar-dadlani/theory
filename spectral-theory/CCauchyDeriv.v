(* ================================================================= *)
(*  CCauchyDeriv.v  (identity-theorem plan, brick B2)                  *)
(*                                                                    *)
(*  The CAUCHY DERIVATIVE FORMULA (first derivative):                  *)
(*     oint_{|z|=R} F(z)/(z-w)^2 dz = 2 pi i . F'(w)   for |w| < R,     *)
(*  where Fd is the derivative of F (is_Cderiv F z (Fd z)) and Fd is    *)
(*  itself holomorphic.                                                *)
(*                                                                    *)
(*  Route (avoids differentiation under the integral): integration by  *)
(*  parts via the closed loop.  H(z) = F(z)/(z-w) has, off w,          *)
(*     H'(z) = Fd(z)/(z-w) - F(z)/(z-w)^2   (product/quotient rule),    *)
(*  and oint_{arc} H' = 0 (pathint_FTC on the closed circle).  Hence    *)
(*     oint F/(z-w)^2 = oint Fd/(z-w) = 2 pi i . Fd(w)                  *)
(*  the last by CCauchyFull.cauchy_interior applied to Fd.             *)
(*                                                                    *)
(*  Axioms: standard classical-Reals only.                            *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra.
Require Import ComplexField Cmodulus CIntegral2 CSegInt CPathIntegral CPathFTC
        CLeibniz Holomorphic CDeriv CHoloCalculus CWinding CWindingOffCenter CCauchyFull.
Open Scope R_scope.

Section CauchyDeriv.
Variable F Fd : C -> C.
Hypothesis HFd : forall z, is_Cderiv F z (Fd z).
Hypothesis HFdhol : forall z, exists d, is_Cderiv Fd z d.
Hypothesis HFcc : CcontC F.
Hypothesis HFdcc : CcontC Fd.
Variable Rr : R.
Variable w : C.
Hypothesis HR : 0 < Rr.
Hypothesis HwR : Cmod w < Rr.

(* the two integrand kernels *)
Definition kFd (z : C) : C := Cmul (Fd z) (Cinv (Cminus z w)).
Definition kF2 (z : C) : C := Cmul (F z) (Cinv (Cmul (Cminus z w) (Cminus z w))).
Definition Hprim (z : C) : C := Cmul (F z) (Cinv (Cminus z w)).

(* z - w never vanishes on the circle |z| = R *)
Lemma arcw_ne : forall u, Cminus (arc Rr u) w <> C0.
Proof.
  intros u Hc.
  assert (Hle : Rr - Cmod w <= Cmod (Cminus (arc Rr u) w)).
  { eapply Rle_trans; [ | apply Cmod_rev_triangle ]. rewrite (Cmod_arc Rr u) by lra. lra. }
  rewrite Hc, (proj2 (Cmod0 C0) eq_refl) in Hle. lra.
Qed.

Lemma arc_ne_w : forall u, arc Rr u <> w.
Proof. intros u Hc. apply (arcw_ne u). rewrite Hc. apply Ceq; simpl; ring. Qed.

(* Hprim' = kFd - kF2  off w  (product rule for F * 1/(z-w)) *)
Lemma Hprim_deriv : forall z, z <> w ->
  is_Cderiv Hprim z (Cminus (kFd z) (kF2 z)).
Proof.
  intros z Hz. assert (Hne : Cminus z w <> C0)
    by (intro Hc; apply Hz; apply Ceq;
        [ apply (f_equal Re) in Hc | apply (f_equal Im) in Hc ];
        unfold Cminus, C0 in Hc; cbn in Hc; lra).
  unfold Hprim.
  replace (Cminus (kFd z) (kF2 z))
     with (Cadd (Cmul (Fd z) (Cinv (Cminus z w)))
                (Cmul (F z)
                  (Cmul (Copp (Cinv (Cmul (Cminus z w) (Cminus z w)))) (Cminus C1 C0)))).
  2:{ unfold kFd, kF2.
      set (X := Cinv (Cmul (Cminus z w) (Cminus z w))). set (Y := Cinv (Cminus z w)).
      unfold Copp, Cadd, Cmul, Cminus, C1, C0; apply Ceq; cbn [Re Im]; ring. }
  apply (Cderiv_mul F (fun z' => Cinv (Cminus z' w)) z (Fd z)
           (Cmul (Copp (Cinv (Cmul (Cminus z w) (Cminus z w)))) (Cminus C1 C0))).
  - apply HFd.
  - apply (Cderiv_invc (fun z' => Cminus z' w) z (Cminus C1 C0)); [ | exact Hne ].
    apply (Cderiv_minus (fun z' => z') (fun _ => w) z C1 C0);
      [ apply Cderiv_id | apply Cderiv_const ].
Qed.

(* continuity of the two bare kernels along the circle *)
Lemma kFd_arc_cont : Ccont (fun u => kFd (arc Rr u)).
Proof.
  unfold kFd.
  apply Ccont_mul; [ apply HFdcc, Ccont_arc | ].
  apply Ccont_inv; [ apply Ccont_minus; [ apply Ccont_arc | apply Ccont_const ] | apply arcw_ne ].
Qed.

Lemma kF2_arc_cont : Ccont (fun u => kF2 (arc Rr u)).
Proof.
  unfold kF2.
  apply Ccont_mul; [ apply HFcc, Ccont_arc | ].
  apply Ccont_inv;
    [ apply Ccont_mul; apply Ccont_minus; solve [ apply Ccont_arc | apply Ccont_const ]
    | intro u; apply Cmul_self_ne0, arcw_ne ].
Qed.

(* oint_{arc} (kFd - kF2) = 0  (integral of a derivative over a closed loop) *)
Lemma loop_zero :
  forall (Hf : Ccont (fun u => Cmul (Cminus (kFd (arc Rr u)) (kF2 (arc Rr u))) (arc' Rr u))),
  pathint (arc Rr) (arc' Rr) (fun z => Cminus (kFd z) (kF2 z)) Hf 0 (2 * PI) = C0.
Proof.
  intro Hf.
  rewrite (pathint_FTC Hprim (fun z => Cminus (kFd z) (kF2 z)) (arc Rr) (arc' Rr) Hf 0 (2 * PI)).
  - rewrite arc_closed. unfold Cminus, C0; apply Ceq; cbn [Re Im]; ring.
  - generalize PI_RGT_0; lra.
  - intros u _. apply Hprim_deriv, arc_ne_w.
  - intros u _; apply arc_Re_deriv.
  - intros u _; apply arc_Im_deriv.
Qed.

(* THE DERIVATIVE FORMULA *)
Theorem cauchy_deriv :
  forall (Hf : Ccont (fun u => Cmul (Cmul (F (arc Rr u))
                     (Cinv (Cmul (Cminus (arc Rr u) w) (Cminus (arc Rr u) w)))) (arc' Rr u))),
  pathint (arc Rr) (arc' Rr)
    (fun z => Cmul (F z) (Cinv (Cmul (Cminus z w) (Cminus z w)))) Hf 0 (2 * PI)
  = Cmul (mkC 0 (2 * PI)) (Fd w).
Proof.
  intro Hf.
  pose proof kFd_arc_cont as HbFd. pose proof kF2_arc_cont as HbF2.
  assert (HcFd : Ccont (fun u => Cmul (kFd (arc Rr u)) (arc' Rr u)))
    by (apply Ccont_mul; [ exact HbFd | apply Ccont_arc' ]).
  assert (HcF2 : Ccont (fun u => Cmul (kF2 (arc Rr u)) (arc' Rr u)))
    by (apply Ccont_mul; [ exact HbF2 | apply Ccont_arc' ]).
  assert (Hsub : Ccont (fun u => Cmul (Cminus (kFd (arc Rr u)) (kF2 (arc Rr u))) (arc' Rr u)))
    by (apply Ccont_mul; [ apply Ccont_sub; [ exact HbFd | exact HbF2 ] | apply Ccont_arc' ]).
  (* the loop of the derivative kernel is 0, and it splits into the two integrals *)
  pose proof (loop_zero Hsub) as Hloop.
  assert (Hsplit : pathint (arc Rr) (arc' Rr) (fun z => Cminus (kFd z) (kF2 z)) Hsub 0 (2 * PI)
    = Cminus (pathint (arc Rr) (arc' Rr) kFd HcFd 0 (2 * PI))
             (pathint (arc Rr) (arc' Rr) kF2 HcF2 0 (2 * PI))).
  { unfold pathint.
    rewrite (Cintf_ext
               (fun u => Cmul (Cminus (kFd (arc Rr u)) (kF2 (arc Rr u))) (arc' Rr u))
               (fun u => Cminus (Cmul (kFd (arc Rr u)) (arc' Rr u))
                                (Cmul (kF2 (arc Rr u)) (arc' Rr u)))
               Hsub (Ccont_sub _ _ HcFd HcF2) 0 (2 * PI)).
    2:{ intro u. unfold Cmul, Cminus; apply Ceq; cbn [Re Im]; ring. }
    apply (Cintf_sub (fun u => Cmul (kFd (arc Rr u)) (arc' Rr u))
             (fun u => Cmul (kF2 (arc Rr u)) (arc' Rr u)) HcFd HcF2
             (Ccont_sub _ _ HcFd HcF2) 0 (2 * PI) ltac:(generalize PI_RGT_0; lra)). }
  rewrite Hsplit in Hloop.
  (* so oint kF2 = oint kFd = 2 pi i Fd(w) *)
  assert (Hba : forall A B : C, Cminus A B = C0 -> B = A).
  { clear. intros A B H. apply Ceq;
      [ apply (f_equal Re) in H | apply (f_equal Im) in H ];
      unfold Cminus, C0 in H; cbn in H; lra. }
  assert (Heq := Hba _ _ Hloop).
  (* kF2 as a pathint equals the goal integrand's pathint (Cintf_irrel on the witness) *)
  assert (Hgoal : pathint (arc Rr) (arc' Rr)
            (fun z => Cmul (F z) (Cinv (Cmul (Cminus z w) (Cminus z w)))) Hf 0 (2 * PI)
          = pathint (arc Rr) (arc' Rr) kF2 HcF2 0 (2 * PI))
    by (unfold pathint, kF2; apply Cintf_irrel).
  rewrite Hgoal, Heq.
  (* oint kFd = oint Fd(z)/(z-w) = 2 pi i Fd(w)  (cauchy_interior on Fd) *)
  destruct (HFdhol w) as [dd Hdd].
  exact (cauchy_interior Fd Rr w dd HFdhol Hdd HR HwR HcFd).
Qed.

End CauchyDeriv.

Print Assumptions cauchy_deriv.
