(* ================================================================= *)
(*  CDerivCoeffDom.v  (identity-theorem plan, DOMAIN-RESTRICTED coeff)  *)
(*                                                                    *)
(*  coeff_recur for g differentiable only on the disk |z| < R+1        *)
(*  (Hgd_disk), instead of everywhere.  Identical to CDerivCoeff except *)
(*  H_deriv gains a  Cmod z < R+1  premise (its sole use of Hgd), which *)
(*  the loop_zero call supplies from |arc| = R < R+1.  Axiom-clean.     *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import ComplexField Cmodulus CIntegral2 CSegInt CPathIntegral CPathFTC
        CGoursatLin CLeibniz CWinding CDeriv CHoloCalculus Holomorphic
        RootsOfUnity CTaylor CWindingOffCenter CDerivCoeff.
Open Scope R_scope.

Section CoeffRecurDom.
Variable Rr : R.
Variable g gd : C -> C.
Hypothesis HR : 0 < Rr.
Hypothesis Hgd_disk : forall z, Cmod z < Rr + 1 -> is_Cderiv g z (gd z).
Hypothesis Hgcc : CcontC g.
Hypothesis Hgdcc : CcontC gd.

Lemma arc_ne0_D : forall u, arc Rr u <> C0.
Proof.
  intros u Hc. assert (HM : Cmod (arc Rr u) = Rr) by (apply Cmod_arc; lra).
  rewrite Hc, (proj2 (Cmod0 C0) eq_refl) in HM. lra.
Qed.

Lemma arcpow_ne0_D : forall k u, Cpow (arc Rr u) k <> C0.
Proof. intros k u; apply Cpow_ne0, arc_ne0_D. Qed.

Lemma Cpow_arc_cont_D : forall k, Ccont (fun u => Cpow (arc Rr u) k).
Proof.
  induction k as [|k IH]; cbn [Cpow].
  - apply Ccont_const.
  - apply Ccont_mul; [ exact (Ccont_arc Rr) | exact IH ].
Qed.

(* the primitive H = g/z^{S m} and its derivative off 0 *)
Lemma H_deriv_D : forall m z, Cmod z < Rr + 1 -> z <> C0 ->
  is_Cderiv (fun z0 => Cmul (g z0) (Cinv (Cpow z0 (S m)))) z
    (Cminus (Cmul (gd z) (Cinv (Cpow z (S m))))
            (Cmul (RtoC (INR (S m))) (Cmul (g z) (Cinv (Cpow z (S (S m))))))).
Proof.
  intros m z Hzd Hz.
  assert (Hpne : Cpow z (S m) <> C0) by (apply Cpow_ne0; exact Hz).
  replace (Cminus (Cmul (gd z) (Cinv (Cpow z (S m))))
            (Cmul (RtoC (INR (S m))) (Cmul (g z) (Cinv (Cpow z (S (S m)))))))
    with (Cadd (Cmul (gd z) (Cinv (Cpow z (S m))))
               (Cmul (g z)
                  (Cmul (Copp (Cinv (Cmul (Cpow z (S m)) (Cpow z (S m)))))
                        (Cmul (RtoC (INR (S m))) (Cpow z m))))).
  2:{ change (Cpow z (S (S m))) with (Cmul z (Cmul z (Cpow z m))).
      change (Cpow z (S m)) with (Cmul z (Cpow z m)).
      set (P := Cpow z m).
      assert (HP : P <> C0) by (apply Cpow_ne0; exact Hz).
      field. split; assumption. }
  apply (Cderiv_mul g (fun z0 => Cinv (Cpow z0 (S m))) z (gd z)
           (Cmul (Copp (Cinv (Cmul (Cpow z (S m)) (Cpow z (S m)))))
                 (Cmul (RtoC (INR (S m))) (Cpow z m)))).
  - apply Hgd_disk; exact Hzd.
  - apply (Cderiv_invc (fun z0 => Cpow z0 (S m)) z (Cmul (RtoC (INR (S m))) (Cpow z m)));
      [ apply Cderiv_Cpow | exact Hpne ].
Qed.

(* the three arc integrands *)
Definition kAi_D (m : nat) (u : R) : C :=      (* gd/z^{S m} . z' *)
  Cmul (Cmul (gd (arc Rr u)) (Cinv (Cpow (arc Rr u) (S m)))) (arc' Rr u).
Definition kBi_D (m : nat) (u : R) : C :=      (* g/z^{S(S m)} . z' *)
  Cmul (Cmul (g (arc Rr u)) (Cinv (Cpow (arc Rr u) (S (S m))))) (arc' Rr u).

Lemma HcA_D : forall m, Ccont (kAi_D m).
Proof.
  intro m; unfold kAi_D. apply Ccont_mul; [ | apply Ccont_arc' ].
  apply Ccont_mul; [ exact (Hgdcc (arc Rr) (Ccont_arc Rr)) | ].
  apply Ccont_inv; [ exact (Cpow_arc_cont_D (S m)) | intro u; apply arcpow_ne0_D ].
Qed.

Lemma HcB_D : forall m, Ccont (kBi_D m).
Proof.
  intro m; unfold kBi_D. apply Ccont_mul; [ | apply Ccont_arc' ].
  apply Ccont_mul; [ exact (Hgcc (arc Rr) (Ccont_arc Rr)) | ].
  apply Ccont_inv; [ exact (Cpow_arc_cont_D (S (S m))) | intro u; apply arcpow_ne0_D ].
Qed.

(* the loop of H' vanishes; splitting it gives the recurrence *)
Theorem coeff_recur_D : forall m,
  Cintf (kAi_D m) (HcA_D m) 0 (2 * PI)
  = Cmul (RtoC (INR (S m))) (Cintf (kBi_D m) (HcB_D m) 0 (2 * PI)).
Proof.
  intro m.
  pose proof (HcA_D m) as HA. pose proof (HcB_D m) as HB.
  set (c := RtoC (INR (S m))).
  (* the loop integrand  H' . z'  and its continuity *)
  assert (HL : Ccont (fun u => Cmul (Cminus
                 (Cmul (gd (arc Rr u)) (Cinv (Cpow (arc Rr u) (S m))))
                 (Cmul c (Cmul (g (arc Rr u)) (Cinv (Cpow (arc Rr u) (S (S m)))))))
                 (arc' Rr u))).
  { apply Ccont_mul; [ | apply Ccont_arc' ].
    apply Ccont_sub.
    - apply Ccont_mul; [ exact (Hgdcc (arc Rr) (Ccont_arc Rr)) | ].
      apply Ccont_inv; [ exact (Cpow_arc_cont_D (S m)) | intro u; apply arcpow_ne0_D ].
    - apply Ccont_scal. apply Ccont_mul; [ exact (Hgcc (arc Rr) (Ccont_arc Rr)) | ].
      apply Ccont_inv; [ exact (Cpow_arc_cont_D (S (S m))) | intro u; apply arcpow_ne0_D ]. }
  (* loop = 0 by pathint_FTC on the closed circle *)
  assert (Hloop : Cintf (fun u => Cmul (Cminus
                 (Cmul (gd (arc Rr u)) (Cinv (Cpow (arc Rr u) (S m))))
                 (Cmul c (Cmul (g (arc Rr u)) (Cinv (Cpow (arc Rr u) (S (S m)))))))
                 (arc' Rr u)) HL 0 (2 * PI) = C0).
  { change (Cintf ?F ?H 0 (2 * PI))
      with (pathint (arc Rr) (arc' Rr)
              (fun z => Cminus (Cmul (gd z) (Cinv (Cpow z (S m))))
                               (Cmul c (Cmul (g z) (Cinv (Cpow z (S (S m))))))) H 0 (2 * PI)).
    rewrite (pathint_FTC (fun z => Cmul (g z) (Cinv (Cpow z (S m))))
               (fun z => Cminus (Cmul (gd z) (Cinv (Cpow z (S m))))
                                (Cmul c (Cmul (g z) (Cinv (Cpow z (S (S m)))))))
               (arc Rr) (arc' Rr) HL 0 (2 * PI)).
    - rewrite arc_closed. unfold Cminus, C0; apply Ceq; cbn [Re Im]; ring.
    - generalize PI_RGT_0; lra.
    - intros u _. unfold c. apply H_deriv_D;
        [ rewrite (Cmod_arc Rr u) by lra; lra | apply arc_ne0_D ].
    - intros u _; apply arc_Re_deriv.
    - intros u _; apply arc_Im_deriv. }
  (* split the loop into  oint kA - c . oint kB  *)
  assert (Hcscal : Ccont (fun u => Cmul c (kBi_D m u)))
    by (apply Ccont_scal; exact HB).
  assert (Hsplit :
    Cintf (fun u => Cmul (Cminus
       (Cmul (gd (arc Rr u)) (Cinv (Cpow (arc Rr u) (S m))))
       (Cmul c (Cmul (g (arc Rr u)) (Cinv (Cpow (arc Rr u) (S (S m)))))))
       (arc' Rr u)) HL 0 (2 * PI)
    = Cminus (Cintf (kAi_D m) HA 0 (2 * PI))
             (Cintf (fun u => Cmul c (kBi_D m u)) Hcscal 0 (2 * PI))).
  { rewrite (Cintf_ext _
               (fun u => Cminus (kAi_D m u) (Cmul c (kBi_D m u)))
               HL (Ccont_sub _ _ HA Hcscal) 0 (2 * PI)).
    2:{ intro u. unfold kAi_D, kBi_D. unfold Cmul, Cminus; apply Ceq; cbn [Re Im]; ring. }
    apply (Cintf_sub (kAi_D m) (fun u => Cmul c (kBi_D m u)) HA Hcscal
             (Ccont_sub _ _ HA Hcscal) 0 (2 * PI) ltac:(generalize PI_RGT_0; lra)). }
  rewrite Hsplit in Hloop.
  rewrite (Cintf_cmul_l c (kBi_D m) HB Hcscal 0 (2 * PI) ltac:(generalize PI_RGT_0; lra)) in Hloop.
  (* Hloop : oint kA - c . oint kB = 0 *)
  assert (Hba : forall A B : C, Cminus A B = C0 -> A = B).
  { clear. intros A B H. apply Ceq;
      [ apply (f_equal Re) in H | apply (f_equal Im) in H ];
      unfold Cminus, C0 in H; cbn in H; lra. }
  pose proof (Hba _ _ Hloop) as Hfin. unfold c in Hfin.
  rewrite (Cintf_irrel (kAi_D m) HA (HcA_D m) 0 (2 * PI)) in Hfin.
  rewrite (Cintf_irrel (kBi_D m) HB (HcB_D m) 0 (2 * PI)) in Hfin.
  exact Hfin.
Qed.

End CoeffRecurDom.

Print Assumptions coeff_recur_D.
