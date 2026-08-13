(* ================================================================= *)
(*  CDerivCoeff.v  (identity-theorem plan, B2-iterate / B5 bridge)     *)
(*                                                                    *)
(*  The Cauchy coefficient recurrence, connecting the Taylor           *)
(*  coefficient integrals a_k = oint f/z^{k+1} to derivatives:         *)
(*                                                                    *)
(*    oint_{|z|=R} g'(z)/z^k dz = k . oint_{|z|=R} g(z)/z^{k+1} dz      *)
(*                                                                    *)
(*  by integration by parts (closed loop of H = g/z^k), the centre     *)
(*  analogue of CCauchyDeriv.  Iterating with the base                 *)
(*  oint g/z = 2 pi i . g(0) (B1) gives a_n(f) = 2 pi i . f^{(n)}(0)/n! *)
(*  so "all a_k = 0" <=> "all derivatives vanish at 0" -- the bridge    *)
(*  feeding B4 (CTaylorRem.taylor_center_zero) from B5.                 *)
(*                                                                    *)
(*  Foundation: Cderiv_Cpow, the derivative of z^n.  Axiom-clean.      *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import ComplexField Cmodulus CIntegral2 CSegInt CPathIntegral CPathFTC
        CGoursatLin CLeibniz CWinding CDeriv CHoloCalculus Holomorphic
        RootsOfUnity CTaylor CWindingOffCenter.
Open Scope R_scope.

(* ---- the derivative of z^{n+1} is (n+1) z^n ---- *)
Lemma Cderiv_Cpow : forall n z,
  is_Cderiv (fun z0 => Cpow z0 (S n)) z (Cmul (RtoC (INR (S n))) (Cpow z n)).
Proof.
  induction n as [|n IH]; intro z.
  - (* z^1, derivative 1 *)
    replace (Cmul (RtoC (INR 1)) (Cpow z 0)) with (Cadd (Cmul C1 C1) (Cmul z C0))
      by (cbn [Cpow INR]; apply Ceq; unfold RtoC, Cmul, Cadd, C1, C0; cbn [Re Im]; ring).
    apply (Cderiv_mul (fun z0 => z0) (fun _ => C1) z C1 C0);
      [ apply Cderiv_id | apply Cderiv_const ].
  - (* z^{S(S n)} = z . z^{S n}, product rule with IH *)
    replace (Cmul (RtoC (INR (S (S n)))) (Cpow z (S n)))
       with (Cadd (Cmul C1 (Cpow z (S n)))
                  (Cmul z (Cmul (RtoC (INR (S n))) (Cpow z n)))).
    2:{ change (Cpow z (S n)) with (Cmul z (Cpow z n)).
        rewrite !S_INR; apply Ceq; unfold RtoC, Cmul, Cadd, C1; cbn [Re Im]; ring. }
    apply (Cderiv_mul (fun z0 => z0) (fun z0 => Cpow z0 (S n)) z C1
             (Cmul (RtoC (INR (S n))) (Cpow z n)));
      [ apply Cderiv_id | exact (IH z) ].
Qed.

(* ================================================================= *)
(*  The coefficient recurrence, by integration by parts               *)
(* ================================================================= *)

Section CoeffRecur.
Variable Rr : R.
Variable g gd : C -> C.
Hypothesis HR : 0 < Rr.
Hypothesis Hgd : forall z, is_Cderiv g z (gd z).
Hypothesis Hgcc : CcontC g.
Hypothesis Hgdcc : CcontC gd.

Lemma arc_ne0 : forall u, arc Rr u <> C0.
Proof.
  intros u Hc. assert (HM : Cmod (arc Rr u) = Rr) by (apply Cmod_arc; lra).
  rewrite Hc, (proj2 (Cmod0 C0) eq_refl) in HM. lra.
Qed.

Lemma arcpow_ne0 : forall k u, Cpow (arc Rr u) k <> C0.
Proof. intros k u; apply Cpow_ne0, arc_ne0. Qed.

Lemma Cpow_arc_cont : forall k, Ccont (fun u => Cpow (arc Rr u) k).
Proof.
  induction k as [|k IH]; cbn [Cpow].
  - apply Ccont_const.
  - apply Ccont_mul; [ exact (Ccont_arc Rr) | exact IH ].
Qed.

(* the primitive H = g/z^{S m} and its derivative off 0 *)
Lemma H_deriv : forall m z, z <> C0 ->
  is_Cderiv (fun z0 => Cmul (g z0) (Cinv (Cpow z0 (S m)))) z
    (Cminus (Cmul (gd z) (Cinv (Cpow z (S m))))
            (Cmul (RtoC (INR (S m))) (Cmul (g z) (Cinv (Cpow z (S (S m))))))).
Proof.
  intros m z Hz.
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
  - apply Hgd.
  - apply (Cderiv_invc (fun z0 => Cpow z0 (S m)) z (Cmul (RtoC (INR (S m))) (Cpow z m)));
      [ apply Cderiv_Cpow | exact Hpne ].
Qed.

(* the three arc integrands *)
Definition kAi (m : nat) (u : R) : C :=      (* gd/z^{S m} . z' *)
  Cmul (Cmul (gd (arc Rr u)) (Cinv (Cpow (arc Rr u) (S m)))) (arc' Rr u).
Definition kBi (m : nat) (u : R) : C :=      (* g/z^{S(S m)} . z' *)
  Cmul (Cmul (g (arc Rr u)) (Cinv (Cpow (arc Rr u) (S (S m))))) (arc' Rr u).

Lemma HcA : forall m, Ccont (kAi m).
Proof.
  intro m; unfold kAi. apply Ccont_mul; [ | apply Ccont_arc' ].
  apply Ccont_mul; [ exact (Hgdcc (arc Rr) (Ccont_arc Rr)) | ].
  apply Ccont_inv; [ exact (Cpow_arc_cont (S m)) | intro u; apply arcpow_ne0 ].
Qed.

Lemma HcB : forall m, Ccont (kBi m).
Proof.
  intro m; unfold kBi. apply Ccont_mul; [ | apply Ccont_arc' ].
  apply Ccont_mul; [ exact (Hgcc (arc Rr) (Ccont_arc Rr)) | ].
  apply Ccont_inv; [ exact (Cpow_arc_cont (S (S m))) | intro u; apply arcpow_ne0 ].
Qed.

(* the loop of H' vanishes; splitting it gives the recurrence *)
Theorem coeff_recur : forall m,
  Cintf (kAi m) (HcA m) 0 (2 * PI)
  = Cmul (RtoC (INR (S m))) (Cintf (kBi m) (HcB m) 0 (2 * PI)).
Proof.
  intro m.
  pose proof (HcA m) as HA. pose proof (HcB m) as HB.
  set (c := RtoC (INR (S m))).
  (* the loop integrand  H' . z'  and its continuity *)
  assert (HL : Ccont (fun u => Cmul (Cminus
                 (Cmul (gd (arc Rr u)) (Cinv (Cpow (arc Rr u) (S m))))
                 (Cmul c (Cmul (g (arc Rr u)) (Cinv (Cpow (arc Rr u) (S (S m)))))))
                 (arc' Rr u))).
  { apply Ccont_mul; [ | apply Ccont_arc' ].
    apply Ccont_sub.
    - apply Ccont_mul; [ exact (Hgdcc (arc Rr) (Ccont_arc Rr)) | ].
      apply Ccont_inv; [ exact (Cpow_arc_cont (S m)) | intro u; apply arcpow_ne0 ].
    - apply Ccont_scal. apply Ccont_mul; [ exact (Hgcc (arc Rr) (Ccont_arc Rr)) | ].
      apply Ccont_inv; [ exact (Cpow_arc_cont (S (S m))) | intro u; apply arcpow_ne0 ]. }
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
    - intros u _. unfold c. apply H_deriv, arc_ne0.
    - intros u _; apply arc_Re_deriv.
    - intros u _; apply arc_Im_deriv. }
  (* split the loop into  oint kA - c . oint kB  *)
  assert (Hcscal : Ccont (fun u => Cmul c (kBi m u)))
    by (apply Ccont_scal; exact HB).
  assert (Hsplit :
    Cintf (fun u => Cmul (Cminus
       (Cmul (gd (arc Rr u)) (Cinv (Cpow (arc Rr u) (S m))))
       (Cmul c (Cmul (g (arc Rr u)) (Cinv (Cpow (arc Rr u) (S (S m)))))))
       (arc' Rr u)) HL 0 (2 * PI)
    = Cminus (Cintf (kAi m) HA 0 (2 * PI))
             (Cintf (fun u => Cmul c (kBi m u)) Hcscal 0 (2 * PI))).
  { rewrite (Cintf_ext _
               (fun u => Cminus (kAi m u) (Cmul c (kBi m u)))
               HL (Ccont_sub _ _ HA Hcscal) 0 (2 * PI)).
    2:{ intro u. unfold kAi, kBi. unfold Cmul, Cminus; apply Ceq; cbn [Re Im]; ring. }
    apply (Cintf_sub (kAi m) (fun u => Cmul c (kBi m u)) HA Hcscal
             (Ccont_sub _ _ HA Hcscal) 0 (2 * PI) ltac:(generalize PI_RGT_0; lra)). }
  rewrite Hsplit in Hloop.
  rewrite (Cintf_cmul_l c (kBi m) HB Hcscal 0 (2 * PI) ltac:(generalize PI_RGT_0; lra)) in Hloop.
  (* Hloop : oint kA - c . oint kB = 0 *)
  assert (Hba : forall A B : C, Cminus A B = C0 -> A = B).
  { clear. intros A B H. apply Ceq;
      [ apply (f_equal Re) in H | apply (f_equal Im) in H ];
      unfold Cminus, C0 in H; cbn in H; lra. }
  pose proof (Hba _ _ Hloop) as Hfin. unfold c in Hfin.
  rewrite (Cintf_irrel (kAi m) HA (HcA m) 0 (2 * PI)) in Hfin.
  rewrite (Cintf_irrel (kBi m) HB (HcB m) 0 (2 * PI)) in Hfin.
  exact Hfin.
Qed.

End CoeffRecur.

Print Assumptions Cderiv_Cpow.
Print Assumptions coeff_recur.
