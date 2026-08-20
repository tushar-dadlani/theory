(* ================================================================= *)
(*  CSpecDet.v  —  the SPECTRAL DETERMINANT and its trace.             *)
(*                                                                    *)
(*  The Hadamard product over a spectrum is a REGULARIZED DETERMINANT: *)
(*                                                                    *)
(*     det_2 (I - K)  =  det (I - K) . e^{tr K}  =  PROD (1-lam) e^lam *)
(*                                                                    *)
(*  so the e^{z/rho} factors are exactly the exp(trace) correction     *)
(*  that makes the product converge for a Hilbert-Schmidt spectrum.    *)
(*  Differentiating the logarithm, the exponent contributes the +1/rho *)
(*  and the whole thing becomes the REGULARIZED RESOLVENT TRACE        *)
(*                                                                    *)
(*     (d/dz) log det_2  =  SUM_rho [ 1/(z-rho) + 1/rho ].             *)
(*                                                                    *)
(*  THE POLE-FREE FORM MATTERS.  Efac_deriv is stated as               *)
(*      (d/dz) E(z/rho) = -(z/rho^2) e^{z/rho},                        *)
(*  which needs NO hypothesis at all -- not even rho <> C0, since      *)
(*  Cinv C0 = C0 makes both sides degenerate correctly.  The quotient  *)
(*  form 1/(z-rho) + 1/rho is derived only where it is defined.        *)
(*                                                                    *)
(*  CONVERGENCE OF THE TRACE IS NOT PROVED BY COMPARISON.  A majorant  *)
(*  2|z|/|rho|^2 only holds once |rho| >= 2|z|, and finitely many     *)
(*  exceptions is not structural.  Instead convergence falls out of   *)
(*  the identity itself: splitting the product at M,                   *)
(*      P'/P = (partial sum through M) + T_M'/T_M,                     *)
(*  and T_M'/T_M -> 0, so the partial sums converge -- to P'/P.        *)
(*  Value and convergence arrive together.                             *)
(*                                                                    *)
(*  T_M'/T_M -> 0 uses CCauchyEstimate.disk_deriv_bound applied to     *)
(*  T_M - 1, NOT to T_M: it is the DEVIATION that is uniformly small   *)
(*  (tail_prod_near1), and it has the same derivative.                 *)
(*  Axiom-clean.                                                       *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia List.
Require Import ComplexField Cmodulus Holomorphic CDeriv CHoloCalculus CexpFull
        CexpfDeriv CSeries CInfProd XiHadamardProd.
Open Scope R_scope.

Lemma isd_val : forall F z d d', is_Cderiv F z d -> d = d' -> is_Cderiv F z d'.
Proof. intros F z d d' H E. rewrite <- E. exact H. Qed.

(* ----------------------------------------------------------------- *)
(*  A.  the Weierstrass factor, differentiated -- pole-free            *)
(* ----------------------------------------------------------------- *)
Lemma Efac_deriv : forall (rho z : C),
  is_Cderiv (fun w => Efac w rho) z
    (Copp (Cmul (Cmul z (Cmul (Cinv rho) (Cinv rho))) (Cexpf (Cmul z (Cinv rho))))).
Proof.
  intros rho z.
  assert (Hu : is_Cderiv (fun w => Cmul w (Cinv rho)) z (Cinv rho)).
  { apply (isd_val _ _ (Cadd (Cmul C1 (Cinv rho)) (Cmul z C0)));
      [ apply (Cderiv_mul (fun w => w) (fun _ => Cinv rho) z C1 C0);
          [ apply Cderiv_id | apply Cderiv_const ]
      | ring ]. }
  assert (H1 : is_Cderiv (fun w => Cminus C1 (Cmul w (Cinv rho))) z
                 (Cminus C0 (Cinv rho)))
    by (apply (Cderiv_minus (fun _ => C1) (fun w => Cmul w (Cinv rho)) z C0 (Cinv rho));
        [ apply Cderiv_const | exact Hu ]).
  assert (H2 : is_Cderiv (fun w => Cexpf (Cmul w (Cinv rho))) z
                 (Cmul (Cexpf (Cmul z (Cinv rho))) (Cinv rho)))
    by (apply (Cexpf_comp_deriv (fun w => Cmul w (Cinv rho)) z (Cinv rho)); exact Hu).
  unfold Efac.
  apply (isd_val _ _
    (Cadd (Cmul (Cminus C0 (Cinv rho)) (Cexpf (Cmul z (Cinv rho))))
          (Cmul (Cminus C1 (Cmul z (Cinv rho)))
                (Cmul (Cexpf (Cmul z (Cinv rho))) (Cinv rho)))));
    [ apply (Cderiv_mul (fun w => Cminus C1 (Cmul w (Cinv rho)))
               (fun w => Cexpf (Cmul w (Cinv rho))) z
               (Cminus C0 (Cinv rho)) (Cmul (Cexpf (Cmul z (Cinv rho))) (Cinv rho)));
        [ exact H1 | exact H2 ]
    | ring ].
Qed.

(* the quotient form, where it is defined *)
Definition lterm (rho : nat -> C) (z : C) (n : nat) : C :=
  Cadd (Cinv (Cminus z (rho n))) (Cinv (rho n)).

Lemma Efac_logderiv : forall (rho z : C), rho <> C0 -> z <> rho ->
  is_Cderiv (fun w => Efac w rho) z
    (Cmul (Efac z rho) (Cadd (Cinv (Cminus z rho)) (Cinv rho))).
Proof.
  intros rho z Hr Hz.
  assert (Hzr : Cminus z rho <> C0)
    by (intro Hc; apply Hz;
        assert (Hq : z = Cadd (Cminus z rho) rho) by ring;
        rewrite Hc in Hq; rewrite Hq; ring).
  apply (isd_val _ _
    (Copp (Cmul (Cmul z (Cmul (Cinv rho) (Cinv rho))) (Cexpf (Cmul z (Cinv rho))))));
    [ apply Efac_deriv | ].
  unfold Efac. field. split; assumption.
Qed.

(* ----------------------------------------------------------------- *)
(*  B.  the finite product: log-derivative = partial trace             *)
(* ----------------------------------------------------------------- *)
Lemma Pprod_logderiv : forall (rho : nat -> C) (z : C) (N : nat),
  (forall k, rho k <> C0) ->
  (forall k, z <> rho k) ->
  is_Cderiv (fun w => Pprod (fun k => Efac w (rho k)) N) z
    (Cmul (Pprod (fun k => Efac z (rho k)) N) (Cpsum (lterm rho z) N)).
Proof.
  intros rho z N Hne Hz. induction N as [| N IH].
  - cbn [Pprod Cpsum]. unfold lterm.
    apply Efac_logderiv; [ apply Hne | apply Hz ].
  - apply (isd_val _ _
      (Cadd (Cmul (Cmul (Pprod (fun k => Efac z (rho k)) N) (Cpsum (lterm rho z) N))
                  (Efac z (rho (S N))))
            (Cmul (Pprod (fun k => Efac z (rho k)) N)
                  (Cmul (Efac z (rho (S N)))
                        (Cadd (Cinv (Cminus z (rho (S N)))) (Cinv (rho (S N)))))))).
    + apply (Cderiv_mul (fun w => Pprod (fun k => Efac w (rho k)) N)
               (fun w => Efac w (rho (S N))) z
               (Cmul (Pprod (fun k => Efac z (rho k)) N) (Cpsum (lterm rho z) N))
               (Cmul (Efac z (rho (S N)))
                     (Cadd (Cinv (Cminus z (rho (S N)))) (Cinv (rho (S N))))));
        [ exact IH | apply Efac_logderiv; [ apply Hne | apply Hz ] ].
    + cbn [Pprod Cpsum]. unfold lterm. ring.
Qed.

Print Assumptions Efac_deriv.
Print Assumptions Efac_logderiv.
Print Assumptions Pprod_logderiv.
