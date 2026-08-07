(* ================================================================= *)
(*  ZetaPoleCancel.v  —  Milestone B, brick B9 (capstone):             *)
(*  Phi(s) - 1/(s-1) = -B'/B  with  B(s) = (s-1) zeta(s)  is holomorphic *)
(*  wherever zeta(s) <> 0 and s <> 1 -- in particular on an open         *)
(*  neighborhood of the line Re s = 1 (s <> 1), where zeta(1+it) <> 0.   *)
(*  The 1/(s-1) pole of Phi = -zeta'/zeta is exactly cancelled.          *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import ComplexField Cmodulus CDeriv Holomorphic CHoloCalculus
        CSeries CZetaTerm CZetaDeriv2 CZetaDeriv3 CZetaDeriv4 CZetaDerivDirichlet
        CVonMangoldtSeries CVonMangoldtZeta CZeta CEulerProductZeta
        ZetaFn ZetaInvHolo ZetaDeriv.
Open Scope R_scope.

(* B(s) = (s-1) zeta(s), and its derivative B'(s) = zeta(s) + (s-1) zeta'(s) *)
Definition Bfn (s : C) : C := Cmul (Cminus s C1) (zF s).
Definition Bderiv (s : C) : C := Cadd (zF s) (Cmul (Cminus s C1) (zDF s)).
Definition Bderiv2 (s : C) (H0 : 0 < Re s) (H1 : Cminus C1 s <> C0) : C :=
  Cadd (Cadd (zDF s) (zDF s)) (Cmul (Cminus s C1) (zD2 s H0 H1)).

Lemma B_deriv : forall z, inDom z -> is_Cderiv Bfn z (Bderiv z).
Proof.
  intros z Hdom; unfold Bfn, Bderiv.
  eapply is_Cderiv_eq.
  - apply Cderiv_mul;
      [ apply Cderiv_minus; [ apply Cderiv_id | apply Cderiv_const ]
      | apply zF_deriv; exact Hdom ].
  - unfold Cadd, Cmul, Cminus, C0, C1; apply Ceq; cbn [Re Im]; ring.
Qed.

Lemma Bderiv_deriv : forall z (H0 : 0 < Re z) (H1 : Cminus C1 z <> C0),
  is_Cderiv (fun w => Bderiv w) z (Bderiv2 z H0 H1).
Proof.
  intros z H0 H1; unfold Bderiv, Bderiv2.
  eapply is_Cderiv_eq.
  - apply Cderiv_add.
    + apply (zF_deriv z (conj H0 H1)).
    + apply Cderiv_mul;
        [ apply Cderiv_minus; [ apply Cderiv_id | apply Cderiv_const ]
        | apply (zDF_deriv z H0 H1) ].
  - unfold Cadd, Cmul, Cminus, C0, C1; apply Ceq; cbn [Re Im]; ring.
Qed.

Definition PhiMinus (s : C) : C := Copp (Cmul (Bderiv s) (Cinv (Bfn s))).

(* ---- THE holomorphy: Phi - 1/(s-1) is holomorphic wherever zeta <> 0 ---- *)
Theorem phi_minus_holo : forall z (H0 : 0 < Re z) (H1 : Cminus C1 z <> C0),
  zF z <> C0 -> exists d, is_Cderiv PhiMinus z d.
Proof.
  intros z H0 H1 Hnz.
  assert (H1' : Cminus z C1 <> C0)
    by (intro Hc; apply H1; replace (Cminus C1 z) with (Copp (Cminus z C1)) by ring;
        rewrite Hc; unfold Copp, C0; apply Ceq; cbn; ring).
  assert (HBnz : Bfn z <> C0) by (unfold Bfn; apply Cmul_ne0; assumption).
  unfold PhiMinus; eexists.
  apply Cderiv_opp; apply Cderiv_div;
    [ apply (Bderiv_deriv z H0 H1) | apply (B_deriv z (conj H0 H1)) | exact HBnz ].
Qed.

(* ---- holomorphic on an open neighborhood of each point 1+it, t <> 0 ---- *)
Corollary phi_minus_line_holo : forall t, t <> 0 -> exists d, is_Cderiv PhiMinus (mkC 1 t) d.
Proof.
  intros t Ht; destruct (line_inDom t Ht) as [H0 H1].
  apply phi_minus_holo; [ exact H0 | exact H1 | apply zF_line_nonzero; exact Ht ].
Qed.

(* ================================================================= *)
(*  Tie-back to Milestone A: PhiMinus s = Phi s - 1/(s-1) on Re s > 1. *)
(* ================================================================= *)

Lemma zDF_eq_dcterm : forall s (H0 : 0 < Re s) (H1 : Cminus C1 s <> C0) (H : 1 < Re s),
  zDF s = proj1_sig (dcterm_cv s H).
Proof.
  intros s H0 H1 H.
  assert (H1' : Cminus s C1 <> C0)
    by (intro Hc; apply H1; replace (Cminus C1 s) with (Copp (Cminus s C1)) by ring;
        rewrite Hc; unfold Copp, C0; apply Ceq; cbn; ring).
  rewrite (zDF_eq s H0 H1), (dcterm_series_eq s H0 H1 H); f_equal.
  rewrite (dsGC_at_1 s); unfold Dhead; field; split; assumption.
Qed.

Theorem phi_minus_eq : forall s (H0 : 0 < Re s) (H1 : Cminus C1 s <> C0) (H : 1 < Re s),
  PhiMinus s = Cminus (Phi s H) (Cinv (Cminus s C1)).
Proof.
  intros s H0 H1 H.
  assert (H1' : Cminus s C1 <> C0)
    by (intro Hc; apply H1; replace (Cminus C1 s) with (Copp (Cminus s C1)) by ring;
        rewrite Hc; unfold Copp, C0; apply Ceq; cbn; ring).
  assert (Hznz : zetaC s H0 H1 <> C0) by (apply zetaC_nonzero; exact H).
  pose proof (phi_eq_neg_zeta_ratio s H0 H1 H) as HP.
  unfold PhiMinus, Bderiv, Bfn.
  rewrite (zF_eq s H0 H1), (zDF_eq_dcterm s H0 H1 H), HP.
  field; split; assumption.
Qed.

Print Assumptions phi_minus_holo.
Print Assumptions phi_minus_eq.

(* ================================================================= *)
(*  END ZetaPoleCancel.v  —  Milestone B: Phi - 1/(s-1) holomorphic     *)
(*  across Re s = 1 (s <> 1).                                          *)
(* ================================================================= *)
