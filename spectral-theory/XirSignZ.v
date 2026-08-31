(* ================================================================= *)
(*  XirSignZ.v  --  where the exponentially small factor lives.       *)
(*                                                                    *)
(*  On the critical line s = 1/2 + it the strip identity              *)
(*  (CZetaStripId.XiC_completed_strip) factors as                     *)
(*                                                                    *)
(*    Xi(1/2+it) = -(1/2)(t^2+1/4) . pi^{-s/2} Gamma(s/2) . zeta(s)   *)
(*                 \_________________________/  \_______/             *)
(*                   real, positive, CLOSED FORM   O(1)               *)
(*                                                                    *)
(*  Writing the archimedean factor as |A| * U with |U| = 1 gives       *)
(*                                                                    *)
(*      xir t = - c(t) * Z(t),      c(t) = (1/2)(t^2+1/4)|A(t)| > 0,   *)
(*      Z(t)  = Re( U(t) * zeta(1/2+it) )   -- the Hardy Z function.   *)
(*                                                                    *)
(*  |A(t)| = pi^{-1/4} |Gamma(1/4+it/2)| (Amod_closed_form): the whole *)
(*  e^{-pi t/4} decay sits in a factor that is POSITIVE and given in   *)
(*  closed form, so it never has to be computed to decide the sign.    *)
(*  Our quadrature pipeline computes xir as 1/2 - (1/4+t^2) Re TC, a   *)
(*  difference of two O(1) quantities, and pays ~1.08 t bits of        *)
(*  cancellation for it.  Z has no such cancellation.                 *)
(*                                                                    *)
(*  No branch of arg is needed anywhere: U is defined as A/|A|.        *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra.
Require Import ComplexField Cmodulus Holomorphic CexpFull CPower
        GammaC RiemannXiEntire ZetaFn CZeta CZetaXiComplex
        CZetaRegular6 CZetaStripId GammaCNe0 CoherenceSingularity.
Open Scope R_scope.

(* ---- elementary facts ---- *)

Lemma Cmod_posz : forall c, c <> C0 -> 0 < Cmod c.
Proof.
  intros c Hc. destruct (Rle_lt_or_eq_dec 0 (Cmod c) (Cmod_nonneg c)) as [H|H].
  - exact H.
  - exfalso; apply Hc; apply (proj1 (Cmod0 c)); symmetry; exact H.
Qed.

Lemma RtoC_ne0 : forall r, r <> 0 -> RtoC r <> C0.
Proof.
  intros r Hr E. apply Hr.
  change (Re (RtoC r) = Re C0). rewrite E. reflexivity.
Qed.

Lemma Re_RtoC_mul : forall r w, Re (Cmul (RtoC r) w) = r * Re w.
Proof. intros r w; unfold Cmul, RtoC; cbn [Re Im]; ring. Qed.

Lemma Cmul_ne0 : forall a b, a <> C0 -> b <> C0 -> Cmul a b <> C0.
Proof.
  intros a b Ha Hb E.
  apply Hb. apply (Cmul_eq0_l a b E Ha).
Qed.

(* ---- the critical line ---- *)

Lemma Re_crit : forall t, Re (crit t) = / 2.
Proof. intro t; reflexivity. Qed.

Lemma crit_Re_pos : forall t, 0 < Re (crit t).
Proof. intro t; rewrite Re_crit; lra. Qed.

Lemma crit_ne1 : forall t, Cminus C1 (crit t) <> C0.
Proof.
  intros t E.
  assert (H : Re (Cminus C1 (crit t)) = Re C0) by (rewrite E; reflexivity).
  unfold Cminus, C1, crit, C0 in H; cbn [Re] in H; lra.
Qed.

Lemma halfz_crit : forall t, halfz (crit t) = mkC (/ 4) (t / 2).
Proof.
  intro t; unfold halfz, crit, RtoC, Cmul, Cadd, C0;
  apply Ceq; cbn [Re Im]; field.
Qed.

(* ---- the archimedean factor  pi^{-s/2} Gamma(s/2) ---- *)

Definition Afac (t : R) : C :=
  Cmul (archexp (crit t)) (GammaC (halfz (crit t))).
Definition Amod (t : R) : R := Cmod (Afac t).
Definition Uvec (t : R) : C := Cmul (Cinv (RtoC (Amod t))) (Afac t).

(* the Hardy Z function, with no arg branch: U = A/|A| *)
Definition Zfun (t : R) : R := Re (Cmul (Uvec t) (zF (crit t))).
Definition cpos (t : R) : R := / 2 * (t ^ 2 + / 4) * Amod t.

Lemma Afac_ne0 : forall t, Afac t <> C0.
Proof.
  intro t. unfold Afac. apply Cmul_ne0.
  - unfold archexp, Cpw. apply Cexpf_ne0.
  - apply GammaC_ne0_final. rewrite halfz_crit. cbn [Re]. lra.
Qed.

Lemma Amod_pos : forall t, 0 < Amod t.
Proof. intro t; apply Cmod_posz; apply Afac_ne0. Qed.

Lemma cpos_pos : forall t, 0 < cpos t.
Proof.
  intro t. unfold cpos.
  apply Rmult_lt_0_compat; [ | apply Amod_pos ].
  assert (0 <= t ^ 2) by (apply pow2_ge_0). lra.
Qed.

Lemma Afac_polar : forall t, Afac t = Cmul (RtoC (Amod t)) (Uvec t).
Proof.
  intro t. unfold Uvec.
  assert (Hne : RtoC (Amod t) <> C0)
    by (apply RtoC_ne0; pose proof (Amod_pos t); lra).
  replace (Cmul (RtoC (Amod t)) (Cmul (Cinv (RtoC (Amod t))) (Afac t)))
    with (Cmul (Cmul (Cinv (RtoC (Amod t))) (RtoC (Amod t))) (Afac t)) by ring.
  rewrite (Cinv_l (RtoC (Amod t)) Hne). ring.
Qed.

(* ---- the real, negative prefactor  (1/2) s (s-1)  at s = 1/2+it ---- *)

Lemma crit_prefac : forall t,
  Cmul (Cmul (RtoC (/ 2)) (crit t)) (Cminus (crit t) C1)
  = RtoC (- (/ 2 * (t ^ 2 + / 4))).
Proof.
  intro t. unfold crit, C1, RtoC, Cmul, Cminus, Cadd, Copp.
  apply Ceq; cbn [Re Im]; field.
Qed.

(* ---- the sign reduction ---- *)

Theorem xir_sign_Z : forall t, xir t = - cpos t * Zfun t.
Proof.
  intro t.
  unfold xir.
  rewrite (XiC_completed_strip (crit t) (crit_Re_pos t)).
  unfold RHSc.
  rewrite (BfnT_eq (crit t) (crit_Re_pos t) (crit_ne1 t)).
  fold (Afac t).
  (* regroup so that the real prefactor (1/2)s(s-1) is together *)
  replace (Cmul (Cmul (Cmul (RtoC (/ 2)) (crit t)) (Afac t))
             (Cmul (Cminus (crit t) C1) (zF (crit t))))
    with (Cmul (Cmul (Cmul (RtoC (/ 2)) (crit t)) (Cminus (crit t) C1))
             (Cmul (Afac t) (zF (crit t)))) by ring.
  rewrite crit_prefac.
  rewrite Afac_polar at 1.
  replace (Cmul (RtoC (- (/ 2 * (t ^ 2 + / 4))))
             (Cmul (Cmul (RtoC (Amod t)) (Uvec t)) (zF (crit t))))
    with (Cmul (RtoC (- (/ 2 * (t ^ 2 + / 4)) * Amod t))
             (Cmul (Uvec t) (zF (crit t))))
    by (rewrite RtoC_mul; ring).
  rewrite Re_RtoC_mul. unfold Zfun, cpos. ring.
Qed.

Corollary xir_pos_iff_Z_neg : forall t, 0 < xir t <-> Zfun t < 0.
Proof.
  intro t. rewrite (xir_sign_Z t). pose proof (cpos_pos t) as Hc.
  split; intro H; nra.
Qed.

Corollary xir_neg_iff_Z_pos : forall t, xir t < 0 <-> 0 < Zfun t.
Proof.
  intro t. rewrite (xir_sign_Z t). pose proof (cpos_pos t) as Hc.
  split; intro H; nra.
Qed.

(* ---- the closed form of the small factor ---- *)

Theorem Amod_closed_form : forall t,
  Amod t = Rpower PI (- / 4) * Cmod (GammaC (mkC (/ 4) (t / 2))).
Proof.
  intro t. unfold Amod, Afac. rewrite Cmod_mul. rewrite halfz_crit.
  f_equal.
  unfold archexp, Cpw. rewrite Cmod_Cexpf. unfold Rpower. f_equal.
  unfold mhalfz, crit, RtoC, Cmul, Cadd, C0; cbn [Re Im]; field.
Qed.
