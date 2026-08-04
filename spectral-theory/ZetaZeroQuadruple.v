(* ================================================================= *)
(*  ZetaZeroQuadruple.v  —  the completed zeta is REAL: XiC commutes    *)
(*  with complex conjugation, giving the conjugate reflection of zeros. *)
(*                                                                    *)
(*  Together with ZetaZeroPairing (reflection z |-> 1 - z about the     *)
(*  centre 1/2), conjugation z |-> conj z (reflection about the real    *)
(*  axis) closes the zeros of XiC under the full Klein 4-group          *)
(*  { z, 1-z, conj z, 1-conj z }.  The LINE reflection z |-> 1 - conj z *)
(*  is the composite, and its fixed set is exactly Re z = 1/2 — so RH   *)
(*  is precisely the statement that every zero is fixed by it.         *)
(*                                                                    *)
(*  The crux is TC_conj: the theta-tail integral TC commutes with       *)
(*  conjugation.  Its complex integrand wkerC has real modulus and      *)
(*  wkerC (conj z) u = conj (wkerC z u) pointwise; pushing conj through  *)
(*  the dominated improper integral (improper_unique, improper_scal)     *)
(*  gives TC (conj z) = conj (TC z).  Axiom-clean.                      *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra.
Require Import ComplexField Cmodulus CexpFull EulerFormula
        ImproperCv1 CImproperIntegral ThetaTailEntire RiemannXiEntire
        ZetaZeroPairing.
Open Scope R_scope.

(* ================================================================= *)
(*  0.  conjugation is a ring homomorphism fixing the reals           *)
(* ================================================================= *)

Lemma Re_Cconj : forall a, Re (Cconj a) = Re a.
Proof. intro a; unfold Cconj; reflexivity. Qed.
Lemma Im_Cconj : forall a, Im (Cconj a) = - Im a.
Proof. intro a; unfold Cconj; reflexivity. Qed.
Lemma Cconj_RtoC : forall r, Cconj (RtoC r) = RtoC r.
Proof. intro r; unfold Cconj, RtoC; apply Ceq; simpl; ring. Qed.
Lemma Cconj_C1 : Cconj C1 = C1.
Proof. unfold Cconj, C1; apply Ceq; simpl; ring. Qed.
Lemma Cconj_C0 : Cconj C0 = C0.
Proof. unfold Cconj, C0; apply Ceq; simpl; ring. Qed.
Lemma Cconj_opp : forall a, Cconj (Copp a) = Copp (Cconj a).
Proof. intro a; unfold Cconj, Copp; apply Ceq; simpl; ring. Qed.
Lemma Cconj_minus : forall a b, Cconj (Cminus a b) = Cminus (Cconj a) (Cconj b).
Proof. intros a b; unfold Cconj, Cminus; apply Ceq; simpl; ring. Qed.

(* ================================================================= *)
(*  1.  the complex exponential / power commute with conjugation       *)
(* ================================================================= *)

Lemma Cexpf_conj : forall w, Cconj (Cexpf w) = Cexpf (Cconj w).
Proof.
  intro w; unfold Cexpf; rewrite Cconj_mul, Cconj_RtoC, Re_Cconj, Im_Cconj.
  rewrite <- Cexp_neg; reflexivity.
Qed.

Lemma Cpw_conj : forall c w, Cconj (Cpw c w) = Cpw c (Cconj w).
Proof.
  intros c w; unfold Cpw; rewrite Cexpf_conj, Cconj_mul, Cconj_RtoC; reflexivity.
Qed.

(* the theta-tail integrand is conjugate-symmetric *)
Lemma wkerC_conj : forall z u, wkerC (Cconj z) u = Cconj (wkerC z u).
Proof.
  intros z u; unfold wkerC.
  rewrite Cconj_mul, Cconj_RtoC, Cpw_conj, Cconj_minus, Cconj_mul, Cconj_RtoC, Cconj_C1.
  reflexivity.
Qed.

(* ================================================================= *)
(*  2.  TC_conj: the theta-tail integral commutes with conjugation     *)
(* ================================================================= *)

Lemma TC_conj : forall z, TC (Cconj z) = Cconj (TC z).
Proof.
  intro z.
  destruct (TC_spec (Cconj z)) as [HRe' HIm'].
  destruct (TC_spec z) as [HRe HIm].
  apply Ceq.
  - (* Re: same integrand, so same limit *)
    rewrite Re_Cconj.
    apply (improper_unique
             (fun u => Re (wkerC (Cconj z) u)) (cont_RI _ (cont_wkerC_re (Cconj z)))
             (fun u => Re (wkerC z u)) (cont_RI _ (cont_wkerC_re z))
             (Re (TC (Cconj z))) (Re (TC z)));
      [ intros x _; rewrite wkerC_conj, Re_Cconj; reflexivity | exact HRe' | exact HRe ].
  - (* Im: negated integrand, so negated limit *)
    rewrite Im_Cconj.
    assert (Hscal : ImproperCv1 (fun x => -1 * Im (wkerC z x))
                      (cont_RI _ (continuity_scal (fun u => Im (wkerC z u)) (-1) (cont_wkerC_im z)))
                      (-1 * Im (TC z))).
    { apply (improper_scal (fun u => Im (wkerC z u)) (-1)
               (cont_RI _ (cont_wkerC_im z))
               (cont_RI _ (continuity_scal (fun u => Im (wkerC z u)) (-1) (cont_wkerC_im z)))
               (Im (TC z))); exact HIm. }
    assert (Heq : Im (TC (Cconj z)) = -1 * Im (TC z)).
    { apply (improper_unique
               (fun u => Im (wkerC (Cconj z) u)) (cont_RI _ (cont_wkerC_im (Cconj z)))
               (fun x => -1 * Im (wkerC z x))
               (cont_RI _ (continuity_scal (fun u => Im (wkerC z u)) (-1) (cont_wkerC_im z)))
               (Im (TC (Cconj z))) (-1 * Im (TC z)));
        [ intros x _; rewrite wkerC_conj, Im_Cconj; ring | exact HIm' | exact Hscal ]. }
    lra.
Qed.

(* ================================================================= *)
(*  3.  XiC is REAL: XiC (conj z) = conj (XiC z)                       *)
(* ================================================================= *)

Lemma one_minus_conj : forall z,
  Cconj (Cadd (Cmul (Copp C1) z) C1) = Cadd (Cmul (Copp C1) (Cconj z)) C1.
Proof. intro z; rewrite Cconj_add, Cconj_mul, Cconj_opp, Cconj_C1; reflexivity. Qed.

Lemma XiC_conj : forall z, XiC (Cconj z) = Cconj (XiC z).
Proof.
  intro z; unfold XiC.
  repeat (rewrite Cconj_add || rewrite Cconj_mul || rewrite Cconj_opp
          || rewrite Cconj_RtoC || rewrite Cconj_C0 || rewrite Cconj_C1).
  rewrite <- !TC_conj, one_minus_conj.
  reflexivity.
Qed.

(* ================================================================= *)
(*  4.  the conjugate reflection of zeros, and the full quadruple       *)
(* ================================================================= *)

(* zeros of XiC are symmetric under conjugation (reflection about R) *)
Theorem XiC_zero_conj : forall z, XiC z = C0 -> XiC (Cconj z) = C0.
Proof. intros z Hz; rewrite XiC_conj, Hz, Cconj_C0; reflexivity. Qed.

(* the full Klein 4-group of a zero: z, 1-z, conj z, 1-conj z *)
Theorem XiC_zero_quadruple : forall z, XiC z = C0 ->
  XiC z = C0 /\ XiC (Cminus C1 z) = C0
  /\ XiC (Cconj z) = C0 /\ XiC (Cminus C1 (Cconj z)) = C0.
Proof.
  intros z Hz; repeat split.
  - exact Hz.
  - apply XiC_zero_reflect; exact Hz.
  - apply XiC_zero_conj; exact Hz.
  - apply XiC_zero_reflect, XiC_zero_conj; exact Hz.
Qed.

(* the LINE reflection z |-> 1 - conj z has fixed set exactly Re z = 1/2, *)
(* so RH = every zero is fixed by it *)
Theorem line_reflection_fixed : forall z, Cminus C1 (Cconj z) = z -> Re z = / 2.
Proof.
  intros z H.
  assert (HR : Re (Cminus C1 (Cconj z)) = Re z) by (rewrite H; reflexivity).
  rewrite Re_one_minus, Re_Cconj in HR; lra.
Qed.

Print Assumptions XiC_zero_conj.

(* ================================================================= *)
(*  END ZetaZeroQuadruple.v                                           *)
(*  XiC commutes with conjugation, so its zeros are symmetric about     *)
(*  BOTH the critical line (z |-> 1-z) and the real axis (z |-> conj z), *)
(*  closing them under the Klein 4-group.  The critical line Re = 1/2    *)
(*  is exactly the fixed set of the composite line-reflection; RH says   *)
(*  every zero sits there.                                             *)
(* ================================================================= *)
