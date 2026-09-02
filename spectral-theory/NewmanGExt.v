(* ================================================================= *)
(*  NewmanGExt.v  --  the g-extension: Newman's transform continued    *)
(*  across Re z = 0.                                                   *)
(*                                                                    *)
(*  NewmanIdentity.newman_identity gives the transform only where the  *)
(*  Dirichlet series converges:                                        *)
(*                                                                    *)
(*      g(z) = Phi(z+1)/(z+1) - 1/z        (Re z > 0)                  *)
(*                                                                    *)
(*  Newman's contour needs g on a neighbourhood of Re z >= 0, and the  *)
(*  1/z term looks like an obstruction at z = 0.  It is not.  Since    *)
(*  PhiMinus(s) = Phi(s) - 1/(s-1), putting s = z+1 gives              *)
(*                                                                    *)
(*      g(z) = (PhiMinus(z+1) - 1)/(z+1)                               *)
(*                                                                    *)
(*  -- the 1/z cancels identically.  And z = 0 is exactly s = 1, which *)
(*  is where ZetaPoleCancel2.PhiMinusT is holomorphic.  So the whole   *)
(*  "g-extension" reduces to writing g in that form.                   *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import ComplexField Cmodulus Holomorphic CDeriv CHoloCalculus
        CZetaDeriv2 CBorelBound
        CVonMangoldtSeries CZeta ZetaFn ZetaInvHolo ZetaPoleCancel
        ExplicitFormulaXiLogDeriv
        CZetaRegular CZetaRegular2 CZetaRegular6 ZetaPoleCancel2.
Open Scope R_scope.

(* the extended transform *)
Definition gext (z : C) : C :=
  Cmul (Cminus (PhiMinusT (Cadd z C1)) C1) (Cinv (Cadd z C1)).

(* ----------------------------------------------------------------- *)
(*  gext is holomorphic wherever PhiMinusT is -- s = 1 (z = 0)        *)
(*  INCLUDED.                                                          *)
(* ----------------------------------------------------------------- *)

Theorem gext_holo : forall z, 0 < Re (Cadd z C1) -> BfnT (Cadd z C1) <> C0 ->
  exists d, is_Cderiv gext z d.
Proof.
  intros z HRe Hne.
  assert (Hz1 : Cadd z C1 <> C0).
  { intro Hc. rewrite Hc in HRe. cbn in HRe. lra. }
  destruct (phi_minusT_holo (Cadd z C1) HRe Hne) as [dP HdP].
  pose proof (is_Cderiv_translate PhiMinusT C1 z dP HdP) as HP.
  pose proof (Cderiv_minus (fun u => PhiMinusT (Cadd u C1)) (fun _ => C1) z dP C0
                HP (Cderiv_const C1 z)) as HN.
  assert (HD0 : is_Cderiv (fun u => Cadd u C1) z C1).
  { apply (is_Cderiv_eq _ _ (Cadd C1 C0)).
    - apply Cderiv_add; [ apply Cderiv_id | apply Cderiv_const ].
    - apply Ceq; cbn; ring. }
  pose proof (Cderiv_invc (fun u => Cadd u C1) z C1 HD0 Hz1) as HI.
  eexists. unfold gext. apply Cderiv_mul; [ exact HN | exact HI ].
Qed.

(* THE point the un-extended g could not reach *)
Theorem gext_at0 : exists d, is_Cderiv gext C0 d.
Proof.
  assert (Hc : Cadd C0 C1 = C1) by (apply Ceq; cbn; ring).
  apply gext_holo; rewrite Hc.
  - cbn. lra.
  - rewrite BfnT_at1. exact C1_ne_C0.
Qed.

(* ----------------------------------------------------------------- *)
(*  gext really IS the Newman transform: it agrees with the limit of   *)
(*  NewmanIdentity.newman_identity on Re z > 0.                        *)
(* ----------------------------------------------------------------- *)

Theorem gext_eq : forall z (H1 : 1 < Re (Cadd z C1)),
  gext z = Cminus (Cmul (Cinv (Cadd z C1)) (Phi (Cadd z C1) H1)) (Cinv z).
Proof.
  intros z H1.
  (* Re z > 0 *)
  assert (HzRe : 0 < Re z) by (cbn in H1; lra).
  assert (Hz0 : z <> C0)
    by (intro Hc; rewrite Hc in HzRe; cbn in HzRe; lra).
  assert (Hs0 : 0 < Re (Cadd z C1)) by lra.
  assert (Hs1 : Cminus C1 (Cadd z C1) <> C0).
  { intro Hc. apply Hz0. apply Ceq.
    - apply (f_equal Re) in Hc; cbn in Hc; cbn; lra.
    - apply (f_equal Im) in Hc; cbn in Hc; cbn; lra. }
  assert (Hz1 : Cadd z C1 <> C0)
    by (intro Hc; rewrite Hc in Hs0; cbn in Hs0; lra).
  unfold gext.
  rewrite (phi_minusT_eq (Cadd z C1) Hs0 Hs1).
  rewrite (phi_minus_eq (Cadd z C1) Hs0 Hs1 H1).
  (* Phi(z+1) - 1/((z+1)-1) = Phi(z+1) - 1/z *)
  replace (Cminus (Cadd z C1) C1) with z by (apply Ceq; cbn; ring).
  field. split; assumption.
Qed.

(* ----------------------------------------------------------------- *)
(*  Discharging the side condition on Re z >= 0: BfnT is nonzero on    *)
(*  Re s >= 1.  Three cases, all already proved elsewhere.             *)
(* ----------------------------------------------------------------- *)

Lemma Csurj : forall c, c = mkC (Re c) (Im c).
Proof. intro c; destruct c; reflexivity. Qed.

Theorem BfnT_ne0_re_ge1 : forall s, 1 <= Re s -> BfnT s <> C0.
Proof.
  intros s Hs.
  destruct (CZetaRegular.Ceq_dec s C1) as [He | Hne].
  - subst s. rewrite BfnT_at1. exact C1_ne_C0.
  - assert (H1 : Cminus C1 s <> C0) by (apply ne_C1_sub; exact Hne).
    assert (H0 : 0 < Re s) by lra.
    rewrite (BfnT_eq s H0 H1).
    apply Cmul_ne0; [ apply ne_C1_sub'; exact Hne | ].
    destruct (Rle_lt_or_eq_dec 1 (Re s) Hs) as [Hlt | Heq].
    + apply zF_ne0_gt1. exact Hlt.
    + destruct s as [sr si]. cbn in Heq. subst sr.
      assert (Him : si <> 0)
        by (intro Hc; subst si; apply Hne; reflexivity).
      apply zF_line_nonzero. exact Him.
Qed.

(* gext is holomorphic on a neighbourhood of the closed right half-plane
   -- exactly what Newman's contour consumes. *)
Corollary gext_holo_re_ge0 : forall z, 0 <= Re z -> exists d, is_Cderiv gext z d.
Proof.
  intros z Hz. apply gext_holo.
  - cbn. lra.
  - apply BfnT_ne0_re_ge1. cbn. lra.
Qed.

Print Assumptions BfnT_ne0_re_ge1.
Print Assumptions gext_holo_re_ge0.
Print Assumptions gext_holo.
Print Assumptions gext_at0.
Print Assumptions gext_eq.
