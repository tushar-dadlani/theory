(* ================================================================= *)
(*  CGoursatAffine.v  —  Milestone C, brick C2a-4a: the affine part of  *)
(*  a holomorphic function integrates to 0 over any triangle.           *)
(*                                                                    *)
(*  The Goursat limit point zc gives an affine approximant               *)
(*    A z = c0 + c1(z - zc)   (c0 = h zc, c1 = deriv of h at zc),         *)
(*  which has the explicit primitive                                    *)
(*    H z = c0 z + c1 (z - zc)^2 / 2,     H' = A,                        *)
(*  so tri_int(A) = 0 (tri_int_primitive_zero).  This is what remains    *)
(*  after subtracting A from h (linearity), leaving the small remainder. *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import ComplexField Cmodulus Holomorphic CDeriv CZetaDeriv2
        CIntegral2 CPathIntegral CSegInt CTriangle CGoursatFTC.
Open Scope R_scope.

Section Affine.
Variables (c0 c1 zc : C).

Definition Aff (z : C) : C := Cadd c0 (Cmul c1 (Cminus z zc)).
Definition AffH (z : C) : C :=
  Cadd (Cmul c0 z)
       (Cmul c1 (Cmul (RtoC (/ 2)) (Cmul (Cminus z zc) (Cminus z zc)))).

Lemma AffH_deriv : forall z, is_Cderiv AffH z (Aff z).
Proof.
  intro z; unfold AffH.
  eapply is_Cderiv_eq.
  - apply Cderiv_add.
    + apply Cderiv_cscal, Cderiv_id.
    + apply Cderiv_cscal, Cderiv_cscal, Cderiv_mul;
        apply Cderiv_minus; solve [ apply Cderiv_id | apply Cderiv_const ].
  - unfold Aff, Cadd, Cmul, RtoC, Cminus, C1; apply Ceq; cbn; field.
Qed.

Lemma Ccont_Aff : CcontC Aff.
Proof.
  intros gam [HR HI]; unfold Aff.
  apply Ccont_add; [ apply Ccont_const | ].
  apply Ccont_mul; [ apply Ccont_const | ].
  split; intro x;
    [ apply (continuity_pt_minus (fun u => Re (gam u)) (fun _ => Re zc))
    | apply (continuity_pt_minus (fun u => Im (gam u)) (fun _ => Im zc)) ];
    solve [ apply HR | apply HI | apply continuity_pt_const; intros p q; reflexivity ].
Qed.

Theorem affine_tri_zero : forall v0 v1 v2,
  tri_int Aff Ccont_Aff v0 v1 v2 = C0.
Proof. intros; apply (tri_int_primitive_zero AffH Aff Ccont_Aff); apply AffH_deriv. Qed.

End Affine.

Print Assumptions affine_tri_zero.

(* ================================================================= *)
(*  END CGoursatAffine.v  —  affine part → 0 over any triangle (C2a-4a).*)
(* ================================================================= *)
