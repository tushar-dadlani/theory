(* ================================================================= *)
(*  CDeriv2.v  —  second derivatives of the two atoms of gtermC:       *)
(*  the complex power c^v (second exponent-derivative (ln c)^2 c^v)     *)
(*  and 1/w (second derivative 2/w^3), the latter via the general       *)
(*  chain rule through w |-> w^2.  Axiom-clean.                        *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra.
Require Import ComplexField Cmodulus CexpFull CPower Holomorphic CDeriv.
Open Scope R_scope.

(* second exponent-derivative of the complex power:
   d/dw (ln c · c^w) = (ln c)^2 · c^w *)
Lemma Cpw_deriv2 : forall c v, 0 < c ->
  is_Cderiv (fun w => Cmul (RtoC (ln c)) (Cpw c w)) v
    (Cmul (RtoC (ln c)) (Cmul (RtoC (ln c)) (Cpw c v))).
Proof. intros c v Hc; apply Cderiv_cscal; apply Cpw_deriv; exact Hc. Qed.

(* second derivative of 1/w: d/dw (-1/w^2) = 2/w^3, i.e.
   d/dw (Copp (Cinv (w*w))) = -(-1/(w^2)^2)·(2w). *)
Lemma Cderiv_inv2 : forall z, z <> C0 ->
  is_Cderiv (fun w => Copp (Cinv (Cmul w w))) z
    (Copp (Cmul (Copp (Cinv (Cmul (Cmul z z) (Cmul z z))))
                (Cadd (Cmul C1 z) (Cmul z C1)))).
Proof.
  intros z Hz.
  apply Cderiv_opp.
  apply (Cderiv_comp Cinv (fun w => Cmul w w) z
           (Copp (Cinv (Cmul (Cmul z z) (Cmul z z)))) (Cadd (Cmul C1 z) (Cmul z C1))).
  - apply Cderiv_inv; apply Cmul_ne0; exact Hz.
  - apply (Cderiv_mul (fun w => w) (fun w => w) z C1 C1); apply Cderiv_id.
Qed.

Print Assumptions Cpw_deriv2.
Print Assumptions Cderiv_inv2.

(* ================================================================= *)
(*  END CDeriv2.v.                                                    *)
(* ================================================================= *)
