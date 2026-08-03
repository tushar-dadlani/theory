(* ================================================================= *)
(*  CZetaDeriv.v  —  each Euler–Maclaurin term gtermC is holomorphic   *)
(*  in s, by composing the derivative rules (Cpw_deriv o affine for    *)
(*  the powers, Cderiv_inv o affine for 1/(1-s), the product rule for  *)
(*  GC = x^{1-s}/(1-s), and Cderiv_minus).  Axiom-clean.               *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import ComplexField Cmodulus CexpFull CPower Holomorphic CDeriv CZetaTerm.
Open Scope R_scope.

Lemma gtermC_holo : forall n s, Cminus C1 s <> C0 ->
  exists d, is_Cderiv (fun w => gtermC w n) s d.
Proof.
  intros n s Hs; eexists; unfold gtermC.
  apply Cderiv_minus.
  - (* gC w (INR (S n)) = (n+1)^{-w} *)
    unfold gC.
    apply (is_Cderiv_ext (fun w => Cpw (INR (S n)) (Cadd (Cmul (Copp C1) w) C0))).
    + intro w; f_equal; ring.
    + apply Cderiv_comp_affine; apply Cpw_deriv; apply lt_0_INR; lia.
  - apply Cderiv_minus.
    + (* GC w (INR (S (S n))) *)
      unfold GC; apply Cderiv_mul.
      * apply (is_Cderiv_ext (fun w => Cpw (INR (S (S n))) (Cadd (Cmul (Copp C1) w) C1))).
        -- intro w; f_equal; ring.
        -- apply Cderiv_comp_affine; apply Cpw_deriv; apply lt_0_INR; lia.
      * apply (is_Cderiv_ext (fun w => Cinv (Cadd (Cmul (Copp C1) w) C1))).
        -- intro w; f_equal; ring.
        -- apply Cderiv_comp_affine; apply Cderiv_inv;
             replace (Cadd (Cmul (Copp C1) s) C1) with (Cminus C1 s) by ring; exact Hs.
    + (* GC w (INR (S n)) *)
      unfold GC; apply Cderiv_mul.
      * apply (is_Cderiv_ext (fun w => Cpw (INR (S n)) (Cadd (Cmul (Copp C1) w) C1))).
        -- intro w; f_equal; ring.
        -- apply Cderiv_comp_affine; apply Cpw_deriv; apply lt_0_INR; lia.
      * apply (is_Cderiv_ext (fun w => Cinv (Cadd (Cmul (Copp C1) w) C1))).
        -- intro w; f_equal; ring.
        -- apply Cderiv_comp_affine; apply Cderiv_inv;
             replace (Cadd (Cmul (Copp C1) s) C1) with (Cminus C1 s) by ring; exact Hs.
Qed.

(* the 1/(s-1) head of zetaC is holomorphic *)
Lemma zetaC_head_holo : forall s, Cminus s C1 <> C0 ->
  exists d, is_Cderiv (fun w => Cinv (Cminus w C1)) s d.
Proof.
  intros s Hs; eexists.
  apply (is_Cderiv_ext (fun w => Cinv (Cadd (Cmul C1 w) (Copp C1)))).
  - intro w; f_equal; ring.
  - apply Cderiv_comp_affine; apply Cderiv_inv;
      replace (Cadd (Cmul C1 s) (Copp C1)) with (Cminus s C1) by ring; exact Hs.
Qed.

Print Assumptions gtermC_holo.
Print Assumptions zetaC_head_holo.

(* ================================================================= *)
(*  END CZetaDeriv.v (part 1).                                         *)
(* ================================================================= *)
