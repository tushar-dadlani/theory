(* ================================================================= *)
(*  ZetaEMExtHolo.v  --  holomorphy of the trapezoid terms in s.       *)
(*                                                                    *)
(*  Step one of Bfn1_holo: each htermC (. ) n is holomorphic in s away *)
(*  from s = 1.  htermC is built from exactly the atoms CZetaDeriv     *)
(*  already differentiates for gtermC --                               *)
(*                                                                    *)
(*     gC s x = x^{-s}                     (Cpw o affine)              *)
(*     GC s x = x^{1-s} / (1-s)            (product of Cpw o affine    *)
(*                                          and Cinv o affine)         *)
(*                                                                    *)
(*  so this is CZetaDeriv.gtermC_holo's proof with the trapezoid       *)
(*  combination in place of the rectangle one.  The 1/(1-s) is the     *)
(*  only source of the s <> 1 side condition.                          *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import ComplexField Cmodulus CexpFull CPower Holomorphic CDeriv
        CZetaTerm CZetaDeriv ZetaTrap ZetaEMExt.
Open Scope R_scope.

(* x^{-s}, holomorphic in s for x > 0 *)
Lemma gC_holo_s : forall (x : R) (s : C), 0 < x ->
  exists d, is_Cderiv (fun w => gC w x) s d.
Proof.
  intros x s Hx; eexists; unfold gC.
  apply (is_Cderiv_ext (fun w => Cpw x (Cadd (Cmul (Copp C1) w) C0))).
  - intro w; f_equal; ring.
  - apply Cderiv_comp_affine; apply Cpw_deriv; exact Hx.
Qed.

(* x^{1-s}/(1-s), holomorphic in s for x > 0 away from s = 1 *)
Lemma GC_holo_s : forall (x : R) (s : C), 0 < x -> Cminus C1 s <> C0 ->
  exists d, is_Cderiv (fun w => GC w x) s d.
Proof.
  intros x s Hx Hs; eexists; unfold GC.
  apply Cderiv_mul.
  - apply (is_Cderiv_ext (fun w => Cpw x (Cadd (Cmul (Copp C1) w) C1))).
    + intro w; f_equal; ring.
    + apply Cderiv_comp_affine; apply Cpw_deriv; exact Hx.
  - apply (is_Cderiv_ext (fun w => Cinv (Cadd (Cmul (Copp C1) w) C1))).
    + intro w; f_equal; ring.
    + apply Cderiv_comp_affine; apply Cderiv_inv;
        replace (Cadd (Cmul (Copp C1) s) C1) with (Cminus C1 s) by ring; exact Hs.
Qed.

(* the trapezoid defect, holomorphic in s away from s = 1 *)
Theorem htermC_holo_s : forall n s, Cminus C1 s <> C0 ->
  exists d, is_Cderiv (fun w => htermC w n) s d.
Proof.
  intros n s Hs.
  assert (H1 : 0 < INR (S n)) by (apply lt_0_INR; lia).
  assert (H2 : 0 < INR (S (S n))) by (apply lt_0_INR; lia).
  destruct (gC_holo_s (INR (S n)) s H1) as [d1 Hd1].
  destruct (gC_holo_s (INR (S (S n))) s H2) as [d2 Hd2].
  destruct (GC_holo_s (INR (S (S n))) s H2 Hs) as [e2 He2].
  destruct (GC_holo_s (INR (S n)) s H1 Hs) as [e1 He1].
  eexists; unfold htermC.
  apply Cderiv_minus.
  - apply (Cderiv_mul (fun _ => RtoC (/ 2))
             (fun w => Cadd (gC w (INR (S n))) (gC w (INR (S (S n)))))).
    + apply Cderiv_const.
    + apply Cderiv_add; [ exact Hd1 | exact Hd2 ].
  - apply Cderiv_minus; [ exact He2 | exact He1 ].
Qed.

Print Assumptions htermC_holo_s.

(* ================================================================= *)
(*  END ZetaEMExtHolo.v  (step one; the Weierstrass assembly of       *)
(*  Bfn1_holo from these terms follows in the same file)              *)
(* ================================================================= *)
