(* ================================================================= *)
(*  CZetaDeriv2.v  —  item 2b.2: explicit first/second s-derivatives    *)
(*  of the Euler–Maclaurin term gtermC, with is_Cderiv relations, and   *)
(*  the identification of the second derivative with the STRUCTURAL      *)
(*  d2gtermC (CZetaTerm2.v) whose modulus item 3b bounds.               *)
(*                                                                    *)
(*  Route: differentiate the two kernels                               *)
(*    gC s x  = x^{-s}                (power)                           *)
(*    GC s x  = x^{1-s}/(1-s)         (antiderivative)                  *)
(*  twice in s via the Cderiv calculus, matching the results to the     *)
(*  structural kernels d2k(-s) = (ln x)^2 x^{-s} and d2sGC.  Axiom-clean.*)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import ComplexField Cmodulus CexpFull CPower Holomorphic CDeriv
               CBaseDeriv CBaseDeriv2 CZetaTerm CZetaTerm2.
Open Scope R_scope.

(* ------------------------------------------------------------------ *)
(*  Power kernel gC s x = x^{-s} = Cpw x (Copp s).                      *)
(*  first s-derivative dsk = -ln x · x^{-s};  second = (ln x)^2 x^{-s}. *)
(* ------------------------------------------------------------------ *)

Definition dsk (s : C) (x : R) : C :=
  Cmul (Copp C1) (Cmul (RtoC (ln x)) (Cpw x (Copp s))).

Lemma gC_sderiv : forall s x, 0 < x ->
  is_Cderiv (fun w => Cpw x (Copp w)) s (dsk s x).
Proof.
  intros s x Hx.
  apply (is_Cderiv_ext (fun w => Cpw x (Cadd (Cmul (Copp C1) w) C0))).
  - intro w; f_equal; ring.
  - unfold dsk.
    replace (Cmul (Copp C1) (Cmul (RtoC (ln x)) (Cpw x (Copp s))))
      with (Cmul (Copp C1) (Cmul (RtoC (ln x)) (Cpw x (Cadd (Cmul (Copp C1) s) C0))))
      by (repeat f_equal; ring).
    apply Cderiv_comp_affine; apply Cpw_deriv; exact Hx.
Qed.

Lemma dsk_sderiv : forall s x, 0 < x ->
  is_Cderiv (fun w => dsk w x) s (d2k (Copp s) x).
Proof.
  intros s x Hx; unfold dsk.
  replace (d2k (Copp s) x)
    with (Cmul (Copp C1) (Cmul (RtoC (ln x)) (dsk s x))).
  2: { unfold dsk, d2k.
       replace (RtoC (ln x * ln x)) with (Cmul (RtoC (ln x)) (RtoC (ln x)))
         by (rewrite <- RtoC_mul; reflexivity).
       ring. }
  apply Cderiv_cscal; apply Cderiv_cscal; apply gC_sderiv; exact Hx.
Qed.

(* ------------------------------------------------------------------ *)
(*  Antiderivative kernel GC s x = x^{1-s}/(1-s) = A·B,                 *)
(*  A = Cpw x (1-s), B = Cinv (1-s).                                    *)
(*  first s-derivative dsGC = -ln x·A·B + A·B^2;                        *)
(*  second = d2sGC (structural, CBaseDeriv2).                          *)
(* ------------------------------------------------------------------ *)

Lemma is_Cderiv_eq : forall F z d d', is_Cderiv F z d -> d = d' -> is_Cderiv F z d'.
Proof. intros F z d d' H Heq; subst; exact H. Qed.

(* atomic clean derivatives of A = x^{1-s} and B = 1/(1-s) *)
Lemma A_sderiv : forall s x, 0 < x ->
  is_Cderiv (fun w => Cpw x (Cminus C1 w)) s (Cmul (RtoC (- ln x)) (Cpw x (Cminus C1 s))).
Proof.
  intros s x Hx.
  apply (is_Cderiv_ext (fun w => Cpw x (Cadd (Cmul (Copp C1) w) C1))).
  - intro w; f_equal; ring.
  - apply (is_Cderiv_eq _ _ (Cmul (Copp C1) (Cmul (RtoC (ln x)) (Cpw x (Cadd (Cmul (Copp C1) s) C1))))).
    + apply Cderiv_comp_affine; apply Cpw_deriv; exact Hx.
    + replace (Cadd (Cmul (Copp C1) s) C1) with (Cminus C1 s) by ring.
      replace (RtoC (- ln x)) with (Cmul (Copp C1) (RtoC (ln x)))
        by (unfold RtoC, Copp, C1, Cmul; apply Ceq; cbn; ring).
      ring.
Qed.

Lemma B_sderiv : forall s, Cminus C1 s <> C0 ->
  is_Cderiv (fun w => Cinv (Cminus C1 w)) s (Cmul (Cinv (Cminus C1 s)) (Cinv (Cminus C1 s))).
Proof.
  intros s Hs.
  apply (is_Cderiv_ext (fun w => Cinv (Cadd (Cmul (Copp C1) w) C1))).
  - intro w; f_equal; ring.
  - apply (is_Cderiv_eq _ _ (Cmul (Copp C1)
             (Copp (Cinv (Cmul (Cadd (Cmul (Copp C1) s) C1) (Cadd (Cmul (Copp C1) s) C1)))))).
    + apply Cderiv_comp_affine; apply Cderiv_inv;
        replace (Cadd (Cmul (Copp C1) s) C1) with (Cminus C1 s) by ring; exact Hs.
    + replace (Cadd (Cmul (Copp C1) s) C1) with (Cminus C1 s) by ring; field; exact Hs.
Qed.

Definition dsGC (s : C) (x : R) : C :=
  Cadd (Cmul (RtoC (- ln x)) (Cmul (Cpw x (Cminus C1 s)) (Cinv (Cminus C1 s))))
       (Cmul (Cpw x (Cminus C1 s)) (Cmul (Cinv (Cminus C1 s)) (Cinv (Cminus C1 s)))).

Lemma GC_sderiv : forall s x, 0 < x -> Cminus C1 s <> C0 ->
  is_Cderiv (fun w => GC w x) s (dsGC s x).
Proof.
  intros s x Hx Hs; unfold GC.
  eapply is_Cderiv_eq.
  - apply Cderiv_mul; [ apply A_sderiv; exact Hx | apply B_sderiv; exact Hs ].
  - unfold dsGC; ring.
Qed.

Lemma dsGC_sderiv : forall s x, 0 < x -> Cminus C1 s <> C0 ->
  is_Cderiv (fun w => dsGC w x) s (d2sGC s x).
Proof.
  intros s x Hx Hs; unfold dsGC.
  eapply is_Cderiv_eq.
  - apply Cderiv_add.
    + apply Cderiv_cscal; apply Cderiv_mul;
        [ apply A_sderiv; exact Hx | apply B_sderiv; exact Hs ].
    + apply Cderiv_mul;
        [ apply A_sderiv; exact Hx | apply Cderiv_mul; apply B_sderiv; exact Hs ].
  - unfold d2sGC.
    replace (RtoC (- ln x)) with (Cmul (Copp C1) (RtoC (ln x)))
      by (unfold RtoC, Copp, C1, Cmul; apply Ceq; cbn; ring).
    replace (RtoC (ln x * ln x)) with (Cmul (RtoC (ln x)) (RtoC (ln x)))
      by (rewrite <- RtoC_mul; reflexivity).
    replace (RtoC (-2 * ln x)) with (Cmul (Copp (Cadd C1 C1)) (RtoC (ln x)))
      by (unfold RtoC, Copp, C1, Cadd, Cmul; apply Ceq; cbn; ring).
    replace (RtoC 2) with (Cadd C1 C1)
      by (unfold RtoC, C1, Cadd; apply Ceq; cbn; ring).
    ring.
Qed.

(* ------------------------------------------------------------------ *)
(*  Assembly: the first/second s-derivatives of gtermC, with the       *)
(*  second matching the structural d2gtermC (CZetaTerm2) exactly.       *)
(* ------------------------------------------------------------------ *)

(* the explicit first s-derivative of gtermC *)
Definition dgtermC (s : C) (n : nat) : C :=
  Cminus (dsk s (INR (S n)))
         (Cminus (dsGC s (INR (S (S n)))) (dsGC s (INR (S n)))).

Lemma gtermC_sderiv : forall s n, Cminus C1 s <> C0 ->
  is_Cderiv (fun w => gtermC w n) s (dgtermC s n).
Proof.
  intros s n Hs; unfold gtermC, dgtermC.
  apply Cderiv_minus.
  - unfold gC; apply gC_sderiv; apply lt_0_INR; lia.
  - apply Cderiv_minus.
    + apply GC_sderiv; [ apply lt_0_INR; lia | exact Hs ].
    + apply GC_sderiv; [ apply lt_0_INR; lia | exact Hs ].
Qed.

(* the second s-derivative of gtermC IS the structural d2gtermC *)
Lemma dgtermC_sderiv : forall s n, Cminus C1 s <> C0 ->
  is_Cderiv (fun w => dgtermC w n) s (d2gtermC s n).
Proof.
  intros s n Hs; unfold dgtermC, d2gtermC.
  apply Cderiv_minus.
  - apply dsk_sderiv; apply lt_0_INR; lia.
  - apply Cderiv_minus.
    + apply dsGC_sderiv; [ apply lt_0_INR; lia | exact Hs ].
    + apply dsGC_sderiv; [ apply lt_0_INR; lia | exact Hs ].
Qed.

Print Assumptions gtermC_sderiv.
Print Assumptions dgtermC_sderiv.

(* ================================================================= *)
(*  END CZetaDeriv2.v (item 2b.2: explicit s-derivatives of gtermC,    *)
(*  with the second = structural d2gtermC whose modulus 3b bounds).    *)
(* ================================================================= *)
