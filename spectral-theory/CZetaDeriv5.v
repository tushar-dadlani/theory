(* ================================================================= *)
(*  CZetaDeriv5.v  —  Milestone B, brick B5: the THIRD s-derivative of  *)
(*  the Euler-Maclaurin term gtermC, one order up from CZetaDeriv2.      *)
(*  Everything is built from the self-reproducing is_Cderiv calculus     *)
(*  (A_sderiv, B_sderiv, gC_sderiv), so no new MVT machinery is needed:  *)
(*    d3k    = d/ds of d2k(Copp .)        = (ln x)^2 * dsk                *)
(*    d3sGC  = d/ds of d2sGC              = A'''B+3A''B'+3A'B''+AB'''     *)
(*             = -ln^3 AB + 3ln^2 AB^2 - 6ln AB^3 + 6 AB^4                *)
(*    d3gtermC = d/ds of d2gtermC (structural)                           *)
(*  giving  is_Cderiv (fun w => d2gtermC w n) s (d3gtermC s n).           *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import ComplexField Cmodulus CexpFull CDeriv Holomorphic
        CBaseDeriv CBaseDeriv2 CZetaTerm CZetaTerm2 CZetaDeriv2.
Open Scope R_scope.

(* ---- the pole-free third derivative term:  ln^2 x * dsk ---- *)
Definition d3k (s : C) (x : R) : C := Cmul (RtoC (ln x * ln x)) (dsk s x).

Lemma d2k_Copp_sderiv : forall s x, 0 < x ->
  is_Cderiv (fun w => d2k (Copp w) x) s (d3k s x).
Proof.
  intros s x Hx.
  apply (is_Cderiv_ext (fun w => Cmul (RtoC (ln x * ln x)) (Cpw x (Copp w)))).
  - intro w; unfold d2k; reflexivity.
  - unfold d3k; apply Cderiv_cscal; apply gC_sderiv; exact Hx.
Qed.

(* ---- the third s-derivative of the antiderivative kernel ---- *)
Definition d3sGC (s : C) (x : R) : C :=
  Cadd (Cadd (Cadd
    (Cmul (RtoC (- (ln x * ln x * ln x)))
          (Cmul (Cpw x (Cminus C1 s)) (Cinv (Cminus C1 s))))
    (Cmul (RtoC (3 * (ln x * ln x)))
          (Cmul (Cpw x (Cminus C1 s)) (Cmul (Cinv (Cminus C1 s)) (Cinv (Cminus C1 s))))))
    (Cmul (RtoC (-6 * ln x))
          (Cmul (Cpw x (Cminus C1 s))
                (Cmul (Cinv (Cminus C1 s)) (Cmul (Cinv (Cminus C1 s)) (Cinv (Cminus C1 s)))))))
    (Cmul (RtoC 6)
          (Cmul (Cpw x (Cminus C1 s))
                (Cmul (Cinv (Cminus C1 s))
                      (Cmul (Cinv (Cminus C1 s))
                            (Cmul (Cinv (Cminus C1 s)) (Cinv (Cminus C1 s))))))).

Lemma d2sGC_sderiv : forall s x, 0 < x -> Cminus C1 s <> C0 ->
  is_Cderiv (fun w => d2sGC w x) s (d3sGC s x).
Proof.
  intros s x Hx Hs; unfold d2sGC.
  eapply is_Cderiv_eq.
  - apply Cderiv_add.
    + apply Cderiv_add.
      * apply Cderiv_cscal; apply Cderiv_mul;
          [ apply A_sderiv; exact Hx | apply B_sderiv; exact Hs ].
      * apply Cderiv_cscal; apply Cderiv_mul;
          [ apply A_sderiv; exact Hx
          | apply Cderiv_mul; apply B_sderiv; exact Hs ].
    + apply Cderiv_cscal; apply Cderiv_mul;
        [ apply A_sderiv; exact Hx
        | apply Cderiv_mul;
            [ apply B_sderiv; exact Hs | apply Cderiv_mul; apply B_sderiv; exact Hs ] ].
  - unfold d3sGC.
    replace (RtoC (ln x * ln x)) with (Cmul (RtoC (ln x)) (RtoC (ln x)))
      by (rewrite <- RtoC_mul; reflexivity).
    replace (RtoC (-2 * ln x)) with (Cmul (Copp (Cadd C1 C1)) (RtoC (ln x)))
      by (unfold RtoC, Copp, C1, Cadd, Cmul; apply Ceq; cbn; ring).
    replace (RtoC 2) with (Cadd C1 C1)
      by (unfold RtoC, C1, Cadd; apply Ceq; cbn; ring).
    replace (RtoC (- ln x)) with (Cmul (Copp C1) (RtoC (ln x)))
      by (unfold RtoC, Copp, C1, Cmul; apply Ceq; cbn; ring).
    replace (RtoC (- (ln x * ln x * ln x)))
      with (Cmul (Copp C1) (Cmul (RtoC (ln x)) (Cmul (RtoC (ln x)) (RtoC (ln x)))))
      by (unfold RtoC, Copp, C1, Cmul; apply Ceq; cbn; ring).
    replace (RtoC (3 * (ln x * ln x)))
      with (Cmul (Cadd C1 (Cadd C1 C1)) (Cmul (RtoC (ln x)) (RtoC (ln x))))
      by (unfold RtoC, C1, Cadd, Cmul; apply Ceq; cbn; ring).
    replace (RtoC (-6 * ln x))
      with (Cmul (Copp (Cadd (Cadd C1 C1) (Cadd (Cadd C1 C1) (Cadd C1 C1)))) (RtoC (ln x)))
      by (unfold RtoC, Copp, C1, Cadd, Cmul; apply Ceq; cbn; ring).
    replace (RtoC 6)
      with (Cadd (Cadd C1 C1) (Cadd (Cadd C1 C1) (Cadd C1 C1)))
      by (unfold RtoC, C1, Cadd; apply Ceq; cbn; ring).
    ring.
Qed.

(* ---- the structural third derivative of gtermC ---- *)
Definition d3gtermC (s : C) (n : nat) : C :=
  Cminus (d3k s (INR (S n)))
         (Cminus (d3sGC s (INR (S (S n)))) (d3sGC s (INR (S n)))).

Lemma d2gtermC_sderiv : forall s n, Cminus C1 s <> C0 ->
  is_Cderiv (fun w => d2gtermC w n) s (d3gtermC s n).
Proof.
  intros s n Hs; unfold d2gtermC, d3gtermC.
  apply Cderiv_minus.
  - apply d2k_Copp_sderiv; apply lt_0_INR; lia.
  - apply Cderiv_minus.
    + apply d2sGC_sderiv; [ apply lt_0_INR; lia | exact Hs ].
    + apply d2sGC_sderiv; [ apply lt_0_INR; lia | exact Hs ].
Qed.

Print Assumptions d2gtermC_sderiv.

(* ================================================================= *)
(*  END CZetaDeriv5.v  —  third s-derivative of gtermC (d3gtermC).       *)
(* ================================================================= *)
