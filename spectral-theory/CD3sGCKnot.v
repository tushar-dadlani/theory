(* ================================================================= *)
(*  CD3sGCKnot.v  —  Milestone B, brick B6b: the THIRD-order knot.       *)
(*  d/dt (d3sGC s t) = d3k s t  (= the pole-free third s-derivative       *)
(*  kernel -(ln t)^3 t^{-s}); the (1-s) and ln t factors telescope.      *)
(*  One order up from CBaseDeriv2's dd_eq / base_deriv_d2sGC.            *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra FunctionalExtensionality.
Require Import ComplexField Cmodulus CexpFull CPowBase CBaseDeriv CBaseDeriv2
        CBaseDeriv3 CZetaTerm CZetaDeriv2 CZetaDeriv5.
Open Scope R_scope.

(* the raw base (t) derivative of d3sGC, as base_deriv_term produces it,
   written flat (right-associated) for easy bracket-balancing. *)
Definition dd3sGC (s : C) (t : R) : C :=
  Cadd (Cmul (RtoC ((- (3 * (ln t * ln t))) * / t))
             (Cmul (Cpw t (Cminus C1 s)) (Cinv (Cminus C1 s))))
  (Cadd (Cmul (RtoC (- (ln t * ln t * ln t)))
              (Cmul (Cmul (Cminus C1 s) (Cpw t (Cminus (Cminus C1 s) C1))) (Cinv (Cminus C1 s))))
  (Cadd (Cmul (RtoC ((6 * ln t) * / t))
              (Cmul (Cpw t (Cminus C1 s)) (Cmul (Cinv (Cminus C1 s)) (Cinv (Cminus C1 s)))))
  (Cadd (Cmul (RtoC (3 * (ln t * ln t)))
              (Cmul (Cmul (Cminus C1 s) (Cpw t (Cminus (Cminus C1 s) C1)))
                    (Cmul (Cinv (Cminus C1 s)) (Cinv (Cminus C1 s)))))
  (Cadd (Cmul (RtoC ((-6) * / t))
              (Cmul (Cpw t (Cminus C1 s))
                    (Cmul (Cinv (Cminus C1 s)) (Cmul (Cinv (Cminus C1 s)) (Cinv (Cminus C1 s))))))
  (Cadd (Cmul (RtoC (-6 * ln t))
              (Cmul (Cmul (Cminus C1 s) (Cpw t (Cminus (Cminus C1 s) C1)))
                    (Cmul (Cinv (Cminus C1 s)) (Cmul (Cinv (Cminus C1 s)) (Cinv (Cminus C1 s))))))
  (Cadd (Cmul (RtoC 0)
              (Cmul (Cpw t (Cminus C1 s))
                    (Cmul (Cinv (Cminus C1 s))
                          (Cmul (Cinv (Cminus C1 s)) (Cmul (Cinv (Cminus C1 s)) (Cinv (Cminus C1 s)))))))
        (Cmul (RtoC 6)
              (Cmul (Cmul (Cminus C1 s) (Cpw t (Cminus (Cminus C1 s) C1)))
                    (Cmul (Cinv (Cminus C1 s))
                          (Cmul (Cinv (Cminus C1 s)) (Cmul (Cinv (Cminus C1 s)) (Cinv (Cminus C1 s))))))))))))).

(* the algebraic telescoping: eight terms collapse to -a^3 Q *)
Lemma d3sGC_cancel : forall (Q onems : C) (a : R), onems <> C0 ->
  Cadd (Cmul (RtoC (- (3 * (a * a)))) (Cmul Q (Cinv onems)))
  (Cadd (Cmul (RtoC (- (a * a * a))) (Cmul (Cmul onems Q) (Cinv onems)))
  (Cadd (Cmul (RtoC (6 * a)) (Cmul Q (Cmul (Cinv onems) (Cinv onems))))
  (Cadd (Cmul (RtoC (3 * (a * a))) (Cmul (Cmul onems Q) (Cmul (Cinv onems) (Cinv onems))))
  (Cadd (Cmul (RtoC (-6)) (Cmul Q (Cmul (Cinv onems) (Cmul (Cinv onems) (Cinv onems)))))
  (Cadd (Cmul (RtoC (-6 * a)) (Cmul (Cmul onems Q) (Cmul (Cinv onems) (Cmul (Cinv onems) (Cinv onems)))))
  (Cadd (Cmul (RtoC 0) (Cmul Q (Cmul (Cinv onems) (Cmul (Cinv onems) (Cmul (Cinv onems) (Cinv onems))))))
        (Cmul (RtoC 6) (Cmul (Cmul onems Q) (Cmul (Cinv onems) (Cmul (Cinv onems) (Cmul (Cinv onems) (Cinv onems))))))))))))
  = Cmul (RtoC (- (a * a * a))) Q.
Proof.
  intros Q onems a H.
  replace (RtoC (- (3 * (a * a)))) with (Cmul (Copp (Cadd C1 (Cadd C1 C1))) (Cmul (RtoC a) (RtoC a)))
    by (unfold RtoC, C1, Copp, Cadd, Cmul; apply Ceq; cbn; ring).
  replace (RtoC (- (a * a * a)))
    with (Cmul (Copp C1) (Cmul (RtoC a) (Cmul (RtoC a) (RtoC a))))
    by (unfold RtoC, C1, Copp, Cmul; apply Ceq; cbn; ring).
  replace (RtoC (6 * a)) with (Cmul (Cadd (Cadd C1 C1) (Cadd (Cadd C1 C1) (Cadd C1 C1))) (RtoC a))
    by (unfold RtoC, C1, Cadd, Cmul; apply Ceq; cbn; ring).
  replace (RtoC (3 * (a * a))) with (Cmul (Cadd C1 (Cadd C1 C1)) (Cmul (RtoC a) (RtoC a)))
    by (unfold RtoC, C1, Cadd, Cmul; apply Ceq; cbn; ring).
  replace (RtoC (-6)) with (Copp (Cadd (Cadd C1 C1) (Cadd (Cadd C1 C1) (Cadd C1 C1))))
    by (unfold RtoC, C1, Copp, Cadd; apply Ceq; cbn; ring).
  replace (RtoC (-6 * a)) with (Cmul (Copp (Cadd (Cadd C1 C1) (Cadd (Cadd C1 C1) (Cadd C1 C1)))) (RtoC a))
    by (unfold RtoC, C1, Copp, Cadd, Cmul; apply Ceq; cbn; ring).
  replace (RtoC 6) with (Cadd (Cadd C1 C1) (Cadd (Cadd C1 C1) (Cadd C1 C1)))
    by (unfold RtoC, C1, Cadd; apply Ceq; cbn; ring).
  replace (RtoC 0) with C0 by (unfold RtoC, C0; apply Ceq; cbn; ring).
  field; exact H.
Qed.

Lemma dd_eq3 : forall s t, 0 < t -> Cminus C1 s <> C0 -> dd3sGC s t = d3k s t.
Proof.
  intros s t Ht Hs; assert (Ht0 : t <> 0) by lra; unfold dd3sGC.
  assert (HP1 : Cpw t (Cminus (Cminus C1 s) C1) = Cpw t (Copp s)) by (f_equal; ring).
  rewrite !HP1, !(Cpw_onems s t Ht).
  rewrite (combine_real (- (3 * (ln t * ln t))) t (Cpw t (Copp s)) (Cinv (Cminus C1 s)) Ht0).
  rewrite (combine_real (6 * ln t) t (Cpw t (Copp s))
             (Cmul (Cinv (Cminus C1 s)) (Cinv (Cminus C1 s))) Ht0).
  rewrite (combine_real (-6) t (Cpw t (Copp s))
             (Cmul (Cinv (Cminus C1 s)) (Cmul (Cinv (Cminus C1 s)) (Cinv (Cminus C1 s)))) Ht0).
  replace (Cmul (RtoC 0)
             (Cmul (Cmul (RtoC t) (Cpw t (Copp s)))
                   (Cmul (Cinv (Cminus C1 s))
                         (Cmul (Cinv (Cminus C1 s)) (Cmul (Cinv (Cminus C1 s)) (Cinv (Cminus C1 s)))))))
    with (Cmul (RtoC 0)
             (Cmul (Cpw t (Copp s))
                   (Cmul (Cinv (Cminus C1 s))
                         (Cmul (Cinv (Cminus C1 s)) (Cmul (Cinv (Cminus C1 s)) (Cinv (Cminus C1 s)))))))
    by (rewrite !RtoC0_mul; reflexivity).
  rewrite (d3sGC_cancel (Cpw t (Copp s)) (Cminus C1 s) (ln t) Hs).
  unfold d3k, dsk.
  replace (RtoC (- (ln t * ln t * ln t)))
    with (Cmul (RtoC (ln t * ln t)) (Cmul (Copp C1) (RtoC (ln t))))
    by (unfold RtoC, Copp, C1, Cmul; apply Ceq; cbn; ring).
  ring.
Qed.

(* the third-order knot, componentwise (target grouped left-assoc for the plus tree) *)
Lemma base_deriv_d3sGC_Re : forall s t, 0 < t -> Cminus C1 s <> C0 ->
  derivable_pt_lim (fun u => Re (d3sGC s u)) t (Re (d3k s t)).
Proof.
  intros s t Ht Hs.
  rewrite <- (dd_eq3 s t Ht Hs).
  assert (Hfun : (fun u => Re (d3sGC s u))
    = (fun u =>
        Re (Cmul (RtoC (- (ln u * ln u * ln u))) (Cmul (Cpw u (Cminus C1 s)) (Cinv (Cminus C1 s))))
      + Re (Cmul (RtoC (3 * (ln u * ln u)))
              (Cmul (Cpw u (Cminus C1 s)) (Cmul (Cinv (Cminus C1 s)) (Cinv (Cminus C1 s)))))
      + Re (Cmul (RtoC (-6 * ln u))
              (Cmul (Cpw u (Cminus C1 s))
                    (Cmul (Cinv (Cminus C1 s)) (Cmul (Cinv (Cminus C1 s)) (Cinv (Cminus C1 s))))))
      + Re (Cmul (RtoC 6)
              (Cmul (Cpw u (Cminus C1 s))
                    (Cmul (Cinv (Cminus C1 s))
                          (Cmul (Cinv (Cminus C1 s)) (Cmul (Cinv (Cminus C1 s)) (Cinv (Cminus C1 s))))))))).
  { apply functional_extensionality; intro u; unfold d3sGC; rewrite !Re_Cadd; reflexivity. }
  rewrite Hfun.
  replace (Re (dd3sGC s t)) with
    (( (- (3 * (ln t * ln t) * / t)) * Re (Cmul (Cpw t (Cminus C1 s)) (Cinv (Cminus C1 s)))
       + - (ln t * ln t * ln t) * Re (Cmul (Cmul (Cminus C1 s) (Cpw t (Cminus (Cminus C1 s) C1))) (Cinv (Cminus C1 s))) )
     + ( 3 * (2 * ln t * / t) * Re (Cmul (Cpw t (Cminus C1 s)) (Cmul (Cinv (Cminus C1 s)) (Cinv (Cminus C1 s))))
       + 3 * (ln t * ln t) * Re (Cmul (Cmul (Cminus C1 s) (Cpw t (Cminus (Cminus C1 s) C1))) (Cmul (Cinv (Cminus C1 s)) (Cinv (Cminus C1 s)))) )
     + ( (-6) * / t * Re (Cmul (Cpw t (Cminus C1 s)) (Cmul (Cinv (Cminus C1 s)) (Cmul (Cinv (Cminus C1 s)) (Cinv (Cminus C1 s)))))
       + -6 * ln t * Re (Cmul (Cmul (Cminus C1 s) (Cpw t (Cminus (Cminus C1 s) C1))) (Cmul (Cinv (Cminus C1 s)) (Cmul (Cinv (Cminus C1 s)) (Cinv (Cminus C1 s))))) )
     + ( 0 * Re (Cmul (Cpw t (Cminus C1 s)) (Cmul (Cinv (Cminus C1 s)) (Cmul (Cinv (Cminus C1 s)) (Cmul (Cinv (Cminus C1 s)) (Cinv (Cminus C1 s))))))
       + 6 * Re (Cmul (Cmul (Cminus C1 s) (Cpw t (Cminus (Cminus C1 s) C1))) (Cmul (Cinv (Cminus C1 s)) (Cmul (Cinv (Cminus C1 s)) (Cmul (Cinv (Cminus C1 s)) (Cinv (Cminus C1 s)))))) ))
    by (unfold dd3sGC; rewrite !Re_Cadd, !Re_RtoC_mul; ring).
  apply derivable_pt_lim_plus;
    [ apply derivable_pt_lim_plus; [ apply derivable_pt_lim_plus | ] | ].
  - apply (base_deriv_term_Re (fun u => - (ln u * ln u * ln u)) ((- (3 * (ln t * ln t) * / t)))
             (Cinv (Cminus C1 s)) s t Ht).
    apply (derivable_pt_lim_opp (fun u => ln u * ln u * ln u) t (3 * (ln t * ln t) * / t));
      apply dln_cube; exact Ht.
  - apply (base_deriv_term_Re (fun u => 3 * (ln u * ln u)) (3 * (2 * ln t * / t))
             (Cmul (Cinv (Cminus C1 s)) (Cinv (Cminus C1 s))) s t Ht).
    apply (derivable_pt_lim_scal (fun u => ln u * ln u) 3 t (2 * ln t * / t)); apply dln_sq; exact Ht.
  - apply (base_deriv_term_Re (fun u => -6 * ln u) ((-6) * / t)
             (Cmul (Cinv (Cminus C1 s)) (Cmul (Cinv (Cminus C1 s)) (Cinv (Cminus C1 s)))) s t Ht).
    apply (derivable_pt_lim_scal ln (-6) t (/ t)); apply derivable_pt_lim_ln; exact Ht.
  - apply (base_deriv_term_Re (fun u => 6) 0
             (Cmul (Cinv (Cminus C1 s)) (Cmul (Cinv (Cminus C1 s)) (Cmul (Cinv (Cminus C1 s)) (Cinv (Cminus C1 s))))) s t Ht).
    apply (derivable_pt_lim_const 6 t).
Qed.

Lemma base_deriv_d3sGC_Im : forall s t, 0 < t -> Cminus C1 s <> C0 ->
  derivable_pt_lim (fun u => Im (d3sGC s u)) t (Im (d3k s t)).
Proof.
  intros s t Ht Hs.
  rewrite <- (dd_eq3 s t Ht Hs).
  assert (Hfun : (fun u => Im (d3sGC s u))
    = (fun u =>
        Im (Cmul (RtoC (- (ln u * ln u * ln u))) (Cmul (Cpw u (Cminus C1 s)) (Cinv (Cminus C1 s))))
      + Im (Cmul (RtoC (3 * (ln u * ln u)))
              (Cmul (Cpw u (Cminus C1 s)) (Cmul (Cinv (Cminus C1 s)) (Cinv (Cminus C1 s)))))
      + Im (Cmul (RtoC (-6 * ln u))
              (Cmul (Cpw u (Cminus C1 s))
                    (Cmul (Cinv (Cminus C1 s)) (Cmul (Cinv (Cminus C1 s)) (Cinv (Cminus C1 s))))))
      + Im (Cmul (RtoC 6)
              (Cmul (Cpw u (Cminus C1 s))
                    (Cmul (Cinv (Cminus C1 s))
                          (Cmul (Cinv (Cminus C1 s)) (Cmul (Cinv (Cminus C1 s)) (Cinv (Cminus C1 s))))))))).
  { apply functional_extensionality; intro u; unfold d3sGC; rewrite !Im_Cadd; reflexivity. }
  rewrite Hfun.
  replace (Im (dd3sGC s t)) with
    (( (- (3 * (ln t * ln t) * / t)) * Im (Cmul (Cpw t (Cminus C1 s)) (Cinv (Cminus C1 s)))
       + - (ln t * ln t * ln t) * Im (Cmul (Cmul (Cminus C1 s) (Cpw t (Cminus (Cminus C1 s) C1))) (Cinv (Cminus C1 s))) )
     + ( 3 * (2 * ln t * / t) * Im (Cmul (Cpw t (Cminus C1 s)) (Cmul (Cinv (Cminus C1 s)) (Cinv (Cminus C1 s))))
       + 3 * (ln t * ln t) * Im (Cmul (Cmul (Cminus C1 s) (Cpw t (Cminus (Cminus C1 s) C1))) (Cmul (Cinv (Cminus C1 s)) (Cinv (Cminus C1 s)))) )
     + ( (-6) * / t * Im (Cmul (Cpw t (Cminus C1 s)) (Cmul (Cinv (Cminus C1 s)) (Cmul (Cinv (Cminus C1 s)) (Cinv (Cminus C1 s)))))
       + -6 * ln t * Im (Cmul (Cmul (Cminus C1 s) (Cpw t (Cminus (Cminus C1 s) C1))) (Cmul (Cinv (Cminus C1 s)) (Cmul (Cinv (Cminus C1 s)) (Cinv (Cminus C1 s))))) )
     + ( 0 * Im (Cmul (Cpw t (Cminus C1 s)) (Cmul (Cinv (Cminus C1 s)) (Cmul (Cinv (Cminus C1 s)) (Cmul (Cinv (Cminus C1 s)) (Cinv (Cminus C1 s))))))
       + 6 * Im (Cmul (Cmul (Cminus C1 s) (Cpw t (Cminus (Cminus C1 s) C1))) (Cmul (Cinv (Cminus C1 s)) (Cmul (Cinv (Cminus C1 s)) (Cmul (Cinv (Cminus C1 s)) (Cinv (Cminus C1 s)))))) ))
    by (unfold dd3sGC; rewrite !Im_Cadd, !Im_RtoC_mul; ring).
  apply derivable_pt_lim_plus;
    [ apply derivable_pt_lim_plus; [ apply derivable_pt_lim_plus | ] | ].
  - apply (base_deriv_term_Im (fun u => - (ln u * ln u * ln u)) ((- (3 * (ln t * ln t) * / t)))
             (Cinv (Cminus C1 s)) s t Ht).
    apply (derivable_pt_lim_opp (fun u => ln u * ln u * ln u) t (3 * (ln t * ln t) * / t));
      apply dln_cube; exact Ht.
  - apply (base_deriv_term_Im (fun u => 3 * (ln u * ln u)) (3 * (2 * ln t * / t))
             (Cmul (Cinv (Cminus C1 s)) (Cinv (Cminus C1 s))) s t Ht).
    apply (derivable_pt_lim_scal (fun u => ln u * ln u) 3 t (2 * ln t * / t)); apply dln_sq; exact Ht.
  - apply (base_deriv_term_Im (fun u => -6 * ln u) ((-6) * / t)
             (Cmul (Cinv (Cminus C1 s)) (Cmul (Cinv (Cminus C1 s)) (Cinv (Cminus C1 s)))) s t Ht).
    apply (derivable_pt_lim_scal ln (-6) t (/ t)); apply derivable_pt_lim_ln; exact Ht.
  - apply (base_deriv_term_Im (fun u => 6) 0
             (Cmul (Cinv (Cminus C1 s)) (Cmul (Cinv (Cminus C1 s)) (Cmul (Cinv (Cminus C1 s)) (Cinv (Cminus C1 s))))) s t Ht).
    apply (derivable_pt_lim_const 6 t).
Qed.

Print Assumptions dd_eq3.
Print Assumptions base_deriv_d3sGC_Re.

(* ================================================================= *)
(*  END CD3sGCKnot.v  —  d/dt d3sGC = d3k (the third-order knot).        *)
(* ================================================================= *)
