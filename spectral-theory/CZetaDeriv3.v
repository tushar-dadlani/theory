(* ================================================================= *)
(*  CZetaDeriv3.v  —  the FIRST-order knot and the convergence of the   *)
(*  derivative series D = sum dgtermC(z,n), needed for zetaC_holo.      *)
(*                                                                    *)
(*  Part 1: the first-order knot  d/dt (dsGC s t) = dsk s t             *)
(*  (dsGC = d_s GC = -ln t A B + A B^2, dsk = d_s gC = -ln t t^{-s}),   *)
(*  the exact analogue of base_deriv_d2sGC, reusing base_deriv_term,    *)
(*  Cpw_onems, combine_real.  Axiom-clean.                             *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia FunctionalExtensionality.
Require Import ComplexField Cmodulus CexpFull CPowBase CBaseDeriv CBaseDeriv2
               CZetaTerm CZetaDeriv2.
Open Scope R_scope.

(* the algebraic heart of the first-order knot: the four terms of
   d/dt(dsGC) collapse (via onems·B = 1) to -a·Q = dsk.  *)
Lemma dsGC_cancel : forall (Q onems : C) (a : R), onems <> C0 ->
  Cadd (Cadd
    (Cmul (RtoC (-1)) (Cmul Q (Cinv onems)))
    (Cmul (RtoC (- a)) (Cmul (Cmul onems Q) (Cinv onems))))
    (Cadd
    (Cmul (RtoC 0) (Cmul Q (Cmul (Cinv onems) (Cinv onems))))
    (Cmul (RtoC 1) (Cmul (Cmul onems Q) (Cmul (Cinv onems) (Cinv onems)))))
  = Cmul (Copp C1) (Cmul (RtoC a) Q).
Proof.
  intros Q onems a H.
  replace (RtoC (- a)) with (Cmul (Copp C1) (RtoC a))
    by (unfold RtoC, Copp, C1, Cmul; apply Ceq; cbn; ring).
  replace (RtoC (-1)) with (Copp C1)
    by (unfold RtoC, Copp, C1; apply Ceq; cbn; ring).
  replace (RtoC 1) with C1 by (unfold RtoC, C1; apply Ceq; cbn; ring).
  replace (RtoC 0) with C0 by (unfold RtoC, C0; apply Ceq; cbn; ring).
  field; exact H.
Qed.

(* the raw base derivative of dsGC (as produced by base_deriv_term) *)
Definition ddsGC (s : C) (t : R) : C :=
  Cadd (Cadd
    (Cmul (RtoC (- / t)) (Cmul (Cpw t (Cminus C1 s)) (Cinv (Cminus C1 s))))
    (Cmul (RtoC (- ln t))
          (Cmul (Cmul (Cminus C1 s) (Cpw t (Cminus (Cminus C1 s) C1))) (Cinv (Cminus C1 s)))))
    (Cadd
    (Cmul (RtoC 0)
          (Cmul (Cpw t (Cminus C1 s)) (Cmul (Cinv (Cminus C1 s)) (Cinv (Cminus C1 s)))))
    (Cmul (RtoC 1)
          (Cmul (Cmul (Cminus C1 s) (Cpw t (Cminus (Cminus C1 s) C1)))
                (Cmul (Cinv (Cminus C1 s)) (Cinv (Cminus C1 s)))))).

Lemma dd_eq_1 : forall s t, 0 < t -> Cminus C1 s <> C0 -> ddsGC s t = dsk s t.
Proof.
  intros s t Ht Hs; assert (Ht0 : t <> 0) by lra; unfold ddsGC, dsk.
  assert (HP1 : Cpw t (Cminus (Cminus C1 s) C1) = Cpw t (Copp s)) by (f_equal; ring).
  rewrite !HP1, !(Cpw_onems s t Ht).
  replace (- / t) with ((-1) * / t) by ring.
  rewrite (combine_real (-1) t (Cpw t (Copp s)) (Cinv (Cminus C1 s)) Ht0).
  replace (Cmul (RtoC 0)
             (Cmul (Cmul (RtoC t) (Cpw t (Copp s)))
                   (Cmul (Cinv (Cminus C1 s)) (Cinv (Cminus C1 s)))))
    with (Cmul (RtoC 0)
             (Cmul (Cpw t (Copp s))
                   (Cmul (Cinv (Cminus C1 s)) (Cinv (Cminus C1 s)))))
    by (rewrite !RtoC0_mul; reflexivity).
  apply (dsGC_cancel (Cpw t (Copp s)) (Cminus C1 s) (ln t) Hs).
Qed.

(* THE FIRST-ORDER KNOT: d/dt (d_s GC) = d_s gC, componentwise. *)
Lemma base_deriv_dsGC_Re : forall s t, 0 < t -> Cminus C1 s <> C0 ->
  derivable_pt_lim (fun u => Re (dsGC s u)) t (Re (dsk s t)).
Proof.
  intros s t Ht Hs.
  rewrite <- (dd_eq_1 s t Ht Hs).
  assert (Hfun : (fun u => Re (dsGC s u))
    = (fun u =>
        Re (Cmul (RtoC (- ln u)) (Cmul (Cpw u (Cminus C1 s)) (Cinv (Cminus C1 s))))
      + Re (Cmul (RtoC 1)
              (Cmul (Cpw u (Cminus C1 s)) (Cmul (Cinv (Cminus C1 s)) (Cinv (Cminus C1 s))))))).
  { apply functional_extensionality; intro u; unfold dsGC; rewrite Re_Cadd.
    f_equal; rewrite Re_RtoC_mul; ring. }
  rewrite Hfun.
  replace (Re (ddsGC s t)) with (
    ((- / t) * Re (Cmul (Cpw t (Cminus C1 s)) (Cinv (Cminus C1 s)))
     + (- ln t) * Re (Cmul (Cmul (Cminus C1 s) (Cpw t (Cminus (Cminus C1 s) C1))) (Cinv (Cminus C1 s))))
    + (0 * Re (Cmul (Cpw t (Cminus C1 s)) (Cmul (Cinv (Cminus C1 s)) (Cinv (Cminus C1 s))))
     + 1 * Re (Cmul (Cmul (Cminus C1 s) (Cpw t (Cminus (Cminus C1 s) C1))) (Cmul (Cinv (Cminus C1 s)) (Cinv (Cminus C1 s))))))
    by (unfold ddsGC; rewrite !Re_Cadd, !Re_RtoC_mul; ring).
  apply derivable_pt_lim_plus.
  - apply (base_deriv_term_Re (fun u => - ln u) (- / t)
             (Cinv (Cminus C1 s)) s t Ht).
    apply derivable_pt_lim_opp; apply derivable_pt_lim_ln; exact Ht.
  - apply (base_deriv_term_Re (fun u => 1) 0
             (Cmul (Cinv (Cminus C1 s)) (Cinv (Cminus C1 s))) s t Ht).
    apply (derivable_pt_lim_const 1 t).
Qed.

Lemma base_deriv_dsGC_Im : forall s t, 0 < t -> Cminus C1 s <> C0 ->
  derivable_pt_lim (fun u => Im (dsGC s u)) t (Im (dsk s t)).
Proof.
  intros s t Ht Hs.
  rewrite <- (dd_eq_1 s t Ht Hs).
  assert (Hfun : (fun u => Im (dsGC s u))
    = (fun u =>
        Im (Cmul (RtoC (- ln u)) (Cmul (Cpw u (Cminus C1 s)) (Cinv (Cminus C1 s))))
      + Im (Cmul (RtoC 1)
              (Cmul (Cpw u (Cminus C1 s)) (Cmul (Cinv (Cminus C1 s)) (Cinv (Cminus C1 s))))))).
  { apply functional_extensionality; intro u; unfold dsGC; rewrite Im_Cadd.
    f_equal; rewrite Im_RtoC_mul; ring. }
  rewrite Hfun.
  replace (Im (ddsGC s t)) with (
    ((- / t) * Im (Cmul (Cpw t (Cminus C1 s)) (Cinv (Cminus C1 s)))
     + (- ln t) * Im (Cmul (Cmul (Cminus C1 s) (Cpw t (Cminus (Cminus C1 s) C1))) (Cinv (Cminus C1 s))))
    + (0 * Im (Cmul (Cpw t (Cminus C1 s)) (Cmul (Cinv (Cminus C1 s)) (Cinv (Cminus C1 s))))
     + 1 * Im (Cmul (Cmul (Cminus C1 s) (Cpw t (Cminus (Cminus C1 s) C1))) (Cmul (Cinv (Cminus C1 s)) (Cinv (Cminus C1 s))))))
    by (unfold ddsGC; rewrite !Im_Cadd, !Im_RtoC_mul; ring).
  apply derivable_pt_lim_plus.
  - apply (base_deriv_term_Im (fun u => - ln u) (- / t)
             (Cinv (Cminus C1 s)) s t Ht).
    apply derivable_pt_lim_opp; apply derivable_pt_lim_ln; exact Ht.
  - apply (base_deriv_term_Im (fun u => 1) 0
             (Cmul (Cinv (Cminus C1 s)) (Cinv (Cminus C1 s))) s t Ht).
    apply (derivable_pt_lim_const 1 t).
Qed.

Print Assumptions base_deriv_dsGC_Re.

(* ================================================================= *)
(*  END CZetaDeriv3.v (part 1: the first-order knot).                 *)
(* ================================================================= *)
