(* ================================================================= *)
(*  CBaseDeriv2.v  —  the knot: the second s-derivative of GC =         *)
(*  t^{1-s}/(1-s) is the base-antiderivative of the second s-derivative *)
(*  kernel d2k(-s) = (ln t)^2 t^{-s}, i.e. d/dt (d2sGC) = d2k(-s).       *)
(*  Proved by direct base differentiation of the explicit               *)
(*  A''B + 2A'B' + AB'' form; the (1-s) and ln t factors collapse.       *)
(*  Axiom-clean.                                                       *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra FunctionalExtensionality.
Require Import ComplexField Cmodulus CexpFull CPowBase CBaseDeriv CZetaTerm.
Open Scope R_scope.

(* base derivative of one term  phi(t)·(t^{1-s}·K):
   d/dt = phi'·(t^{1-s}·K) + phi·((1-s)·t^{-s}·K). *)
Lemma base_deriv_term_Re : forall (phi : R -> R) (phi' : R) (K s : C) (t : R), 0 < t ->
  derivable_pt_lim phi t phi' ->
  derivable_pt_lim (fun u => Re (Cmul (RtoC (phi u)) (Cmul (Cpw u (Cminus C1 s)) K))) t
    (phi' * Re (Cmul (Cpw t (Cminus C1 s)) K)
     + phi t * Re (Cmul (Cmul (Cminus C1 s) (Cpw t (Cminus (Cminus C1 s) C1))) K)).
Proof.
  intros phi phi' K s t Ht Hphi.
  assert (Heq : (fun u => Re (Cmul (RtoC (phi u)) (Cmul (Cpw u (Cminus C1 s)) K)))
              = (fun u => phi u * Re (Cmul (Cpw u (Cminus C1 s)) K)))
    by (apply functional_extensionality; intro u; unfold Cmul, RtoC; cbn; ring).
  rewrite Heq.
  apply (derivable_pt_lim_mult phi (fun u => Re (Cmul (Cpw u (Cminus C1 s)) K)) t
           phi' (Re (Cmul (Cmul (Cminus C1 s) (Cpw t (Cminus (Cminus C1 s) C1))) K))).
  - exact Hphi.
  - apply Re_Cmul_deriv; exact Ht.
Qed.

Lemma base_deriv_term_Im : forall (phi : R -> R) (phi' : R) (K s : C) (t : R), 0 < t ->
  derivable_pt_lim phi t phi' ->
  derivable_pt_lim (fun u => Im (Cmul (RtoC (phi u)) (Cmul (Cpw u (Cminus C1 s)) K))) t
    (phi' * Im (Cmul (Cpw t (Cminus C1 s)) K)
     + phi t * Im (Cmul (Cmul (Cminus C1 s) (Cpw t (Cminus (Cminus C1 s) C1))) K)).
Proof.
  intros phi phi' K s t Ht Hphi.
  assert (Heq : (fun u => Im (Cmul (RtoC (phi u)) (Cmul (Cpw u (Cminus C1 s)) K)))
              = (fun u => phi u * Im (Cmul (Cpw u (Cminus C1 s)) K)))
    by (apply functional_extensionality; intro u; unfold Cmul, RtoC; cbn; ring).
  rewrite Heq.
  apply (derivable_pt_lim_mult phi (fun u => Im (Cmul (Cpw u (Cminus C1 s)) K)) t
           phi' (Im (Cmul (Cmul (Cminus C1 s) (Cpw t (Cminus (Cminus C1 s) C1))) K))).
  - exact Hphi.
  - apply Im_Cmul_deriv; exact Ht.
Qed.

(* the algebraic heart of the knot: with B = 1/onems, the six terms of
   d/dt(d2sGC) collapse (via onems·B = 1 and RtoC coefficient cancellation)
   to a·a·Q.  Q = t^{-s}, onems = 1-s, a = ln t. *)
Lemma d2sGC_cancel : forall (Q onems : C) (a : R), onems <> C0 ->
  Cadd (Cadd
    (Cadd (Cmul (RtoC (2 * a)) (Cmul Q (Cinv onems)))
          (Cmul (RtoC (a * a)) (Cmul (Cmul onems Q) (Cinv onems))))
    (Cadd (Cmul (RtoC (-2)) (Cmul Q (Cmul (Cinv onems) (Cinv onems))))
          (Cmul (RtoC (-2 * a)) (Cmul (Cmul onems Q) (Cmul (Cinv onems) (Cinv onems))))))
    (Cadd (Cmul (RtoC 0) (Cmul Q (Cmul (Cinv onems) (Cmul (Cinv onems) (Cinv onems)))))
          (Cmul (RtoC 2) (Cmul (Cmul onems Q) (Cmul (Cinv onems) (Cmul (Cinv onems) (Cinv onems))))))
  = Cmul (RtoC (a * a)) Q.
Proof.
  intros Q onems a H.
  replace (RtoC (2 * a)) with (Cmul (Cadd C1 C1) (RtoC a))
    by (unfold RtoC, C1, Cadd, Cmul; apply Ceq; cbn; ring).
  replace (RtoC (-2 * a)) with (Cmul (Copp (Cadd C1 C1)) (RtoC a))
    by (unfold RtoC, C1, Copp, Cadd, Cmul; apply Ceq; cbn; ring).
  replace (RtoC (a * a)) with (Cmul (RtoC a) (RtoC a))
    by (rewrite <- RtoC_mul; reflexivity).
  replace (RtoC 2) with (Cadd C1 C1)
    by (unfold RtoC, C1, Cadd; apply Ceq; cbn; ring).
  replace (RtoC (-2)) with (Copp (Cadd C1 C1))
    by (unfold RtoC, C1, Copp, Cadd; apply Ceq; cbn; ring).
  replace (RtoC 0) with C0 by (unfold RtoC, C0; apply Ceq; cbn; ring).
  field; exact H.
Qed.

Print Assumptions base_deriv_term_Re.
Print Assumptions d2sGC_cancel.

(* ================================================================= *)
(*  END CBaseDeriv2.v (part 2: the cancellation identity).            *)
(* ================================================================= *)
