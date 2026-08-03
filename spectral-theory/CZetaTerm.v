(* ================================================================= *)
(*  CZetaTerm.v  —  the complex Euler–Maclaurin term and its bound.    *)
(*                                                                    *)
(*  Part 1: derivatives of Re/Im of (c^w · K) for a complex constant   *)
(*  K (needed for the antiderivative G(x)=x^{1-s}/(1-s), whose         *)
(*  derivative is x^{-s}), and the modulus of the base derivative      *)
(*  |w·x^{w-1}| = |w|·x^{Re w-1}.  Axiom-clean.                        *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra FunctionalExtensionality.
Require Import ComplexField Cmodulus CexpFull CPowBase.
Open Scope R_scope.

(* modulus of the base derivative  w·x^{w-1} *)
Lemma Cmod_wCpw : forall w x,
  Cmod (Cmul w (Cpw x (Cminus w C1))) = Cmod w * Rpower x (Re w - 1).
Proof.
  intros w x; rewrite Cmod_mul, Cpw_mod.
  replace (Re (Cminus w C1)) with (Re w - 1)
    by (unfold Cminus, Cadd, Copp, C1; simpl; ring).
  reflexivity.
Qed.

(* derivative of Re/Im of (c^w · K) in the base *)
Lemma Re_Cmul_deriv : forall w K x, 0 < x ->
  derivable_pt_lim (fun t => Re (Cmul (Cpw t w) K)) x
    (Re (Cmul (Cmul w (Cpw x (Cminus w C1))) K)).
Proof.
  intros w K x Hx.
  assert (Heq : (fun t => Re (Cmul (Cpw t w) K))
              = (fun t => Re K * Re (Cpw t w) - Im K * Im (Cpw t w)))
    by (apply functional_extensionality; intro t; unfold Cmul; cbn [Re]; ring).
  rewrite Heq.
  replace (Re (Cmul (Cmul w (Cpw x (Cminus w C1))) K))
    with (Re K * Re (Cmul w (Cpw x (Cminus w C1)))
          - Im K * Im (Cmul w (Cpw x (Cminus w C1))))
    by (unfold Cmul; cbn [Re Im]; ring).
  apply (derivable_pt_lim_minus
           (fun t => Re K * Re (Cpw t w)) (fun t => Im K * Im (Cpw t w)) x
           (Re K * Re (Cmul w (Cpw x (Cminus w C1))))
           (Im K * Im (Cmul w (Cpw x (Cminus w C1))))).
  - apply (derivable_pt_lim_scal (fun t => Re (Cpw t w)) (Re K) x
             (Re (Cmul w (Cpw x (Cminus w C1))))); apply Re_Cpw_deriv; exact Hx.
  - apply (derivable_pt_lim_scal (fun t => Im (Cpw t w)) (Im K) x
             (Im (Cmul w (Cpw x (Cminus w C1))))); apply Im_Cpw_deriv; exact Hx.
Qed.

Lemma Im_Cmul_deriv : forall w K x, 0 < x ->
  derivable_pt_lim (fun t => Im (Cmul (Cpw t w) K)) x
    (Im (Cmul (Cmul w (Cpw x (Cminus w C1))) K)).
Proof.
  intros w K x Hx.
  assert (Heq : (fun t => Im (Cmul (Cpw t w) K))
              = (fun t => Re K * Im (Cpw t w) + Im K * Re (Cpw t w)))
    by (apply functional_extensionality; intro t; unfold Cmul; cbn [Im]; ring).
  rewrite Heq.
  replace (Im (Cmul (Cmul w (Cpw x (Cminus w C1))) K))
    with (Re K * Im (Cmul w (Cpw x (Cminus w C1)))
          + Im K * Re (Cmul w (Cpw x (Cminus w C1))))
    by (unfold Cmul; cbn [Re Im]; ring).
  apply (derivable_pt_lim_plus
           (fun t => Re K * Im (Cpw t w)) (fun t => Im K * Re (Cpw t w)) x
           (Re K * Im (Cmul w (Cpw x (Cminus w C1))))
           (Im K * Re (Cmul w (Cpw x (Cminus w C1))))).
  - apply (derivable_pt_lim_scal (fun t => Im (Cpw t w)) (Re K) x
             (Im (Cmul w (Cpw x (Cminus w C1))))); apply Im_Cpw_deriv; exact Hx.
  - apply (derivable_pt_lim_scal (fun t => Re (Cpw t w)) (Im K) x
             (Re (Cmul w (Cpw x (Cminus w C1))))); apply Re_Cpw_deriv; exact Hx.
Qed.

Print Assumptions Re_Cmul_deriv.

(* ================================================================= *)
(*  END CZetaTerm.v (part 1).                                          *)
(* ================================================================= *)
