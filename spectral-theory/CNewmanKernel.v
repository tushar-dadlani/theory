(* ================================================================= *)
(*  CNewmanKernel.v  —  Milestone C, brick C4-K: Newman's kernel.       *)
(*                                                                    *)
(*  The Zagier/Newman kernel  K_R(z) = 1/z + z/R²  has the decisive     *)
(*  property that ON the circle |z| = R it collapses to the REAL value  *)
(*  2·Re(z)/R²  (since 1/z = z̄/R² there), so |K_R(z)| = 2|Re z|/R².      *)
(*  This is what powers Newman's right-semicircle O(B/R) estimate.       *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import ComplexField Cmodulus.
Open Scope R_scope.

Definition newman_kernel (R : R) (z : C) : C :=
  Cadd (Cinv z) (Cmul z (RtoC (/ (R * R)))).

(* on |z| = R the kernel is the real number 2·Re z / R² *)
Lemma newman_kernel_on_circle : forall R z, 0 < R -> Cnorm2 z = R * R ->
  newman_kernel R z = RtoC (2 * Re z / (R * R)).
Proof.
  intros R z HR Hz.
  unfold newman_kernel, Cinv, Cnorm2 in *; rewrite Hz.
  unfold Cmul, Cadd, RtoC; apply Ceq; cbn; field; nra.
Qed.

(* hence its modulus is 2·|Re z| / R² on the circle *)
Lemma Cmod_newman_kernel : forall R z, 0 < R -> Cnorm2 z = R * R ->
  Cmod (newman_kernel R z) = 2 * Rabs (Re z) / (R * R).
Proof.
  intros R z HR Hz.
  rewrite (newman_kernel_on_circle R z HR Hz), Cmod_RtoC.
  unfold Rdiv; rewrite Rabs_mult, Rabs_mult, (Rabs_pos_eq 2) by lra.
  rewrite Rabs_inv, (Rabs_pos_eq (R * R)) by nra; ring.
Qed.

(* the kernel splits into the residue part (1/z) and a holomorphic part (z/R²) *)
Lemma newman_kernel_split : forall R z,
  newman_kernel R z = Cadd (Cinv z) (Cmul z (RtoC (/ (R * R)))).
Proof. reflexivity. Qed.

Print Assumptions Cmod_newman_kernel.

(* ================================================================= *)
(*  END CNewmanKernel.v  —  |1/z + z/R²| = 2|Re z|/R² on |z|=R.         *)
(* ================================================================= *)
