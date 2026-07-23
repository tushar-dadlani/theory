(* ================================================================= *)
(*  DirichletKernel.v                                                *)
(*                                                                    *)
(*  THE DIRICHLET KERNEL, on the Cexp / Euler foundation.            *)
(*                                                                    *)
(*  The kernel of Fourier-series convergence,                        *)
(*                                                                    *)
(*     D_n(t) = sum_{k=-n}^{n} e^{i k t} = sin((n+1/2) t) / sin(t/2). *)
(*                                                                    *)
(*  We give it two faces:                                            *)
(*    * REAL closed form (the classical identity, division-free):     *)
(*        Dsum n t = 1 + 2 sum_{k=1}^{n} cos(k t),  and              *)
(*        Dsum n t * sin(t/2) = sin((n+1/2) t)                        *)
(*      by telescoping the product-to-sum identity                    *)
(*        2 cos A sin B = sin(A+B) - sin(A-B).                        *)
(*    * COMPLEX skeleton (leveraging EulerFormula.Cexp):              *)
(*        DK n t = sum_{k=-n}^{n} Cexp(k t),  with the geometric       *)
(*        closed form  (Cexp t - 1) * DK n t                          *)
(*                       = Cexp(-n t) * (Cexp(t)^(2n+1) - 1),         *)
(*      which is RootsOfUnity.geom_sum read through Euler.            *)
(*                                                                    *)
(*  Uses the classical Reals axioms (quarantined, via cos/sin).       *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia Arith.
Require Import ComplexField RootsOfUnity DFTInversion EulerFormula.
Open Scope R_scope.

(* ================================================================= *)
(*  1.  THE REAL DIRICHLET KERNEL and its closed form                *)
(* ================================================================= *)

Fixpoint Rsum (f : nat -> R) (n : nat) : R :=
  match n with O => 0 | S k => Rsum f k + f (S k) end.

Definition Dsum (n : nat) (t : R) : R := 1 + 2 * Rsum (fun k => cos (INR k * t)) n.

Lemma Dsum_S : forall n t, Dsum (S n) t = Dsum n t + 2 * cos (INR (S n) * t).
Proof. intros n t; unfold Dsum; cbn [Rsum]; ring. Qed.

(* product-to-sum: 2 cos A sin B = sin(A+B) - sin(A-B) *)
Lemma prod_to_sum : forall A B, 2 * cos A * sin B = sin (A + B) - sin (A - B).
Proof. intros A B; rewrite sin_plus, sin_minus; ring. Qed.

(* THE closed form (division-free): Dsum n t * sin(t/2) = sin((n+1/2) t) *)
Theorem dirichlet_kernel : forall n t, Dsum n t * sin (t / 2) = sin ((INR n + / 2) * t).
Proof.
  intros n; induction n as [|n IH]; intro t.
  - unfold Dsum; simpl (Rsum _ 0).
    replace ((INR 0 + / 2) * t) with (t / 2) by (simpl INR; field).
    lra.
  - rewrite Dsum_S, Rmult_plus_distr_r, IH.
    replace (2 * cos (INR (S n) * t) * sin (t / 2))
      with (sin (INR (S n) * t + t / 2) - sin (INR (S n) * t - t / 2))
      by (rewrite <- prod_to_sum; ring).
    replace (INR (S n) * t - t / 2) with ((INR n + / 2) * t) by (rewrite S_INR; field).
    replace (INR (S n) * t + t / 2) with ((INR (S n) + / 2) * t) by (rewrite S_INR; field).
    lra.
Qed.

(* the usual divided form, where sin(t/2) <> 0 *)
Corollary dirichlet_kernel_div : forall n t, sin (t / 2) <> 0 ->
  Dsum n t = sin ((INR n + / 2) * t) / sin (t / 2).
Proof.
  intros n t H; rewrite <- dirichlet_kernel; field; exact H.
Qed.

(* ================================================================= *)
(*  2.  THE COMPLEX KERNEL  D_n(t) = sum_{k=-n}^{n} Cexp(k t)         *)
(* ================================================================= *)

(* symmetric sum, indexed j = k + n in [0, 2n]: exponent (j - n) t *)
Definition DK (n : nat) (t : R) : C :=
  Csum (fun j => Cexp ((INR j - INR n) * t)) (2 * n + 1).

Lemma DK_shift : forall n t,
  DK n t = Cmul (Cexp (- INR n * t)) (Csum (fun j => Cpow (Cexp t) j) (2 * n + 1)).
Proof.
  intros n t; unfold DK.
  rewrite (Csum_ext (fun j => Cexp ((INR j - INR n) * t))
                    (fun j => Cmul (Cexp (- INR n * t)) (Cpow (Cexp t) j)) (2 * n + 1)).
  - symmetry; apply Csum_scale_l.
  - intro j; rewrite (Cpow_Cexp t j), <- Cexp_add; f_equal; ring.
Qed.

(* geometric closed form: (Cexp t - 1) * D_n = Cexp(-n t) * (Cexp(t)^(2n+1) - 1) *)
Theorem dk_geom : forall n t,
  Cmul (Cminus (Cexp t) C1) (DK n t)
  = Cmul (Cexp (- INR n * t)) (Cminus (Cpow (Cexp t) (2 * n + 1)) C1).
Proof.
  intros n t; rewrite DK_shift, <- (geom_sum (Cexp t) (2 * n + 1)); ring.
Qed.

(* ----------------------------------------------------------------- *)
(*  MASTER                                                           *)
(* ----------------------------------------------------------------- *)

Theorem dirichlet_kernel_thm :
  (* real closed form *)
     (forall n t, Dsum n t * sin (t / 2) = sin ((INR n + / 2) * t))
  /\ (forall n t, sin (t / 2) <> 0 -> Dsum n t = sin ((INR n + / 2) * t) / sin (t / 2))
  (* complex geometric skeleton (Cexp / Euler) *)
  /\ (forall n t, Cmul (Cminus (Cexp t) C1) (DK n t)
                  = Cmul (Cexp (- INR n * t)) (Cminus (Cpow (Cexp t) (2 * n + 1)) C1)).
Proof.
  split; [ exact dirichlet_kernel | ].
  split; [ exact dirichlet_kernel_div | exact dk_geom ].
Qed.

Print Assumptions dirichlet_kernel_thm.

(* ================================================================= *)
(*  END DirichletKernel.v                                            *)
(*  The Dirichlet kernel D_n(t) = sum_{k=-n}^n e^{ikt}: the real       *)
(*  closed form Dsum n t * sin(t/2) = sin((n+1/2)t) (telescoping       *)
(*  product-to-sum), and the complex geometric skeleton over          *)
(*  EulerFormula.Cexp (RootsOfUnity.geom_sum).  Classical Reals        *)
(*  axioms (quarantined, via cos/sin).                                *)
(* ================================================================= *)
