(* ================================================================= *)
(*  BerryKeatingRep.v                                                 *)
(*                                                                    *)
(*  A REPRESENTATION of the free *-algebra and the MOMENT SEQUENCE    *)
(*  of the Berry-Keating Hamiltonian H = q p + p q.                   *)
(*                                                                    *)
(*  The left-regular (vacuum / GNS) representation:                   *)
(*     pi(a) = left convolution by a  (Fmul a .),                     *)
(*     cyclic vacuum vector  v = Fone = delta_[]  (the algebra unit), *)
(*     vacuum pairing  <v, x> = x([]) = omega0 x.                     *)
(*  The moment sequence of H is                                       *)
(*     mu_n = <v, pi(H)^n v> = omega0 (H^n) = (H^n)([]).               *)
(*                                                                    *)
(*  RESULT (moment_0, moment_Sn):  mu_0 = 1,  mu_n = 0 (n >= 1).       *)
(*  So the vacuum spectral measure of H is the point mass delta_0     *)
(*  (H acts as 0 in this representation): the moments carry NO         *)
(*  spectral information -- as expected, the natural representation    *)
(*  is spectrally trivial for H.  Getting the Riemann zero ordinates  *)
(*  requires a DIFFERENT (non-vacuum, infinite-dimensional,           *)
(*  boundary-conditioned) representation -- the open Hilbert-Polya    *)
(*  step.  Representation-dependence is real: e.g. sending q,p to      *)
(*  suitable self-adjoint 2x2 matrices gives H a spectrum {+-1}, still *)
(*  not the zeros.                                                    *)
(*                                                                    *)
(*  Axioms: standard classical-Reals + functional_extensionality.     *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra List.
Require Import ComplexField BerryKeating BerryKeatingFree BerryKeatingH.
Import ListNotations.
Open Scope R_scope.

(* the vacuum vector = the algebra unit delta_[] *)
Definition Fone : Elt := fun w => if list_eq_dec gen_eq_dec w [] then C1 else C0.

Lemma Fone_nil : Fone [] = C1.
Proof. unfold Fone; destruct (list_eq_dec gen_eq_dec [] []) as [_|N]; [ reflexivity | exfalso; apply N; reflexivity ]. Qed.

(* convolution read off at the empty word: only the trivial split ([],[]) *)
Lemma Fmul_nil : forall a b, Fmul a b [] = Cmul (a []) (b []).
Proof. intros a b; unfold Fmul, splits; simpl; apply Ceq; simpl; ring. Qed.

Lemma H_nil : H [] = C0.
Proof. unfold H, Fadd, Fmul, splits, q, p; simpl; apply Ceq; simpl; ring. Qed.

(* pi(H)^n v  =  H^n  (n-fold convolution power applied to the vacuum) *)
Fixpoint Hpow (n : nat) : Elt :=
  match n with 0%nat => Fone | S k => Fmul H (Hpow k) end.

(* the moment sequence  mu_n = <v, pi(H)^n v> = omega0 (H^n) *)
Definition moment (n : nat) : C := omega0 (Hpow n).

Lemma moment_0 : moment 0 = C1.
Proof. unfold moment, omega0; simpl; apply Fone_nil. Qed.

Lemma moment_Sn : forall k, moment (S k) = C0.
Proof.
  intro k. unfold moment, omega0; simpl.
  rewrite Fmul_nil, H_nil. apply Ceq; simpl; ring.
Qed.

(* Packaged: the vacuum moment sequence of H is (1,0,0,...) -- the      *)
(* moments of the ZERO operator, i.e. spectral measure delta_0.         *)
Theorem vacuum_moments : forall n,
  moment n = (if Nat.eqb n 0 then C1 else C0).
Proof. intros [|k]; [ apply moment_0 | apply moment_Sn ]. Qed.

(* The moments are real (as they must be: H is self-adjoint). *)
Corollary moments_real : forall n, Im (moment n) = 0.
Proof. intro n; rewrite vacuum_moments; destruct (Nat.eqb n 0); reflexivity. Qed.

Print Assumptions vacuum_moments.
