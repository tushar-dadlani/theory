(* ================================================================= *)
(*  ObserverTriad.v                                                  *)
(*                                                                    *)
(*  A HERMITIAN (self-adjoint) OPERATOR ON THE 3-WAY SPLIT            *)
(*     Role = { Observer, Observed, Observation }.                    *)
(*                                                                    *)
(*  Over R "Hermitian" is self-adjointness w.r.t. the real inner       *)
(*  product (= a symmetric matrix); there is no C here, so we state     *)
(*  the honest real form, exactly as WalshHadamardHilbert does.        *)
(*                                                                    *)
(*  The operator M encodes MEASUREMENT: the observation is coupled to   *)
(*  both the observer and the observed (a measurement links them        *)
(*  THROUGH the observation), with observer and observed not coupled    *)
(*  directly.  As a matrix on (Observer, Observed, Observation):        *)
(*        [ 0 0 1 ]                                                    *)
(*        [ 0 0 1 ]   -- symmetric, hence self-adjoint.                *)
(*        [ 1 1 0 ]                                                    *)
(*                                                                    *)
(*  Its real spectrum is { 0, +sqrt 2, -sqrt 2 } with orthogonal       *)
(*  eigenvectors:                                                     *)
(*    - eigenvalue 0  : v0 = Observer - Observed  (the difference the   *)
(*        measurement CANNOT resolve -- the unobservable/kernel mode);  *)
(*    - eigenvalue +/- sqrt 2 : v+/- = Observer + Observed +/- sqrt2 .  *)
(*        Observation  (the two observable measurement modes).          *)
(*                                                                    *)
(*  This is the Hermitian spectral theorem's payoff on the triad: real  *)
(*  eigenvalues, orthogonal eigenbasis, and a kernel that is exactly     *)
(*  the observer-minus-observed gauge.  Uses the classical Reals         *)
(*  axioms (quarantined).                                             *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra.
Open Scope R_scope.

Inductive Role : Type := Observer | Observed | Observation.

Definition State := Role -> R.

(* real inner product on the triad *)
Definition inner (f g : State) : R :=
  f Observer * g Observer + f Observed * g Observed + f Observation * g Observation.

Lemma inner_sym : forall f g, inner f g = inner g f.
Proof. intros f g; unfold inner; ring. Qed.

(* scalar multiple, for stating eigen-equations *)
Definition smul (a : R) (f : State) : State := fun r => a * f r.

(* the measurement operator: observation couples observer and observed *)
Definition M (f : State) : State :=
  fun r => match r with
           | Observer    => f Observation
           | Observed    => f Observation
           | Observation => f Observer + f Observed
           end.

(* ----------------------------------------------------------------- *)
(*  HERMITIAN: M is self-adjoint w.r.t. the real inner product        *)
(* ----------------------------------------------------------------- *)

Theorem M_self_adjoint : forall f g, inner (M f) g = inner f (M g).
Proof. intros f g; unfold inner, M; ring. Qed.

(* ----------------------------------------------------------------- *)
(*  THE REAL SPECTRUM { 0, +sqrt 2, -sqrt 2 } AND ITS EIGENVECTORS    *)
(* ----------------------------------------------------------------- *)

Definition v0 : State :=
  fun r => match r with Observer => 1 | Observed => -1 | Observation => 0 end.
Definition vp : State :=
  fun r => match r with Observer => 1 | Observed => 1 | Observation => sqrt 2 end.
Definition vm : State :=
  fun r => match r with Observer => 1 | Observed => 1 | Observation => - sqrt 2 end.

(* the observer-minus-observed difference is in the kernel: the        *)
(* measurement cannot see it (eigenvalue 0) *)
Theorem eig_0 : forall r, M v0 r = smul 0 v0 r.
Proof. intro r; destruct r; unfold M, v0, smul; ring. Qed.

Theorem eig_p : forall r, M vp r = smul (sqrt 2) vp r.
Proof.
  intro r; destruct r; unfold M, vp, smul;
    try (rewrite sqrt_sqrt by lra); ring.
Qed.

Theorem eig_m : forall r, M vm r = smul (- sqrt 2) vm r.
Proof.
  intro r; destruct r; unfold M, vm, smul;
    [ ring | ring | ].
  replace (- sqrt 2 * - sqrt 2) with (sqrt 2 * sqrt 2) by ring;
    rewrite sqrt_sqrt by lra; ring.
Qed.

(* ----------------------------------------------------------------- *)
(*  ORTHOGONAL EIGENBASIS                                            *)
(* ----------------------------------------------------------------- *)

Theorem ortho_0p : inner v0 vp = 0.
Proof. unfold inner, v0, vp; ring. Qed.

Theorem ortho_0m : inner v0 vm = 0.
Proof. unfold inner, v0, vm; ring. Qed.

Theorem ortho_pm : inner vp vm = 0.
Proof.
  unfold inner, vp, vm.
  replace (sqrt 2 * - sqrt 2) with (- (sqrt 2 * sqrt 2)) by ring;
    rewrite sqrt_sqrt by lra; lra.
Qed.

(* ----------------------------------------------------------------- *)
(*  MASTER THEOREM                                                   *)
(* ----------------------------------------------------------------- *)

Theorem observer_triad_hermitian :
  (* self-adjoint (Hermitian over R) *)
  (forall f g, inner (M f) g = inner f (M g))
  (* real spectrum {0, +sqrt2, -sqrt2} with these eigenvectors *)
  /\ (forall r, M v0 r = smul 0 v0 r)
  /\ (forall r, M vp r = smul (sqrt 2) vp r)
  /\ (forall r, M vm r = smul (- sqrt 2) vm r)
  (* pairwise orthogonal eigenbasis *)
  /\ inner v0 vp = 0 /\ inner v0 vm = 0 /\ inner vp vm = 0.
Proof.
  split; [ exact M_self_adjoint | ].
  split; [ exact eig_0 | ].
  split; [ exact eig_p | ].
  split; [ exact eig_m | ].
  split; [ exact ortho_0p | ].
  split; [ exact ortho_0m | exact ortho_pm ].
Qed.

Print Assumptions observer_triad_hermitian.

(* ================================================================= *)
(*  END ObserverTriad.v                                              *)
(*  A self-adjoint (Hermitian-over-R) measurement operator on the      *)
(*  observer/observed/observation triad: real spectrum {0,+-sqrt2},     *)
(*  orthogonal eigenbasis, with the eigenvalue-0 mode = the observer-    *)
(*  minus-observed difference the measurement cannot resolve.  Uses     *)
(*  the classical Reals axioms (quarantined).                          *)
(* ================================================================= *)
