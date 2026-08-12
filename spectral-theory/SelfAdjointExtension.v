(* ================================================================= *)
(*  SelfAdjointExtension.v                                            *)
(*                                                                    *)
(*  The BOUNDARY-TRIPLE / self-adjoint-extension mechanism at         *)
(*  deficiency index (1,1), attacking the inserted-`zord` gap of      *)
(*  BerryKeatingDilation.v.                                           *)
(*                                                                    *)
(*  A symmetric (Hermitian) operator that is not yet self-adjoint has *)
(*  deficiency subspaces  N_pm = ker(T* -/+ i).  When both are one-   *)
(*  dimensional (index (1,1)) its self-adjoint extensions are         *)
(*  parametrised by a single unit phase  u in U(1); the extension     *)
(*  T_u has REAL spectrum, and each eigenvalue lambda is the Cayley    *)
(*  preimage of u:   c(lambda) = u,   c(z) = (z - i)/(z + i).          *)
(*                                                                    *)
(*  Cayley  c : R -> U(1)  (cayley_maps_unit) sends the real spectral *)
(*  axis onto the unit circle; its inverse                            *)
(*     icayley u = i (1 + u)/(1 - u)                                   *)
(*  is REAL for every unit phase u <> 1 (icayley_real).  So a self-    *)
(*  adjoint extension (a unit phase) PRODUCES a real spectral point    *)
(*  (extension_spectrum_real) -- reality is DERIVED from the phase,    *)
(*  not inserted as a hypothesis on `zord`.                            *)
(*                                                                    *)
(*  Tie-in: a phase sequence u : nat -> U(1) yields extension-derived  *)
(*  ordinates  zord_of_phase u n = ext_point (u n),  each provably     *)
(*  real, feeding the diagonal realisation Dmul of BerryKeatingDilation *)
(*  WITHOUT assuming reality (zord_of_phase_real).                     *)
(*                                                                    *)
(*  STILL OPEN (the Hilbert-Polya gap, unchanged): that the geometric  *)
(*  boundary phase realising XiC's zeros is the correct u.  What is     *)
(*  removed here is the circular INSERTION of real ordinates: the       *)
(*  extension mechanism now supplies their reality.                    *)
(*                                                                    *)
(*  Axioms: standard classical-Reals only.                            *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra.
Require Import ComplexField BerryKeatingDilation Ell2 Ell2Basis Ell2Operator
        RiemannXiEntire CoherenceSingularity.
Open Scope R_scope.

(* the imaginary unit *)
Definition Ci : C := mkC 0 1.

Lemma Ci_norm2 : Cnorm2 Ci = 1.
Proof. unfold Cnorm2, Ci; simpl; ring. Qed.

(* Cnorm2 is multiplicative and inverts under Cinv -- clean algebra.    *)
Lemma Cnorm2_mul : forall a b, Cnorm2 (Cmul a b) = Cnorm2 a * Cnorm2 b.
Proof. intros a b; unfold Cnorm2, Cmul; simpl; ring. Qed.

Lemma Cnorm2_inv : forall b, b <> C0 -> Cnorm2 (Cinv b) = / Cnorm2 b.
Proof.
  intros b Hb. pose proof (Cnorm2_neq_0 b Hb) as HN.
  unfold Cinv, Cnorm2; cbn [Re Im]. field; exact HN.
Qed.

(* ----------------------------------------------------------------- *)
(*  A.  The Cayley transform  c(z) = (z - i)/(z + i)                  *)
(* ----------------------------------------------------------------- *)

Definition cayley (z : C) : C := Cdiv (Cminus z Ci) (Cadd z Ci).

(* the unit circle U(1) = deficiency phases *)
Definition U1 (u : C) : Prop := Cnorm2 u = 1.

(* Cayley maps the REAL spectral axis onto the unit circle:            *)
(* a real eigenvalue has a unit-modulus extension phase.               *)
Lemma cayley_maps_unit : forall x : R, U1 (cayley (RtoC x)).
Proof.
  intro x. unfold U1, cayley, Cdiv.
  assert (Hden : Cadd (RtoC x) Ci <> C0).
  { intro Hz. apply (f_equal Im) in Hz.
    unfold Cadd, RtoC, Ci, C0 in Hz; simpl in Hz; lra. }
  rewrite Cnorm2_mul, Cnorm2_inv by exact Hden.
  assert (Heq : Cnorm2 (Cminus (RtoC x) Ci) = Cnorm2 (Cadd (RtoC x) Ci)).
  { unfold Cnorm2, Cminus, Cadd, RtoC, Ci; simpl; ring. }
  rewrite Heq. apply Rinv_r.
  pose proof (Cnorm2_neq_0 (Cadd (RtoC x) Ci) Hden) as H. unfold Cnorm2; exact H.
Qed.

(* ----------------------------------------------------------------- *)
(*  B.  Inverse Cayley  icayley u = i (1 + u)/(1 - u):  REAL on U(1)  *)
(* ----------------------------------------------------------------- *)

Definition icayley (u : C) : C := Cdiv (Cmul Ci (Cadd C1 u)) (Cminus C1 u).

(* on the unit circle the denominator (1 - u) vanishes only at u = 1. *)
Lemma one_minus_u_norm : forall u, U1 u -> u <> C1 ->
  (1 - Re u) * (1 - Re u) + (0 - Im u) * (0 - Im u) <> 0.
Proof.
  intros u HU Hne Hz. apply Hne.
  unfold U1, Cnorm2 in HU. apply Ceq; simpl; nra.
Qed.

(* KEY: a self-adjoint extension phase u yields a REAL spectral point. *)
(* Im (icayley u) = 0 whenever |u| = 1 and u <> 1.                      *)
Lemma icayley_real : forall u, U1 u -> u <> C1 -> Im (icayley u) = 0.
Proof.
  intros u HU Hne. unfold U1, Cnorm2 in HU.
  (* Im(icayley u) is a rational function whose numerator is 1 - |u|^2. *)
  assert (Heq : Im (icayley u) =
    (1 - (Re u * Re u + Im u * Im u)) /
    ((1 - Re u) * (1 - Re u) + (0 - Im u) * (0 - Im u))).
  { unfold icayley, Cdiv, Cmul, Cadd, Cminus, Cinv, Cnorm2, Ci, C1; cbn [Re Im].
    field; (intro Hz; apply Hne; apply Ceq; unfold C1; cbn [Re Im]; nra). }
  rewrite Heq, HU. unfold Rdiv; ring.
Qed.

(* the real spectral point of the extension u (the Cayley preimage).   *)
Definition ext_point (u : C) : R := Re (icayley u).

(* on U(1) the inverse-Cayley value IS that real point.                *)
Lemma icayley_is_real_point : forall u, U1 u -> u <> C1 ->
  icayley u = RtoC (ext_point u).
Proof.
  intros u HU Hne. unfold ext_point, RtoC.
  apply Ceq; simpl; [ reflexivity | apply icayley_real; assumption ].
Qed.

(* HEADLINE: every self-adjoint extension (unit phase u <> 1) has a     *)
(* REAL spectral point -- reality DERIVED, not inserted.               *)
Theorem extension_spectrum_real : forall u, U1 u -> u <> C1 ->
  exists r : R, icayley u = RtoC r.
Proof.
  intros u HU Hne. exists (ext_point u). apply icayley_is_real_point; assumption.
Qed.

(* ----------------------------------------------------------------- *)
(*  C.  Extension-derived ordinates for the diagonal realisation      *)
(* ----------------------------------------------------------------- *)

(* A phase sequence supplies real ordinates WITHOUT assuming reality:  *)
(* each ordinate is the Cayley preimage of a self-adjoint extension.   *)
Definition zord_of_phase (u : nat -> C) (n : nat) : R := ext_point (u n).

(* those ordinates are the diagonal eigenvalues of Hdil, and their      *)
(* reality is DERIVED from the unit-phase extension (icayley_real),      *)
(* replacing BerryKeatingDilation's inserted real `zord`.               *)
Corollary Hdil_phase_eigen : forall (u : nat -> C) n m,
  Hdil (zord_of_phase u) (e n) m = zord_of_phase u n * e n m.
Proof. intros u n m; apply Hdil_eigen. Qed.

Corollary zord_of_phase_derived_real :
  forall (u : nat -> C),
    (forall n, U1 (u n)) -> (forall n, u n <> C1) ->
    forall n, icayley (u n) = RtoC (zord_of_phase u n).
Proof. intros u HU Hne n; apply icayley_is_real_point; auto. Qed.

(* ----------------------------------------------------------------- *)
(*  D.  The Hilbert-Polya target, reality no longer assumed           *)
(* ----------------------------------------------------------------- *)

(* Upgraded target: there is a self-adjoint-extension PHASE sequence     *)
(* (unit phases, <> 1) whose Cayley-preimage ordinates are exactly the   *)
(* on-seam zeros -- reality of the ordinates is now a THEOREM            *)
(* (icayley_real), so the open step is purely that the phase is the       *)
(* geometric one, not that the ordinates happen to be real.              *)
Definition hp_target_via_extension : Prop :=
  exists u : nat -> C,
    (forall n, U1 (u n)) /\ (forall n, u n <> C1) /\
    (forall n, spec Bxi (zord_of_phase u n)) /\
    (forall z, XiC z = C0 -> Re z = / 2 ->
       exists n, z = crit (zord_of_phase u n)).

Print Assumptions cayley_maps_unit.
Print Assumptions icayley_real.
Print Assumptions extension_spectrum_real.
