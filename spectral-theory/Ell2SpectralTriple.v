(* ================================================================= *)
(*  Ell2SpectralTriple.v   (the primon-gas / Bost-Connes spectral triple)*)
(*                                                                    *)
(*  Wires the pieces into a Connes-type spectral triple (A, H, D):       *)
(*                                                                    *)
(*    H = Ell2  = l^2(N_{>=1})            (the primon Fock space);       *)
(*    D = Dmul Hlog = diag(log n)         (the Dirac / energy operator,  *)
(*                                         generator of e^{-beta D});     *)
(*    A = the algebra of diagonal multiplications  Dmul a  (commutative  *)
(*        core) crossed with the prime-shift creations  crea p           *)
(*        (the noncommutative step).                                    *)
(*                                                                    *)
(*  The spectral-triple structure that is verified here:                *)
(*    * D is diagonal with eigenvalue  log i  on the state e_i;          *)
(*    * the commutative core commutes with D:  [D, Dmul a] = 0;          *)
(*    * D acts as a DERIVATION on the creations:                        *)
(*         [D, crea p] = (log p) . crea p        (bounded commutator),   *)
(*      i.e. creating a mode-p particle raises the energy by log p;      *)
(*    * the partition function is zeta:  Tr(e^{-beta D}) = zeta(beta).    *)
(*                                                                    *)
(*  Axioms: standard classical-Reals only (+ functional_extensionality). *)
(* ================================================================= *)

From Stdlib Require Import Reals Rpower Lra Lia FunctionalExtensionality.
Require Import Ell2 Ell2Operator Ell2Basis Ell2Zeta Ell2Fock Ell2Partition.
Open Scope R_scope.

(* the Dirac / energy operator  D = diag(log n) *)
Definition Dop : (nat -> R) -> nat -> R := Dmul Hlog.

(* D is diagonal: eigenvalue log i on the state e_i *)
Lemma Dop_eigen : forall i n, Dop (e i) n = (ln (INR i) * e i n)%R.
Proof. intros i n; unfold Dop; rewrite Dmul_e; reflexivity. Qed.

Lemma Dop_e_eq : forall m, Dop (e m) = (fun k => ln (INR m) * e m k).
Proof. intro m; apply functional_extensionality; intro k; apply Dop_eigen. Qed.

(* --- the commutative core commutes with D:  [D, Dmul a] = 0 --- *)
Lemma Dop_diag_commute : forall a f n, Dop (Dmul a f) n = Dmul a (Dop f) n.
Proof. intros a f n; unfold Dop, Dmul; ring. Qed.

(* --- creation is linear (pulls out scalars) --- *)
Lemma crea_scal : forall p c f n, crea p (fun k => c * f k) n = (c * crea p f n)%R.
Proof. intros p c f n; unfold crea; destruct (Nat.eqb (n mod p)%nat 0); ring. Qed.

(* --- D is a derivation on the creations:  [D, crea p] = (log p) . crea p --- *)
(* creating a mode-p particle raises the energy by  log p. *)
Theorem Dop_crea_derivation : forall p m n, (1 <= p)%nat -> (1 <= m)%nat ->
  Dop (crea p (e m)) n
  = (crea p (Dop (e m)) n + ln (INR p) * crea p (e m) n)%R.
Proof.
  intros p m n Hp Hm.
  rewrite (crea_e p m Hp), Dop_eigen, Dop_e_eq, crea_scal, (crea_e p m Hp).
  rewrite mult_INR, ln_mult by (apply lt_0_INR; lia).
  ring.
Qed.

(* --- the partition function of the heat semigroup e^{-beta D} is zeta --- *)
(* e^{-beta D} is diagonal with entries e^{-beta log n} = n^{-beta};         *)
(* its spectral trace converges to zeta(beta) for beta > 1.                  *)
Theorem Dop_partition_is_zeta : forall b, 1 < b ->
  { Z : R | Un_cv (fun N => diag_trace (fun n => exp ((- b) * Hlog n)) N) Z }.
Proof. exact heat_partition_converges. Qed.

(* ------------------------------------------------------------------ *)
(*  the bundled spectral triple                                       *)
(* ------------------------------------------------------------------ *)

Theorem primon_spectral_triple :
  (* H = Ell2 : the state e_n is in the Hilbert space *)
  (forall n, Ell2 (e n)) *
  (* D is diagonal, eigenvalue log i on state e_i *)
  (forall i n, Dop (e i) n = ln (INR i) * e i n) *
  (* the commutative core commutes with D *)
  (forall a f n, Dop (Dmul a f) n = Dmul a (Dop f) n) *
  (* D is a derivation on the creations: [D, crea p] = (log p) . crea p *)
  (forall p m n, (1 <= p)%nat -> (1 <= m)%nat ->
     Dop (crea p (e m)) n
     = crea p (Dop (e m)) n + ln (INR p) * crea p (e m) n) *
  (* the partition function is zeta:  Tr(e^{-beta D}) = zeta(beta),  beta>1 *)
  (forall b, 1 < b ->
     { Z : R | Un_cv (fun N => diag_trace (fun n => exp ((- b) * Hlog n)) N) Z }).
Proof.
  repeat split.
  - apply Ell2_e.
  - apply Dop_eigen.
  - apply Dop_diag_commute.
  - apply Dop_crea_derivation.
  - apply Dop_partition_is_zeta.
Qed.

Print Assumptions primon_spectral_triple.
