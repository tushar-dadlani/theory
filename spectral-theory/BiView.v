(* ================================================================= *)
(*  BiView.v                                                          *)
(*                                                                    *)
(*  ONE OBJECT, TWO VIEWS: the local-global (adelic) duality as a     *)
(*  GALOIS CONNECTION -- over Q, axiom-free, NO topology.             *)
(*                                                                    *)
(*  A Galois connection is pure order theory (two posets + monotone   *)
(*  adjoint maps), so the archimedean completeness / p-adic topology   *)
(*  the full adeles need is deliberately avoided (and is unavailable   *)
(*  in the stdlib anyway).                                            *)
(*                                                                    *)
(*  The two views:                                                    *)
(*    - GLOBAL: (Z, <=), the valuation / divisibility coordinate       *)
(*      (a single prime's exponent chain -- p^z ordered by z);         *)
(*    - LOCAL:  (Q, <=), the archimedean coordinate.                   *)
(*  The connection is the canonical  alpha = inject_Z  (global -> local *)
(*  inclusion)  and  gamma = Qfloor  (local -> global round-down),      *)
(*  adjoint:  z <= gamma q  <->  alpha z <= q.                         *)
(*                                                                    *)
(*  Then, at resolution n, the local DENSITY  dens z = z/n in [0,1]    *)
(*  carries the SHARED INVOLUTION: the global complement z |-> n - z    *)
(*  (BitDensity's k |-> n-k) maps under dens to the local reflection    *)
(*  q |-> 1 - q (RiemannHypothesisSpectral's s |-> 1-s), fixed at 1/2. *)
(*  So the reflection about the centre is literally the SAME involution *)
(*  seen in the two views, intertwined by the connection.             *)
(* ================================================================= *)

From Stdlib Require Import ZArith QArith Qround Lqa Lia.
Open Scope Q_scope.

(* ----------------------------------------------------------------- *)
(* SECTION 1 — the Galois connection  inject_Z (global) -| Qfloor     *)
(* ----------------------------------------------------------------- *)

Definition alpha (z : Z) : Q := inject_Z z.   (* global valuation -> local *)
Definition gamma (q : Q) : Z := Qfloor q.     (* local -> global valuation *)

(* THE ADJUNCTION (division-free): z <= gamma q  <->  alpha z <= q. *)
Theorem galois_connection : forall z q, (z <= gamma q)%Z <-> alpha z <= q.
Proof.
  intros z q; unfold alpha, gamma; split; intro H.
  - apply (Qle_trans _ (inject_Z (Qfloor q))).
    + rewrite <- Zle_Qle; exact H.
    + apply Qfloor_le.
  - rewrite <- (Qfloor_Z z); apply Qfloor_resp_le; exact H.
Qed.

(* both maps are monotone (order-preserving) *)
Theorem alpha_monotone : forall z z', (z <= z')%Z -> alpha z <= alpha z'.
Proof. intros z z' H; unfold alpha; rewrite <- Zle_Qle; exact H. Qed.

Theorem gamma_monotone : forall q q', q <= q' -> (gamma q <= gamma q')%Z.
Proof. intros q q' H; unfold gamma; apply Qfloor_resp_le; exact H. Qed.

(* the global coordinate round-trips: gamma (alpha z) = z (a retract) *)
Theorem gamma_alpha : forall z, gamma (alpha z) = z.
Proof. intro z; unfold gamma, alpha; apply Qfloor_Z. Qed.

(* the counit: alpha (gamma q) <= q *)
Theorem alpha_gamma_le : forall q, alpha (gamma q) <= q.
Proof. intro q; unfold alpha, gamma; apply Qfloor_le. Qed.

(* ----------------------------------------------------------------- *)
(* SECTION 2 — the two reflections about the centre                  *)
(* ----------------------------------------------------------------- *)

Definition Lref (q : Q) : Q := 1 - q.                     (* local, fixed at 1/2 *)
Definition Gref (n : nat) (z : Z) : Z := (Z.of_nat n - z)%Z. (* global, fixed at n/2 *)

Theorem Lref_involutive : forall q, Lref (Lref q) == q.
Proof. intro q; unfold Lref; ring. Qed.

Theorem Gref_involutive : forall n z, Gref n (Gref n z) = z.
Proof. intros n z; unfold Gref; lia. Qed.

(* the local reflection is fixed exactly at 1/2 (the critical line) *)
Theorem Lref_fixed : forall q, Lref q == q <-> q == 1 # 2.
Proof. intro q; unfold Lref; split; intro H; lra. Qed.

(* the global reflection is fixed exactly at the half-weight n/2 *)
Theorem Gref_fixed : forall n z, Gref n z = z <-> (2 * z = Z.of_nat n)%Z.
Proof. intros n z; unfold Gref; lia. Qed.

(* inject_Z is a ring morphism: it respects subtraction *)
Lemma inject_Z_sub : forall a b, inject_Z (a - b) == inject_Z a - inject_Z b.
Proof.
  intros a b; replace (a - b)%Z with (a + - b)%Z by ring.
  rewrite inject_Z_plus, inject_Z_opp; ring.
Qed.

(* ----------------------------------------------------------------- *)
(* SECTION 3 — the density interpretation and the shared involution  *)
(* ----------------------------------------------------------------- *)

Section Resolution.

Variable n : nat.
Hypothesis Hn : (0 < n)%nat.

Definition Nq : Q := inject_Z (Z.of_nat n).

Lemma Nq_pos : 0 < Nq.
Proof. unfold Nq, Qlt; simpl; lia. Qed.

Lemma Nq_neq0 : ~ Nq == 0.
Proof. pose proof Nq_pos as H; intro Hc; rewrite Hc in H; apply (Qlt_irrefl 0); exact H. Qed.

(* the local density of a global valuation z : the point z/n in [0,1] *)
Definition dens (z : Z) : Q := inject_Z z / Nq.

(* THE SHARED INVOLUTION: the global complement maps under the density *)
(* to the local reflection -- the same reflection in the two views.    *)
Theorem shared_reflection : forall z, dens (Gref n z) == Lref (dens z).
Proof.
  intro z; unfold dens, Gref, Lref, Nq.
  rewrite inject_Z_sub; field; exact Nq_neq0.
Qed.

End Resolution.

(* ----------------------------------------------------------------- *)
(* SECTION 4 — a concrete instance (n = 2)                           *)
(* ----------------------------------------------------------------- *)

Example dens2_one_half : dens 2 1 == 1 # 2.
Proof. unfold dens, Nq; reflexivity. Qed.

Example gamma_half : gamma (1 # 2) = 0%Z.
Proof. reflexivity. Qed.

Example shared2 : dens 2 (Gref 2 0) == Lref (dens 2 0).
Proof. apply shared_reflection; lia. Qed.

(* ----------------------------------------------------------------- *)
(* MASTER THEOREM                                                     *)
(* ----------------------------------------------------------------- *)

Theorem biview_galois :
  (* the Galois connection (adjunction) + monotonicity + retract *)
  (forall z q, (z <= gamma q)%Z <-> alpha z <= q)
  /\ (forall z z', (z <= z')%Z -> alpha z <= alpha z')
  /\ (forall q q', q <= q' -> (gamma q <= gamma q')%Z)
  /\ (forall z, gamma (alpha z) = z)
  (* the shared reflection: global complement = local 1-s under density *)
  /\ (forall n, (0 < n)%nat -> forall z, dens n (Gref n z) == Lref (dens n z))
  /\ (forall q, Lref (Lref q) == q)
  /\ (forall n z, Gref n (Gref n z) = z).
Proof.
  split; [ exact galois_connection | ].
  split; [ exact alpha_monotone | ].
  split; [ exact gamma_monotone | ].
  split; [ exact gamma_alpha | ].
  split; [ exact shared_reflection | ].
  split; [ exact Lref_involutive | exact Gref_involutive ].
Qed.

Print Assumptions biview_galois.

(* ================================================================= *)
(*  END BiView.v                                                      *)
(*  The local-global duality as a Galois connection over Q, with the   *)
(*  reflection about the centre shared across the two views.           *)
(*  ZERO Admitted; no Reals axioms, no topology.                      *)
(* ================================================================= *)
