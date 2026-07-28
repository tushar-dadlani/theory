(* ================================================================= *)
(*  ZetaClosureBridge.v  —  ZETA = THE LINEARIZED GALOIS CLOSURE.     *)
(*                                                                    *)
(*  Makes precise the slogan: Möbius/zeta is the ring-linearized,     *)
(*  invertible version of a Galois connection — on the single-prime   *)
(*  divisibility chain [0..n] (exponents under ≤).                    *)
(*                                                                    *)
(*  Both operators AGGREGATE OVER THE DOWN-SET {d ≤ n}; they differ   *)
(*  only in the monoid used to aggregate:                            *)
(*                                                                    *)
(*    • order / Boolean layer:  join ⋁  (idempotent)                 *)
(*        dclose P n  =  existsb P (seq 0 (S n))  =  ∃ d ≤ n, P d     *)
(*      — a genuine CLOSURE OPERATOR (extensive/monotone/idempotent,  *)
(*      proved below), i.e. exactly what PosetTopology.poset_topology *)
(*      derives from a GALOIS CONNECTION (cl = γ∘α).  NOT invertible. *)
(*                                                                    *)
(*    • additive / ring layer:  sum +  (a group)                     *)
(*        zeta_t (ind P) n  =  qsum (map (ind P) (seq 0 (S n)))       *)
(*        (PosetMobiusFTC.zeta_t on the indicator ind P = 0/1) —      *)
(*      INVERTIBLE, its inverse being the Möbius/backward-difference  *)
(*      mobius_t (ftc_1 / ftc_2).                                     *)
(*                                                                    *)
(*  THE BRIDGE (zeta_pos_iff_dclose): reading + as ⋁ — i.e. testing   *)
(*  the sum for being nonzero — turns zeta back into the closure:     *)
(*                                                                    *)
(*        0 < zeta_t (ind P) n     ⟺     dclose P n = true.           *)
(*                                                                    *)
(*  And the closure is genuinely lossy (dclose_lossy: distinct P, Q   *)
(*  with equal closure), whereas zeta_t is a bijection — which is why *)
(*  MÖBIUS INVERSION needs the group (+), not the idempotent lattice  *)
(*  (⋁): subtraction (inclusion–exclusion) is the inverse the Boolean *)
(*  closure can never have.  AXIOM-FREE.                             *)
(* ================================================================= *)

Require Import PrimonGas PosetMobiusFTC.
From Stdlib Require Import QArith Lqa ZArith List Bool Arith Lia.
Import ListNotations.
Open Scope Q_scope.

(* the indicator of a predicate, as a 0/1-valued rational function *)
Definition ind (P : nat -> bool) (d : nat) : Q := if P d then 1 else 0.

(* the Boolean down-closure: ⋁_{d ≤ n} P d, over the SAME list zeta sums *)
Definition dclose (P : nat -> bool) (n : nat) : bool := existsb P (seq 0 (S n)).

(* ----------------------------------------------------------------- *)
(*  indicator facts                                                  *)
(* ----------------------------------------------------------------- *)
Lemma ind_nonneg : forall P d, 0 <= ind P d.
Proof. intros P d; unfold ind; destruct (P d); lra. Qed.

Lemma ind_pos_iff : forall P d, 0 < ind P d <-> P d = true.
Proof.
  intros P d; unfold ind; destruct (P d).
  - split; intro H; [ reflexivity | lra ].
  - split; intro H; [ exfalso; lra | discriminate H ].
Qed.

(* ----------------------------------------------------------------- *)
(*  the "+ read as ⋁" lemma, over an arbitrary index list            *)
(* ----------------------------------------------------------------- *)
Lemma qsum_ind_nonneg : forall P L, 0 <= qsum (map (ind P) L).
Proof.
  intros P L; induction L as [|a L IH]; simpl.
  - lra.
  - pose proof (ind_nonneg P a); lra.
Qed.

Lemma qsum_ind_pos : forall P L, 0 < qsum (map (ind P) L) <-> existsb P L = true.
Proof.
  intros P L; induction L as [|a L IH]; simpl.
  - split; intro H; [ exfalso; lra | discriminate H ].
  - pose proof (ind_nonneg P a) as na; pose proof (qsum_ind_nonneg P L) as nn.
    rewrite orb_true_iff, <- IH, <- (ind_pos_iff P a); split.
    + intro H; destruct (Qlt_le_dec 0 (ind P a)) as [Ha | Ha];
        [ left; exact Ha | right; lra ].
    + intro H; destruct H as [Ha | Hb]; lra.
Qed.

(* ================================================================= *)
(*  THE BRIDGE: zeta (as a nonzero-test) IS the down-closure.        *)
(* ================================================================= *)
Theorem zeta_pos_iff_dclose : forall P n,
  0 < zeta_t (ind P) n <-> dclose P n = true.
Proof.
  intros P n; unfold zeta_t, dclose; exact (qsum_ind_pos P (seq 0 (S n))).
Qed.

(* ----------------------------------------------------------------- *)
(*  dclose IS a closure operator — the three laws that                *)
(*  PosetTopology.poset_topology proves come from a Galois connection *)
(*  (cl_extensive / cl_monotone / cl_idempotent).                     *)
(* ----------------------------------------------------------------- *)
Lemma dclose_extensive : forall P n, P n = true -> dclose P n = true.
Proof.
  intros P n H; unfold dclose; apply existsb_exists.
  exists n; split; [ apply in_seq; lia | exact H ].
Qed.

Lemma dclose_monotone : forall P Q n,
  (forall k, P k = true -> Q k = true) -> dclose P n = true -> dclose Q n = true.
Proof.
  intros P Q n Hpq H; unfold dclose in *.
  apply existsb_exists in H; destruct H as [x [Hin Hx]].
  apply existsb_exists; exists x; split; [ exact Hin | apply Hpq; exact Hx ].
Qed.

Lemma dclose_idempotent : forall P n, dclose (dclose P) n = dclose P n.
Proof.
  intros P n; apply eq_true_iff_eq; split; intro H.
  - apply existsb_exists in H; destruct H as [x [Hin Hx]].
    apply existsb_exists in Hx; destruct Hx as [y [Hiny Hy]].
    apply in_seq in Hin; apply in_seq in Hiny.
    apply existsb_exists; exists y; split; [ apply in_seq; lia | exact Hy ].
  - apply dclose_extensive; exact H.
Qed.

(* ----------------------------------------------------------------- *)
(*  The closure is LOSSY (non-injective) — so it has no inverse,      *)
(*  unlike zeta_t (invertible: PosetMobiusFTC.ftc_1 / ftc_2).  This   *)
(*  is exactly why Möbius inversion needs the group (+), not ⋁.       *)
(* ----------------------------------------------------------------- *)

(* if the least true position is 1, the down-closure is just (1 ≤ ·),  *)
(* regardless of the predicate's values above 1 — the lost information. *)
Lemma dclose_first_at_1 : forall (P : nat -> bool),
  P 0%nat = false -> P 1%nat = true -> forall n, dclose P n = (1 <=? n)%nat.
Proof.
  intros P H0 H1 n; apply eq_true_iff_eq; split; intro H.
  - apply Nat.leb_le; unfold dclose in H.
    apply existsb_exists in H; destruct H as [x [Hin Hx]]; apply in_seq in Hin.
    destruct x as [|x']; [ rewrite H0 in Hx; discriminate | lia ].
  - apply Nat.leb_le in H; unfold dclose; apply existsb_exists.
    exists 1%nat; split; [ apply in_seq; lia | exact H1 ].
Qed.

Definition P1 : nat -> bool := fun n => Nat.eqb n 1.
Definition Q1 : nat -> bool := fun n => (Nat.eqb n 1) || (Nat.eqb n 3).

Lemma dclose_lossy :
  P1 3%nat <> Q1 3%nat /\ (forall n, dclose P1 n = dclose Q1 n).
Proof.
  split.
  - unfold P1, Q1; cbn; discriminate.
  - intro n; rewrite (dclose_first_at_1 P1 eq_refl eq_refl),
                     (dclose_first_at_1 Q1 eq_refl eq_refl); reflexivity.
Qed.

Print Assumptions zeta_pos_iff_dclose.

(* ================================================================= *)
(*  END ZetaClosureBridge.v                                          *)
(*  zeta (nonzero-tested) = the Galois down-closure (dclose,          *)
(*  extensive/monotone/idempotent); dclose is lossy while zeta_t is   *)
(*  invertible — the group (+) vs the idempotent join (⋁) is exactly  *)
(*  what makes Möbius inversion possible.  Closed under global ctx.   *)
(* ================================================================= *)
