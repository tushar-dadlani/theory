(* GHS.v — Merged minimal theory: well-located substrates + tower construction.
   Axioms beyond CIC: None. Parameters: 0. Admitted: 0. *)

From Stdlib Require Import Lia.

(* ================================================================ *)
(* Part I: Well-located substrates and the observer                 *)
(* ================================================================ *)

(* A predicate S on nat is well-located if it has a complement element
   and a minimum element. *)
Definition well_located (S : nat -> Prop) : Prop :=
  (exists n, ~ S n) /\
  (exists n, S n /\ forall m, S m -> n <= m).

(* The minimum of a well-located S is unique: antisymmetry of <= on nat. *)
Theorem observer_exists_unique :
  forall S, well_located S ->
  exists! obs, S obs /\ (forall m, S m -> obs <= m).
Proof.
  intros S [_ [obs [Hobs Hmin]]].
  exists obs. split.
  - exact (conj Hobs Hmin).
  - intros obs' [Hobs' Hmin'].
    pose proof (Hmin obs' Hobs'). pose proof (Hmin' obs Hobs). lia.
Qed.

(* Everything below the minimum is in the complement; the minimum itself
   is in S; everything in S is at or above the minimum. *)
Theorem observer_is_boundary :
  forall S obs,
  S obs -> (forall m, S m -> obs <= m) ->
  (forall n, n < obs -> ~ S n) /\
  S obs /\
  (forall m, S m -> m >= obs).
Proof.
  intros S obs Hobs Hmin.
  refine (conj _ (conj Hobs Hmin)).
  intros n Hlt Hn. apply Hmin in Hn. lia.
Qed.

(* ================================================================ *)
(* Part II: The tower of initial segments                           *)
(* ================================================================ *)

(* tower_substrate n = {0, 1, ..., n}, the initial segment of length n+1. *)
Definition tower_substrate (n : nat) : nat -> Prop :=
  fun x => x < n + 1.

Theorem tower_substrate_well_located :
  forall n, well_located (tower_substrate n).
Proof.
  intros n. unfold well_located, tower_substrate. split.
  - exists (n + 1). lia.
  - exists 0. split; [lia | intros m _; lia].
Qed.

(* The boundary element n+1 is outside the segment at level n. *)
Theorem boundary_in_cause :
  forall n, ~ tower_substrate n (n + 1).
Proof. unfold tower_substrate. intros. lia. Qed.

(* At the next level, the boundary element enters the segment. *)
Theorem boundary_promoted :
  forall n, tower_substrate (n + 1) (n + 1).
Proof. unfold tower_substrate. intros. lia. Qed.

(* Segments grow monotonically. *)
Theorem effect_monotone :
  forall n x, tower_substrate n x -> tower_substrate (n + 1) x.
Proof. unfold tower_substrate. intros. lia. Qed.

(* S = nat (everything in S) has no complement element. *)
Theorem all_effect_no_triple :
  forall S, (forall n, S n) -> ~ well_located S.
Proof. intros S Hall [[n Hn] _]. exact (Hn (Hall n)). Qed.

(* S = empty (nothing in S) has no minimum element. *)
Theorem all_cause_no_triple :
  forall S, (forall n, ~ S n) -> ~ well_located S.
Proof. intros S Hnone [_ [n [Hn _]]]. exact (Hnone n Hn). Qed.

(* ================================================================ *)
(* Part III: Formal systems and the tower construction              *)
(* ================================================================ *)

Record FormalSystem : Type := mkFS {
  domain : nat -> Prop;
  kernel : nat -> Prop;
  kernel_in_domain : forall p, kernel p -> domain p;
}.

(* One step: absorb kernel into domain; new kernel = old kernel minus old domain. *)
Definition tower_step (F : FormalSystem) : FormalSystem := mkFS
  (fun p => F.(domain) p \/ F.(kernel) p)
  (fun p => F.(kernel) p /\ ~ F.(domain) p)
  (fun p H => or_intror (proj1 H)).

(* Iterate tower_step n times from F0. *)
Fixpoint tower (F0 : FormalSystem) (n : nat) : FormalSystem :=
  match n with
  | O   => F0
  | S m => tower_step (tower F0 m)
  end.

(* The limit: domain = union of all finite depths, kernel = empty. *)
Definition tower_limit (F0 : FormalSystem) : FormalSystem := mkFS
  (fun p => exists n, (tower F0 n).(domain) p)
  (fun _ => False)
  (fun _ H => match H with end).

(* Once in the domain, always in the domain. *)
Lemma domain_monotone :
  forall F0 n p,
  (tower F0 n).(domain) p -> (tower F0 (S n)).(domain) p.
Proof. intros. simpl. left. exact H. Qed.

(* Every kernel element enters the domain one step later. *)
Lemma vanishing_unit :
  forall F0 n p,
  (tower F0 n).(kernel) p -> (tower F0 (S n)).(domain) p.
Proof. intros. simpl. right. exact H. Qed.

(* The limit has empty kernel. *)
Lemma limit_is_fixed_point :
  forall F0 p, ~ (tower_limit F0).(kernel) p.
Proof. intros F0 p H. exact H. Qed.

(* Every finite depth is contained in the limit. *)
Lemma limit_subsumes :
  forall F0 n p,
  (tower F0 n).(domain) p -> (tower_limit F0).(domain) p.
Proof. intros. exists n. exact H. Qed.

(* Axiom audit *)
Print Assumptions observer_exists_unique.
Print Assumptions observer_is_boundary.
Print Assumptions tower_substrate_well_located.
Print Assumptions limit_subsumes.
