(* GHS_self_triple.v — GHS applied to itself.

   GHS proves 12 results (indexed 0–11). Its effect zone is tower_substrate 11.
   By GHS's own tower_substrate_well_located, GHS is well-located.
   Its observer is 0 (the minimum). Its cause zone — what GHS can see
   but cannot prove — is everything beyond index 11.

   THE OBSERVER
     well_located is GHS's observer — the minimum of the effect zone.
     Every theorem in GHS depends on it. Without it, nothing can be stated.

   EFFECT ZONE (12 proven results, indexed 0–11)
     0  well_located (def)           Core concept — GHS's observer
     1  observer_exists_unique       Minimum is unique (antisymmetry of ≤)
     2  observer_is_boundary         Below minimum = complement
     3  tower_substrate (def)        Initial segments {0, ..., n}
     4  tower_substrate_well_located Initial segments are well-located
     5  boundary_in_cause            n+1 ∉ {0, ..., n}
     6  boundary_promoted            n+1 ∈ {0, ..., n+1}
     7  effect_monotone              Segments only grow
     8  all_effect_no_triple         S = ℕ fails (no complement)
     9  all_cause_no_triple          S = ∅ fails (no minimum)
     10 domain_monotone              Once in domain, always in domain
        vanishing_unit               Kernel elements enter domain one step later
     11 limit_is_fixed_point         Tower limit has empty kernel
        limit_subsumes               Every finite depth ⊆ limit

   CAUSE ZONE (what GHS can see but cannot prove)
     1. Diagonal lemma — the engine of Gödel incompleteness.
        GHS formalizes the SHAPE of incompleteness (cause/effect partition)
        but not its ENGINE. The diagonal lemma is absent.
        (Triple.v, Honesty Notes, line 27)
     2. Arithmetic representability — encoding provability as arithmetic.
        GHS works with predicates on nat, not with arithmetic formulas
        that represent their own provability. The reflexive step is missing.
        (Triple.v, Honesty Notes, line 27)
     3. Definability operator Def(L_α) — the core of Gödel's constructible
        universe L. GHS's tower_substrate uses cumulative structure (initial
        segments grow), but Def — the operation that builds each level from
        definable subsets of the previous — is entirely absent.
        (Triple.v, Honesty Notes, line 31)
     4. tower_limit = GodelianOne extensionally — the TowerConstruction file
        claims an analogy between the tower limit and a "Gödelian One" but
        never proves any extensional equivalence. The connection is asserted,
        not formalized.
        (TowerConstruction.v)
     5. Classical logic (LEM, choice) — GHS is constructive throughout.
        Print Assumptions reports "Closed under the global context" for every
        theorem. This is a strength (no hidden axioms) but also a boundary:
        results requiring classical reasoning are outside GHS's reach.
     6. Self-encoding — GHS cannot represent itself as a predicate on ℕ.
        There is no Gödel numbering. GHS can index its results as naturals
        (which this file does) but cannot construct a predicate within its
        own language that captures "provable in GHS." The self-application
        here is meta-theoretic, not internal.

   WHY GHS MUST HAVE BOTH ZONES
     all_effect_no_triple: if everything were proven, well_located fails
       (no complement element).
     all_cause_no_triple: if nothing were proven, well_located fails
       (no minimum element).
     A well-located system is necessarily incomplete — and GHS is no exception.

   THE FORMALSYSTEM TENSION
     In GHS's FormalSystem framework, kernel ⊆ domain. But GHS's cause zone
     lives OUTSIDE the effect zone. The two frameworks model complementary
     aspects: well_located captures the static partition; FormalSystem captures
     dynamic absorption. GHS's cause zone cannot be modeled as a kernel.
     Recognizing this is itself a cause-zone observation about GHS.

   WHAT THIS TELLS US
     GHS is honest. It proves its own incompleteness structure. The self-
     application is an instantiation of existing machinery (tower_substrate_
     well_located 11), not a new proof. GHS doesn't just describe the
     cause/observer/effect structure — it IS an instance of it.

   Axioms beyond CIC: None.  Admitted: 0. *)

From GHS.proven Require Import 
From Stdlib Require Import Lia.

(* ================================================================ *)
(* Section I: GHS's effect zone as a well-located predicate         *)
(* ================================================================ *)

(* GHS proves 12 results, indexed 0 through 11.
   Its effect zone is the initial segment {0, ..., 11}. *)
Definition GHS_effect : nat -> Prop := tower_substrate 11.

(* GHS is well-located: an instantiation, not a new proof. *)
Theorem GHS_effect_well_located : well_located GHS_effect.
Proof. exact (tower_substrate_well_located 11). Qed.

(* The observer of GHS is 0 — the minimum of {0, ..., 11}. *)
Theorem GHS_observer : GHS_effect 0.
Proof. unfold GHS_effect, tower_substrate. lia. Qed.

Theorem GHS_observer_minimum : forall m, GHS_effect m -> 0 <= m.
Proof. intros. lia. Qed.

(* Index 12 is outside: the first element of GHS's cause zone. *)
Theorem GHS_boundary_outside : ~ GHS_effect 12.
Proof. exact (boundary_in_cause 11). Qed.

(* ================================================================ *)
(* Section II: Structural properties                                *)
(* ================================================================ *)

(* The effect zone is bounded: every proven result has index < 12. *)
Theorem GHS_effect_bounded : forall x, GHS_effect x -> x < 12.
Proof. unfold GHS_effect, tower_substrate. lia. Qed.

(* The cause zone is unbounded: beyond any bound, unprovable items exist. *)
Theorem GHS_cause_unbounded : forall n, exists m, m > n /\ ~ GHS_effect m.
Proof.
  intro n. exists (max (n + 1) 12).
  unfold GHS_effect, tower_substrate. split; lia.
Qed.

(* Irreducibility: GHS must have both zones.
   - all_effect_no_triple: S = nat has no complement → not well-located.
   - all_cause_no_triple: S = empty has no minimum → not well-located. *)
Theorem GHS_irreducible :
  ~ (forall n, GHS_effect n) /\ ~ (forall n, ~ GHS_effect n).
Proof.
  split.
  - intro H. exact (all_effect_no_triple GHS_effect H GHS_effect_well_located).
  - intro H. exact (all_cause_no_triple GHS_effect H GHS_effect_well_located).
Qed.

(* ================================================================ *)
(* Section III: Growth dynamics                                     *)
(* ================================================================ *)

(* At each stage k of GHS's development, tower_substrate k models
   "the theorems proven so far."  GHS's own dynamics apply to it:
   - boundary_in_cause: the next theorem is outside at stage k
   - boundary_promoted: it enters at stage k+1
   - effect_monotone:   nothing proven is ever lost *)

(* Example: at stage 10, theorem 11 is outside. *)
Example stage_10_boundary : ~ tower_substrate 10 11.
Proof. exact (boundary_in_cause 10). Qed.

(* At stage 11, theorem 11 enters. *)
Example stage_11_promotion : tower_substrate 11 11.
Proof. exact (boundary_promoted 10). Qed.

(* Everything proven at stage 10 remains at stage 11. *)
Example stage_10_to_11 : forall x, tower_substrate 10 x -> tower_substrate 11 x.
Proof. exact (effect_monotone 10). Qed.

(* ================================================================ *)
(* Note on FormalSystem and the cause zone                          *)
(*                                                                  *)
(* In GHS's FormalSystem framework, kernel ⊆ domain (by the field   *)
(* kernel_in_domain). But GHS's cause zone — propositions GHS can   *)
(* see but not prove — lives OUTSIDE the effect zone, not inside.   *)
(* The two frameworks model complementary aspects:                  *)
(*   - well_located captures the static partition (effect | cause)  *)
(*   - FormalSystem captures dynamic absorption (kernel → domain)   *)
(* GHS's cause zone cannot be modeled as a kernel, because a kernel *)
(* must be a subset of the domain. Recognizing this tension is      *)
(* itself a cause-zone observation about GHS.                       *)
(* ================================================================ *)

(* Axiom audit *)
Print Assumptions GHS_effect_well_located.
Print Assumptions GHS_irreducible.
Print Assumptions GHS_cause_unbounded.
