(* ================================================================== *)
(* INVARIANT_HIERARCHY.V                                               *)
(*                                                                     *)
(* HIERARCHICAL INVARIANT ORGANIZATION                                *)
(*                                                                     *)
(* Formalizes the derivation of hierarchical invariants from fixed     *)
(* points, edges, and language profiles.  Invariants are the top-level *)
(* organizing concept; fixed points are evidence beneath them.         *)
(*                                                                     *)
(* The hierarchy has exactly depth 2:                                  *)
(*   Level 0: Invariant (statement, source, trust)                    *)
(*   Level 1: Evidence  (fixed point IDs supporting the invariant)    *)
(*                                                                     *)
(* Derivation rules correspond to theorems T1-T9 in Axioms.md.       *)
(* All derivation is graph-only (deterministic, no LLM).              *)
(*                                                                     *)
(* Key results:                                                       *)
(*   1. Derivation rules are well-typed (source + conditions → inv)  *)
(*   2. Evidence monotonicity (adding evidence never removes inv)     *)
(*   3. Depth-2 guarantee (no deeper nesting)                         *)
(*   4. Source unification (human + agent in same structure)          *)
(*                                                                     *)
(* Follows Stratum convention: self-contained, no .vo imports.        *)
(*                                                                     *)
(* Corresponds to: examples/memory_server.rs :: derive_invariants()   *)
(* ================================================================== *)

From Stdlib Require Import Arith.
From Stdlib Require Import QArith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.
Import ListNotations.
Open Scope Q_scope.

(* ================================================================== *)
(* I. SOURCE CLASSIFICATION                                            *)
(*                                                                     *)
(* Every invariant has a source: who or what produced it.              *)
(*   Human   — from the user's cause-zone fixed points (T1, T3, T8) *)
(*   Agent   — from the system's effect-zone patterns (T2)           *)
(*   Language — from per-language profiles (T9)                       *)
(*   Derived  — synthesized from graph structure (T5, T6, T7)        *)
(*                                                                     *)
(* In the Rust code:                                                  *)
(*   enum InvariantSource { Human, Agent, Language, Derived }         *)
(* ================================================================== *)

Inductive InvariantSource :=
  | Human    (* from what you do *)
  | Agent    (* from the system *)
  | Language (* when you write [language] *)
  | Derived  (* patterns working together *).

(* ================================================================== *)
(* II. TRUST LEVELS                                                    *)
(*                                                                     *)
(* Mirrors A12 from Axioms.md.                                        *)
(*   High   — confident, well-established                             *)
(*   Medium — learning, gathering evidence                            *)
(*   Low    — new, just starting to see                               *)
(* ================================================================== *)

Inductive TrustLevel := High | Medium | Low.

(* Trust ordering: High > Medium > Low *)
Definition trust_ge (a b : TrustLevel) : Prop :=
  match a, b with
  | High, _      => True
  | Medium, Low  => True
  | Medium, Medium => True
  | Low, Low     => True
  | _, _         => False
  end.

(* Max of two trust levels *)
Definition trust_max (a b : TrustLevel) : TrustLevel :=
  match a, b with
  | High, _ | _, High => High
  | Medium, _ | _, Medium => Medium
  | Low, Low => Low
  end.

Lemma trust_max_ge_left : forall a b, trust_ge (trust_max a b) a.
Proof. destruct a, b; simpl; trivial. Qed.

Lemma trust_max_ge_right : forall a b, trust_ge (trust_max a b) b.
Proof. destruct a, b; simpl; trivial. Qed.

(* ================================================================== *)
(* III. ZONES                                                          *)
(*                                                                     *)
(* Mirrors A8-A10 from Axioms.md.                                     *)
(* ================================================================== *)

Inductive Zone := Cause | Effect | Crossing.

(* ================================================================== *)
(* IV. FIXED POINTS AND EDGES (PARAMETERS)                            *)
(*                                                                     *)
(* We parameterize over the concrete data — the Rust code provides    *)
(* these at runtime from MemoryState.                                  *)
(* ================================================================== *)

Parameter FixedPointId : Type.
Parameter fp_id_eq_dec : forall (a b : FixedPointId), {a = b} + {a <> b}.

Record FixedPoint := mkFP {
  fp_id        : FixedPointId;
  fp_zone      : Zone;
  fp_trust     : TrustLevel;
  fp_invariants : list nat;    (* indices into a global string table *)
  fp_residual_history_len : nat;
  fp_residual_monotone : bool; (* whether residual_history is monotone *)
  fp_tower_level : nat;        (* 1-10 *)
}.

Record Edge := mkEdge {
  edge_from   : FixedPointId;
  edge_to     : FixedPointId;
  edge_weight : Q;
}.

Parameter LangName : Type.

Record LangProfile := mkLang {
  lang_name       : LangName;
  lang_invariants : list nat;  (* indices into global string table *)
  lang_event_count : nat;
}.

(* ================================================================== *)
(* V. EVIDENCE AND HIERARCHICAL INVARIANT                              *)
(*                                                                     *)
(* An invariant is a statement with source, trust, and a set of       *)
(* evidence links (fixed points supporting it).                        *)
(*                                                                     *)
(* The evidence set is a list (not a tree) — depth is exactly 2.     *)
(*                                                                     *)
(* In the Rust code:                                                  *)
(*   struct HierarchicalInvariant { statement, source, trust,         *)
(*                                   evidence: Vec<EvidenceLink> }    *)
(* ================================================================== *)

Record EvidenceLink := mkEvidence {
  ev_fp_id  : FixedPointId;
  ev_zone   : Zone;
  ev_trust  : TrustLevel;
  ev_weight : Q;              (* edge weight or 1.0 for direct *)
}.

Record HierarchicalInvariant := mkHInv {
  hinv_statement : nat;       (* index into global string table *)
  hinv_source    : InvariantSource;
  hinv_trust     : TrustLevel;
  hinv_evidence  : list EvidenceLink;
  hinv_language  : option LangName;  (* Some if language-scoped *)
}.

(* ================================================================== *)
(* VI. DEPTH-2 GUARANTEE                                               *)
(*                                                                     *)
(* The hierarchy is exactly:                                           *)
(*   Invariant → list of EvidenceLink                                 *)
(* EvidenceLink contains only scalar fields (id, zone, trust, weight) *)
(* — no nested invariants, no recursive structure.                    *)
(*                                                                     *)
(* This is structural: EvidenceLink has no field of type               *)
(* HierarchicalInvariant, so depth > 2 is impossible by construction. *)
(* ================================================================== *)

(* The depth of the hierarchy is always exactly 2:
   level 0 = invariant, level 1 = evidence links.
   This is guaranteed by the type structure — EvidenceLink
   contains no HierarchicalInvariant fields. *)
Definition hierarchy_depth (_ : HierarchicalInvariant) : nat := 2%nat.

Theorem depth_is_two : forall inv : HierarchicalInvariant,
  hierarchy_depth inv = 2%nat.
Proof. reflexivity. Qed.

(* ================================================================== *)
(* VII. DERIVATION RULES                                               *)
(*                                                                     *)
(* Each rule maps conditions on fixed points/edges/languages to        *)
(* the construction of a HierarchicalInvariant.                        *)
(*                                                                     *)
(* The rules correspond to theorems T1-T9 from Axioms.md:             *)
(*   derive_direct   — T1 (cause+High), T2 (effect+High),            *)
(*                     T3 (crossing+High), T4 (Low trust)            *)
(*   derive_cluster  — T5 (connected fps sharing invariants)          *)
(*   derive_chain    — T6 (cause→effect edge, both High trust)       *)
(*   derive_deepen   — T7 (monotone residual, tower_level 1-3)       *)
(*   derive_language — T9 (language profile invariants)               *)
(* ================================================================== *)

(* Helper: source from zone and trust *)
Definition source_of (z : Zone) (t : TrustLevel) : InvariantSource :=
  match z, t with
  | Cause, High      => Human    (* T1: Core Habit *)
  | Cause, _         => Human    (* T4 variant *)
  | Effect, High     => Agent    (* T2: System Signature *)
  | Effect, _        => Agent    (* T4 variant *)
  | Crossing, High   => Human    (* T3: Established Dialogue *)
  | Crossing, _      => Human    (* T4 variant *)
  end.

(* The derivation judgment: "from these inputs, this invariant is valid" *)
Inductive valid_derivation :
  list FixedPoint -> list Edge -> list LangProfile ->
  HierarchicalInvariant -> Prop :=

  (* T1/T2/T3/T4: Direct — a fixed point carries an invariant string *)
  | derive_direct :
      forall fps edges langs fp stmt,
      In fp fps ->
      In stmt (fp_invariants fp) ->
      valid_derivation fps edges langs
        (mkHInv stmt
                (source_of (fp_zone fp) (fp_trust fp))
                (fp_trust fp)
                [mkEvidence (fp_id fp) (fp_zone fp) (fp_trust fp) 1]
                None)

  (* T5: Cluster — connected fps sharing an invariant string,
     all edges have weight > 0.2 *)
  | derive_cluster :
      forall fps edges langs fp1 fp2 e stmt,
      In fp1 fps -> In fp2 fps -> In e edges ->
      fp_id fp1 <> fp_id fp2 ->
      edge_from e = fp_id fp1 -> edge_to e = fp_id fp2 ->
      edge_weight e > (1 # 5) ->  (* > 0.2 *)
      In stmt (fp_invariants fp1) ->
      In stmt (fp_invariants fp2) ->
      valid_derivation fps edges langs
        (mkHInv stmt Derived
                (trust_max (fp_trust fp1) (fp_trust fp2))
                [mkEvidence (fp_id fp1) (fp_zone fp1) (fp_trust fp1) (edge_weight e);
                 mkEvidence (fp_id fp2) (fp_zone fp2) (fp_trust fp2) (edge_weight e)]
                None)

  (* T6: Cause-Effect Chain — cause→effect edge, both High trust *)
  | derive_chain :
      forall fps edges langs fp_cause fp_effect e stmt,
      In fp_cause fps -> In fp_effect fps -> In e edges ->
      fp_zone fp_cause = Cause -> fp_zone fp_effect = Effect ->
      fp_trust fp_cause = High -> fp_trust fp_effect = High ->
      edge_from e = fp_id fp_cause -> edge_to e = fp_id fp_effect ->
      edge_weight e > (1 # 5) ->
      valid_derivation fps edges langs
        (mkHInv stmt Derived High
                [mkEvidence (fp_id fp_cause) Cause High (edge_weight e);
                 mkEvidence (fp_id fp_effect) Effect High (edge_weight e)]
                None)

  (* T7: Deepening — monotone residual decrease, tower_level 1-3 *)
  | derive_deepen :
      forall fps edges langs fp stmt,
      In fp fps ->
      fp_residual_monotone fp = true ->
      (fp_residual_history_len fp >= 5)%nat ->
      (fp_tower_level fp <= 3)%nat ->
      In stmt (fp_invariants fp) ->
      valid_derivation fps edges langs
        (mkHInv stmt Derived (fp_trust fp)
                [mkEvidence (fp_id fp) (fp_zone fp) (fp_trust fp) 1]
                None)

  (* T9: Language — invariant from a language profile *)
  | derive_language :
      forall fps edges langs lp stmt,
      In lp langs ->
      In stmt (lang_invariants lp) ->
      valid_derivation fps edges langs
        (mkHInv stmt Language Medium [] (Some (lang_name lp))).

(* ================================================================== *)
(* VIII. EVIDENCE MONOTONICITY                                         *)
(*                                                                     *)
(* Adding a fixed point to the evidence of an existing invariant      *)
(* never invalidates it. If inv was derivable before adding fp_new,   *)
(* it remains derivable after.                                         *)
(*                                                                     *)
(* This is the key stability property: the invariant hierarchy only   *)
(* grows as new fixed points are discovered.                           *)
(* ================================================================== *)

(* Adding a fixed point to the list preserves membership *)
Lemma in_cons_preserved :
  forall (A : Type) (x y : A) (l : list A),
  In x l -> In x (y :: l).
Proof. intros. right. exact H. Qed.

(* Adding a fixed point to the input never removes a derivation *)
Theorem evidence_monotonicity :
  forall fps edges langs inv fp_new,
  valid_derivation fps edges langs inv ->
  valid_derivation (fp_new :: fps) edges langs inv.
Proof.
  intros fps edges langs inv fp_new Hderiv.
  induction Hderiv.
  - (* derive_direct *)
    apply derive_direct with (fp := fp).
    + right. exact H.
    + exact H0.
  - (* derive_cluster *)
    apply derive_cluster with (fp1 := fp1) (fp2 := fp2) (e := e).
    + right. exact H.
    + right. exact H0.
    + exact H1.
    + exact H2.
    + exact H3.
    + exact H4.
    + exact H5.
    + exact H6.
    + exact H7.
  - (* derive_chain *)
    apply derive_chain with (fp_cause := fp_cause) (fp_effect := fp_effect) (e := e).
    + right. exact H.
    + right. exact H0.
    + exact H1.
    + exact H2.
    + exact H3.
    + exact H4.
    + exact H5.
    + exact H6.
    + exact H7.
    + exact H8.
  - (* derive_deepen *)
    apply derive_deepen with (fp := fp).
    + right. exact H.
    + exact H0.
    + exact H1.
    + exact H2.
    + exact H3.
  - (* derive_language *)
    apply derive_language with (lp := lp).
    + exact H.
    + exact H0.
Qed.

(* Adding an edge never removes a derivation *)
Theorem edge_monotonicity :
  forall fps edges langs inv e_new,
  valid_derivation fps edges langs inv ->
  valid_derivation fps (e_new :: edges) langs inv.
Proof.
  intros fps edges langs inv e_new Hderiv.
  induction Hderiv.
  - apply derive_direct with (fp := fp); assumption.
  - apply derive_cluster with (fp1 := fp1) (fp2 := fp2) (e := e);
    try assumption. right. exact H1.
  - apply derive_chain with (fp_cause := fp_cause) (fp_effect := fp_effect) (e := e);
    try assumption. right. exact H1.
  - apply derive_deepen with (fp := fp); assumption.
  - apply derive_language with (lp := lp); assumption.
Qed.

(* Adding a language profile never removes a derivation *)
Theorem language_monotonicity :
  forall fps edges langs inv lp_new,
  valid_derivation fps edges langs inv ->
  valid_derivation fps edges (lp_new :: langs) inv.
Proof.
  intros fps edges langs inv lp_new Hderiv.
  induction Hderiv.
  - apply derive_direct with (fp := fp); assumption.
  - apply derive_cluster with (fp1 := fp1) (fp2 := fp2) (e := e); assumption.
  - apply derive_chain with (fp_cause := fp_cause) (fp_effect := fp_effect) (e := e); assumption.
  - apply derive_deepen with (fp := fp); assumption.
  - apply derive_language with (lp := lp).
    + right. exact H.
    + exact H0.
Qed.

(* ================================================================== *)
(* IX. SOURCE UNIFICATION                                              *)
(*                                                                     *)
(* Human and agent invariants live in the same HierarchicalInvariant  *)
(* type, distinguished only by the source field. This means:           *)
(*   - A single derivation function handles both                      *)
(*   - The UI can display them uniformly                               *)
(*   - The push_habits endpoint reads one structure                    *)
(*                                                                     *)
(* Prove: every source type is reachable by some derivation rule.     *)
(* ================================================================== *)

(* Human source is reachable via derive_direct with Cause zone *)
Lemma human_source_reachable :
  forall fps edges langs fp stmt,
  In fp fps ->
  In stmt (fp_invariants fp) ->
  fp_zone fp = Cause ->
  fp_trust fp = High ->
  exists inv, valid_derivation fps edges langs inv /\
              hinv_source inv = Human.
Proof.
  intros.
  exists (mkHInv stmt (source_of (fp_zone fp) (fp_trust fp))
                     (fp_trust fp)
          [mkEvidence (fp_id fp) (fp_zone fp) (fp_trust fp) 1] None).
  split.
  - apply (derive_direct fps edges langs fp stmt H H0).
  - rewrite H1, H2. reflexivity.
Qed.

(* Agent source is reachable via derive_direct with Effect zone *)
Lemma agent_source_reachable :
  forall fps edges langs fp stmt,
  In fp fps ->
  In stmt (fp_invariants fp) ->
  fp_zone fp = Effect ->
  fp_trust fp = High ->
  exists inv, valid_derivation fps edges langs inv /\
              hinv_source inv = Agent.
Proof.
  intros.
  exists (mkHInv stmt (source_of (fp_zone fp) (fp_trust fp))
                     (fp_trust fp)
          [mkEvidence (fp_id fp) (fp_zone fp) (fp_trust fp) 1] None).
  split.
  - apply (derive_direct fps edges langs fp stmt H H0).
  - rewrite H1, H2. reflexivity.
Qed.

(* Language source is reachable via derive_language *)
Lemma language_source_reachable :
  forall fps edges langs lp stmt,
  In lp langs ->
  In stmt (lang_invariants lp) ->
  exists inv, valid_derivation fps edges langs inv /\
              hinv_source inv = Language.
Proof.
  intros.
  exists (mkHInv stmt Language Medium [] (Some (lang_name lp))).
  split.
  - exact (derive_language fps edges langs lp stmt H H0).
  - reflexivity.
Qed.

(* Derived source is reachable via derive_cluster *)
Lemma derived_source_reachable :
  forall fps edges langs fp1 fp2 e stmt,
  In fp1 fps -> In fp2 fps -> In e edges ->
  fp_id fp1 <> fp_id fp2 ->
  edge_from e = fp_id fp1 -> edge_to e = fp_id fp2 ->
  edge_weight e > (1 # 5) ->
  In stmt (fp_invariants fp1) ->
  In stmt (fp_invariants fp2) ->
  exists inv, valid_derivation fps edges langs inv /\
              hinv_source inv = Derived.
Proof.
  intros.
  eexists. split.
  - exact (derive_cluster fps edges langs fp1 fp2 e stmt
           H H0 H1 H2 H3 H4 H5 H6 H7).
  - reflexivity.
Qed.

(* ================================================================== *)
(* X. THE MAIN THEOREM                                                 *)
(*                                                                     *)
(* Assembles all properties of the hierarchical invariant system.      *)
(* ================================================================== *)

Theorem INVARIANT_HIERARCHY :
  (** 1. Depth is always exactly 2 *)
  (forall inv, hierarchy_depth inv = 2%nat)
  /\
  (** 2. Evidence monotonicity — adding fps/edges/langs never removes *)
  (forall fps edges langs inv fp_new,
    valid_derivation fps edges langs inv ->
    valid_derivation (fp_new :: fps) edges langs inv)
  /\
  (forall fps edges langs inv e_new,
    valid_derivation fps edges langs inv ->
    valid_derivation fps (e_new :: edges) langs inv)
  /\
  (forall fps edges langs inv lp_new,
    valid_derivation fps edges langs inv ->
    valid_derivation fps edges (lp_new :: langs) inv)
  /\
  (** 3. Trust max is an upper bound *)
  (forall a b, trust_ge (trust_max a b) a /\ trust_ge (trust_max a b) b).
Proof.
  split. { exact depth_is_two. }
  split. { exact evidence_monotonicity. }
  split. { exact edge_monotonicity. }
  split. { exact language_monotonicity. }
  intros. split; [exact (trust_max_ge_left a b) | exact (trust_max_ge_right a b)].
Qed.

(* ================================================================== *)
(* Print assumptions to make Cause-zone axioms visible.               *)
(* ================================================================== *)

Print Assumptions INVARIANT_HIERARCHY.
