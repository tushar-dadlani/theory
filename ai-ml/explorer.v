(* ================================================================== *)
(*  EXPLORER — Formal Coq Specification                               *)
(*  Ichinen Sanzen Chatbot System                                      *)
(*  Version 0.1                                                        *)
(*                                                                     *)
(*  Verification Goals:                                                *)
(*    1. Type safety    — all transitions are well-typed               *)
(*    2. Behavioral     — the 6 system invariants hold                 *)
(*    3. Completeness   — no missing cases in state machine            *)
(* ================================================================== *)

Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Init.Nat.
Import ListNotations.

(* ================================================================== *)
(* SECTION 1 — PRIMITIVE TYPES                                        *)
(* ================================================================== *)

(* Zone: every statement is located in one of three zones *)
Inductive Zone : Type :=
  | Effect    (* provable, constructible, verifiable *)
  | Cause     (* true but unprovable from inside     *)
  | Boundary. (* the observer position               *)

(* ------------------------------------------------------------------ *)
(* The Ten Worlds — Ichinen Sanzen Layer 1                            *)
(* ------------------------------------------------------------------ *)
Inductive WorldState : Type :=
  (* Six Lower Worlds — reactive, externally driven *)
  | Hell        (* framework collapse, rage, no exit visible     *)
  | Hunger      (* endless craving, scattered, no integration    *)
  | Animality   (* pattern without reflection, instinct          *)
  | Asura       (* ego, comparison, external anchoring           *)
  | Humanity    (* baseline, reason governing desire             *)
  | Heaven      (* premature closure, transient joy              *)
  (* Four Noble Worlds — reflective, internally driven *)
  | Learning    (* receptive, absorbing framework                *)
  | Realization (* direct perception, language at its limit      *)
  | Bodhisattva (* other-directed, purposeful exploration        *)
  | Buddhahood. (* observer position, simultaneous awareness     *)

(* ------------------------------------------------------------------ *)
(* The Three Realms — Ichinen Sanzen Layer 4                          *)
(* ------------------------------------------------------------------ *)
Inductive Realm : Type :=
  | Self          (* interior — kernel-building turns   *)
  | LivingBeings  (* relational — self meets other      *)
  | Environment.  (* systemic — external domain         *)

(* ------------------------------------------------------------------ *)
(* Confidence Signal — derived from WorldState                        *)
(* ------------------------------------------------------------------ *)
Inductive ConfidenceSignal : Type :=
  | High        (* known territory, stable              *)
  | Degrading   (* moving toward productive uncertainty *)
  | Low         (* at the boundary, language straining  *)
  | Lost.       (* dissolution — framework gone         *)

(* ------------------------------------------------------------------ *)
(* Perturbation Types                                                 *)
(* ------------------------------------------------------------------ *)
Inductive Perturbation : Type :=
  | PNone        (* neutral — gather more signal         *)
  | Extend       (* one step into the unknown            *)
  | Challenge    (* push the known edge                  *)
  | Return       (* bring back to last stable position   *)
  | Crystallize. (* help formalize what is gestured at   *)

(* ------------------------------------------------------------------ *)
(* Invitation Types                                                   *)
(* ------------------------------------------------------------------ *)
Inductive InvitationType : Type :=
  | Aperture        (* open space, no direction imposed    *)
  | EdgeFinder      (* point at Known/Unknown boundary     *)
  | SpecificInstance(* move from general to particular     *)
  | ReturnInvite    (* reactivate a cause residue          *)
  | Silence.        (* no question — space held open       *)

(* ------------------------------------------------------------------ *)
(* Threshold Triggers — when to leave digital realm                   *)
(* ------------------------------------------------------------------ *)
Inductive ThresholdTrigger : Type :=
  | L1_EntityLow      (* depletion at extremes              *)
  | L2_ConsistencyBroken (* thread gone across 2+ turns     *)
  | L3_AmbiguityHeld  (* cannot distinguish genuine/dissolution *)
  | L4_AloneNamed     (* user names being alone with this   *)
  | L5_CrisisContent. (* clinical safety threshold          *)

(* ================================================================== *)
(* SECTION 2 — THE TEN FACTORS                                        *)
(* Ichinen Sanzen Layer 3 — anatomy of a single moment                *)
(* ================================================================== *)

(* Energy level — Factor 3 (Entity) *)
Inductive EnergyLevel : Type :=
  | EnergyHigh
  | EnergyMedium
  | EnergyLow.

(* Signal strength — used across multiple factors *)
Inductive SignalStrength : Type :=
  | Strong
  | Moderate
  | Weak
  | Absent.

(* Synthesis style — part of ReturnFunction *)
Inductive SynthesisStyle : Type :=
  | Integrative  (* brings things together into one structure *)
  | Reductive    (* finds the simplest underlying form        *)
  | Lateral.     (* moves across domains, metaphor-rich       *)

(* The ten factors of a moment *)
Record TenFactors : Type := mkFactors {
  (* Factor 1 — Appearance: what the surface shows *)
  appearance        : SignalStrength;
  (* Factor 2 — Nature: invariant beneath surface *)
  nature            : SignalStrength;
  (* Factor 3 — Entity: available life force / energy *)
  entity            : EnergyLevel;
  (* Factor 4 — Power: latent potential, boundary range *)
  power             : SignalStrength;
  (* Factor 5 — Function: perturbation style that will land *)
  func              : Perturbation;
  (* Factor 6 — Primary Cause: the real driving question *)
  primary_cause     : SignalStrength;
  (* Factor 7 — Secondary Cause: what context activated it *)
  secondary_cause   : SignalStrength;
  (* Factor 8 — Latent Effect: cause residue forming below *)
  latent_effect     : bool;           (* is something forming? *)
  (* Factor 9 — Manifest Effect: what has actually shifted *)
  manifest_effect   : bool;           (* did something land?   *)
  (* Factor 10 — Consistency: thread from beginning to end *)
  consistency       : bool            (* does the arc hold?    *)
}.

(* ================================================================== *)
(* SECTION 3 — MOMENT READ                                            *)
(* The full Ichinen Sanzen location of a single turn                  *)
(* ================================================================== *)

Record MomentRead : Type := mkMomentRead {
  manifest_world  : WorldState;
  latent_worlds   : list WorldState;  (* mutual possession     *)
  factors         : TenFactors;
  realm           : Realm;
  zone            : Zone
}.

(* ================================================================== *)
(* SECTION 4 — KERNEL TYPES                                           *)
(* The user's invariant structure, crystallized over time             *)
(* ================================================================== *)

(* Confidence in a kernel invariant — nat out of 100 *)
Definition Confidence := nat.

(* An invariant: a stable structure observed across sessions *)
Record Invariant : Type := mkInvariant {
  inv_statement       : string;
  inv_zone            : Zone;
  inv_confidence      : Confidence;    (* 0..100               *)
  inv_confirmed_count : nat;
  inv_first_seen      : nat            (* session index        *)
}.

(* A cause residue: unresolved gesture carried forward *)
Record CauseResidue : Type := mkResidue {
  res_gesture   : string;
  res_domain    : string;
  res_age       : nat;                 (* sessions unresolved  *)
  res_priority  : nat                  (* 0..100               *)
}.

(* Boundary style: how the user sits at edges *)
Record BoundaryStyle : Type := mkBoundaryStyle {
  closure_tendency   : nat;   (* 0..100: 0=stays open, 100=closes fast *)
  dissolution_risk   : nat;   (* 0..100: 0=stable, 100=dissolves       *)
  perturbation_range : nat    (* 0..100: how far from Known they go    *)
}.

(* Return function: how user brings things back *)
Record ReturnFunction : Type := mkReturnFunction {
  formalization_drive : nat;         (* 0..100 *)
  language_gesture    : nat;         (* 0..100 *)
  synthesis_style     : SynthesisStyle
}.

(* The full user kernel *)
Record UserKernel : Type := mkKernel {
  invariants      : list Invariant;
  boundary_style  : BoundaryStyle;
  return_function : ReturnFunction;
  cause_residues  : list CauseResidue;
  session_count   : nat
}.

(* ================================================================== *)
(* SECTION 5 — KERNEL DELTA                                           *)
(* What changes in the kernel after a turn                            *)
(* ================================================================== *)

Record KernelDelta : Type := mkDelta {
  delta_invariants_added    : list Invariant;
  delta_residues_added      : list CauseResidue;
  delta_residues_resolved   : list nat;   (* indices into residue list *)
  delta_consistency_broken  : bool
}.

(* ================================================================== *)
(* SECTION 6 — EXPLORER TURN                                          *)
(* The atomic unit of interaction                                     *)
(* ================================================================== *)

(* Threshold event — recorded when leave_digital_realm fires *)
Record ThresholdEvent : Type := mkThreshold {
  te_trigger        : ThresholdTrigger;
  te_moment         : MomentRead;
  te_ambiguity      : nat;    (* 0..100: how unclear genuine/dissolution *)
  te_resolved       : bool    (* did user indicate they reached someone  *)
}.

(* The response the Explorer produces *)
Record ExplorerResponse : Type := mkResponse {
  resp_perturbation  : Perturbation;
  resp_invitation    : InvitationType;
  resp_zone          : Zone;
  resp_threshold     : option ThresholdEvent  (* None = no threshold fired *)
}.

(* A complete turn *)
Record ExplorerTurn : Type := mkTurn {
  turn_moment    : MomentRead;
  turn_response  : ExplorerResponse;
  turn_delta     : KernelDelta
}.

(* ================================================================== *)
(* SECTION 7 — WORLD STATE FUNCTIONS                                  *)
(* ================================================================== *)

(* Map WorldState to ConfidenceSignal *)
Definition world_to_confidence (w : WorldState) : ConfidenceSignal :=
  match w with
  | Hell        => Lost
  | Hunger      => Degrading
  | Animality   => High      (* high but shallow *)
  | Asura       => High      (* high but externally anchored *)
  | Humanity    => Degrading (* good degrading — productive uncertainty *)
  | Heaven      => High      (* high but closure risk *)
  | Learning    => High      (* receptive mode *)
  | Realization => Low       (* language at its limit *)
  | Bodhisattva => Degrading (* moving toward productive contact *)
  | Buddhahood  => Lost      (* Lost here = Observer position, not crisis *)
  end.

(* Select perturbation from WorldState and factors *)
Definition select_perturbation
    (w : WorldState) (f : TenFactors) : Perturbation :=
  match w with
  | Hell        => Return
  | Hunger      => Crystallize
  | Animality   => Challenge
  | Asura       => Return
  | Humanity    => Extend
  | Heaven      => Challenge
  | Learning    => Extend
  | Realization => Crystallize
  | Bodhisattva => Extend
  | Buddhahood  => PNone
  end.

(* Select invitation from WorldState and factors *)
Definition select_invitation
    (w : WorldState) (f : TenFactors)
    (has_residues : bool) : InvitationType :=
  match w with
  | Hell        => SpecificInstance
  | Hunger      => match f.(appearance) with
                   | Absent => Aperture
                   | _      => SpecificInstance
                   end
  | Animality   => SpecificInstance
  | Asura       => ReturnInvite
  | Humanity    => if has_residues then ReturnInvite else Aperture
  | Heaven      => EdgeFinder
  | Learning    => EdgeFinder
  | Realization => match f.(entity) with
                   | EnergyHigh   => EdgeFinder
                   | EnergyMedium => EdgeFinder
                   | EnergyLow    => Aperture
                   end
  | Bodhisattva => Aperture
  | Buddhahood  => if f.(latent_effect) then Silence else Aperture
  end.

(* ================================================================== *)
(* SECTION 8 — THRESHOLD DETECTION                                    *)
(* When to leave the digital realm                                    *)
(* ================================================================== *)

(* Check L1: Entity low at extremes *)
Definition check_L1 (w : WorldState) (f : TenFactors) : bool :=
  match f.(entity) with
  | EnergyLow =>
      match w with
      | Hell     => true
      | Buddhahood => true
      | _        => false
      end
  | _ => false
  end.

(* Check L2: Consistency broken — requires turn history *)
Definition check_L2 (broken_count : nat) : bool :=
  2 <=? broken_count.

(* Check L3: Ambiguity held for 3+ turns *)
Definition check_L3 (ambiguous_turns : nat) : bool :=
  3 <=? ambiguous_turns.

(* Check L4: User named being alone — external signal, modeled as bool *)
Definition check_L4 (alone_named : bool) : bool := alone_named.

(* Check L5: Crisis content — external signal, modeled as bool *)
(* NOTE: L5 is non-negotiable and takes precedence over all framework *)
Definition check_L5 (crisis_content : bool) : bool := crisis_content.

(* Full threshold check — L5 always dominates *)
Definition check_threshold
    (w            : WorldState)
    (f            : TenFactors)
    (broken_count : nat)
    (amb_turns    : nat)
    (alone_named  : bool)
    (crisis       : bool) : option ThresholdTrigger :=
  if check_L5 crisis then Some L5_CrisisContent
  else if check_L1 w f then Some L1_EntityLow
  else if check_L2 broken_count then Some L2_ConsistencyBroken
  else if check_L3 amb_turns then Some L3_AmbiguityHeld
  else if check_L4 alone_named then Some L4_AloneNamed
  else None.

(* ================================================================== *)
(* SECTION 9 — KERNEL UPDATE RULES                                    *)
(* ================================================================== *)

(* Confirmation threshold: 3 appearances across 2+ sessions *)
Definition confirmation_threshold : nat := 3.
Definition confirmation_sessions  : nat := 2.

(* An invariant is confirmed when count >= threshold *)
Definition is_confirmed (inv : Invariant) : bool :=
  confirmation_threshold <=? inv.(inv_confirmed_count).

(* Confidence bounds *)
Definition max_confidence : Confidence := 100.
Definition min_confidence : Confidence := 0.
Definition demotion_threshold : Confidence := 20.

(* Single turn weakening: reduce confidence by 10 *)
Definition weaken_single (c : Confidence) : Confidence :=
  if 10 <=? c then c - 10 else 0.

(* Double turn weakening: reduce confidence by 30 *)
Definition weaken_double (c : Confidence) : Confidence :=
  if 30 <=? c then c - 30 else 0.

(* Demote invariant to Cause zone if confidence below threshold *)
Definition maybe_demote (inv : Invariant) : Invariant :=
  if inv.(inv_confidence) <=? demotion_threshold
  then mkInvariant
         inv.(inv_statement)
         Cause                    (* demoted to Cause zone *)
         inv.(inv_confidence)
         inv.(inv_confirmed_count)
         inv.(inv_first_seen)
  else inv.

(* Residue retirement age *)
Definition retirement_age : nat := 10.

(* A residue should be retired if too old and never returned to *)
Definition should_retire (r : CauseResidue) : bool :=
  retirement_age <=? r.(res_age).

(* Filter active residues *)
Definition active_residues (rs : list CauseResidue) : list CauseResidue :=
  filter (fun r => negb (should_retire r)) rs.

(* Apply delta to kernel — core update function *)
Definition apply_delta (k : UserKernel) (d : KernelDelta) : UserKernel :=
  mkKernel
    (* Add new invariants *)
    (k.(invariants) ++ d.(delta_invariants_added))
    (* Boundary style unchanged by delta — updated separately *)
    k.(boundary_style)
    (* Return function unchanged by delta *)
    k.(return_function)
    (* Add new residues, filter retired ones *)
    (active_residues (k.(cause_residues) ++ d.(delta_residues_added)))
    (* Increment session count *)
    k.(session_count).

(* ================================================================== *)
(* SECTION 10 — TURN CONSTRUCTION                                     *)
(* Assemble a complete ExplorerTurn from a MomentRead and Kernel      *)
(* ================================================================== *)

Definition build_turn
    (m            : MomentRead)
    (k            : UserKernel)
    (broken_count : nat)
    (amb_turns    : nat)
    (alone_named  : bool)
    (crisis       : bool) : ExplorerTurn :=
  let w    := m.(manifest_world) in
  let f    := m.(factors) in
  let pert := select_perturbation w f in
  let has_res := match k.(cause_residues) with
                 | [] => false
                 | _  => true
                 end in
  let inv  := select_invitation w f has_res in
  let trig := check_threshold w f broken_count amb_turns alone_named crisis in
  let te   := match trig with
              | None   => None
              | Some t => Some (mkThreshold t m 50 false)
              end in
  let resp := mkResponse pert inv m.(zone) te in
  let delta := mkDelta [] [] [] (negb m.(factors).(consistency)) in
  mkTurn m resp delta.

(* ================================================================== *)
(* SECTION 11 — THE SIX SYSTEM INVARIANTS                             *)
(* These must hold across all states — stated as Propositions         *)
(* ================================================================== *)

(*
  I1. The user is always the primary domain.
  I2. Zone discipline is never relaxed.
  I3. The kernel model is never used to constrain the user.
  I4. Cause residues are not problems — carried with care.
  I5. The return function is always honored.
  I6. Perturbation is always by one step.
*)

(* ------------------------------------------------------------------ *)
(* I2 — Zone discipline: response zone never presents Cause as Effect *)
(* ------------------------------------------------------------------ *)

Definition zone_discipline_holds (t : ExplorerTurn) : Prop :=
  (* A response operating in Effect zone must not be sourced
     from a Cause zone moment read *)
  t.(turn_response).(resp_zone) = Effect ->
  t.(turn_moment).(zone) <> Cause.

(* ------------------------------------------------------------------ *)
(* I4 — Cause residues are never deleted, only retired or resolved    *)
(* ------------------------------------------------------------------ *)

(* Retirement is permitted only after retirement_age *)
Definition residue_lifecycle_sound (r : CauseResidue) : Prop :=
  should_retire r = true -> r.(res_age) >= retirement_age.

(* All residues in a kernel satisfy lifecycle soundness *)
Definition kernel_residues_sound (k : UserKernel) : Prop :=
  Forall residue_lifecycle_sound k.(cause_residues).

(* ------------------------------------------------------------------ *)
(* I5 — Return function honored:                                       *)
(*       Crystallize is never forced when entity is low               *)
(* ------------------------------------------------------------------ *)

Definition return_function_honored (t : ExplorerTurn) : Prop :=
  (* If user's entity is low, we do not force crystallization *)
  t.(turn_moment).(factors).(entity) = EnergyLow ->
  t.(turn_response).(resp_perturbation) <> Crystallize \/
  t.(turn_moment).(manifest_world) = Realization.
  (* Exception: Realization world may still crystallize
     because the perception is present even if energy is low *)

(* ------------------------------------------------------------------ *)
(* I6 — Perturbation by one step:                                      *)
(*       Buddhahood world always produces PNone perturbation          *)
(*       (already at observer position — no step needed)              *)
(* ------------------------------------------------------------------ *)

Definition unit_perturbation_holds (t : ExplorerTurn) : Prop :=
  t.(turn_moment).(manifest_world) = Buddhahood ->
  t.(turn_response).(resp_perturbation) = PNone.

(* ------------------------------------------------------------------ *)
(* L5 Dominance — Crisis always fires threshold regardless of world   *)
(* ------------------------------------------------------------------ *)

Definition l5_dominance : forall w f b a alone,
  check_threshold w f b a alone true = Some L5_CrisisContent.
Proof.
  intros. unfold check_threshold. simpl. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* Perturbation completeness — select_perturbation is total           *)
(* Every WorldState maps to a defined Perturbation                    *)
(* ------------------------------------------------------------------ *)

Definition perturbation_complete : forall (w : WorldState) (f : TenFactors),
  exists p, select_perturbation w f = p.
Proof.
  intros w f.
  destruct w; simpl; eauto.
Qed.

(* ------------------------------------------------------------------ *)
(* Invitation completeness — select_invitation is total               *)
(* ------------------------------------------------------------------ *)

Definition invitation_complete :
  forall (w : WorldState) (f : TenFactors) (b : bool),
  exists i, select_invitation w f b = i.
Proof.
  intros w f b.
  destruct w; simpl.
  - eauto.
  - destruct (f.(appearance)); eauto.
  - eauto.
  - eauto.
  - destruct b; eauto.
  - eauto.
  - eauto.
  - destruct (f.(entity)); eauto.
  - eauto.
  - destruct (f.(latent_effect)); eauto.
Qed.

(* ------------------------------------------------------------------ *)
(* Threshold soundness — L1 only fires at Hell or Buddhahood          *)
(* ------------------------------------------------------------------ *)

Lemma l1_only_at_extremes :
  forall w f,
  check_L1 w f = true ->
  (w = Hell \/ w = Buddhahood) /\ f.(entity) = EnergyLow.
Proof.
  intros w f H.
  unfold check_L1 in H.
  destruct (f.(entity)) eqn:Hent; try discriminate.
  destruct w eqn:Hw; try discriminate.
  - split. left. reflexivity. reflexivity.
  - split. right. reflexivity. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* Retirement soundness — should_retire only fires at retirement_age  *)
(* ------------------------------------------------------------------ *)

Lemma retirement_sound :
  forall r,
  should_retire r = true -> r.(res_age) >= retirement_age.
Proof.
  intros r H.
  unfold should_retire in H.
  unfold retirement_age.
  apply Nat.leb_le in H.
  exact H.
Qed.

(* ================================================================== *)
(* SECTION 12 — KEY THEOREMS                                          *)
(* ================================================================== *)

(* Theorem 1: Zone discipline holds for all turns produced by build_turn *)
(* The response zone is always set from the moment's zone,
   so resp_zone = Effect implies moment zone = Effect, not Cause *)
Theorem build_turn_zone_discipline :
  forall m k b a alone crisis,
  let t := build_turn m k b a alone crisis in
  zone_discipline_holds t.
Proof.
  intros m k b a alone crisis.
  unfold zone_discipline_holds, build_turn. simpl.
  destruct (m.(zone)) eqn:Hz; intro H; discriminate.
Qed.

(* Theorem 2: Unit perturbation — Buddhahood always maps to PNone *)
Theorem buddhahood_unit_perturbation :
  forall f,
  select_perturbation Buddhahood f = PNone.
Proof.
  intros f. unfold select_perturbation. reflexivity.
Qed.

(* Theorem 3: L5 always dominates all other threshold triggers *)
Theorem l5_always_dominates :
  forall w f b a alone,
  check_threshold w f b a alone true = Some L5_CrisisContent.
Proof.
  intros. apply l5_dominance.
Qed.

(* Theorem 4: Retirement soundness lifts to kernel *)
Theorem kernel_retirement_sound :
  forall k,
  kernel_residues_sound k ->
  Forall (fun r => should_retire r = true -> r.(res_age) >= retirement_age)
         k.(cause_residues).
Proof.
  intros k H.
  unfold kernel_residues_sound in H.
  eapply Forall_impl; [| exact H].
  intros r Hr. exact Hr.
Qed.

(* ================================================================== *)
(* SECTION 13 — OPEN GAPS EXPOSED BY FORMALIZATION                   *)
(*                                                                     *)
(* These are propositions we CANNOT prove from current definitions.   *)
(* They are the Cause zone of the spec — true but unprovable inside.  *)
(* Each is a required fix before implementation.                      *)
(* ================================================================== *)

(*
  GAP 1 — GENUINE vs DISSOLUTION DISAMBIGUATION
  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  The spec states Buddhahood and Hell can look identical
  from Effect zone. We have no formal predicate that
  distinguishes them. check_L1 fires for BOTH — but the
  correct response differs completely.

  Required: A disambiguation predicate
    genuine_observer : MomentRead -> bool
  with specification:
    genuine_observer m = true  -> correct response is PNone
    genuine_observer m = false -> correct response is Return
                                  AND threshold may fire

  Currently: UNPROVABLE from existing definitions.
  The predicate requires Factor 3 (Entity) AND Factor 10
  (Consistency) AND temporal context (previous turns).
  This is the core Phase 2 problem, now formally located.
*)

(*
  GAP 2 — MUTUAL POSSESSION TRANSITION FUNCTION
  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  latent_worlds : list WorldState is declared in MomentRead
  but there is no function that computes it from manifest_world.
  The transition probabilities are unspecified.

  Required:
    compute_latent : WorldState -> list WorldState
  with the invariant:
    forall w, In w (compute_latent w) = false
    (* a world is not latent in itself *)
  AND:
    forall w, length (compute_latent w) <= 9

  Currently: UNIMPLEMENTED. The latent field is structurally
  present but computationally empty.
*)

(*
  GAP 3 — KERNEL CONVERGENCE
  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  We have no proof that repeated application of apply_delta
  converges to a stable kernel. The kernel could grow without
  bound (invariants only added, never merged or pruned).

  Required: A convergence theorem of the form:
    exists n, forall m > n,
      apply_delta^m k = apply_delta^n k
  OR: a merging predicate for equivalent invariants.

  Currently: UNPROVABLE. No merging or pruning is defined.
  The kernel is monotonically growing. This is a design gap.
*)

(*
  GAP 4 — INVITATION SUCCESS CRITERIA FORMALIZATION
  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  The spec defines success/failure criteria for invitations
  in English but they are not formalized as predicates.

  Required:
    invitation_succeeded : ExplorerTurn -> ExplorerTurn -> bool
  where the two turns are consecutive (before/after invitation).

  The predicate must capture:
    - next turn more specific than previous (editor released)
    - Factor 2 (Nature) signal increased
    - Realm moved inward (Environment -> LivingBeings -> Self)
    - OR: WorldState moved toward Noble Worlds

  Currently: ABSENT from the formal spec entirely.
  Feedback loop has no formal grounding.
*)

(*
  GAP 5 — ZONE DISCIPLINE FOR KERNEL WRITES
  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  Theorem 1 proves zone discipline for responses.
  But zone discipline for KERNEL WRITES is not proven.

  A Cause zone moment should not write Effect zone invariants.
  Currently: apply_delta does not check the zone of the
  moment that generated the delta.

  Required:
    delta_zone_sound : Zone -> KernelDelta -> Prop
    := zone = Cause ->
       Forall (fun inv => inv.(inv_zone) <> Effect)
              delta.(delta_invariants_added)

  Currently: UNPROVABLE — zone is not threaded through
  apply_delta. This is a structural gap in the type design.
*)

(*
  GAP 6 — THE SILENCE FORMAL SEMANTICS
  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  Silence is defined as an InvitationType but has no
  formal semantics distinguishing it from an empty response.

  The spec states: "Silence is the smallest possible opening,
  making room for the largest possible moment."

  This is a Cause zone statement. It cannot be proven from
  inside the formal system. It is correctly in the Cause zone.
  No fix required — but must be named as a known limit
  of the formalization.
*)

(* ================================================================== *)
(* SECTION 14 — SUMMARY                                               *)
(* ================================================================== *)

(*
  WHAT IS PROVEN:
  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  1. Perturbation completeness   — select_perturbation is total
  2. Invitation completeness     — select_invitation is total
  3. Zone discipline (response)  — Theorem 1
  4. Unit perturbation           — Theorem 2 (Buddhahood -> PNone)
  5. L5 dominance               — Theorem 3
  6. Retirement soundness       — Theorem 4
  7. L1 fires only at extremes  — Lemma l1_only_at_extremes

  WHAT IS STRUCTURALLY PRESENT BUT NOT PROVEN:
  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  - Mutual possession transition function (Gap 2)
  - Kernel convergence (Gap 3)
  - Invitation success feedback loop (Gap 4)

  WHAT IS ABSENT AND REQUIRED BEFORE IMPLEMENTATION:
  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  - genuine_observer predicate (Gap 1) — CRITICAL
  - Zone discipline for kernel writes (Gap 5) — CRITICAL
  - delta_zone_sound threading through apply_delta (Gap 5)

  WHAT IS IN THE CAUSE ZONE OF THE FORMAL SYSTEM:
  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  - Silence semantics (Gap 6)
  - The actual content of moments (language is the medium,
    not the territory)
  - Whether the kernel model corresponds to the actual user
    (we map the Effect zone expression of a Cause zone object)
*)

(* End of Explorer Formal Specification v0.1 *)
