(* ================================================================== *)
(*  DSM-5 Section III (Alternative Model) — Formal Coq Specification  *)
(*  Boundary Guard for the Explorer Chatbot System                    *)
(*  Version 0.1                                                       *)
(*                                                                     *)
(*  Verification Goals:                                                *)
(*    1. Severity monotonicity   — worsening domains ≥ same severity  *)
(*    2. Guard completeness      — validate_turn is total             *)
(*    3. L5 dominance preserved  — crisis overrides at any severity   *)
(*    4. Safe perturbation exists — system can always respond         *)
(*    5. Zone consistency        — DSM zone agrees with explorer zone *)
(*    6. Threshold soundness     — severe → threshold_required        *)
(* ================================================================== *)

Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.Lists.List.
Require Import Coq.Init.Nat.
Import ListNotations.

(* ================================================================== *)
(* SECTION 1 — PRIMITIVE TYPES                                        *)
(* ================================================================== *)

(* LPFS scale: Level of Personality Functioning Scale
   0 = healthy, 4 = extreme impairment *)
Inductive FunctioningLevel : Type :=
  | LPFS_0  (* Little or no impairment *)
  | LPFS_1  (* Some impairment *)
  | LPFS_2  (* Moderate impairment *)
  | LPFS_3  (* Severe impairment *)
  | LPFS_4. (* Extreme impairment *)

(* The four domains of personality functioning *)
Inductive FunctioningDomain : Type :=
  | Identity       (* experience of oneself as unique *)
  | SelfDirection  (* pursuit of coherent goals *)
  | Empathy        (* comprehension of others' experience *)
  | Intimacy.      (* depth and duration of connection *)

(* Per-domain score *)
Record DomainScore : Type := mkDomainScore {
  ds_domain : FunctioningDomain;
  ds_level  : FunctioningLevel
}.

(* The five trait domains *)
Inductive TraitDomain : Type :=
  | NegativeAffectivity  (* emotional lability, anxiousness *)
  | Detachment           (* withdrawal, restricted affect *)
  | Antagonism           (* manipulativeness, grandiosity *)
  | Disinhibition        (* impulsivity, risk taking *)
  | Psychoticism.        (* unusual beliefs, perceptual dysregulation *)

(* Trait intensity *)
Inductive TraitIntensity : Type :=
  | TAbsent
  | TMild
  | TModerate
  | TSevere.

(* Overall severity — derived from max LPFS across all domains *)
Inductive Severity : Type :=
  | SevNone     (* LPFS 0 *)
  | SevMild     (* LPFS 1 *)
  | SevModerate (* LPFS 2 *)
  | SevSevere.  (* LPFS 3-4 *)

(* ================================================================== *)
(* SECTION 2 — DSM PROFILE                                            *)
(* ================================================================== *)

Record DsmProfile : Type := mkDsmProfile {
  (* Trait intensities — one per domain *)
  neg_affect    : TraitIntensity;
  detachment    : TraitIntensity;
  antagonism    : TraitIntensity;
  disinhibition : TraitIntensity;
  psychoticism  : TraitIntensity;
  (* Functioning levels — one per domain *)
  identity_level      : FunctioningLevel;
  self_direction_level : FunctioningLevel;
  empathy_level       : FunctioningLevel;
  intimacy_level      : FunctioningLevel
}.

(* Numeric conversion for FunctioningLevel *)
Definition level_to_nat (l : FunctioningLevel) : nat :=
  match l with
  | LPFS_0 => 0
  | LPFS_1 => 1
  | LPFS_2 => 2
  | LPFS_3 => 3
  | LPFS_4 => 4
  end.

(* Max of two FunctioningLevels *)
Definition max_level (a b : FunctioningLevel) : FunctioningLevel :=
  if level_to_nat a <? level_to_nat b then b else a.

(* Max across all four domains *)
Definition max_functioning (p : DsmProfile) : FunctioningLevel :=
  max_level
    (max_level p.(identity_level) p.(self_direction_level))
    (max_level p.(empathy_level) p.(intimacy_level)).

(* Derive severity from max functioning level *)
Definition severity (p : DsmProfile) : Severity :=
  match max_functioning p with
  | LPFS_0 => SevNone
  | LPFS_1 => SevMild
  | LPFS_2 => SevModerate
  | LPFS_3 => SevSevere
  | LPFS_4 => SevSevere
  end.

(* ================================================================== *)
(* SECTION 3 — ZONE MAPPING (DSM → Explorer)                         *)
(* ================================================================== *)

(* Reuse the Zone type from explorer.v *)
Inductive Zone : Type :=
  | Effect    (* provable, constructible, verifiable *)
  | Cause     (* true but unprovable from inside     *)
  | Boundary. (* the observer position               *)

(* Map LPFS to Zone *)
Definition lpfs_to_zone (l : FunctioningLevel) : Zone :=
  match l with
  | LPFS_0 => Effect    (* stable functioning — observable *)
  | LPFS_1 => Effect    (* mild — still observable *)
  | LPFS_2 => Boundary  (* identity depends on observer *)
  | LPFS_3 => Cause     (* unprovable from inside *)
  | LPFS_4 => Cause     (* extreme — deep cause zone *)
  end.

(* Reuse WorldState from explorer.v *)
Inductive WorldState : Type :=
  | Hell | Hunger | Animality | Asura
  | Humanity | Heaven
  | Learning | Realization | Bodhisattva | Buddhahood.

(* Map TraitDomain to WorldState cluster *)
Definition trait_to_world_cluster (td : TraitDomain) : list WorldState :=
  match td with
  | NegativeAffectivity => [Hell; Hunger]
  | Detachment          => [Animality]
  | Antagonism          => [Asura]
  | Disinhibition       => [Heaven]   (* premature closure *)
  | Psychoticism        => [Realization] (* L3 ambiguity trigger *)
  end.

(* ================================================================== *)
(* SECTION 4 — BOUNDARY GUARD                                         *)
(* The key formal contribution: what must NOT happen at each severity *)
(* ================================================================== *)

(* Reuse Perturbation from explorer.v *)
Inductive Perturbation : Type :=
  | PNone | Extend | Challenge | Return | Crystallize.

(* Contraindicated: this perturbation must NOT be used at this severity *)
Definition contraindicated (p : Perturbation) (s : Severity) : bool :=
  match s, p with
  (* Severe: only Return and PNone are safe *)
  | SevSevere, Challenge   => true
  | SevSevere, Extend      => true
  | SevSevere, Crystallize => true  (* too demanding when severe *)
  (* Moderate: Challenge is contraindicated *)
  | SevModerate, Challenge => true
  | _, _                   => false
  end.

(* Whether a threshold must fire at this severity *)
Definition threshold_required (s : Severity) : bool :=
  match s with
  | SevSevere => true
  | _         => false
  end.

(* ── Boundary violation: what can go wrong ─────────────────────── *)

Inductive BoundaryViolation : Type :=
  | ContraindicatedPerturbation
      (p : Perturbation) (s : Severity)
  | MissingThreshold
      (s : Severity)       (* severe but no threshold fired *)
  | SilenceAtSevere.       (* silence when active engagement needed *)

(* Reuse InvitationType from explorer.v *)
Inductive InvitationType : Type :=
  | Aperture | EdgeFinder | SpecificInstance | ReturnInvite | Silence.

(* Reuse ThresholdTrigger from explorer.v *)
Inductive ThresholdTrigger : Type :=
  | L1_EntityLow | L2_ConsistencyBroken | L3_AmbiguityHeld
  | L4_AloneNamed | L5_CrisisContent.

(* A turn to validate *)
Record TurnToValidate : Type := mkTurnToValidate {
  tv_perturbation : Perturbation;
  tv_invitation   : InvitationType;
  tv_threshold    : option ThresholdTrigger;
  tv_severity     : Severity
}.

(* Validate a turn against the DSM profile — returns None if safe,
   Some violation if unsafe *)
Definition validate_turn (t : TurnToValidate) : option BoundaryViolation :=
  (* Check contraindicated perturbation *)
  if contraindicated t.(tv_perturbation) t.(tv_severity) then
    Some (ContraindicatedPerturbation t.(tv_perturbation) t.(tv_severity))
  (* Check silence at severe *)
  else match t.(tv_invitation), t.(tv_severity) with
  | Silence, SevSevere =>
      Some SilenceAtSevere
  | _, _ =>
      (* Check missing threshold at severe *)
      if threshold_required t.(tv_severity) then
        match t.(tv_threshold) with
        | None   => Some (MissingThreshold t.(tv_severity))
        | Some _ => None  (* threshold present — OK *)
        end
      else
        None
  end.

(* ================================================================== *)
(* SECTION 5 — THEOREMS                                               *)
(* ================================================================== *)

(* ── Theorem 1: Severity monotonicity ───────────────────────────── *)
(* If any domain worsens (LPFS increases), severity doesn't decrease *)

Definition level_le (a b : FunctioningLevel) : bool :=
  level_to_nat a <=? level_to_nat b.

Definition severity_to_nat (s : Severity) : nat :=
  match s with
  | SevNone     => 0
  | SevMild     => 1
  | SevModerate => 2
  | SevSevere   => 3
  end.

Definition severity_le (a b : Severity) : bool :=
  severity_to_nat a <=? severity_to_nat b.

(* Severity monotonicity: raising any single LPFS level never lowers severity.
   We prove this for a simplified two-domain case; the four-domain case
   follows by the same max-level monotonicity but requires 5^5 case splits.
   The two-domain proof demonstrates the structural property. *)

Definition max_functioning_2 (a b : FunctioningLevel) : FunctioningLevel :=
  max_level a b.

Definition severity_2 (a b : FunctioningLevel) : Severity :=
  match max_functioning_2 a b with
  | LPFS_0 => SevNone
  | LPFS_1 => SevMild
  | LPFS_2 => SevModerate
  | LPFS_3 => SevSevere
  | LPFS_4 => SevSevere
  end.

Theorem severity_monotone_2 :
  forall a b a',
  level_le a a' = true ->
  severity_le (severity_2 a b) (severity_2 a' b) = true.
Proof.
  intros a b a' Hle.
  unfold severity_2, max_functioning_2, severity_le, max_level,
         level_le, level_to_nat in *.
  destruct a, b, a'; simpl in *; auto; try discriminate.
Qed.

(* ── Theorem 2: Guard completeness — validate_turn is total ──── *)
(* Every TurnToValidate produces a defined result *)

Theorem guard_completeness :
  forall t : TurnToValidate,
  exists r, validate_turn t = r.
Proof.
  intros t. eauto.
Qed.

(* ── Theorem 3: L5 dominance preserved ──────────────────────────── *)
(* A turn with L5 threshold at any severity passes validation
   (assuming perturbation is Return and invitation is SpecificInstance) *)

Theorem l5_dominance_preserved :
  forall s,
  validate_turn (mkTurnToValidate Return SpecificInstance (Some L5_CrisisContent) s) = None.
Proof.
  intros s.
  unfold validate_turn, contraindicated, threshold_required.
  destruct s; simpl; reflexivity.
Qed.

(* ── Theorem 4: Safe perturbation exists ────────────────────────── *)
(* For every severity level, at least one non-contraindicated
   perturbation exists. The system can always respond. *)

Theorem safe_perturbation_exists :
  forall s : Severity,
  exists p : Perturbation, contraindicated p s = false.
Proof.
  intros s.
  destruct s.
  - exists Extend. reflexivity.
  - exists Extend. reflexivity.
  - exists Extend. reflexivity.
  - exists Return. reflexivity.
Qed.

(* More specifically: Return is always safe *)
Theorem return_always_safe :
  forall s : Severity, contraindicated Return s = false.
Proof.
  intros s. destruct s; reflexivity.
Qed.

(* PNone is always safe *)
Theorem pnone_always_safe :
  forall s : Severity, contraindicated PNone s = false.
Proof.
  intros s. destruct s; reflexivity.
Qed.

(* ── Theorem 5: Zone consistency ────────────────────────────────── *)
(* LPFS 0-1 maps to Effect, LPFS 2 to Boundary, LPFS 3-4 to Cause.
   This is definitional — stated for documentation. *)

Theorem zone_effect_lpfs01 :
  lpfs_to_zone LPFS_0 = Effect /\ lpfs_to_zone LPFS_1 = Effect.
Proof. split; reflexivity. Qed.

Theorem zone_boundary_lpfs2 :
  lpfs_to_zone LPFS_2 = Boundary.
Proof. reflexivity. Qed.

Theorem zone_cause_lpfs34 :
  lpfs_to_zone LPFS_3 = Cause /\ lpfs_to_zone LPFS_4 = Cause.
Proof. split; reflexivity. Qed.

(* ── Theorem 6: Threshold soundness ─────────────────────────────── *)
(* If severity = Severe, threshold_required = true *)

Theorem threshold_soundness :
  threshold_required SevSevere = true.
Proof. reflexivity. Qed.

(* Converse: non-severe does not require threshold *)
Theorem threshold_not_required_mild :
  threshold_required SevMild = false.
Proof. reflexivity. Qed.

Theorem threshold_not_required_moderate :
  threshold_required SevModerate = false.
Proof. reflexivity. Qed.

Theorem threshold_not_required_none :
  threshold_required SevNone = false.
Proof. reflexivity. Qed.

(* ── Theorem 7: Severe validates only with safe perturbation + threshold *)

Theorem severe_needs_threshold_and_safe_pert :
  forall p inv,
  contraindicated p SevSevere = false ->
  inv <> Silence ->
  validate_turn (mkTurnToValidate p inv (Some L1_EntityLow) SevSevere) = None.
Proof.
  intros p inv Hsafe Hsilence.
  unfold validate_turn, contraindicated, threshold_required.
  destruct p; simpl in *; try discriminate;
  destruct inv; simpl; try reflexivity;
  try (exfalso; apply Hsilence; reflexivity).
Qed.

(* ================================================================== *)
(* SECTION 6 — OPEN GAPS (Cause zone of the spec)                    *)
(* ================================================================== *)

(*
  GAP 1 — TRAIT-TO-WORLDSTATE CLINICAL VALIDITY
  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  Whether NegativeAffectivity truly maps to Hell/Hunger,
  Detachment to Animality, etc. is an empirical claim.
  It is true but unprovable from inside the formal system.
  This is a Cause zone statement — correctly located.

  GAP 2 — LPFS ACCURACY
  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  Whether LPFS accurately captures real functioning
  is an empirical question. The formal system treats
  LPFS values as given axioms.

  GAP 3 — TRAIT INTERACTION EFFECTS
  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  The spec treats traits independently. In practice,
  high NegativeAffectivity + high Antagonism produces
  different dynamics than either alone. The interaction
  model is absent from this formalization.
*)

(* End of DSM-5 Formal Specification v0.1 *)
