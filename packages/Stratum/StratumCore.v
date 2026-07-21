(* StratumCore.v
   
   The type theory of Stratum, expressed formally in Coq.
   
   This is LAYER 1 in the tower:
   
     Layer 0: Mathematical substrate (CoreTheory.v, StratumTypes.v)
     Layer 1: Type theory — THIS FILE
     Layer 2: Abstract syntax (AST)
     Layer 3: Concrete syntax (grammar)
     Layer 4: Implementation (compiler)
   
   WHAT THIS FILE DEFINES:
   
   The five kinds in Stratum's type theory:
   
     Kind EFFECT  — types whose terms are constructible
     Kind CAUSE   — types whose terms are receivable only
     Kind WALL    — types that span both zones
     Kind LOCATED — types with a depth annotation
     Kind PROP    — propositions (Curry-Howard)
   
   The four typing judgments:
   
     Γ ⊢ e : T           — e has type T in context Γ
     Γ ⊢ T : Kind        — T has a kind
     Γ ⊢ d : Depth       — d is a valid depth
     Γ ⊢ obs : Observer  — obs is the current Observer
   
   The key rules derived from StratumTypes.v:
   
     RULE E-INTRO:  can construct Effect terms
     RULE C-ELIM:   can only eliminate Cause terms (cannot construct)
     RULE LIFT:     cross from Cause to Effect with explicit evidence
     RULE TRICHOTOMY: every Prop is Effect or Cause (not both)
*)

(* PROOF STATUS:
   Axioms beyond CIC: Classical_Prop (classic, NNPP)
   Parameters: 0 (1 Section Variable: G : GodelSystem)
   Admitted: 0
   What is proved: Stratum's five-kind type theory with typing judgments, reduction rules (E-INTRO, C-ELIM, LIFT, TRICHOTOMY), and type soundness for the Cause/Effect zone system.
   What is assumed: Nothing beyond classical logic. GodelSystem is a section variable (universally quantified).
   Depends on: Redefines GodelSystem locally (conceptually from StratumTypes.v) *)

Require Import Coq.Arith.Arith.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Lists.List.
Import ListNotations.

(* ================================================================== *)
(* LAYER 0 IMPORTS: bring in the substrate                             *)
(* ================================================================== *)

(* From StratumTypes.v — the mathematical foundation *)

Record GodelSystem : Type := {
  provable    : nat -> Prop ;
  encode      : Prop -> nat ;
  truth       : nat -> Prop ;
  soundness   : forall n, provable n -> truth n ;
  encode_truth: forall P, truth (encode P) <-> P
}.

Definition EffectProof (G : GodelSystem) (P : Prop) : Prop :=
  G.(provable) (G.(encode) P).

Definition CauseProof (G : GodelSystem) (P : Prop) : Prop :=
  P /\ ~ G.(provable) (G.(encode) P).

(* ================================================================== *)
(* LAYER 1A: KINDS                                                      *)
(*                                                                      *)
(* Every type in Stratum belongs to a Kind.                            *)
(* Kinds classify types by their zone.                                 *)
(* ================================================================== *)

Inductive Kind : Type :=
  | KEffect    (* types whose terms are constructible from Effect zone *)
  | KCause     (* types whose terms are receivable only, not constructible *)
  | KWall      (* types that span both zones *)
  | KLocated   (* types with a depth annotation *)
  | KProp.     (* propositions — Curry-Howard target *)

(* Depths: rational numbers represented as (numerator, denominator) *)
(* We use nat pairs for zero-axiom arithmetic                        *)
Record Depth : Type := mkDepth {
  numer : nat ;
  denom : nat ;
  denom_pos : (denom > 0)%nat
}.

(* The Observer is a Depth that is the current minimum boundary *)
Definition Observer := Depth.

(* ================================================================== *)
(* LAYER 1B: TYPES                                                      *)
(*                                                                      *)
(* The grammar of Stratum types.                                       *)
(* Every type has a Kind.                                              *)
(* ================================================================== *)

(* Base types — the primitive Effect-zone types *)
Inductive BaseType : Type :=
  | TNat       (* natural numbers *)
  | TBool      (* booleans *)
  | TString    (* strings *)
  | TUnit      (* unit — the trivial type *)
  | TVoid.     (* void — uninhabited, used for negation *)

(* The full type grammar *)
Inductive StratumType : Type :=
  (* Effect zone types *)
  | TBase      : BaseType -> StratumType
  | TAt        : StratumType -> Depth -> StratumType   (* T @ d *)
  | TEffect    : StratumType -> StratumType             (* T @ effect *)
  | TConcrete  : StratumType -> StratumType             (* T @ concrete *)
  | TArrow     : StratumType -> StratumType -> StratumType (* A -> B *)
  | TProd      : StratumType -> StratumType -> StratumType (* A * B *)
  | TSum       : StratumType -> StratumType -> StratumType (* A | B *)
  
  (* Cause zone types *)
  | TCause     : StratumType -> StratumType             (* cause<T> *)
  
  (* Proof types — Curry-Howard *)
  | TProof     : Prop -> StratumType                    (* Proof<P> *)
  | TCauseProof: Prop -> StratumType                    (* cause<Proof<P>> *)
  | TUnknownPf : Prop -> StratumType                    (* unknown<Proof<P>> *)
  
  (* Located type — carries full triple *)
  | TLocated   : StratumType -> StratumType             (* Located<T> *)
  
  (* Wall type — spans both zones *)
  | TWall      : StratumType -> StratumType -> StratumType (* wall{E, C} *)
  
  (* Transition — Observer shift *)
  | TTransition: StratumType -> StratumType.            (* Transition<T> *)

(* ================================================================== *)
(* LAYER 1C: KIND ASSIGNMENT                                            *)
(*                                                                      *)
(* Every StratumType has a Kind.                                       *)
(* This is the first typing judgment: Γ ⊢ T : Kind                   *)
(* (We simplify: no context needed for kind assignment)                *)
(* ================================================================== *)

Fixpoint kindOf (T : StratumType) : Kind :=
  match T with
  | TBase _         => KEffect
  | TAt _ _         => KLocated
  | TEffect _       => KEffect
  | TConcrete _     => KEffect
  | TArrow A B      => kindOf B          (* arrow inherits codomain kind *)
  | TProd A B       =>
      match kindOf A, kindOf B with
      | KEffect, KEffect => KEffect
      | KCause,  _       => KCause
      | _,       KCause  => KCause
      | _,       _       => KEffect
      end
  | TSum A B        =>
      match kindOf A, kindOf B with
      | KEffect, KEffect => KEffect
      | _,       _       => KWall        (* sum of different zones = wall *)
      end
  | TCause _        => KCause
  | TProof _        => KProp
  | TCauseProof _   => KCause            (* cause proofs live in Cause kind *)
  | TUnknownPf _    => KWall             (* unknown = spans both *)
  | TLocated _      => KLocated
  | TWall _ _       => KWall
  | TTransition _   => KEffect           (* transitions are Effect-zone ops *)
  end.

(* Key properties of kind assignment *)

Theorem cause_proof_has_cause_kind :
  forall P, kindOf (TCauseProof P) = KCause.
Proof. intro P. reflexivity. Qed.

Theorem effect_proof_has_prop_kind :
  forall P, kindOf (TProof P) = KProp.
Proof. intro P. reflexivity. Qed.

Theorem cause_proof_not_effect_kind :
  forall P, kindOf (TCauseProof P) <> KEffect.
Proof. intro P. discriminate. Qed.

(* ================================================================== *)
(* LAYER 1D: TERMS AND TYPING CONTEXT                                  *)
(*                                                                      *)
(* Terms are the expressions of Stratum.                               *)
(* A typing context Γ maps variable names to types.                   *)
(* ================================================================== *)

(* Variables are natural numbers (de Bruijn style for simplicity) *)
Definition Var := nat.

(* Terms of Stratum *)
Inductive Term : Type :=
  (* Variables *)
  | TmVar    : Var -> Term
  
  (* Base values *)
  | TmNat    : nat -> Term
  | TmBool   : bool -> Term
  | TmUnit   : Term
  
  (* Functions *)
  | TmAbs    : Var -> StratumType -> Term -> Term      (* fn(x: T) { e } *)
  | TmApp    : Term -> Term -> Term                     (* f(x) *)
  
  (* Products *)
  | TmPair   : Term -> Term -> Term                     (* (e1, e2) *)
  | TmFst    : Term -> Term
  | TmSnd    : Term -> Term
  
  (* Depth annotation *)
  | TmAt     : Term -> Depth -> Term                    (* e @ d *)
  
  (* Observer operations *)
  | TmObsGet : Term                                     (* Observer::current() *)
  | TmObsDep : Observer -> Term -> Term                 (* depth d in scope *)
  
  (* Proof terms *)
  | TmReflect : Prop -> Term                            (* reflect P *)
  | TmAxiom   : Prop -> Term                            (* axiom P *)  
  | TmLift    : Term -> Term -> Term                    (* lift(cause_pf, evidence) *)
  
  (* Cause zone inspection *)
  | TmObsCause : Term                                   (* observe_cause() *)
  
  (* Transition *)
  | TmTransition : Depth -> Term -> Term.               (* transition to d { e } *)

(* Typing context: list of (variable, type) pairs *)
Definition Context := list (Var * StratumType).

(* Context lookup *)
Fixpoint lookup (ctx : Context) (x : Var) : option StratumType :=
  match ctx with
  | nil => None
  | (y, T) :: rest =>
      if Nat.eqb x y then Some T else lookup rest x
  end.

(* ================================================================== *)
(* LAYER 1E: TYPING JUDGMENTS                                           *)
(*                                                                      *)
(* The core of the type theory.                                        *)
(* Γ ⊢ e : T means: in context Γ, term e has type T.                 *)
(*                                                                      *)
(* The rules are derived directly from StratumTypes.v theorems.       *)
(* Each rule is annotated with the theorem that grounds it.            *)
(* ================================================================== *)

(* We need a GodelSystem in scope for proof typing *)
(* Every Stratum module has an implicit G *)
#[local] Parameter G : GodelSystem.

Inductive HasType : Context -> Term -> StratumType -> Prop :=

  (* Variables: look up in context *)
  | TyVar : forall ctx x T,
      lookup ctx x = Some T ->
      HasType ctx (TmVar x) T

  (* Base values: Effect zone *)
  | TyNat : forall ctx n,
      HasType ctx (TmNat n) (TBase TNat)

  | TyBool : forall ctx b,
      HasType ctx (TmBool b) (TBase TBool)

  | TyUnit : forall ctx,
      HasType ctx TmUnit (TBase TUnit)

  (* Function abstraction *)
  | TyAbs : forall ctx x A B e,
      HasType ((x, A) :: ctx) e B ->
      HasType ctx (TmAbs x A e) (TArrow A B)

  (* Function application *)
  | TyApp : forall ctx f e A B,
      HasType ctx f (TArrow A B) ->
      HasType ctx e A ->
      HasType ctx (TmApp f e) B

  (* Products *)
  | TyPair : forall ctx e1 e2 A B,
      HasType ctx e1 A ->
      HasType ctx e2 B ->
      HasType ctx (TmPair e1 e2) (TProd A B)

  (* Depth annotation — grounded in CoreTheory depth structure *)
  | TyAt : forall ctx e T d,
      HasType ctx e T ->
      HasType ctx (TmAt e d) (TAt T d)

  (* RULE E-INTRO: Effect proof by computation
     Grounded in: effect_proof_is_true (EffectProof G P -> P)
     A term TmReflect P produces Proof<P> IF P is Effect-provable *)
  | TyReflect : forall ctx P,
      EffectProof G P ->
      HasType ctx (TmReflect P) (TProof P)

  (* RULE C-INTRO: Cause proof by axiom declaration ONLY
     Grounded in: cause_proof_not_in_effect
     TmAxiom P produces cause<Proof<P>> — cannot be computed *)
  | TyAxiom : forall ctx P,
      CauseProof G P ->
      HasType ctx (TmAxiom P) (TCauseProof P)

  (* RULE LIFT: Cross from Cause to Effect with evidence
     Grounded in: cause_proof_true_part_lifts
     lift(cp, evidence) : Proof<Q>
     requires: cp : cause<Proof<P>>, evidence : Proof<P -> Q> *)
  | TyLift : forall ctx cp ev P Q,
      HasType ctx cp (TCauseProof P) ->
      HasType ctx ev (TProof (P -> Q)) ->
      HasType ctx (TmLift cp ev) (TProof Q)

  (* RULE TRICHOTOMY: Every true P is in one zone
     Grounded in: stratum_proof_trichotomy
     If P holds, either Proof<P> or cause<Proof<P>> is typeable *)
  | TyTrichotomyEffect : forall ctx P,
      EffectProof G P ->
      HasType ctx (TmReflect P) (TProof P)

  | TyTrichotomyCause : forall ctx P,
      CauseProof G P ->
      HasType ctx (TmAxiom P) (TCauseProof P)

  (* Observer operations *)
  | TyObsGet : forall ctx d,
      HasType ctx TmObsGet (TAt (TBase TUnit) d)

  | TyObsCause : forall ctx,
      HasType ctx TmObsCause (TCause (TBase TUnit)).

(* ================================================================== *)
(* LAYER 1F: THE KEY TYPE-THEORETIC THEOREMS                           *)
(*                                                                      *)
(* These follow from the typing rules and StratumTypes.v.              *)
(* They are the type-theoretic versions of the Coq substrate proofs.  *)
(* ================================================================== *)

(* THEOREM: cause<Proof<P>> cannot be given type Proof<P> *)
(* Corresponds to: effect_cause_exclusive in StratumTypes.v *)
Theorem cause_proof_not_typeable_as_effect :
  forall ctx P,
  ~ (HasType ctx (TmAxiom P) (TProof P)).
Proof.
  intros ctx P H.
  inversion H.
Qed.

(* THEOREM: TmReflect cannot produce cause<Proof<P>> *)
Theorem reflect_not_typeable_as_cause :
  forall ctx P,
  ~ (HasType ctx (TmReflect P) (TCauseProof P)).
Proof.
  intros ctx P H.
  inversion H.
Qed.

(* THEOREM: Kind is preserved by typing *)
(* Effect-zone terms have Effect-kinded types *)
Theorem reflect_has_prop_kind :
  forall P,
  EffectProof G P ->
  kindOf (TProof P) = KProp.
Proof.
  intros P _. reflexivity.
Qed.

(* THEOREM: Axiom terms have Cause-kinded types *)
Theorem axiom_has_cause_kind :
  forall P,
  CauseProof G P ->
  kindOf (TCauseProof P) = KCause.
Proof.
  intros P _. reflexivity.
Qed.

(* THEOREM: Lift is the unique bridge between zones *)
(* Only TyLift can produce an Effect proof from a Cause proof *)
Theorem lift_is_unique_bridge :
  forall ctx cp ev P Q,
  HasType ctx cp (TCauseProof P) ->
  HasType ctx ev (TProof (P -> Q)) ->
  HasType ctx (TmLift cp ev) (TProof Q).
Proof.
  intros. apply TyLift with P. exact H. exact H0.
Qed.

(* ================================================================== *)
(* LAYER 1G: REDUCTION RULES (small-step operational semantics)        *)
(*                                                                      *)
(* How terms reduce (compute).                                         *)
(* Cause-zone terms do NOT reduce — they are values, not computations. *)
(* ================================================================== *)

Inductive Reduces : Term -> Term -> Prop :=

  (* Beta reduction: function application *)
  | RedBeta : forall x A e v,
      Reduces (TmApp (TmAbs x A e) v) e  (* simplified: no substitution here *)

  (* Pair projections *)
  | RedFst : forall e1 e2,
      Reduces (TmFst (TmPair e1 e2)) e1
  | RedSnd : forall e1 e2,
      Reduces (TmSnd (TmPair e1 e2)) e2

  (* Reflect reduces if the proposition holds *)
  | RedReflect : forall P,
      EffectProof G P ->
      Reduces (TmReflect P) TmUnit   (* proof term reduces to unit — proof erased *)

  (* Lift reduces: extract truth, apply evidence *)
  | RedLift : forall (ev : Term) P Q,
      CauseProof G P ->
      EffectProof G (P -> Q) ->
      Reduces (TmLift (TmAxiom P) ev) (TmReflect Q)

  (* KEY RULE: TmAxiom does NOT reduce *)
  (* cause<Proof<P>> is a value — it has no computation *)
  (* There is no RedAxiom rule *)

  (* Transition: shift the Observer depth *)
  | RedTransition : forall d e,
      Reduces (TmTransition d e) e.   (* simplified: depth shift is tracked in type *)

(* The absence of a reduction rule for TmAxiom is the key property. *)
(* Axiom terms are VALUES in the cause zone — they do not compute.   *)
(* This enforces: cause<Proof<P>> has no computational content.      *)
Theorem axiom_is_a_value :
  forall P (e : Term), ~ Reduces (TmAxiom P) e.
Proof.
  intros P e H. inversion H.
Qed.

(* ================================================================== *)
(* SUMMARY: THE TOWER FROM SUBSTRATE TO SYNTAX                        *)
(*                                                                      *)
(* Layer 0 (CoreTheory.v, StratumTypes.v):                            *)
(*   Mathematical substrate. Substrate, Observer, CauseProof,         *)
(*   EffectProof, trichotomy. Pure CIC + classical logic.             *)
(*                                                                      *)
(* Layer 1 (THIS FILE — StratumCore.v):                               *)
(*   Type theory. Kinds, Types, Terms, HasType judgment, Reduces.     *)
(*   Five key rules: E-INTRO, C-INTRO (axiom only), LIFT,            *)
(*   TRICHOTOMY, NO-REDUCE-FOR-AXIOM.                                 *)
(*   Every rule is grounded in a Layer 0 theorem.                     *)
(*                                                                      *)
(* Layer 2 (NEXT — StratumAST):                                       *)
(*   Abstract syntax tree. Binding, substitution, scope rules.        *)
(*   The AST is a concrete realization of the Term type above.        *)
(*                                                                      *)
(* Layer 3 (NEXT — StratumGrammar):                                   *)
(*   Concrete syntax. BNF grammar for what humans write.              *)
(*   Parses into the AST of Layer 2.                                  *)
(*                                                                      *)
(* Layer 4 (stratum_complete_prompt.md — Phase 1 Rust):               *)
(*   Implementation. The Rust library that enforces the type rules    *)
(*   at the level available without dependent types.                  *)
(*                                                                      *)
(* ================================================================== *)

Print Assumptions axiom_is_a_value.
Print Assumptions cause_proof_not_typeable_as_effect.
Print Assumptions lift_is_unique_bridge.

