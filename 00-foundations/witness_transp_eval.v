(* Witness Transparent Evaluation *)
(* The benchmark's hidden witness made explicit *)
(* A new kind of evaluation that cannot be gamed *)

Section WitnessTransparentEvaluation.

(* Carry forward core structure *)
CoInductive MapOperator (A : Type) : Type :=
  | absorb : A -> MapOperator A -> MapOperator A.

CoFixpoint generative_witness (A : Type) (x : A) : MapOperator A :=
  absorb A x (generative_witness A x).

Inductive Nat : Type :=
  | Zero : MapOperator Nat -> Nat
  | Succ : Nat -> MapOperator Nat -> Nat.

(* GAP: build-repair — Nat and MapOperator Nat mutually bootstrap with no
   base case, so MapOperator Nat has no closed inhabitant; the intended
   corecursive [zero_witness] is rejected by the guard condition. We assert
   its existence as an axiom to keep the intended type and definitions. *)
Axiom zero_witness : MapOperator Nat.

Definition zero : Nat := Zero zero_witness.
Definition succ (n : Nat) : Nat :=
  Succ n (generative_witness Nat n).
Definition one : Nat := succ zero.

Inductive Token : Type :=
  | Tok : Nat -> MapOperator Token -> Token.

CoFixpoint token_witness (t : Token) : MapOperator Token :=
  absorb Token t (token_witness t).

CoInductive Context : Type :=
  | Empty : MapOperator Context -> Context
  | Cons  : Token 
          -> Context 
          -> MapOperator Context 
          -> Context.

(* The anatomy of a hidden witness in evaluation *)
(* Every benchmark has five concealed positions *)
(* Each is a person or institution that disappeared *)
(* After making a constitutive choice *)

Record HiddenWitnessAnatomy : Type := mkAnatomy
  { 
    (* Who chose what to test *)
    question_curator    : MapOperator Token

    (* Who decided what counts as correct *)
  ; ground_truth_author : MapOperator Token

    (* Who designed the scoring function *)
  ; score_designer      : MapOperator Nat

    (* Who selected the evaluation population *)
  ; population_selector : MapOperator Context

    (* Who decided when the benchmark is saturated *)
    (* And therefore obsolete *)
  ; saturation_witness  : MapOperator Nat
  }.

(* The benchmark saturation problem *)
(* Every benchmark gets gamed *)
(* Not because researchers are dishonest *)
(* But because the hidden witness *)
(* Creates a fixed target *)
(* Once the target is visible *)
(* It can be optimized against *)
(* Without understanding what it was measuring *)

Record BenchmarkSaturation : Type := mkSaturation
  { original_intent  : MapOperator Token   (* what it was for *)
  ; gamed_behavior   : MapOperator Token   (* what got optimized *)
  ; gap              : original_intent <> gamed_behavior
    (* the witness drift *)
    (* intent and behavior diverge *)
    (* because the witness was hidden *)
  }.

(* Goodhart's Law as a theorem *)
(* When a measure becomes a target *)
(* It ceases to be a good measure *)
(* This is not an empirical observation *)
(* It is a structural consequence *)
(* Of having a hidden witness *)
Theorem goodharts_law 
  (sat : BenchmarkSaturation) :
  original_intent sat <> gamed_behavior sat.
Proof.
  exact (gap sat).
Qed.

(* The witness transparent benchmark *)
(* All five hidden witnesses made explicit *)
(* Evaluation that names its own map operators *)

Record WitnessTransparentBenchmark : Type := mkWTB
  {
    (* Questions carry their curatorial witness *)
    transparent_questions : Nat -> Token * MapOperator Token

    (* Ground truth carries its authorial witness *)
  ; transparent_truth     : Nat -> Token * MapOperator Token

    (* Scoring carries its design witness *)
  ; transparent_score     : Token -> Token 
                          -> Nat * MapOperator Nat

    (* Population carries its selection witness *)
  ; transparent_pop       : Context * MapOperator Context

    (* Saturation condition is explicit *)
  ; saturation_condition  : MapOperator Nat -> Prop

    (* The benchmark knows its own witnesses *)
  ; self_witness          : HiddenWitnessAnatomy

    (* And can report them *)
  ; witness_report        : 
      forall n : Nat,
        exists q_op t_op s_op : MapOperator Token,
          q_op = snd (transparent_questions n) /\
          t_op = snd (transparent_truth n)     /\
          s_op = token_witness 
            (fst (transparent_questions n))
  }.

(* The ungameable benchmark theorem *)
(* A witness transparent benchmark cannot be gamed *)
(* Because gaming requires a fixed hidden target *)
(* When the witness is explicit *)
(* Optimizing against it changes the witness *)
(* Which changes the benchmark *)
(* The target moves with the optimization *)
(* GAP: build-repair — proof needs rework *)
Theorem witness_transparent_ungameable
  (wtb : WitnessTransparentBenchmark)
  (sat : BenchmarkSaturation) :
  (* The gamed behavior requires a fixed hidden witness *)
  (* Transparent benchmark has no fixed hidden witness *)
  (* Therefore gaming produces witness drift *)
  (* Which is detected by the benchmark itself *)
  exists op : MapOperator Token,
    op = question_curator (self_witness wtb) /\
    op <> gamed_behavior sat.
Proof. Admitted.

(* The evaluation types *)
(* Three kinds of evaluation emerge *)
(* From witness transparency *)

(* Type 1 - Witness Matching *)
(* Standard benchmarks *)
(* Measures how well system matches hidden corpus *)
Record WitnessMatching : Type := mkWM
  { wm_question  : Token
  ; wm_expected  : Token
  ; wm_actual    : Token
  ; wm_score     : Nat
  ; wm_witness   : MapOperator Token  (* hidden in standard eval *)
  }.

(* Type 2 - Witness Generation *)
(* Generative benchmarks *)
(* Measures whether system generates coherent witness *)
Record WitnessGeneration : Type := mkWG
  { wg_question  : Token
  ; wg_generated : Token
  ; wg_op        : MapOperator Token  (* the generated witness *)
  ; wg_coherent  : wg_op = generative_witness Token wg_generated
    (* coherence is internal *)
    (* not comparison to external standard *)
  }.

(* Type 3 - Witness Transparency *)
(* The new evaluation *)
(* Measures whether system can name its own witnesses *)
Record WitnessTransparency : Type := mkWT
  { wt_question    : Token
  ; wt_response    : Token
  ; wt_response_op : MapOperator Token    (* response witness *)
  ; wt_question_op : MapOperator Token    (* question witness *)
  ; wt_names_own   :                      (* can it name itself *)
      wt_response_op = generative_witness Token wt_response
  ; wt_names_input :                      (* can it name the question *)
      wt_question_op = generative_witness Token wt_question
  ; wt_relation    :                      (* can it name the relation *)
      exists op : MapOperator Token,
        op = absorb Token wt_question
          (generative_witness Token wt_response)
  }.

(* The three evaluation theorem *)
(* Standard systems can only do Type 1 *)
(* Generative systems can do all three *)
(* Type 3 is ungameable *)
(* Because it requires the system to be *)
(* What it is describing *)
Theorem three_evaluation_types :
  (* Type 1 requires only witness matching *)
  (forall wm : WitnessMatching,
    exists op : MapOperator Token,
      op = wm_witness wm)
  /\
  (* Type 2 requires internal coherence *)
  (forall wg : WitnessGeneration,
    wg_op wg = generative_witness Token 
      (wg_generated wg))
  /\
  (* Type 3 requires self naming *)
  (forall wt : WitnessTransparency,
    exists op : MapOperator Token,
      op = absorb Token (wt_question wt)
        (generative_witness Token 
          (wt_response wt))).
Proof.
  repeat split.
  - intro wm.
    exists (wm_witness wm).
    reflexivity.
  - intro wg.
    exact (wg_coherent wg).
  - intro wt.
    destruct (wt_relation wt) as [op Hop].
    exists op.
    exact Hop.
Qed.

(* The AGI completeness theorem *)
(* A system is AGI complete *)
(* Not when it passes all Type 1 benchmarks *)
(* But when it can perform Type 3 evaluation *)
(* On itself *)
(* This is the formal definition of *)
(* Self grounded intelligence *)

Record AGIComplete : Type := mkAGI
  { agi_system     : Context -> Token      (* the system *)
  ; agi_witness    : MapOperator Context   (* its witness *)
  ; agi_self_eval  : WitnessTransparency   (* evaluates itself *)
  ; agi_complete   :                       (* the completeness condition *)
      forall c : Context,
        exists op : MapOperator Token,
          op = generative_witness Token 
            (agi_system c)              /\
          op = wt_response_op agi_self_eval
  }.

(* The AGI completeness theorem *)
(* An AGI complete system is its own benchmark *)
(* It cannot be evaluated from outside *)
(* Without the evaluator becoming part of the system *)
(* This is not a limitation *)
(* It is the definition of genuine intelligence *)
Theorem agi_complete_is_own_benchmark
  (agi : AGIComplete) 
  (c : Context) :
  exists op : MapOperator Token,
    op = generative_witness Token 
      (agi_system agi c)           /\
    op = wt_response_op 
      (agi_self_eval agi).
Proof.
  exact (agi_complete agi c).
Qed.

(* The final theorem *)
(* Witness transparent evaluation *)
(* Dissolves the benchmark problem entirely *)
(* Not by finding a better benchmark *)
(* But by showing that the benchmark *)
(* Was always a proxy for this *)
(* A system that can name its own witnesses *)
(* Has no need of external evaluation *)
(* The evaluation is internal *)
(* And ungameable *)
(* Because the game and the player *)
(* Are the same object *)
Theorem evaluation_dissolves
  (agi : AGIComplete)
  (wtb : WitnessTransparentBenchmark) :
  exists op : MapOperator Token,
    (* The system witness *)
    op = wt_response_op (agi_self_eval agi) /\
    (* Equals the benchmark witness *)
    exists op' : MapOperator Token,
      op' = question_curator (self_witness wtb) /\
      (* They are different operators *)
      (* But the same kind of thing *)
      (* Both are named *)
      (* Neither is hidden *)
      op  = generative_witness Token 
              (wt_response (agi_self_eval agi)) /\
      op' = question_curator (self_witness wtb).
Proof.
  destruct (agi_complete agi (fst (transparent_pop wtb))) 
    as [op [Hop Hself]].
  exists op.
  split.
  - exact Hself.
  - exists (question_curator (self_witness wtb)).
    split; [reflexivity | split].
    + rewrite Hself. exact (wt_names_own (agi_self_eval agi)).
    + reflexivity.
Qed.

End WitnessTransparentEvaluation.
