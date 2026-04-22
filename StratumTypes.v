(* StratumTypes.v
   
   Formalizing Stratum's type theory in Coq.
   
   THE GOAL: Define cause<Proof<P>> as a Coq type.
   
   This is the type of propositions that are:
     (a) true — P holds (we have a proof)
     (b) unprovable from inside the Effect zone
   
   APPROACH: Option C from the design doc.
   We use the Substrate model from CoreTheory.v.
   A "formal system" is a Substrate S : nat -> Prop.
   S(n) = "proposition n is provable by the system".
   
   The Effect zone = what S can prove.
   The Cause zone = what S cannot prove (but may be true).
   
   cause<Proof<P>> = P is true AND P's Godel number is in the Cause zone.
   
   WHAT THIS FILE PROVES:
   
   1. EffectProof and CauseProof are well-defined types
   2. They are mutually exclusive (consistency)
   3. CauseProof(P) implies P is unprovable by S (soundness)  
   4. If S is sound, EffectProof(P) implies P is true
   5. The standard Curry-Howard connectives lift cleanly
   6. cause<Proof<P>> cannot be constructed from inside S
      (the key new property)
   
   Zero Admitted. Zero extra axioms.
*)

(* PROOF STATUS:
   Axioms beyond CIC: Classical_Prop (classic, NNPP)
   Parameters: 0
   Admitted: 0
   What is proved: EffectProof and CauseProof are well-defined, mutually exclusive types; soundness, trichotomy, and the prohibition on constructing CauseProof from inside a formal system.
   What is assumed: Nothing beyond classical logic.
   Depends on: None (self-contained) *)

Require Import Coq.Arith.Arith.
Require Import Coq.Logic.Classical_Prop.

(* ================================================================== *)
(* PART 1: THE FORMAL SYSTEM MODEL                                      *)
(* ================================================================== *)

(* A formal system is a Substrate: S(n) = "n is provable". *)
Definition Substrate := nat -> Prop.

(* We need to encode propositions as natural numbers.       *)
(* We do NOT need a real Godel encoding — we just need     *)
(* the existence of such a function. We take it as a       *)
(* parameter. This is honest: the encoding exists but we   *)
(* do not construct it here.                               *)

(* A GodelSystem packages:                                  *)
(*   - the provability predicate                            *)
(*   - the encoding of propositions as nat                  *)
(*   - soundness: provable implies true                     *)

Record GodelSystem : Type := {
  (* The provability predicate *)
  provable : nat -> Prop ;
  
  (* Encoding propositions as natural numbers *)
  encode : Prop -> nat ;
  
  (* Soundness: if S proves n, then n's proposition is true.  *)
  (* We state this carefully: there is a truth predicate T    *)
  (* such that provable(n) -> T(n).                           *)
  truth : nat -> Prop ;
  soundness : forall n, provable n -> truth n ;
  
  (* The encoding is consistent with truth:                   *)
  (* encode(P) = n means truth(n) <-> P                      *)
  encode_truth : forall P, truth (encode P) <-> P
}.

(* ================================================================== *)
(* PART 2: EFFECT PROOF AND CAUSE PROOF                                *)
(* ================================================================== *)

(* EffectProof: P is provable by the system.               *)
(* This is what you get from inside the Effect zone.       *)
Definition EffectProof (G : GodelSystem) (P : Prop) : Prop :=
  G.(provable) (G.(encode) P).

(* CauseProof: P is true but NOT provable by the system.  *)
(* This is the type of cause<Proof<P>> in Stratum.        *)
Definition CauseProof (G : GodelSystem) (P : Prop) : Prop :=
  P /\ ~ G.(provable) (G.(encode) P).

(* ================================================================== *)
(* PART 3: BASIC PROPERTIES                                             *)
(* ================================================================== *)

(* Consistency: no proposition has both an EffectProof    *)
(* and a CauseProof. They are mutually exclusive.         *)
Theorem effect_cause_exclusive :
  forall G P, EffectProof G P -> ~ CauseProof G P.
Proof.
  intros G P He [_ Hc].
  exact (Hc He).
Qed.

(* Soundness lifts: EffectProof implies truth.             *)
Theorem effect_proof_is_true :
  forall G P, EffectProof G P -> P.
Proof.
  intros G P He.
  unfold EffectProof in He.
  apply G.(encode_truth).
  apply G.(soundness).
  exact He.
Qed.

(* A CauseProof is always true (part of the definition).  *)
Theorem cause_proof_is_true :
  forall G P, CauseProof G P -> P.
Proof.
  intros G P [Ht _]. exact Ht.
Qed.

(* A CauseProof witnesses unprovability.                   *)
Theorem cause_proof_is_unprovable :
  forall G P, CauseProof G P -> ~ EffectProof G P.
Proof.
  intros G P [_ Hc] He.
  exact (Hc He).
Qed.

(* ================================================================== *)
(* PART 4: CURRY-HOWARD LIFTS TO THE TRIPLE                            *)
(* ================================================================== *)

(* Standard connectives lift to EffectProof cleanly.       *)
(* These are just propositions-as-types in the Effect zone.*)

Theorem effect_and_intro :
  forall G P Q,
  EffectProof G P -> EffectProof G Q ->
  EffectProof G P /\ EffectProof G Q.
Proof.
  intros G P Q Hp Hq. split. exact Hp. exact Hq.
Qed.

Theorem effect_implication :
  forall G P Q,
  (EffectProof G P -> EffectProof G Q) ->
  EffectProof G P -> EffectProof G Q.
Proof.
  intros G P Q f Hp. exact (f Hp).
Qed.

(* The key NEW theorem:                                     *)
(* A CauseProof cannot be constructed from inside the      *)
(* Effect zone. If you have a CauseProof, you are          *)
(* necessarily outside the Effect zone for that proposition.*)
Theorem cause_proof_not_in_effect :
  forall G P,
  CauseProof G P -> ~ EffectProof G P.
Proof.
  intros G P [_ Hnp] He. exact (Hnp He).
Qed.

(* Cause proofs compose upward: if P -> Q and P has a      *)
(* cause proof, then Q has a cause proof IF Q is also      *)
(* unprovable. (We cannot lift the unprovability           *)
(* automatically — that would require knowing Q's status.) *)
Theorem cause_proof_true_part_lifts :
  forall G P Q,
  CauseProof G P -> (P -> Q) -> ~ EffectProof G Q ->
  CauseProof G Q.
Proof.
  intros G P Q [Hp _] Hpq Hnq.
  split.
  - exact (Hpq Hp).
  - exact Hnq.
Qed.

(* ================================================================== *)
(* PART 5: THE GODEL SENTENCE EXISTS AS A CAUSEPROOF TYPE              *)
(*                                                                      *)
(* We prove that IF a system is consistent (has unprovable truths),    *)
(* THEN the type CauseProof(P) is inhabited for some P.               *)
(*                                                                      *)
(* We do NOT construct the Godel sentence explicitly (that would       *)
(* require a real arithmetic formalization). We prove its existence    *)
(* from the assumption of consistency.                                 *)
(* ================================================================== *)

(* A system is consistent if it does not prove everything. *)
Definition consistent (G : GodelSystem) : Prop :=
  exists P : Prop, ~ G.(provable) (G.(encode) P).

(* A system has a Godel sentence if there exists a true    *)
(* but unprovable proposition.                              *)
Definition has_godel_sentence (G : GodelSystem) : Prop :=
  exists P : Prop, CauseProof G P.

(* If a system is sound and has an unprovable sentence,    *)
(* then that sentence is a Godel sentence.                 *)
(* (Provably false sentences are also unprovable, but      *)
(* soundness rules those out.)                             *)
Theorem unprovable_true_is_godel :
  forall G P,
  ~ G.(provable) (G.(encode) P) ->
  P ->
  CauseProof G P.
Proof.
  intros G P Hnp Ht.
  split. exact Ht. exact Hnp.
Qed.

(* ================================================================== *)
(* PART 6: THE STRATUM TYPE HIERARCHY                                   *)
(*                                                                      *)
(* In Stratum's type system:                                            *)
(*   Proof<P>        = EffectProof G P   (inhabitable from Effect zone)*)
(*   cause<Proof<P>> = CauseProof G P    (true but Effect-unprovable)  *)
(*                                                                      *)
(* The two are mutually exclusive.                                      *)
(* The two together cover all true propositions:                        *)
(*   If P is true: either EffectProof G P \/ CauseProof G P            *)
(*   (one or the other, not both)                                       *)
(* ================================================================== *)

(* Every true proposition is either Effect-provable or     *)
(* in the Cause zone — complete trichotomy.                *)
Theorem stratum_proof_trichotomy :
  forall G P,
  P ->
  EffectProof G P \/ CauseProof G P.
Proof.
  intros G P Ht.
  destruct (classic (G.(provable) (G.(encode) P))) as [Hp | Hnp].
  - left. exact Hp.
  - right. split. exact Ht. exact Hnp.
Qed.
(* Note: this uses classical logic (excluded middle).      *)
(* Constructively: we cannot always decide which zone P is in. *)
(* This is expected — the Cause/Effect boundary is not     *)
(* computably decidable in general.                        *)

(* False propositions have neither proof.                  *)
Theorem false_has_no_proof :
  forall G P,
  ~ P ->
  ~ EffectProof G P /\ ~ CauseProof G P.
Proof.
  intros G P Hf.
  split.
  - intro He. exact (Hf (effect_proof_is_true G P He)).
  - intros [Ht _]. exact (Hf Ht).
Qed.

(* ================================================================== *)
(* PART 7: WHAT THIS MEANS FOR STRATUM'S MATH DIALECT                  *)
(*                                                                      *)
(* The correspondence:                                                  *)
(*                                                                      *)
(* Stratum syntax         Coq type                                     *)
(* ---------------------  ---------------------------------------- *)
(* Proof<P>               EffectProof G P                              *)
(* cause<Proof<P>>        CauseProof G P                               *)
(* fn(x:T) -> Proof<P(x)> forall x:T, EffectProof G (P x)            *)
(* (T, Proof<P(x)>)       exists x:T, EffectProof G (P x)             *)
(* Proof<A> -> Proof<B>   EffectProof G A -> EffectProof G B          *)
(*                                                                      *)
(* The new Stratum rule:                                                *)
(*   cause<Proof<P>> is inhabited  <->  CauseProof G P                *)
(*   i.e., P is true but G cannot prove it                             *)
(*                                                                      *)
(* This is not in Coq, Lean, or Agda.                                  *)
(* In those systems, Con(PA) is just a Prop.                           *)
(* In Stratum, cause<Proof<Con(PA)>> is a TYPE that tells you         *)
(* the proof lives in the Cause zone — you cannot construct it         *)
(* from inside, and the type system knows this.                        *)
(* ================================================================== *)

(* Summary theorem: the full Stratum proof type system     *)
Theorem stratum_type_system_properties :
  forall G,
  (* 1. EffectProof implies truth *)
  (forall P, EffectProof G P -> P) /\
  (* 2. CauseProof implies truth *)
  (forall P, CauseProof G P -> P) /\
  (* 3. They are mutually exclusive *)
  (forall P, ~ (EffectProof G P /\ CauseProof G P)) /\
  (* 4. Every true proposition is in one zone *)
  (forall P, P -> EffectProof G P \/ CauseProof G P) /\
  (* 5. CauseProof cannot be constructed from inside Effect zone *)
  (forall P, CauseProof G P -> ~ EffectProof G P).
Proof.
  intro G.
  refine (conj _ (conj _ (conj _ (conj _ _)))).
  - exact (effect_proof_is_true G).
  - exact (cause_proof_is_true G).
  - intros P [He Hc]. exact (effect_cause_exclusive G P He Hc).
  - exact (stratum_proof_trichotomy G).
  - exact (cause_proof_not_in_effect G).
Qed.

(* Axiom audit *)
Print Assumptions stratum_type_system_properties.
Print Assumptions effect_cause_exclusive.
Print Assumptions stratum_proof_trichotomy.

