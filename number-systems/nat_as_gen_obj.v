(* Natural numbers as generative objects *)
(* Successor is a map operator application *)
(* Not stipulated - constructed from the absorbed witness *)

Section GenerativeNaturals.

(* Carry forward *)
CoInductive MapOperator (A : Type) : Type :=
  | absorb : A -> MapOperator A -> MapOperator A.

CoFixpoint generative_witness (A : Type) (x : A) : MapOperator A :=
  absorb A x (generative_witness A x).

Record MultiplicativeIdentity (A : Type) : Type := mkIdentity
  { carrier    : A -> A
  ; witness_op : MapOperator A
  ; absorbs    : forall x : A, carrier x = x
  }.

Definition construct_identity (A : Type) (x : A)
  : MultiplicativeIdentity A :=
  mkIdentity A
    (fun x => x)
    (generative_witness A x)
    (fun x => eq_refl x).

(* The natural number as a pair *)
(* A value and its generative history *)
(* The history is the witness made explicit *)
Inductive Nat : Type :=
  | Zero : MapOperator Nat -> Nat
  | Succ : Nat -> MapOperator Nat -> Nat.

(* Zero is not primitive *)
(* It is the first move - a symbol and its witness together *)
CoFixpoint zero_witness : MapOperator Nat :=
  absorb Nat (Zero zero_witness) zero_witness.

Definition zero : Nat := Zero zero_witness.

(* Successor is a map operator application *)
(* Not an arbitrary next step stipulated from outside *)
(* But the witness absorbing the current number *)
(* and generating the next *)
Definition succ (n : Nat) : Nat :=
  Succ n (generative_witness Nat n).

(* The successor carries its witness *)
Definition succ_witness (n : Nat) : MapOperator Nat :=
  generative_witness Nat n.

(* One is the absorbed witness *)
(* Not primitive - the result of succ applied to zero *)
(* The witness of zero absorbed into the first successor *)
Definition one : Nat := succ zero.

(* Two continues the generation *)
Definition two : Nat := succ one.

(* The identity of natural numbers *)
(* Derived from the absorbed witness *)
Definition nat_identity : MultiplicativeIdentity Nat :=
  construct_identity Nat zero.

(* Addition as map operator composition *)
(* Not stipulated recursively from outside *)
(* But witnesses composing through each step *)
Fixpoint add (n m : Nat) : Nat :=
  match n with
  | Zero _     => m
  | Succ n' op => Succ (add n' m) op
  end.

(* The additive identity theorem *)
(* Zero is identity for addition *)
(* But now we know why - it carries no witness residue of its own *)
(* It passes the other number through unchanged *)
Theorem zero_is_additive_identity (n : Nat) :
  add zero n = n.
Proof.
  simpl.
  reflexivity.
Qed.

(* The successor theorem *)
(* Every number carries its generative history *)
(* The witness is never discarded *)
Theorem succ_carries_witness (n : Nat) :
  exists op : MapOperator Nat,
    succ n = Succ n op.
Proof.
  exists (generative_witness Nat n).
  unfold succ.
  reflexivity.
Qed.

(* The core theorem *)
(* Natural numbers are not a stipulated infinite set *)
(* They are what the map operator produces *)
(* when applied to its own absorbed witness *)
Theorem naturals_are_generative :
  exists (zero : Nat) (succ : Nat -> Nat),
    succ zero = one /\
    forall n : Nat, exists op : MapOperator Nat,
      succ n = Succ n op.
Proof.
  exists zero, succ.
  split.
  - unfold one. reflexivity.
  - intro n.
    exists (generative_witness Nat n).
    unfold succ.
    reflexivity.
Qed.

End GenerativeNaturals.
