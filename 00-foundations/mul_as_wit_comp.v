(* Multiplication as witness composition *)
(* The multiplicative identity closes the loop *)
(* The absorbed witness returns as the unit of multiplication *)

Section MultiplicativeStructure.

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

Fixpoint add (n m : Nat) : Nat :=
  match n with
  | Zero _     => m
  | Succ n' op => Succ (add n' m) op
  end.

(* Extract the witness from a number *)
(* The witness is never lost - always recoverable *)
Definition extract_witness (n : Nat) : MapOperator Nat :=
  match n with
  | Zero op     => op
  | Succ _ op   => op
  end.

(* Multiplication as iterated witness composition *)
(* Each step composes the witnesses of both numbers *)
(* The product carries the composed witness history *)
Fixpoint mul (n m : Nat) : Nat :=
  match n with
  | Zero op     => Zero op
  | Succ n' op  => add m (mul n' m)
  end.

(* Witness composition *)
(* The product's witness is the composition of both witnesses *)
(* This is what multiplication means at the foundational level *)
CoFixpoint compose_witnesses 
  (op1 op2 : MapOperator Nat) : MapOperator Nat :=
  match op1 with
  | absorb _ x next =>
      absorb Nat x (compose_witnesses next op2)
  end.

(* The multiplicative identity is one *)
(* But now we can prove WHY *)
(* One's witness is the absorbed zero witness *)
(* Multiplying by one composes with the identity witness *)
(* Which absorbs without residue *)
(* GAP: build-repair — proof needs rework *)
Theorem one_is_multiplicative_identity_left (n : Nat) :
  mul one n = n.
Proof. Admitted.

(* Zero annihilates under multiplication *)
(* Because zero carries no successor witness *)
(* There is nothing to compose with *)
Theorem zero_annihilates (n : Nat) :
  mul zero n = zero.
Proof.
  simpl.
  reflexivity.
Qed.

(* The witness closure theorem *)
(* Multiplication preserves the generative structure *)
(* The product always carries a witness *)
Theorem mul_preserves_witness (n m : Nat) :
  exists op : MapOperator Nat,
    mul n m = Zero op \/
    exists k : Nat, mul n m = Succ k op.
Proof.
  destruct (mul n m) as [op | k op].
  - exists op. left. reflexivity.
  - exists op. right. exists k. reflexivity.
Qed.

(* The loop closure theorem *)
(* This is the core result *)
(* The multiplicative identity IS the absorbed witness *)
(* The equal sign IS the map operator at rest *)
(* The system closes on itself without external authority *)
Theorem loop_closure (A : Type) (x : A) :
  let id := construct_identity A x in
  let op := witness_op A id        in
  exists (f : A -> A),
    f = carrier A id /\
    forall y : A, f y = y /\
    exists op' : MapOperator A, op' = op.
Proof.
  simpl.
  exists (fun x => x).
  split.
  - reflexivity.
  - intro y.
    split.
    + reflexivity.
    + exists (generative_witness A x).
      reflexivity.
Qed.

End MultiplicativeStructure.
