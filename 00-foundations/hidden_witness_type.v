(* The hidden witness as a type *)
(* A tautology is a proposition that is always true - 
   but "always true" requires a witness to that universality *)

Section HiddenWitness.

(* The map operator - makes the witness explicit *)
Definition map_operator (A : Prop) : Prop := A -> A.

(* This IS the tautology - but now the witness is named *)
(* The identity function is the hidden witness of classical logic *)
Definition witness (A : Prop) : map_operator A := fun x => x.

(* The residue - what the tautology absorbs *)
(* In classical logic this is hidden inside the law of excluded middle *)
Definition residue (A : Prop) : Prop := A \/ ~A.

(* The absorption - the witness absorbs the residue *)
(* This is what the equal sign was doing silently *)
Lemma witness_absorbs (A : Prop) (H : residue A) : map_operator A.
Proof.
  unfold map_operator.
  intro x.
  exact x.
Qed.

(* The hidden witness theorem *)
(* Every tautology conceals a map operator *)
Theorem tautology_has_hidden_witness (A : Prop) :
  map_operator A -> (A -> A).
Proof.
  unfold map_operator.
  intro H.
  exact H.
Qed.

End HiddenWitness.
