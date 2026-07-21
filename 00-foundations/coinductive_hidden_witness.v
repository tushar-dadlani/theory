(* Co-inductive hidden witness *)
(* The witness persists as an ongoing generative capacity *)

Section GenerativeWitness.

(* The co-inductive map operator *)
(* Unlike the inductive case, this never terminates *)
(* It keeps absorbing residue indefinitely *)
CoInductive MapOperator (A : Type) : Type :=
  | absorb : A -> MapOperator A -> MapOperator A.

(* The generative witness *)
(* Produces itself at each step - the witness is its own residue *)
CoFixpoint generative_witness (A : Type) (x : A) : MapOperator A :=
  absorb A x (generative_witness A x).

(* The symbol constructor *)
(* First move - creates a witness and a symbol simultaneously *)
Inductive Symbol (A : Type) : Type :=
  | mark : A -> MapOperator A -> Symbol A.

(* The first move *)
(* Creates the distinction that starts the system *)
Definition first_move (A : Type) (x : A) : Symbol A :=
  mark A x (generative_witness A x).

(* Minimization to 1 *)
(* The second step collapses the witness into the multiplicative identity *)
Definition minimize (A : Type) (s : Symbol A) : MapOperator A :=
  match s with
  | mark _ x op => op
  end.

(* One-step unfolding helper for the co-inductive map operator *)
Definition unfold_op (A : Type) (m : MapOperator A) : MapOperator A :=
  match m with absorb _ a b => absorb A a b end.
Lemma unfold_op_eq : forall (A : Type) (m : MapOperator A), m = unfold_op A m.
Proof. intros A m. destruct m. reflexivity. Qed.

(* The absorption theorem *)
(* The map operator absorbs its own witness at every step *)
(* This is the co-inductive proof obligation *)
Theorem map_absorbs_witness (A : Type) (x : A) :
  exists op : MapOperator A,
    op = absorb A x op.
Proof.
  exists (generative_witness A x).
  transitivity (unfold_op A (generative_witness A x)).
  - apply unfold_op_eq.
  - cbn. reflexivity.
Qed.

End GenerativeWitness.
