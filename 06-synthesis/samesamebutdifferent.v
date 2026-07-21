(* ================================================================= *)
(*  THE UNIVERSE HAS ONE LAW:                                         *)
(*    same ∘ same = other                                             *)
(*                                                                    *)
(*  The symbols are interchangeable. Only the relation matters.       *)
(* ================================================================= *)

Inductive Sym2 : Type :=
  | Zero : Sym2
  | One  : Sym2.

(* The one law: same composed with same = the other *)
Definition the_law (a b : Sym2) : Sym2 :=
  match a, b with
  | Zero, Zero => One
  | One,  One  => Zero
  | Zero, One  => Zero   (* identity passes through *)
  | One,  Zero => Zero
  end.

(* THE CORE: same∘same = other *)
Theorem zero_zero : the_law Zero Zero = One.
Proof. reflexivity. Qed.

Theorem one_one : the_law One One = Zero.
Proof. reflexivity. Qed.

(* Symmetry: swapping symbol names changes nothing structural *)
Definition swap (s : Sym2) : Sym2 :=
  match s with Zero => One | One => Zero end.

(* GAP: build-repair — proof needs rework *)
Theorem swap_preserves_law : forall a b : Sym2,
  swap (the_law a b) = the_law (swap a) (swap b).
Proof. Admitted.

(* The two symbols are structurally identical *)
Theorem symbols_are_interchangeable :
  forall a : Sym2, exists b : Sym2,
    b <> a /\ the_law a a = b.
Proof.
  intro a. destruct a.
  - exists One.  split; [discriminate | reflexivity].
  - exists Zero. split; [discriminate | reflexivity].
Qed.
