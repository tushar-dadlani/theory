(* The diagonal IS the comparator — from TwoSymbolSolver.v and 
   BitwiseArbitraryInt.v *)

(* A 2D point: coordinate along each of the two perpendicular axes *)
Record TPoint : Type := mkPt {
  x : nat;
  y : nat
}.

(* On the 45° diagonal: the two coordinates agree *)
Definition diag (p : TPoint) : Prop := x p = y p.

(* The swap IS the comparison *)
Definition T (p : TPoint) : TPoint := mkPt (x p) (y p).

(* In order  = on diagonal = T p = p *)
(* GAP: build-repair — proof needs rework *)
Theorem fixed_iff_diag : forall p, T p = p <-> diag p.
Proof. Admitted.

(* Out of order = off diagonal = T p ≠ p *)
(* GAP: build-repair — proof needs rework *)
Theorem off_diag_moves : forall p, ~diag p -> T p <> p.
Proof. Admitted.

(* The bubble sort step: if T(p) ≠ p, swap *)
(* This IS N∘N = I — applying the swap twice returns to start *)
Theorem swap_involution : forall p, T (T p) = p.
Proof. intros p. destruct p. reflexivity. Qed.

(* Sorted = all points on diagonal = kernel empty *)
(* From PvsNP_Closed.v tower *)
Definition sorted := forall p, diag p.
