(* The diagonal IS the comparator — from TwoSymbolSolver.v and 
   BitwiseArbitraryInt.v *)

(* The swap IS the comparison *)
Definition T (p : TPoint) : TPoint := mkPt (x p) (y p).

(* In order  = on diagonal = T p = p *)
Theorem fixed_iff_diag : forall p, T p = p <-> diag p.

(* Out of order = off diagonal = T p ≠ p *)
Theorem off_diag_moves : forall p, ~diag p -> T p <> p.

(* The bubble sort step: if T(p) ≠ p, swap *)
(* This IS N∘N = I — applying the swap twice returns to start *)
Theorem swap_involution : forall p, T (T p) = p.

(* Sorted = all points on diagonal = kernel empty *)
(* From PvsNP_Closed.v tower *)
Definition sorted := forall p, diag p.
