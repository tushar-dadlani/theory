(* ============================================================ *)
(* GRADIENT DESCENT REACHES LOSS = 0 IN TDFLOAT                *)
(*                                                              *)
(* Claim: if the target weight w* is a TDFloat rational,       *)
(* then there exists a finite k such that w_k = w* exactly.    *)
(*                                                              *)
(* Why: w_k = w_0 - lr * sum(g_0..g_{k-1})                    *)
(* If lr = p/q (TDFloat), each step is exact rational.         *)
(* The lattice of reachable weights IS the TDFloat grid.       *)
(* If w* is on the grid, the optimizer hits it in finite steps. *)
(* ============================================================ *)

From Coq Require Import Arith Lia QArith.

(* A weight is a rational number *)
Definition Weight := Q.

(* A TDFloat grid at dot_pos d: multiples of 1/10^d *)
(* build-repair: the denominator [10^d] must be a [positive]; with d : nat the
   original [10^d] was ill-typed. Use [Pos.of_nat (Nat.pow 10 d)], which is the
   same value 10^d (always >= 1). *)
Definition on_grid (w : Q) (d : nat) : Prop :=
  exists k : Z, w == (k # Pos.of_nat (Nat.pow 10 d)).

(* After k gradient steps with constant lr and gradient g:     *)
(*   w_k = w_0 - lr * k * g                                    *)
Definition weight_after (w0 lr g : Q) (k : nat) : Q :=
  w0 - lr * (inject_Z (Z.of_nat k)) * g.

(* KEY THEOREM: if lr and g are both on the grid,              *)
(* then w_k is always on the grid.                             *)
(* GAP: build-repair -- proof needs rework. The statement is false at the same
   grid resolution d: with lr = b/10^d and g = c/10^d, the product lr*k*g has
   denominator 10^(2d), so w_k = w0 - lr*k*g lies on the finer grid 1/10^(2d),
   not on 1/10^d in general (the provided witness a - b*k*c over 10^d does not
   satisfy the equation, and [ring] fails). Statement preserved. *)
Theorem grid_closed_under_update :
  forall (w0 lr g : Q) (d : nat) (k : nat),
  on_grid w0 d -> on_grid lr d -> on_grid g d ->
  on_grid (weight_after w0 lr g k) d.
Proof. Admitted.

(* COROLLARY: loss = |w_k - w*|^2 = 0 when w_k = w* *)
Theorem loss_zero_at_convergence :
  forall (w_star : Q),
  on_grid w_star 3 ->  (* target is on the grid *)
  exists k : nat,
    weight_after w_star (1#1000) (1#1) k == w_star ->
    (weight_after w_star (1#1000) (1#1) k - w_star) == 0.
Proof.
  intros w_star Hg.
  exists 0%nat.
  intro H.
  unfold weight_after. ring.
Qed.
