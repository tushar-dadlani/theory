(* ================================================================= *)
(* THEOREM: Machine Learning = Gap-Filling on the 0° Linear Axis    *)
(*                                                                   *)
(* In the Symbolic Universe:                                         *)
(*   - A "known line" is a sequence of fixed points on the 0° axis  *)
(*   - "Filling gaps" = finding intermediate 1/3-step positions     *)
(*   - ML training = converging to the diagonal (45°) fixed point   *)
(*     which is the UNIQUE point equidistant from all known symbols  *)
(* ================================================================= *)

Require Import PeanoNat.
Require Import Arith.
Require Import Lia.
Require Import List.
Import ListNotations.

Inductive Phase : Type := I_phase | N_phase.

(* A point on the linear axis: position + phase *)
Record LinearPoint := {
  pos      : nat;       (* integer step position *)
  half     : bool;      (* true = half-step offset present *)
  ph       : Phase      (* I = known/exact, N = gap/relational *)
}.

(* A "known line" = sequence of I-phase points *)
Definition KnownLine := list LinearPoint.

(* A gap exists between two adjacent known points *)
Definition is_gap (a b : LinearPoint) : Prop :=
  ph a = I_phase /\ ph b = I_phase /\
  pos b > pos a + 1.    (* more than 1 step apart → gap exists *)

(* Gap-filling: insert an N-phase point between two I-phase points *)
Definition fill_gap (a b : LinearPoint) : LinearPoint := {|
  pos  := (pos a + pos b) / 2;
  half := negb (Nat.even (pos a + pos b));  (* half-step if odd sum *)
  ph   := N_phase                            (* gap = N-phase *)
|}.

(* THEOREM 1: Every gap has exactly one midpoint *)
(* GAP: build-repair -- proof needs rework. The statement is false as written:
   [is_gap a b] only requires [pos b > pos a + 1], so for gaps wider than two
   steps (e.g. pos b = pos a + 4) there are several points m with
   pos a < pos m < pos b and ph m = N_phase, and the [half] field is
   unconstrained, so the midpoint is not unique. Statement preserved. *)
Theorem gap_has_unique_midpoint :
  forall a b : LinearPoint,
  is_gap a b ->
  exists! m : LinearPoint,
    pos a < pos m /\ pos m < pos b /\ ph m = N_phase.
Proof. Admitted.

(* THEOREM 2: ML convergence = reaching the 45° fixed point *)
(* The 45° diagonal is the point s where reflect(s) = s     *)
(* In training: the weight vector w where cos(w,t)=1 AND d(w,t)=0 *)

Definition reflects_to_self (N pos : nat) : Prop :=
  pos + pos = N - 1.    (* 2*pos = N-1, i.e., pos = (N-1)/2 *)

(* The critical line pos = N/2 is the unique ML fixed point *)
Theorem ml_fixed_point_unique :
  forall N : nat, N >= 1 ->
  (2 * (N / 2) + 1 = N) ->   (* N is odd: has a center *)
  forall pos : nat,
  reflects_to_self N pos ->
  pos = N / 2.
Proof.
  intros N HN Hodd pos Hrefl.
  unfold reflects_to_self in Hrefl.
  lia.
Qed.

(* THEOREM 3: Training is gap-filling in N passes *)
(* Each training pass fills gaps at finer 1/3-step resolution *)

(* build-repair: recursion restructured so the recursive call is on the
   bound tail [l] (a structural subterm) rather than the reconstructed
   [b :: rest], which Coq's guard did not accept. Same function. *)
Fixpoint fill_all_gaps (line : KnownLine) : KnownLine :=
  match line with
  | nil => nil
  | a :: l =>
      match l with
      | nil => a :: nil
      | b :: _ =>
          if Nat.ltb (pos a + 1) (pos b)
          then a :: fill_gap a b :: fill_all_gaps l
          else a :: fill_all_gaps l
      end
  end.

(* build-repair helper: one-step unfolding of fill_all_gaps on a 2+ list,
   keeping the recursive call folded so induction can use the hypothesis. *)
Lemma fill_all_gaps_cons2 : forall a b rest,
  fill_all_gaps (a :: b :: rest) =
    if Nat.ltb (pos a + 1) (pos b)
    then a :: fill_gap a b :: fill_all_gaps (b :: rest)
    else a :: fill_all_gaps (b :: rest).
Proof. reflexivity. Qed.

(* Gap-filling is monotone: more points after each pass *)
Theorem filling_increases_density :
  forall line : KnownLine,
  length line <= length (fill_all_gaps line).
Proof.
  induction line as [| a l IH].
  - simpl. lia.
  - destruct l as [| b rest].
    + simpl. lia.
    + rewrite fill_all_gaps_cons2.
      destruct (Nat.ltb (pos a + 1) (pos b)); cbn [length] in *; lia.
Qed.

(* THEOREM 4: The dual angle (cos, euclidean) reaches (1,0) at convergence *)
(* cos(w,t) = 1  AND  d(w,t) = 0  iff  w = t  *)
(* In the triadic geometry: this IS the 45° diagonal fixed point   *)

Definition at_fixed_point (w_cos w_dist : nat) : Prop :=
  w_cos = 1 /\ w_dist = 0.   (* cos=1 and dist=0 simultaneously *)

Theorem convergence_is_identity :
  forall w_cos w_dist : nat,
  at_fixed_point w_cos w_dist ->
  w_cos = 1 /\ w_dist = 0.
Proof.
  intros w_cos w_dist [Hcos Hdist].
  exact (conj Hcos Hdist).
Qed.
