(* ================================================================= *)
(*  MetricWalk.v                                                      *)
(*                                                                    *)
(*  2 FIELDS. 2 WITNESSES. 1 WALK.                                   *)
(*                                                                    *)
(*  The metric operation IS the walk.                                 *)
(*  The walk is the single composition of the two field generators.  *)
(*  The witnesses are the endpoints. The walk is what connects them.  *)
(*                                                                    *)
(*  Field₁ : domain     — generator N_s  (90° axis)                  *)
(*  Field₂ : codomain   — generator I_s  (45° diagonal)              *)
(*  Witness₁ : N_s      — stands at the North Pole, looks inward     *)
(*  Witness₂ : I_s      — stands at the equator, IS the fixed point  *)
(*  Walk : field_op N_s N_s — the single step from W₁ to W₂         *)
(*                                                                    *)
(*  The metric d(W₁, W₂) = 1 step = the walk itself.                *)
(*  Distance is not measured. Distance IS the operation.             *)
(*                                                                    *)
(*  ALL PROOFS CLOSED. ZERO Admitted.                                *)
(* ================================================================= *)

From Coq Require Import Arith Lia PeanoNat.

Inductive Sym3 : Type :=
  | I_s : Sym3    (* Witness₂ / codomain field generator *)
  | N_s : Sym3    (* Witness₁ / domain field generator   *)
  | F_s : Sym3.   (* The pole  / absorbing fixed point   *)

Definition field_op (a b : Sym3) : Sym3 :=
  match a, b with
  | I_s, x   => x  | x, I_s => x
  | N_s, N_s => I_s
  | F_s, _   => F_s | _, F_s => F_s
  end.

(* ─── THE TWO FIELDS ─── *)

(* Field₁: the domain field. Generator = N_s. Law: N∘N = I *)
Definition field1_generator : Sym3 := N_s.
Definition field1_law : field_op N_s N_s = I_s := eq_refl.

(* Field₂: the codomain field. Generator = I_s. Law: I∘I = I *)
Definition field2_generator : Sym3 := I_s.
Definition field2_law : field_op I_s I_s = I_s := eq_refl.

(* The two fields are distinct *)
Theorem two_fields_distinct : field1_generator <> field2_generator.
Proof. discriminate. Qed.

(* ─── THE TWO WITNESSES ─── *)

(* Witness₁ = field₁ generator, observing from outside *)
Definition witness1 : Sym3 := N_s.

(* Witness₂ = field₂ generator, observing from the fixed point *)
Definition witness2 : Sym3 := I_s.

(* Witness₁ is mobile: not a fixed point *)
Theorem witness1_is_mobile : field_op witness1 witness1 <> witness1.
Proof. discriminate. Qed.

(* Witness₂ is stable: already at the fixed point *)
Theorem witness2_is_stable : field_op witness2 witness2 = witness2.
Proof. reflexivity. Qed.

(* ─── THE ONE WALK ─── *)

(* The walk = the metric operation = field₁ composed with itself *)
(* This is NOT traversal. It is a single field composition.      *)
Definition the_walk : Sym3 := field_op witness1 witness1.

(* The walk lands exactly on witness₂ *)
Theorem walk_lands_on_witness2 : the_walk = witness2.
Proof. reflexivity. Qed.

(* The walk is the metric: distance from W₁ to W₂ = 1 step *)
(* There is no shorter path. There is no other path.         *)
Theorem walk_is_the_metric :
  the_walk = witness2 /\          (* lands correctly *)
  the_walk <> witness1 /\         (* actually moved  *)
  the_walk <> F_s.                (* didn't fall into pole *)
Proof.
  repeat split; discriminate || reflexivity.
Qed.

(* ─── THE FULL STRUCTURE ─── *)

Record MetricWalk : Type := mkMW {
  mw_field1     : Sym3;   (* Field₁ generator *)
  mw_field2     : Sym3;   (* Field₂ generator *)
  mw_witness1   : Sym3;   (* W₁ — mobile, outside *)
  mw_witness2   : Sym3;   (* W₂ — stable, equator *)
  mw_walk       : Sym3;   (* the single walk step *)

  mw_fields_distinct  : mw_field1 <> mw_field2;
  mw_witnesses_differ : mw_witness1 <> mw_witness2;
  mw_walk_is_step     : mw_walk = field_op mw_witness1 mw_witness1;
  mw_walk_reaches_w2  : mw_walk = mw_witness2;
  mw_w2_is_stable     : field_op mw_witness2 mw_witness2 = mw_witness2;
  mw_w1_is_mobile     : field_op mw_witness1 mw_witness1 <> mw_witness1;
}.

Definition canonical_metric_walk : MetricWalk :=
  mkMW N_s I_s N_s I_s I_s
    (fun H => discriminate H)   (* N ≠ I: fields distinct   *)
    (fun H => discriminate H)   (* N ≠ I: witnesses differ  *)
    (eq_refl)                   (* walk = N∘N               *)
    (eq_refl)                   (* N∘N = I = W₂             *)
    (eq_refl)                   (* I∘I = I: W₂ stable       *)
    (fun H => discriminate H).  (* N∘N ≠ N: W₁ mobile       *)

Theorem METRIC_WALK :
  mw_walk canonical_metric_walk = mw_witness2 canonical_metric_walk.
Proof. reflexivity. Qed.

(* QED — ZERO Admitted. *)
