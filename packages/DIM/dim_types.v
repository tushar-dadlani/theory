(** * DIM Types
    Primitive types of the Delegatable Identity Machine.
    Updated: fixed imports for Rocq/Coq 8.18+ stdlib paths. *)

From Stdlib Require Import List.
From Stdlib Require Import Nat.
From Stdlib Require Import Bool.
Open Scope list_scope.

Parameter Data : Type.
Definition Hash := nat.

Parameter PublicKey  : Type.
Parameter PrivateKey : Type.
Parameter Signature  : Type.
Parameter KeyPair : PublicKey -> PrivateKey -> Prop.

Definition Timestamp := nat.
Definition State     := nat.

(** Cost model: every cryptographic operation has a unit cost.
    We model cost as a natural number (abstract "steps"). *)
Definition Cost := nat.

Definition cost_hash  : Cost := 1.
Definition cost_sign  : Cost := 1.
Definition cost_verify : Cost := 1.
