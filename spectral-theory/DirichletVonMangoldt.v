(* ================================================================= *)
(*  DirichletVonMangoldt.v                                           *)
(*                                                                    *)
(*  THE VON MANGOLDT IDENTITY, multiplicative form:                   *)
(*        ∏_{d ∣ n} vexp(d) = n,                                      *)
(*  where vexp = exp∘Λ is the "exponential of von Mangoldt":          *)
(*        vexp(p^k) = p  (k ≥ 1),   vexp(n) = 1 otherwise.            *)
(*                                                                    *)
(*  This is the additive identity  Σ_{d∣n} Λ(d) = log n  with `log`    *)
(*  stripped by exponentiation — the honest content over ℤ/ℕ (no      *)
(*  transcendental `log`).  vexp is defined *computably* (least prime  *)
(*  factor + strip), and the identity is VALIDATED BY REFLECTION for   *)
(*  n ≤ 100.  (The fully general proof reduces to unique              *)
(*  factorization / prime-power peeling; this file follows the repo's  *)
(*  own reflective pattern, cf. JacobiRHS.jacobi_upto.)  AXIOM-FREE.  *)
(* ================================================================= *)

From Stdlib Require Import Arith Lia List.
Import ListNotations.
Require Import Totient.

(* strip all factors of p out of n (fuel-bounded) *)
Fixpoint strip (fuel n p : nat) : nat :=
  match fuel with
  | O => n
  | S f => if (n mod p =? 0)%nat then strip f (n / p) p else n
  end.

(* least divisor ≥ 2 of n (= least prime factor); n itself if none *)
Definition least_factor (n : nat) : nat :=
  match find (fun d => (n mod d =? 0)%nat) (seq 2 (n - 1)) with
  | Some d => d
  | None => n
  end.

(* vexp n = exp(Λ(n)):  the base prime if n is a prime power, else 1 *)
Definition vexp (n : nat) : nat :=
  if (n <=? 1)%nat then 1
  else let p := least_factor n in
       if (strip n n p =? 1)%nat then p else 1.

(* product of f over a list *)
Definition prodf (l : list nat) (f : nat -> nat) : nat :=
  fold_right (fun k acc => f k * acc) 1 l.

(* ∏_{d∣n} vexp(d) *)
Definition vmprod (n : nat) : nat := prodf (divisors n) vexp.

(* the reflective check:  ∏_{d∣n} vexp(d) = n  for 1 ≤ n ≤ N *)
Definition vm_check (N : nat) : bool :=
  forallb (fun n => (vmprod n =? n)%nat) (seq 1 N).

(* sanity samples *)
Example vexp_8  : vexp 8  = 2. Proof. reflexivity. Qed.   (* 8 = 2^3      *)
Example vexp_12 : vexp 12 = 1. Proof. reflexivity. Qed.   (* 12 = 2^2·3   *)
Example vexp_1  : vexp 1  = 1. Proof. reflexivity. Qed.
Example vmprod_12 : vmprod 12 = 12. Proof. reflexivity. Qed.

(* VALIDATION: ∏_{d∣n} vexp(d) = n for all n ≤ 100 *)
Theorem vonmangoldt_upto : vm_check 100 = true.
Proof. vm_compute; reflexivity. Qed.

Print Assumptions vonmangoldt_upto.

(* ================================================================= *)
(*  END DirichletVonMangoldt.v                                       *)
(*  The multiplicative von Mangoldt identity ∏_{d∣n} vexp(d) = n,      *)
(*  with vexp = exp∘Λ defined computably, validated by reflection for  *)
(*  n ≤ 100.  Closed under the global context (axiom-free).           *)
(* ================================================================= *)
