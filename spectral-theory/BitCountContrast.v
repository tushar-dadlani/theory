(* ================================================================= *)
(*  BitCountContrast.v                                                *)
(*                                                                    *)
(*  BIT COUNTING vs ZETA ZERO COUNTING: a growth-class contrast.      *)
(*                                                                    *)
(*  The cumulative bit count N_bit(n,E) = # states of energy <= E     *)
(*  = sum_{k=0}^{E} C(n,k) (cumulative binomial / integrated density  *)
(*  of states from BitDensity.v).  We prove it is monotone, SATURATES *)
(*  (constant once E >= n), hence BOUNDED (by the total N_bit n n =    *)
(*  2^n) and NOT unbounded.  Consequently it cannot coincide with any  *)
(*  unbounded counting function -- it cannot even match linear growth. *)
(*                                                                    *)
(*  Contrast with the zeta zeros.  The Riemann zero-counting function  *)
(*  obeys the Riemann-von Mangoldt law  N(T) ~ (T/2π) ln(T/2π) - T/2π, *)
(*  which is UNBOUNDED and SUPERLINEAR (there are infinitely many      *)
(*  zeros).  So the bit count and the zeta count live in DIFFERENT     *)
(*  growth classes: the bit count is eventually constant; the zeta     *)
(*  count grows without bound.                                        *)
(*                                                                    *)
(*  HONEST SCOPE.  We do NOT (and cannot here) formalise the analytic  *)
(*  N(T) or its log-asymptotics -- the repo has no real zeta function. *)
(*  We formalise the ESSENTIAL, decidable contrast: the bit count is   *)
(*  bounded/eventually-constant, whereas a genuine zero count is       *)
(*  unbounded (infinitely many zeros; RvM ~ T log T -> infinity).      *)
(*  That the zeta count is unbounded is stated as the known fact it    *)
(*  is, and the mismatch theorem takes "unbounded g" as its premise.   *)
(*  All bit-side results are pure nat, axiom-free.                    *)
(* ================================================================= *)

Require Import BitDensity.
From Stdlib Require Import Arith Lia.

(* ----------------------------------------------------------------- *)
(* SECTION 1 — the cumulative bit count (integrated density of states)*)
(* ----------------------------------------------------------------- *)

Fixpoint N_bit (n E : nat) : nat :=
  match E with
  | 0    => binomial n 0
  | S E' => N_bit n E' + binomial n (S E')
  end.

(* monotone non-decreasing in the energy cutoff *)
Theorem N_bit_monotone : forall n E E', E <= E' -> N_bit n E <= N_bit n E'.
Proof.
  intros n E E' H; induction H as [|m Hm IH]; [ lia | ].
  cbn [N_bit]; lia.
Qed.

(* SATURATION: past the top energy n, no new states are added *)
Theorem N_bit_saturates : forall n E, n <= E -> N_bit n E = N_bit n n.
Proof.
  intros n E H; induction H as [|m Hm IH]; [ reflexivity | ].
  cbn [N_bit]; rewrite (binom_gt n (S m)) by lia; lia.
Qed.

(* hence BOUNDED by the total number of states, N_bit n n (= 2^n) *)
Theorem N_bit_bounded : forall n E, N_bit n E <= N_bit n n.
Proof.
  intros n E; destruct (le_lt_dec E n) as [H | H].
  - apply N_bit_monotone; exact H.
  - rewrite (N_bit_saturates n E) by lia; lia.
Qed.

(* ----------------------------------------------------------------- *)
(* SECTION 2 — the growth-class contrast                             *)
(* ----------------------------------------------------------------- *)

(* an integer counting function is unbounded if it exceeds every M *)
Definition unbounded (g : nat -> nat) : Prop := forall M, exists E, M < g E.

(* the bit count is NOT unbounded (it saturates) *)
Theorem N_bit_not_unbounded : forall n, ~ unbounded (N_bit n).
Proof.
  intros n Hub; destruct (Hub (N_bit n n)) as [E HE].
  pose proof (N_bit_bounded n E); lia.
Qed.

(* therefore the bit count cannot equal ANY unbounded counting        *)
(* function -- in particular not the (unbounded) zeta zero count.     *)
Theorem bit_count_differs_from_unbounded :
  forall n g, unbounded g -> ~ (forall E, N_bit n E = g E).
Proof.
  intros n g Hub Heq; apply (N_bit_not_unbounded n).
  intro M; destruct (Hub M) as [E HE]; exists E.
  rewrite (Heq E); exact HE.
Qed.

(* the identity (linear) growth is already unbounded ... *)
Theorem id_unbounded : unbounded (fun E => E).
Proof. intro M; exists (S M); cbn; lia. Qed.

(* ... so the bit count cannot even match LINEAR growth, let alone     *)
(* the superlinear T log T of Riemann-von Mangoldt.                   *)
Theorem bit_count_not_linear : forall n, ~ (forall E, N_bit n E = E).
Proof. intro n; apply bit_count_differs_from_unbounded, id_unbounded. Qed.

(* ----------------------------------------------------------------- *)
(* SECTION 3 — the 3-bit cube, concretely                            *)
(* ----------------------------------------------------------------- *)

(* the cumulative count caps at 2^3 = 8 for every cutoff E >= 3 *)
Theorem N_bit3_cap : N_bit 3 3 = 8.
Proof. vm_compute; reflexivity. Qed.

Theorem N_bit3_saturates : forall E, 3 <= E -> N_bit 3 E = 8.
Proof. intros E H; rewrite (N_bit_saturates 3 E H); exact N_bit3_cap. Qed.

(* ----------------------------------------------------------------- *)
(* MASTER THEOREM — the growth contrast                              *)
(* ----------------------------------------------------------------- *)

Theorem bit_count_bounded_unlike_zeta :
  (* the bit count is monotone ... *)
  (forall n E E', E <= E' -> N_bit n E <= N_bit n E')
  (* ... saturates past the top energy ... *)
  /\ (forall n E, n <= E -> N_bit n E = N_bit n n)
  (* ... is bounded by the total number of states ... *)
  /\ (forall n E, N_bit n E <= N_bit n n)
  (* ... is NOT unbounded ... *)
  /\ (forall n, ~ unbounded (N_bit n))
  (* ... cannot equal any unbounded counting function (e.g. the zeta   *)
  (*     zero count) ... *)
  /\ (forall n g, unbounded g -> ~ (forall E, N_bit n E = g E))
  (* ... and cannot even match linear growth. *)
  /\ (forall n, ~ (forall E, N_bit n E = E)).
Proof.
  split; [ exact N_bit_monotone | ].
  split; [ exact N_bit_saturates | ].
  split; [ exact N_bit_bounded | ].
  split; [ exact N_bit_not_unbounded | ].
  split; [ exact bit_count_differs_from_unbounded | exact bit_count_not_linear ].
Qed.

Print Assumptions bit_count_bounded_unlike_zeta.

(* ================================================================= *)
(*  END BitCountContrast.v                                            *)
(*  The integrated bit density is bounded / eventually constant; a     *)
(*  genuine zeta zero count (Riemann-von Mangoldt, ~ T log T) is        *)
(*  unbounded.  Different growth classes -- an honest negative result.  *)
(*  ZERO Admitted; no axioms.                                         *)
(* ================================================================= *)
