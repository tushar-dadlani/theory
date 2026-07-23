(* ================================================================= *)
(*  SelfPowerFixedCount.v                                            *)
(*                                                                    *)
(*  COUNTING the fixed points of the self-power map  x |-> x^x mod p  *)
(*  on the units of F_p.  `SelfPowerDynamics` characterised them as    *)
(*      selfpow p x = x   <=>   ord(x) | (x-1).                       *)
(*                                                                    *)
(*  The exact count  nfix p = #{x in [1,p-1] : x^x = x (mod p)}  is a   *)
(*  genuinely IRREGULAR arithmetic function -- there is no known        *)
(*  closed form.  So we make the count a rigorous computable object     *)
(*  and prove what IS universal:                                       *)
(*                                                                    *)
(*   * set-characterisation  In x (fixed_pts p) <-> ord(x) | (x-1);    *)
(*   * x = 1 is ALWAYS a fixed point         => nfix p >= 1;            *)
(*   * x = p-1 is NEVER a fixed point (odd p, selfpow = 1 != p-1)       *)
(*                                             => nfix p <= p-2;        *)
(*   * hence the sandwich  1 <= nfix p <= p-2  (odd p), which PINS       *)
(*     nfix 3 = 1;                                                     *)
(*   * concrete values (vm_compute, feasible only up to p=7 because     *)
(*     x^x is built in unary nat):  nfix 2 = nfix 3 = nfix 5 = 1,       *)
(*     nfix 7 = 2 -- the irregular sequence begins  1, 1, 1, 2, ...     *)
(*                                                                    *)
(*  Axiom-free ("Closed under the global context").                  *)
(* ================================================================= *)

From Stdlib Require Import ZArith Znumtheory Arith Lia List Bool.
Require Import ZmodPStar ZmodOrder FpField SelfPowerDynamics.
Import ListNotations.
Open Scope nat_scope.

(* the fixed points among the units, and their count *)
Definition fixed_pts (p : nat) : list nat :=
  filter (fun x => selfpow p x =? x) (seq 1 (p - 1)).

Definition nfix (p : nat) : nat := length (fixed_pts p).

(* ----------------------------------------------------------------- *)
(*  Membership characterisations                                     *)
(* ----------------------------------------------------------------- *)

Lemma fixed_pts_spec : forall p x,
  In x (fixed_pts p) <-> (1 <= x <= p - 1 /\ selfpow p x = x).
Proof.
  intros p x; unfold fixed_pts; rewrite filter_In, in_seq; split.
  - intros [Hin Heq]; split; [ lia | apply Nat.eqb_eq; exact Heq ].
  - intros [Hr Heq]; split; [ lia | apply Nat.eqb_eq; exact Heq ].
Qed.

Lemma fixed_pts_ord : forall p x, prime (Z.of_nat p) ->
  (In x (fixed_pts p) <-> 1 <= x <= p - 1 /\ Nat.divide (ord p x) (x - 1)).
Proof.
  intros p x Hp; rewrite fixed_pts_spec; split.
  - intros [Hr Heq]; split; [ exact Hr | apply (selfpow_fixed_ord p x Hp Hr); exact Heq ].
  - intros [Hr Hdvd]; split; [ exact Hr | apply (selfpow_fixed_ord p x Hp Hr); exact Hdvd ].
Qed.

Lemma fixed_pts_nodup : forall p, NoDup (fixed_pts p).
Proof. intro p; apply NoDup_filter, seq_NoDup. Qed.

(* ----------------------------------------------------------------- *)
(*  x = 1 is always fixed  =>  nfix >= 1                             *)
(* ----------------------------------------------------------------- *)

Lemma one_fixed : forall p, prime (Z.of_nat p) -> In 1 (fixed_pts p).
Proof.
  intros p Hp; assert (Hp2 : 2 <= p) by (destruct Hp; lia).
  apply fixed_pts_spec; split; [ lia | apply selfpow_1; exact Hp2 ].
Qed.

Lemma nfix_pos : forall p, prime (Z.of_nat p) -> 1 <= nfix p.
Proof.
  intros p Hp; pose proof (one_fixed p Hp) as H1.
  unfold nfix; destruct (fixed_pts p) as [|a l] eqn:E; [ destruct H1 | simpl; lia ].
Qed.

(* ----------------------------------------------------------------- *)
(*  x = p-1 is never fixed (odd p)  =>  nfix <= p-2                  *)
(* ----------------------------------------------------------------- *)

Lemma pm1_not_fixed : forall p, prime (Z.of_nat p) -> 3 <= p -> ~ In (p - 1) (fixed_pts p).
Proof.
  intros p Hp Hp3 Hin; apply fixed_pts_spec in Hin as [_ Heq].
  rewrite selfpow_pm1 in Heq by exact Hp; lia.
Qed.

Lemma nfix_ub : forall p, nfix p <= p - 1.
Proof.
  intro p; unfold nfix, fixed_pts.
  pose proof (filter_length_le (fun x => selfpow p x =? x) (seq 1 (p - 1))) as H.
  rewrite length_seq in H; exact H.
Qed.

Lemma nfix_ub_odd : forall p, prime (Z.of_nat p) -> 3 <= p -> nfix p <= p - 2.
Proof.
  intros p Hp Hp3.
  assert (Hincl : incl (fixed_pts p) (seq 1 (p - 2))).
  { intros x Hx.
    pose proof (pm1_not_fixed p Hp Hp3) as Hpm1.
    assert (Hne : x <> p - 1) by (intro E; apply Hpm1; rewrite <- E; exact Hx).
    apply fixed_pts_spec in Hx as [Hr _]; apply in_seq; lia. }
  pose proof (NoDup_incl_length (fixed_pts_nodup p) Hincl) as Hlen.
  rewrite length_seq in Hlen; exact Hlen.
Qed.

Theorem nfix_sandwich : forall p, prime (Z.of_nat p) -> 3 <= p -> 1 <= nfix p <= p - 2.
Proof.
  intros p Hp Hp3; split; [ apply nfix_pos; exact Hp | apply nfix_ub_odd; assumption ].
Qed.

(* ----------------------------------------------------------------- *)
(*  Concrete counts (vm_compute; feasible only up to p = 7)          *)
(*  The sequence 1,1,1,2,... is irregular; at p=7 the extra fixed     *)
(*  point beyond 1 is x=4  (ord(4)=3 divides 4-1=3).                   *)
(* ----------------------------------------------------------------- *)

Example nfix_2 : nfix 2 = 1. Proof. vm_compute; reflexivity. Qed.
Example nfix_3 : nfix 3 = 1. Proof. vm_compute; reflexivity. Qed.
Example nfix_5 : nfix 5 = 1. Proof. vm_compute; reflexivity. Qed.
Example nfix_7 : nfix 7 = 2. Proof. vm_compute; reflexivity. Qed.

(* ----------------------------------------------------------------- *)
(*  MASTER                                                           *)
(* ----------------------------------------------------------------- *)

Theorem self_power_fixed_count : forall p, prime (Z.of_nat p) -> 3 <= p ->
  (* fixed points characterised by the multiplicative order *)
     (forall x, In x (fixed_pts p) <-> 1 <= x <= p - 1 /\ Nat.divide (ord p x) (x - 1))
  (* 1 always fixed, p-1 never fixed *)
  /\ In 1 (fixed_pts p)
  /\ ~ In (p - 1) (fixed_pts p)
  (* the universal count sandwich *)
  /\ 1 <= nfix p <= p - 2.
Proof.
  intros p Hp Hp3.
  split; [ intro x; apply fixed_pts_ord; exact Hp | ].
  split; [ apply one_fixed; exact Hp | ].
  split; [ apply pm1_not_fixed; assumption | apply nfix_sandwich; assumption ].
Qed.

Print Assumptions self_power_fixed_count.

(* ================================================================= *)
(*  END SelfPowerFixedCount.v                                        *)
(*  nfix p = #{x in [1,p-1] : x^x = x (mod p)}: rigorous computable    *)
(*  count, characterised by ord(x) | (x-1), with the universal         *)
(*  sandwich 1 <= nfix p <= p-2 (odd p; 1 always fixed, p-1 never) and  *)
(*  the irregular small table nfix in {1,1,1,2} for p in {2,3,5,7}.     *)
(*  No closed form for nfix p is known / claimed.  Closed under the     *)
(*  global context.                                                   *)
(* ================================================================= *)
