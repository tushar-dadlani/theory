(* ================================================================= *)
(*  ChainTower.v                                                      *)
(*                                                                    *)
(*  AN INFINITE FAMILY OF FINITE TOPOLOGIES connected by continuous    *)
(*  maps, over an N-indexed tower, axiom-free.                        *)
(*                                                                    *)
(*  For each n, the finite chain  Chain n = { k | k <= n }  is a        *)
(*  finite poset (n+1 points), hence a finite Alexandrov space.  The    *)
(*  truncation / bonding maps                                          *)
(*                                                                    *)
(*     trunc : Chain (S n) -> Chain n,   k |-> min k n                 *)
(*                                                                    *)
(*  are monotone, hence CONTINUOUS.  So { Chain n }_{n in N} is an      *)
(*  infinite INVERSE SYSTEM of finite topologies -- infinitely many    *)
(*  finite spaces, all wired together by continuous bonding maps.      *)
(*                                                                    *)
(*  Chain n is exactly the divisor lattice Div(p^n) (divisors of p^n,   *)
(*  indexed by the exponent), so this is the divisor-lattice tower.     *)
(*  Its INVERSE LIMIT lim_n Chain n (min-truncation) is omega+1 =        *)
(*  N u {infinity}, the profinite completion of the chain N (built in    *)
(*  InvLimit.v); its DIRECT limit (with the inclusions) is the full      *)
(*  chain N.  Both limits are INFINITE -- that is the boundary where     *)
(*  the family stops being finite.  (NB: the p-adic integers Z_p are the *)
(*  inverse limit of the DIFFERENT tower Z/p^n under mod-p^n reduction,  *)
(*  whose bonding maps are ring quotients, not order truncations.)       *)
(*                                                                    *)
(*  Reuses PosetTopology.Op (the Alexandrov opens = up-sets) and the    *)
(*  monotone => continuous pattern.                                    *)
(* ================================================================= *)

Require Import PosetTopology.
From Stdlib Require Import List Lia Arith.
Import ListNotations.

(* the n-th finite space: the chain of n+1 points *)
Definition Chain (n : nat) : Type := { k : nat | (k <= n)%nat }.
Definition val {n} (x : Chain n) : nat := proj1_sig x.
Definition leC {n} (x y : Chain n) : Prop := (val x <= val y)%nat.

Lemma leC_refl : forall n (x : Chain n), leC x x.
Proof. intros n x; unfold leC; lia. Qed.

Lemma leC_trans : forall n (x y z : Chain n), leC x y -> leC y z -> leC x z.
Proof. intros n x y z; unfold leC; lia. Qed.

(* each level is FINITE: every element's value lies in the finite {0..n} *)
Lemma chain_finite : forall n (x : Chain n), In (val x) (seq 0 (S n)).
Proof. intros n [k Hk]; rewrite in_seq; cbn [val proj1_sig]; lia. Qed.

(* ================================================================= *)
(*  THE BONDING MAPS  trunc : Chain (S n) -> Chain n  (continuous)    *)
(* ================================================================= *)

Definition trunc {n} (x : Chain (S n)) : Chain n :=
  exist _ (Nat.min (val x) n) (Nat.le_min_r _ _).

Lemma trunc_mono : forall n (x y : Chain (S n)), leC x y -> leC (trunc x) (trunc y).
Proof.
  intros n x y H; unfold leC, trunc, val in *; cbn [proj1_sig]; lia.
Qed.

Definition preimt {n} (V : Chain n -> Prop) : Chain (S n) -> Prop :=
  fun x => V (trunc x).

(* CONTINUITY of every bonding map: preimage of an open is open *)
Lemma trunc_continuous : forall n (V : Chain n -> Prop),
  Op leC V -> Op leC (preimt V).
Proof.
  intros n V HV x y Hx Hxy; unfold preimt in *; eapply HV;
    [ exact Hx | apply trunc_mono; exact Hxy ].
Qed.

(* ================================================================= *)
(*  DYNAMIC SIZING: the GROWING direction  incl : Chain n -> Chain(Sn) *)
(* ================================================================= *)

(* The family has DYNAMIC size: Chain n has n+1 points, so the size is  *)
(* a parameter that varies with n.  Besides the shrinking bonding maps   *)
(* (trunc, inverse system -> Z_p), there are the GROWING inclusion maps  *)
(* incl : Chain n -> Chain (S n) (a directed system whose colimit is the *)
(* unbounded chain N).  Both are monotone, hence continuous.            *)
Definition incl {n} (x : Chain n) : Chain (S n) :=
  exist _ (val x) (le_S _ _ (proj2_sig x)).

Lemma incl_mono : forall n (x y : Chain n), leC x y -> leC (incl x) (incl y).
Proof.
  intros n x y H; unfold leC, incl, val in *; cbn [proj1_sig]; lia.
Qed.

Definition preimi {n} (V : Chain (S n) -> Prop) : Chain n -> Prop :=
  fun x => V (incl x).

Lemma incl_continuous : forall n (V : Chain (S n) -> Prop),
  Op leC V -> Op leC (preimi V).
Proof.
  intros n V HV x y Hx Hxy; unfold preimi in *; eapply HV;
    [ exact Hx | apply incl_mono; exact Hxy ].
Qed.

(* ----------------------------------------------------------------- *)
(*  MASTER THEOREM — an infinite tower of finite topologies          *)
(* ----------------------------------------------------------------- *)

Theorem chain_tower :
  (* each level is a finite Alexandrov space: a finite preorder *)
  (forall n (x : Chain n), leC x x)
  /\ (forall n (x y z : Chain n), leC x y -> leC y z -> leC x z)
  /\ (forall n (x : Chain n), In (val x) (seq 0 (S n)))
  (* the bonding maps trunc : Chain (S n) -> Chain n are monotone ... *)
  /\ (forall n (x y : Chain (S n)), leC x y -> leC (trunc x) (trunc y))
  (* ... hence continuous: preimage of every open is open *)
  /\ (forall n (V : Chain n -> Prop), Op leC V -> Op leC (preimt V))
  (* DYNAMIC SIZING: the growing inclusion maps are monotone/continuous too *)
  /\ (forall n (x y : Chain n), leC x y -> leC (incl x) (incl y))
  /\ (forall n (V : Chain (S n) -> Prop), Op leC V -> Op leC (preimi V)).
Proof.
  split; [ exact leC_refl | ].
  split; [ exact leC_trans | ].
  split; [ exact chain_finite | ].
  split; [ exact trunc_mono | ].
  split; [ exact trunc_continuous | ].
  split; [ exact incl_mono | exact incl_continuous ].
Qed.

Print Assumptions chain_tower.

(* ================================================================= *)
(*  END ChainTower.v                                                  *)
(*  An N-indexed inverse system of finite Alexandrov spaces (the        *)
(*  divisor-lattice / prime-power chains Chain n = Div(p^n)) with        *)
(*  continuous truncation bonding maps.  Infinitely many finite          *)
(*  topologies; the inverse limit (omega+1, built in InvLimit.v) is where *)
(*  it goes infinite.                                                    *)
(*  ZERO Admitted; Closed under the global context.                    *)
(* ================================================================= *)
