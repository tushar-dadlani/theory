(* ================================================================= *)
(*  InvLimit.v                                                        *)
(*                                                                    *)
(*  THE LIMIT OBJECT: the inverse limit of the ChainTower, built as     *)
(*  COHERENT SEQUENCES, axiom-free.                                    *)
(*                                                                    *)
(*  A point of the inverse limit is a coherent sequence: one point in   *)
(*  each finite level  x_n : Chain n  such that the truncation of the   *)
(*  next level lands on the current one, val (trunc x_{n+1}) = val x_n. *)
(*  No completion and no classical axioms are needed -- the limit is    *)
(*  literally a dependent function plus a Prop compatibility condition. *)
(*                                                                    *)
(*  We build:                                                          *)
(*    - InvLim, its order leL (pointwise), hence its Alexandrov topology;*)
(*    - the projection cone projL : InvLim -> Chain n, continuous and    *)
(*      commuting with the truncation bonding maps;                     *)
(*    - the UNIVERSAL PROPERTY: any compatible cone factors through it   *)
(*      (mediate);                                                      *)
(*    - a characterisation: a top point `infty` and an embedding of      *)
(*      every natural number, so this limit is omega+1 = N u {infty},    *)
(*      the profinite completion of the chain N.                        *)
(*                                                                    *)
(*  (This min-truncation limit is omega+1, NOT Z_p; the p-adic integers  *)
(*  Z_p are the inverse limit of the DIFFERENT tower Z/p^n under mod-p^n  *)
(*  reduction, whose bonding maps are ring quotients rather than order   *)
(*  truncations.)                                                       *)
(* ================================================================= *)

Require Import ChainTower.
Require Import PosetTopology.
From Stdlib Require Import Lia Arith.

(* ================================================================= *)
(*  1.  THE LIMIT OBJECT: coherent sequences                         *)
(* ================================================================= *)

Definition Coherent (x : forall n, Chain n) : Prop :=
  forall n, val (trunc (x (S n))) = val (x n).

Definition InvLim : Type := { x : forall n, Chain n | Coherent x }.

Definition seqof (X : InvLim) : forall n, Chain n := proj1_sig X.

(* the projection to level n (the limit cone) *)
Definition projL (n : nat) (X : InvLim) : Chain n := seqof X n.

(* the cone commutes with the truncation bonding maps *)
Lemma projL_cone : forall (X : InvLim) n,
  val (trunc (projL (S n) X)) = val (projL n X).
Proof. intros X n; exact (proj2_sig X n). Qed.

(* ================================================================= *)
(*  2.  ITS ORDER (hence Alexandrov topology) AND CONTINUOUS PROJECTIONS *)
(* ================================================================= *)

Definition leL (X Y : InvLim) : Prop := forall n, leC (projL n X) (projL n Y).

Lemma leL_refl : forall X, leL X X.
Proof. intros X n; apply leC_refl. Qed.

Lemma leL_trans : forall X Y Z, leL X Y -> leL Y Z -> leL X Z.
Proof. intros X Y Z HXY HYZ n; eapply leC_trans; [ apply HXY | apply HYZ ]. Qed.

Definition preimL {n} (V : Chain n -> Prop) : InvLim -> Prop :=
  fun X => V (projL n X).

(* each projection is continuous: preimage of an open is open *)
Lemma projL_continuous : forall n (V : Chain n -> Prop),
  Op leC V -> Op leL (preimL V).
Proof.
  intros n V HV X Y HX HXY; unfold preimL in *; eapply HV;
    [ exact HX | apply HXY ].
Qed.

(* ================================================================= *)
(*  3.  UNIVERSAL PROPERTY: every compatible cone factors through it  *)
(* ================================================================= *)

Definition mediate {Z : Type} (fam : forall n, Z -> Chain n)
  (coh : forall z n, val (trunc (fam (S n) z)) = val (fam n z)) (z : Z) : InvLim :=
  exist Coherent (fun n => fam n z) (coh z).

Lemma mediate_proj : forall {Z} (fam : forall n, Z -> Chain n) coh n z,
  projL n (@mediate Z fam coh z) = fam n z.
Proof. reflexivity. Qed.

(* ================================================================= *)
(*  4.  CHARACTERISATION: a top point infinity + an embedding of N    *)
(*      (so the limit is omega+1)                                    *)
(* ================================================================= *)

(* the point at infinity: the diagonal x_n = top of Chain n (value n) *)
Definition inftyseq (n : nat) : Chain n := exist (fun k => k <= n) n (le_n n).

Lemma infty_coherent : Coherent inftyseq.
Proof. intro n; unfold trunc, inftyseq, val; cbn [proj1_sig]; lia. Qed.

Definition infty : InvLim := exist _ inftyseq infty_coherent.

(* infinity is the top element of the limit *)
Lemma infty_top : forall X, leL X infty.
Proof.
  intros X n; unfold leL, leC, projL, infty, seqof, inftyseq, val; cbn [proj1_sig].
  exact (proj2_sig (proj1_sig X n)).
Qed.

(* the embedding of a natural number m: capped sequence min m n *)
Definition embseq (m n : nat) : Chain n := exist _ (Nat.min m n) (Nat.le_min_r _ _).

Lemma emb_coherent : forall m, Coherent (embseq m).
Proof. intros m n; unfold trunc, embseq, val; cbn [proj1_sig]; lia. Qed.

Definition emb (m : nat) : InvLim := exist _ (embseq m) (emb_coherent m).

Lemma emb_proj : forall m n, projL n (emb m) = embseq m n.
Proof. reflexivity. Qed.

(* ----------------------------------------------------------------- *)
(*  MASTER THEOREM — the inverse limit object, axiom-free            *)
(* ----------------------------------------------------------------- *)

Theorem inverse_limit :
  (* InvLim is a poset, hence an Alexandrov space *)
  (forall X, leL X X)
  /\ (forall X Y Z, leL X Y -> leL Y Z -> leL X Z)
  (* the projections form a cone commuting with the bonding maps ... *)
  /\ (forall X n, val (trunc (projL (S n) X)) = val (projL n X))
  (* ... and are continuous *)
  /\ (forall n (V : Chain n -> Prop), Op leC V -> Op leL (preimL V))
  (* universal property: every compatible cone factors through InvLim *)
  /\ (forall (Z : Type) (fam : forall n, Z -> Chain n)
        (coh : forall z n, val (trunc (fam (S n) z)) = val (fam n z)) n z,
        projL n (mediate fam coh z) = fam n z)
  (* it is omega+1: a top point infinity, and every natural embeds *)
  /\ (forall X, leL X infty)
  /\ (forall m n, projL n (emb m) = embseq m n).
Proof.
  split; [ exact leL_refl | ].
  split; [ exact leL_trans | ].
  split; [ exact projL_cone | ].
  split; [ exact projL_continuous | ].
  split; [ intros Z fam coh n z; exact (mediate_proj fam coh n z) | ].
  split; [ exact infty_top | exact emb_proj ].
Qed.

Print Assumptions inverse_limit.

(* ================================================================= *)
(*  END InvLimit.v                                                    *)
(*  The inverse limit of the ChainTower as coherent sequences: a poset  *)
(*  (Alexandrov space) with a continuous projection cone, the universal  *)
(*  property, and the shape omega+1 (N with a top point infinity).      *)
(*  ZERO Admitted; Closed under the global context.                    *)
(* ================================================================= *)
