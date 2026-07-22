(* ================================================================= *)
(*  InvolutionQ.v                                                     *)
(*                                                                    *)
(*  The residue decomposition ("no involution is free"), over Q --    *)
(*  the axiom-free rational version of Involution.v, built on the     *)
(*  WalshHadamardHilbertQ pilot.  Print Assumptions reports Closed     *)
(*  under the global context (no Reals axioms).                       *)
(* ================================================================= *)

From Stdlib Require Import QArith Lqa Bool.
Require Import WalshHadamardHilbertQ.
Open Scope Q_scope.

(* the free (symmetric) part and the residue (antisymmetric part) *)
Definition symQ  (f : Sig) : Sig := fun c => (1 # 2) * (f c + Rop f c).
Definition antiQ (f : Sig) : Sig := fun c => (1 # 2) * (f c - Rop f c).

(* the apex reflection is a genuine involution on the square *)
Lemma xorSDS_inv : forall c, xorS DS (xorS DS c) = c.
Proof. intros [b0 b1]; destruct b0, b1; reflexivity. Qed.

Lemma decompose : forall f c, f c == symQ f c + antiQ f c.
Proof. intros f c; unfold symQ, antiQ; ring. Qed.

Lemma sym_fixed : forall f c, Rop (symQ f) c == symQ f c.
Proof. intros f c; unfold symQ, Rop; cbv beta; rewrite xorSDS_inv; ring. Qed.

Lemma anti_neg : forall f c, Rop (antiQ f) c == - antiQ f c.
Proof. intros f c; unfold antiQ, Rop; cbv beta; rewrite xorSDS_inv; ring. Qed.

Lemma anti_zero_iff_fixed : forall f,
  (forall c, antiQ f c == 0) <-> (forall c, Rop f c == f c).
Proof.
  intro f; split; intros H c; pose proof (H c) as Hc; unfold antiQ in *; lra.
Qed.

(* free part _|_ residue *)
Lemma sym_anti_orthogonal : forall f, innerQ (symQ f) (antiQ f) == 0.
Proof.
  intro f; apply (eigenspaces_orthogonal (symQ f) (antiQ f)).
  - exact (sym_fixed f).
  - exact (anti_neg f).
Qed.

(* ----------------------------------------------------------------- *)
(* the reflection is NOT free: a concrete residue                    *)
(* ----------------------------------------------------------------- *)

(* the standing-wave amplitude on the square: (-1, 0, 0, +1) *)
Definition ampQ (c : Sq) : Q :=
  match c with
  | mkSq false false => -1
  | mkSq true  true  => 1
  | _                => 0
  end.

Lemma ampQ_eigen : forall c, Rop ampQ c == - ampQ c.
Proof.
  intros [b0 b1]; destruct b0, b1;
    unfold Rop, ampQ, xorS, DS, s0, s1; cbn; ring.
Qed.

(* the amplitude is a PURE residue (its own antisymmetric part) *)
Lemma amplitude_is_pure_residue : forall c, antiQ ampQ c == ampQ c.
Proof. intro c; unfold antiQ; cbv beta; rewrite (ampQ_eigen c); ring. Qed.

Theorem not_globally_free : ~ (forall f c, antiQ f c == 0).
Proof.
  intro H; specialize (H ampQ ZS).
  rewrite (amplitude_is_pure_residue ZS) in H.
  unfold ampQ, ZS in H; cbn in H; lra.
Qed.

(* ----------------------------------------------------------------- *)
(* MASTER THEOREM — the residue principle, over Q, axiom-free        *)
(* ----------------------------------------------------------------- *)

Theorem no_involution_is_free :
  (forall f c, f c == symQ f c + antiQ f c)
  /\ (forall f c, Rop (symQ f) c == symQ f c)
  /\ (forall f c, Rop (antiQ f) c == - antiQ f c)
  /\ (forall f, innerQ (symQ f) (antiQ f) == 0)
  /\ (forall f, (forall c, antiQ f c == 0) <-> (forall c, Rop f c == f c))
  /\ ~ (forall f c, antiQ f c == 0).
Proof.
  split; [ exact decompose | ].
  split; [ exact sym_fixed | ].
  split; [ exact anti_neg | ].
  split; [ exact sym_anti_orthogonal | ].
  split; [ exact anti_zero_iff_fixed | exact not_globally_free ].
Qed.

Print Assumptions no_involution_is_free.

(* ================================================================= *)
(*  END InvolutionQ.v — residue decomposition over Q, no axioms.      *)
(* ================================================================= *)
