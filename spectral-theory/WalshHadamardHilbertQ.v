(* ================================================================= *)
(*  WalshHadamardHilbertQ.v                                           *)
(*                                                                    *)
(*  THE RATIONAL (Q) PILOT: WalshHadamardHilbert without the Reals.   *)
(*                                                                    *)
(*  WalshHadamardHilbert.v proves the finite Hilbert-space facts over  *)
(*  R, which forces Coq's classical Reals axioms into Print            *)
(*  Assumptions.  But every constant in that development is RATIONAL   *)
(*  (entries +/-1; coefficients 1/2, 1/4, 2, 4) -- no completeness, no *)
(*  transcendentals.  So the whole thing lives over Q, which is        *)
(*  constructive and AXIOM-FREE.  This file re-proves the same results *)
(*  over Q; Print Assumptions reports Closed under the global context  *)
(*  -- no Reals axioms, no admits.                                    *)
(*                                                                    *)
(*  Self-contained (own square type Sq) to avoid the name clash        *)
(*  between StandingWaveSpectrum's square Q and QArith's rationals Q.  *)
(*  The one price of working over Q is that the meaningful equality is *)
(*  Qeq (==), not Leibniz =.                                          *)
(* ================================================================= *)

From Stdlib Require Import QArith Lqa Bool.
Open Scope Q_scope.

(* ----------------------------------------------------------------- *)
(* SECTION 0 — the observer square and the rational signal space     *)
(* ----------------------------------------------------------------- *)

Record Sq : Type := mkSq { s0 : bool; s1 : bool }.

Definition xorS (a b : Sq) : Sq :=
  mkSq (xorb (s0 a) (s0 b)) (xorb (s1 a) (s1 b)).

Definition ZS := mkSq false false.
Definition RS := mkSq false true.
Definition IS := mkSq true false.
Definition DS := mkSq true true.

Definition dotS (a y : Sq) : bool :=
  xorb (andb (s0 a) (s0 y)) (andb (s1 a) (s1 y)).

Definition chr (a y : Sq) : Q := if dotS a y then -1 else 1.

Definition Sig := Sq -> Q.

Definition innerQ (f g : Sig) : Q :=
  f ZS * g ZS + f RS * g RS + f IS * g IS + f DS * g DS.

Definition WHq (f : Sig) : Sig :=
  fun y => chr ZS y * f ZS + chr RS y * f RS + chr IS y * f IS + chr DS y * f DS.

Definition Uq (f : Sig) : Sig := fun y => (1 # 2) * WHq f y.

Definition Rop (f : Sig) : Sig := fun c => f (xorS DS c).

(* Full reduction of the chr-based (integer-coefficient) goals: unfold  *)
(* everything and let cbn collapse chr to +/-1, then close by ring.      *)
Ltac crush :=
  unfold innerQ, WHq, Rop, chr, dotS, xorS, ZS, RS, IS, DS, s0, s1;
  cbn; ring.

(* ----------------------------------------------------------------- *)
(* SECTION 1 — the inner product is positive-definite                *)
(* ----------------------------------------------------------------- *)

Lemma innerQ_pos : forall f, 0 <= innerQ f f.
Proof. intro f; unfold innerQ; nra. Qed.

Lemma innerQ_definite : forall f,
  innerQ f f == 0 ->
  f ZS == 0 /\ f RS == 0 /\ f IS == 0 /\ f DS == 0.
Proof.
  intros f H; unfold innerQ in H; repeat split.
  - assert (Hsq : f ZS * f ZS == 0) by nra.
    destruct (Qmult_integral _ _ Hsq); assumption.
  - assert (Hsq : f RS * f RS == 0) by nra.
    destruct (Qmult_integral _ _ Hsq); assumption.
  - assert (Hsq : f IS * f IS == 0) by nra.
    destruct (Qmult_integral _ _ Hsq); assumption.
  - assert (Hsq : f DS * f DS == 0) by nra.
    destruct (Qmult_integral _ _ Hsq); assumption.
Qed.

Lemma innerQ_congr : forall f f' g g',
  (forall c, f c == f' c) -> (forall c, g c == g' c) ->
  innerQ f g == innerQ f' g'.
Proof.
  intros f f' g g' Hf Hg; unfold innerQ.
  rewrite (Hf ZS), (Hf RS), (Hf IS), (Hf DS),
          (Hg ZS), (Hg RS), (Hg IS), (Hg DS); reflexivity.
Qed.

Lemma innerQ_neg_r : forall f g, innerQ f (fun c => - g c) == - innerQ f g.
Proof. intros f g; unfold innerQ; cbv beta; ring. Qed.

(* inner product scales bilinearly (symbolic scalars -- no cbn hazard) *)
Lemma innerQ_scale2 : forall a b f g,
  innerQ (fun c => a * f c) (fun c => b * g c) == a * b * innerQ f g.
Proof. intros a b f g; unfold innerQ; cbv beta; ring. Qed.

(* ----------------------------------------------------------------- *)
(* SECTION 2 — WHq is self-adjoint, linear, and satisfies Parseval   *)
(* ----------------------------------------------------------------- *)

Theorem WHq_self_adjoint : forall f g, innerQ (WHq f) g == innerQ f (WHq g).
Proof. intros f g; crush. Qed.

Theorem WHq_parseval : forall f g, innerQ (WHq f) (WHq g) == 4 * innerQ f g.
Proof. intros f g; crush. Qed.

Theorem WHq_involution : forall f y, WHq (WHq f) y == 4 * f y.
Proof. intros f [b0 b1]; destruct b0, b1; crush. Qed.

(* WHq commutes with scaling (symbolic scalar a -- no 1#2 in sight) *)
Lemma WHq_scale : forall a f y, WHq (fun x => a * f x) y == a * WHq f y.
Proof. intros a f [b0 b1]; destruct b0, b1; crush. Qed.

(* ----------------------------------------------------------------- *)
(* SECTION 3 — the normalised transform Uq = (1/2) WHq is UNITARY    *)
(* (proved via the WHq lemmas + ring, keeping 1#2 away from cbn)      *)
(* ----------------------------------------------------------------- *)

Theorem Uq_involution : forall f y, Uq (Uq f) y == f y.
Proof.
  intros f y; unfold Uq.
  rewrite (WHq_scale (1 # 2) (WHq f) y), WHq_involution; ring.
Qed.

Theorem Uq_isometry : forall f g, innerQ (Uq f) (Uq g) == innerQ f g.
Proof.
  intros f g; unfold Uq.
  rewrite (innerQ_scale2 (1 # 2) (1 # 2) (WHq f) (WHq g)), WHq_parseval; ring.
Qed.

(* ----------------------------------------------------------------- *)
(* SECTION 4 — the apex reflection is a self-adjoint involution      *)
(* ----------------------------------------------------------------- *)

Theorem Rop_self_adjoint : forall f g, innerQ (Rop f) g == innerQ f (Rop g).
Proof. intros f g; crush. Qed.

Theorem Rop_involution : forall f c, Rop (Rop f) c == f c.
Proof.
  intros f [b0 b1]; destruct b0, b1;
    unfold Rop, xorS, DS, s0, s1; cbn; reflexivity.
Qed.

(* self-adjoint => orthogonal +/-1 eigenspaces (nodes _|_ antinodes) *)
Theorem eigenspaces_orthogonal : forall f g,
  (forall c, Rop f c == f c) ->
  (forall c, Rop g c == - g c) ->
  innerQ f g == 0.
Proof.
  intros f g Hf Hg.
  assert (K : innerQ f g == - innerQ f g).
  { transitivity (innerQ (Rop f) g).
    - apply innerQ_congr; [ intro c; symmetry; apply Hf | intro c; reflexivity ].
    - transitivity (innerQ f (Rop g)).
      + apply Rop_self_adjoint.
      + transitivity (innerQ f (fun c => - g c)).
        * apply innerQ_congr; [ intro c; reflexivity | intro c; apply Hg ].
        * apply innerQ_neg_r. }
  lra.
Qed.

(* ----------------------------------------------------------------- *)
(* MASTER THEOREM — the Hilbert-space lift, over Q, AXIOM-FREE        *)
(* ----------------------------------------------------------------- *)

Theorem walsh_hadamard_hilbert_Q :
  (forall f, 0 <= innerQ f f)
  /\ (forall f, innerQ f f == 0 ->
        f ZS == 0 /\ f RS == 0 /\ f IS == 0 /\ f DS == 0)
  /\ (forall f g, innerQ (WHq f) g == innerQ f (WHq g))
  /\ (forall f g, innerQ (WHq f) (WHq g) == 4 * innerQ f g)
  /\ (forall f g, innerQ (Uq f) (Uq g) == innerQ f g)
  /\ (forall f y, Uq (Uq f) y == f y)
  /\ (forall f g, innerQ (Rop f) g == innerQ f (Rop g))
  /\ (forall f c, Rop (Rop f) c == f c)
  /\ (forall f g, (forall c, Rop f c == f c) -> (forall c, Rop g c == - g c) ->
                  innerQ f g == 0).
Proof.
  split; [ exact innerQ_pos | ].
  split; [ exact innerQ_definite | ].
  split; [ exact WHq_self_adjoint | ].
  split; [ exact WHq_parseval | ].
  split; [ exact Uq_isometry | ].
  split; [ exact Uq_involution | ].
  split; [ exact Rop_self_adjoint | ].
  split; [ exact Rop_involution | exact eigenspaces_orthogonal ].
Qed.

Print Assumptions walsh_hadamard_hilbert_Q.

(* ================================================================= *)
(*  END WalshHadamardHilbertQ.v                                       *)
(*  The finite Hilbert-space structure over Q -- unitary, self-adjoint *)
(*  operator, orthogonal eigenspaces -- with NO Reals axioms.          *)
(*  ZERO Admitted; Closed under the global context.                   *)
(* ================================================================= *)
