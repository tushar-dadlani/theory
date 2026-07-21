(* ================================================================= *)
(*  WalshHadamardHilbert.v                                            *)
(*                                                                    *)
(*  LIFTING THE WALSH-HADAMARD TRANSFORM TO A REAL INNER-PRODUCT      *)
(*  (HILBERT) SPACE.                                                  *)
(*                                                                    *)
(*  WalshHadamard.v / StandingWaveSpectrum.v worked with integer-     *)
(*  valued signals and could only state unitarity up to the scale     *)
(*  N.  Here we equip the signal space on the observer square F_2^2    *)
(*  with the real inner product  <f,g> = sum_c f(c) g(c),  making it  *)
(*  a genuine (4-dimensional) Hilbert space, and prove:               *)
(*                                                                    *)
(*    * <.,.> is symmetric, bilinear, and positive-DEFINITE           *)
(*      (<f,f> >= 0, and = 0 only when f is identically 0);           *)
(*    * the Hadamard operator WHr is SELF-ADJOINT: <WHr f, g> =       *)
(*      <f, WHr g>  (a genuine self-adjoint operator = a Hamiltonian);*)
(*    * PARSEVAL/PLANCHEREL: <WHr f, WHr g> = 4 <f,g>;                *)
(*    * the NORMALISED transform  Ur = (1/2) WHr  is a genuine        *)
(*      UNITARY (orthogonal) involution: <Ur f, Ur g> = <f,g> and     *)
(*      Ur (Ur f) = f;                                                *)
(*    * the apex reflection Rop is self-adjoint, orthogonal, and an    *)
(*      involution -> real spectrum {+1,-1};                          *)
(*    * SELF-ADJOINT => ORTHOGONAL EIGENSPACES: the +1 eigenspace     *)
(*      (nodes) is orthogonal to the -1 eigenspace (antinodes);       *)
(*    * the StandingWave amplitude is a (-1)-eigenvector, hence has    *)
(*      norm^2 = 2, is preserved in norm by the unitary Ur, and is    *)
(*      orthogonal to every node signal.                              *)
(*                                                                    *)
(*  No `admit`s and no CUSTOM axioms; the only assumptions are the    *)
(*  standard Coq `Reals` axioms (classical Dedekind reals +           *)
(*  functional extensionality) that any development over R uses.      *)
(*                                                                    *)
(*  HONEST SCOPE: this is a finite-dimensional (dim 4) real Hilbert    *)
(*  space, so unitary/self-adjoint are the genuine linear-algebra     *)
(*  notions, fully machine-checked (standard Reals axioms only).      *)
(*  It is NOT the                                                     *)
(*  infinite-dimensional l^2/L^2 setting the Hilbert-Polya program    *)
(*  needs; that lift requires a real analysis library (completeness,  *)
(*  unbounded operators, the spectral theorem) and is a much larger   *)
(*  undertaking.  This is the first honest rung of that ladder.       *)
(* ================================================================= *)

Require Import StandingWaveSpectrum.
From Stdlib Require Import Reals List Bool Lra.
Import ListNotations.
Open Scope R_scope.

(* We reuse from StandingWaveSpectrum: the square type Q, its cells    *)
(* ZERO/REAL/IMAG/DIAG, xorq, dotq, and the integer amplitude `amp`.   *)

(* ----------------------------------------------------------------- *)
(* SECTION 1 — The real signal space and its inner product          *)
(* ----------------------------------------------------------------- *)

Definition RSig := Q -> R.

(* the inner product, written out over the 4 cells *)
Definition innerR (f g : RSig) : R :=
  f ZERO * g ZERO + f REAL * g REAL + f IMAG * g IMAG + f DIAG * g DIAG.

Lemma innerR_sym : forall f g, innerR f g = innerR g f.
Proof. intros f g; unfold innerR; ring. Qed.

Lemma innerR_linear_l : forall a f g h,
  innerR (fun c => a * f c + g c) h = a * innerR f h + innerR g h.
Proof. intros; unfold innerR; ring. Qed.

(* positive semi-definite *)
Lemma innerR_pos : forall f, 0 <= innerR f f.
Proof. intro f; unfold innerR; nra. Qed.

(* positive DEFINITE: zero norm forces the signal to vanish *)
Lemma innerR_definite : forall f,
  innerR f f = 0 ->
  f ZERO = 0 /\ f REAL = 0 /\ f IMAG = 0 /\ f DIAG = 0.
Proof.
  intros f H; unfold innerR in H.
  repeat split; apply Rsqr_0_uniq; unfold Rsqr; nra.
Qed.

(* congruence: the inner product only sees the values on the 4 cells *)
Lemma innerR_congr : forall f f' g g',
  (forall c, f c = f' c) -> (forall c, g c = g' c) ->
  innerR f g = innerR f' g'.
Proof.
  intros f f' g g' Hf Hg; unfold innerR.
  rewrite (Hf ZERO), (Hf REAL), (Hf IMAG), (Hf DIAG),
          (Hg ZERO), (Hg REAL), (Hg IMAG), (Hg DIAG); reflexivity.
Qed.

Lemma innerR_neg_r : forall f g, innerR f (fun c => - g c) = - innerR f g.
Proof. intros; unfold innerR; ring. Qed.

(* ----------------------------------------------------------------- *)
(* SECTION 2 — The Walsh-Hadamard operator over R                    *)
(* ----------------------------------------------------------------- *)

Definition chr (a y : Q) : R := if dotq a y then -1 else 1.

Definition WHr (f : RSig) : RSig :=
  fun y => chr ZERO y * f ZERO + chr REAL y * f REAL
         + chr IMAG y * f IMAG + chr DIAG y * f DIAG.

Ltac crush := unfold innerR, WHr, chr, dotq, ZERO, REAL, IMAG, DIAG, q0, q1;
              cbn; try ring; try field; try lra.

(* WHr is SELF-ADJOINT: <WHr f, g> = <f, WHr g>. *)
Theorem WHr_self_adjoint : forall f g, innerR (WHr f) g = innerR f (WHr g).
Proof. intros f g; crush. Qed.

(* PARSEVAL / PLANCHEREL: <WHr f, WHr g> = 4 <f,g>. *)
Theorem WHr_parseval : forall f g, innerR (WHr f) (WHr g) = 4 * innerR f g.
Proof. intros f g; crush. Qed.

(* the involution H^2 = 4 I (N = 4 for the square) *)
Theorem WHr_involution : forall f y, WHr (WHr f) y = 4 * f y.
Proof. intros f [b0 b1]; destruct b0, b1; crush. Qed.

Lemma WHr_scale : forall a f y, WHr (fun x => a * f x) y = a * WHr f y.
Proof. intros a f [b0 b1]; destruct b0, b1; crush. Qed.

(* ----------------------------------------------------------------- *)
(* SECTION 3 — The normalised transform Ur = (1/2) WHr is UNITARY    *)
(* ----------------------------------------------------------------- *)

Definition Ur (f : RSig) : RSig := fun y => / 2 * WHr f y.

(* Ur is an involution: Ur (Ur f) = f. *)
Theorem Ur_involution : forall f y, Ur (Ur f) y = f y.
Proof. intros f [b0 b1]; destruct b0, b1; unfold Ur; crush. Qed.

(* Ur is an ISOMETRY (orthogonal / unitary over R): <Ur f, Ur g> = <f,g>. *)
Theorem Ur_isometry : forall f g, innerR (Ur f) (Ur g) = innerR f g.
Proof. intros f g; unfold Ur; crush. Qed.

(* in particular it preserves the norm *)
Corollary Ur_norm_preserving : forall f, innerR (Ur f) (Ur f) = innerR f f.
Proof. intro f; apply Ur_isometry. Qed.

(* ----------------------------------------------------------------- *)
(* SECTION 4 — The apex reflection as a self-adjoint involution      *)
(* ----------------------------------------------------------------- *)

Definition Rop (f : RSig) : RSig := fun c => f (xorq DIAG c).

Theorem Rop_self_adjoint : forall f g, innerR (Rop f) g = innerR f (Rop g).
Proof. intros f g; unfold innerR, Rop, xorq, ZERO, REAL, IMAG, DIAG, q0, q1; cbn; ring. Qed.

Theorem Rop_orthogonal : forall f g, innerR (Rop f) (Rop g) = innerR f g.
Proof. intros f g; unfold innerR, Rop, xorq, ZERO, REAL, IMAG, DIAG, q0, q1; cbn; ring. Qed.

Theorem Rop_involution : forall f c, Rop (Rop f) c = f c.
Proof. intros f [b0 b1]; destruct b0, b1; unfold Rop, xorq, DIAG, q0, q1; cbn; reflexivity. Qed.

(* SELF-ADJOINT => ORTHOGONAL EIGENSPACES:                            *)
(* a (+1)-eigenvector (node) is orthogonal to a (-1)-eigenvector      *)
(* (antinode).  This is the spectral separation of the standing wave. *)
Theorem eigenspaces_orthogonal : forall f g,
  (forall c, Rop f c = f c) ->
  (forall c, Rop g c = - g c) ->
  innerR f g = 0.
Proof.
  intros f g Hf Hg.
  assert (K : innerR f g = - innerR f g).
  { transitivity (innerR (Rop f) g).
    - apply innerR_congr; [ intro c; symmetry; apply Hf | reflexivity ].
    - transitivity (innerR f (Rop g)).
      + apply Rop_self_adjoint.
      + transitivity (innerR f (fun c => - g c)).
        * apply innerR_congr; [ reflexivity | intro c; apply Hg ].
        * apply innerR_neg_r. }
  lra.
Qed.

(* ----------------------------------------------------------------- *)
(* SECTION 5 — The StandingWave amplitude in the Hilbert space       *)
(* ----------------------------------------------------------------- *)

(* the real amplitude = the image of StandingWaveSpectrum's integer amp *)
Definition ampR (c : Q) : R := IZR (amp c).

Lemma ampR_values :
  ampR ZERO = -1 /\ ampR REAL = 0 /\ ampR IMAG = 0 /\ ampR DIAG = 1.
Proof.
  unfold ampR; destruct amp_values as (H0 & Hr & Hi & Hd).
  rewrite H0, Hr, Hi, Hd; repeat split; reflexivity.
Qed.

(* ampR is a (-1)-eigenvector of the apex reflection (the standing    *)
(* wave property lifted to the Hilbert space). *)
Lemma ampR_eigen : forall c, Rop ampR c = - ampR c.
Proof.
  intro c; unfold Rop, ampR.
  change (amp (xorq DIAG c)) with (apex amp c).
  rewrite (amp_apex_antisym c), opp_IZR; reflexivity.
Qed.

(* its squared norm is 2 = |A(ZERO)|^2 + |A(DIAG)|^2 = 1 + 1 *)
Lemma ampR_norm_sq : innerR ampR ampR = 2.
Proof.
  destruct ampR_values as (H0 & Hr & Hi & Hd).
  unfold innerR; rewrite H0, Hr, Hi, Hd; lra.
Qed.

(* the unitary Ur preserves the amplitude's norm *)
Corollary ampR_norm_preserved : innerR (Ur ampR) (Ur ampR) = 2.
Proof. rewrite Ur_isometry; exact ampR_norm_sq. Qed.

(* and the amplitude is orthogonal to every node signal *)
Corollary ampR_orthogonal_to_nodes : forall g,
  (forall c, Rop g c = g c) -> innerR g ampR = 0.
Proof. intros g Hg; apply (eigenspaces_orthogonal g ampR Hg ampR_eigen). Qed.

(* ----------------------------------------------------------------- *)
(* MASTER THEOREM — the Hilbert-space lift, packaged                 *)
(* ----------------------------------------------------------------- *)

Theorem walsh_hadamard_hilbert_lift :
  (* the inner product is positive-definite *)
  (forall f, 0 <= innerR f f) /\
  (forall f, innerR f f = 0 ->
     f ZERO = 0 /\ f REAL = 0 /\ f IMAG = 0 /\ f DIAG = 0) /\
  (* WHr is self-adjoint and satisfies Parseval *)
  (forall f g, innerR (WHr f) g = innerR f (WHr g)) /\
  (forall f g, innerR (WHr f) (WHr g) = 4 * innerR f g) /\
  (* the normalised transform Ur is a unitary involution *)
  (forall f g, innerR (Ur f) (Ur g) = innerR f g) /\
  (forall f y, Ur (Ur f) y = f y) /\
  (* the apex reflection is a self-adjoint involution ... *)
  (forall f g, innerR (Rop f) g = innerR f (Rop g)) /\
  (forall f c, Rop (Rop f) c = f c) /\
  (* ... with orthogonal +/-1 eigenspaces (nodes _|_ antinodes) *)
  (forall f g, (forall c, Rop f c = f c) -> (forall c, Rop g c = - g c) ->
               innerR f g = 0) /\
  (* the amplitude is a (-1)-eigenvector of norm^2 = 2, preserved by Ur *)
  (forall c, Rop ampR c = - ampR c) /\
  (innerR ampR ampR = 2) /\
  (innerR (Ur ampR) (Ur ampR) = 2).
Proof.
  split; [ exact innerR_pos | ].
  split; [ exact innerR_definite | ].
  split; [ exact WHr_self_adjoint | ].
  split; [ exact WHr_parseval | ].
  split; [ exact Ur_isometry | ].
  split; [ exact Ur_involution | ].
  split; [ exact Rop_self_adjoint | ].
  split; [ exact Rop_involution | ].
  split; [ exact eigenspaces_orthogonal | ].
  split; [ exact ampR_eigen | ].
  split; [ exact ampR_norm_sq | ].
  exact ampR_norm_preserved.
Qed.

Print Assumptions walsh_hadamard_hilbert_lift.

(* ================================================================= *)
(*  END WalshHadamardHilbert.v                                        *)
(*  The Walsh-Hadamard transform is a genuine unitary, the apex       *)
(*  reflection a genuine self-adjoint operator, on a real 4-dim       *)
(*  Hilbert space.  ZERO Admitted; standard Reals axioms only.        *)
(* ================================================================= *)
