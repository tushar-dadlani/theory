(* ================================================================= *)
(*  StandingWaveSpectrum.v                                            *)
(*                                                                    *)
(*  TYING StandingWave.v's AMPLITUDE COUNTS TO A REAL FOURIER         *)
(*  SPECTRUM.                                                         *)
(*                                                                    *)
(*  StandingWave.v computes, on the 4-cell observer square, the net   *)
(*  amplitude A(c) = forward_count(c) - infinity_count(c):            *)
(*     A(ZERO) = 1-2 = -1   A(REAL) = 2-2 = 0                         *)
(*     A(IMAG) = 2-2 =  0   A(DIAG) = 2-1 = +1                        *)
(*  but leaves the "standing wave / nodes / antinodes" reading in     *)
(*  the comments.                                                     *)
(*                                                                    *)
(*  The observer square is F_2^2 (WalshHadamard.v did the Fano cube   *)
(*  F_2^3; the square is its 4-point sibling).  Here we:              *)
(*    1. define the amplitude signal `amp` DIRECTLY from StandingWave *)
(*       's own fwd_*/inf_* constants (so it is tied by construction) *)
(*       and prove amp = (-1, 0, 0, +1) on (ZERO,REAL,IMAG,DIAG);     *)
(*    2. prove the apex reflection (xor DIAG) sends amp |-> -amp,     *)
(*       i.e. amp lies in the (-1)-eigenspace of the reflection;      *)
(*    3. conclude, via the shift theorem, that the Walsh spectrum of  *)
(*       amp VANISHES on every "node" frequency (chi(DIAG,.) = +1)    *)
(*       and is supported entirely on the "antinode" frequencies      *)
(*       (chi(DIAG,.) = -1) — and compute it: WH amp = (0,-2,-2,0).   *)
(*                                                                    *)
(*  So StandingWave.v's hand-counted amplitude table becomes the      *)
(*  eigen-spectrum of a genuine self-adjoint Fourier transform, with  *)
(*  its nodes/antinodes the +/-1 eigenspaces of the apex reflection.  *)
(*  All proofs closed, axiom-free.                                    *)
(* ================================================================= *)

Require Import StandingWave.
From Stdlib Require Import ZArith List Bool Lia Ring.
Import ListNotations.
Open Scope Z_scope.

(* ----------------------------------------------------------------- *)
(* SECTION 1 — The observer square F_2^2 and its 4 cells             *)
(* ----------------------------------------------------------------- *)

Record Q : Type := mkQ { q0 : bool; q1 : bool }.

Definition xorq (a b : Q) : Q :=
  mkQ (xorb (q0 a) (q0 b)) (xorb (q1 a) (q1 b)).

Definition allQ : list Q :=
  [ mkQ false false ; mkQ false true ; mkQ true false ; mkQ true true ].

(* the four cells of the observer square *)
Definition ZERO : Q := mkQ false false.
Definition REAL : Q := mkQ false true.
Definition IMAG : Q := mkQ true false.
Definition DIAG : Q := mkQ true true.

(* ----------------------------------------------------------------- *)
(* SECTION 2 — The Walsh-Hadamard transform on the square           *)
(* ----------------------------------------------------------------- *)

Definition dotq (a y : Q) : bool :=
  xorb (andb (q0 a) (q0 y)) (andb (q1 a) (q1 y)).

Definition chiq (a y : Q) : Z := if dotq a y then -1 else 1.

Definition Sig := Q -> Z.

Definition WHq (f : Sig) : Sig :=
  fun y => fold_right Z.add 0 (map (fun x => chiq x y * f x) allQ).

(* ----------------------------------------------------------------- *)
(* SECTION 3 — The amplitude, built FROM StandingWave's counts       *)
(* ----------------------------------------------------------------- *)

(* net amplitude at a cell = forward count - infinity count, as an   *)
(* integer, read straight off StandingWave.v's definitions.          *)
Definition amp (c : Q) : Z :=
  match q0 c, q1 c with
  | false, false => Z.of_nat fwd_ZERO - Z.of_nat inf_ZERO
  | false, true  => Z.of_nat fwd_REAL - Z.of_nat inf_REAL
  | true,  false => Z.of_nat fwd_IMAG - Z.of_nat inf_IMAG
  | true,  true  => Z.of_nat fwd_DIAG - Z.of_nat inf_DIAG
  end.

(* the amplitude table is exactly (-1, 0, 0, +1) *)
Theorem amp_values :
  amp ZERO = -1 /\ amp REAL = 0 /\ amp IMAG = 0 /\ amp DIAG = 1.
Proof. repeat split; vm_compute; reflexivity. Qed.

(* the magnitudes agree with StandingWave's amp_magnitude_* (both 1) *)
Theorem amp_magnitudes_match_standingwave :
  Z.abs (amp ZERO) = Z.of_nat amp_magnitude_ZERO /\
  Z.abs (amp DIAG) = Z.of_nat amp_magnitude_DIAG.
Proof. split; vm_compute; reflexivity. Qed.

(* ----------------------------------------------------------------- *)
(* SECTION 4 — The apex reflection sends amp to -amp                 *)
(* ----------------------------------------------------------------- *)

(* reflecting the square through the apex = xoring by DIAG. *)
Definition apex (f : Sig) : Sig := fun c => f (xorq DIAG c).

(* amp is ANTI-symmetric under the apex reflection: it sits in the   *)
(* (-1)-eigenspace.  This is the "standing wave" property: the       *)
(* forward surplus at DIAG mirrors the deficit at ZERO.              *)
Theorem amp_apex_antisym : forall c, apex amp c = - amp c.
Proof. intros [c0 c1]; destruct c0, c1; vm_compute; reflexivity. Qed.

(* ----------------------------------------------------------------- *)
(* SECTION 5 — Transform lemmas (shift, negation, congruence)        *)
(* ----------------------------------------------------------------- *)

(* congruence: WHq depends only on the signal's values *)
Lemma WHq_ext : forall f g y, (forall x, f x = g x) -> WHq f y = WHq g y.
Proof.
  intros f g y H; unfold WHq; f_equal; apply map_ext; intro x; now rewrite H.
Qed.

(* negation is linear under the transform *)
Lemma WHq_neg : forall f y, WHq (fun x => - f x) y = - WHq f y.
Proof.
  intros f [y0 y1]; destruct y0, y1;
    cbv [WHq allQ chiq dotq q0 q1 andb xorb map fold_right]; ring.
Qed.

(* SHIFT THEOREM on the square: translation by a becomes the sign     *)
(* chi(a,.) in the transform domain. *)
Theorem WHq_shift : forall a f y,
  WHq (fun x => f (xorq a x)) y = chiq a y * WHq f y.
Proof.
  intros [a0 a1] f [y0 y1]; destruct a0, a1, y0, y1;
    cbv [WHq allQ chiq dotq xorq q0 q1 andb xorb map fold_right]; ring.
Qed.

(* ----------------------------------------------------------------- *)
(* SECTION 6 — THE SPECTRUM LIVES ON THE ANTINODES                   *)
(* ----------------------------------------------------------------- *)

(* the reflection eigenvalue chi(DIAG,.) is +1 on the NODES           *)
(* {ZERO,DIAG} and -1 on the ANTINODES {REAL,IMAG}. *)
Theorem chiq_DIAG_nodes :
  chiq DIAG ZERO = 1  /\ chiq DIAG DIAG = 1 /\
  chiq DIAG REAL = -1 /\ chiq DIAG IMAG = -1.
Proof. repeat split; vm_compute; reflexivity. Qed.

(* MAIN (structural): because apex amp = -amp, the shift theorem      *)
(* forces the Walsh spectrum of amp to vanish at every node frequency *)
(* (where chi(DIAG,.) = +1).  No computation of amp's values is used  *)
(* here — only its (-1)-eigen property. *)
Theorem spectrum_vanishes_on_nodes : forall y,
  chiq DIAG y = 1 -> WHq amp y = 0.
Proof.
  intros y Hnode.
  assert (Hs : WHq (fun x => amp (xorq DIAG x)) y = chiq DIAG y * WHq amp y)
    by apply WHq_shift.
  assert (He : WHq (fun x => amp (xorq DIAG x)) y = WHq (fun x => - amp x) y).
  { apply WHq_ext; intro x; apply (amp_apex_antisym x). }
  rewrite He, WHq_neg, Hnode in Hs.
  lia.
Qed.

(* MAIN (concrete): the full Walsh spectrum of the amplitude, matched *)
(* to StandingWave's counts, is (0, -2, -2, 0) — zero on the nodes    *)
(* {ZERO,DIAG}, and -2 on the antinodes {REAL,IMAG}.                  *)
(* The antinode magnitude 2 = |A(ZERO)| + |A(DIAG)| = 1 + 1: the      *)
(* deficit and surplus add coherently in the transform.              *)
Theorem amp_spectrum : map (WHq amp) allQ = [0; -2; -2; 0].
Proof. vm_compute; reflexivity. Qed.

Theorem spectrum_nodes_zero :
  WHq amp ZERO = 0 /\ WHq amp DIAG = 0.
Proof. split; vm_compute; reflexivity. Qed.

Theorem spectrum_antinodes_carry_amplitude :
  WHq amp REAL = -2 /\ WHq amp IMAG = -2.
Proof. split; vm_compute; reflexivity. Qed.

(* ----------------------------------------------------------------- *)
(* MASTER THEOREM                                                     *)
(* ----------------------------------------------------------------- *)

Theorem standing_wave_spectrum :
  (* (1) the amplitude equals StandingWave's (-1,0,0,+1) *)
  (amp ZERO = -1 /\ amp REAL = 0 /\ amp IMAG = 0 /\ amp DIAG = 1) /\
  (* (2) apex reflection negates it: amp is a (-1)-eigenvector *)
  (forall c, apex amp c = - amp c) /\
  (* (3) hence its Walsh spectrum vanishes on the node frequencies *)
  (forall y, chiq DIAG y = 1 -> WHq amp y = 0) /\
  (* (4) and the full spectrum is (0,-2,-2,0): supported on antinodes *)
  (map (WHq amp) allQ = [0; -2; -2; 0]).
Proof.
  split. exact amp_values.
  split. exact amp_apex_antisym.
  split. exact spectrum_vanishes_on_nodes.
  exact amp_spectrum.
Qed.

Print Assumptions standing_wave_spectrum.

(* ================================================================= *)
(*  END StandingWaveSpectrum.v                                        *)
(*  StandingWave's amplitude counts = the eigen-spectrum of the       *)
(*  Walsh-Hadamard transform, living on the antinode frequencies.     *)
(*  ZERO Admitted.  ALL PROOFS CLOSED.                               *)
(* ================================================================= *)
