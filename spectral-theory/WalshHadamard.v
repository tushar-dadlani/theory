(* ================================================================= *)
(*  WalshHadamard.v                                                   *)
(*                                                                    *)
(*  THE FOURIER TRANSFORM NATIVE TO THE TRIADIC / FANO STRUCTURE      *)
(*                                                                    *)
(*  The whole framework is built on xor over F_2^n ("xb") and the     *)
(*  8-point Boolean cube F_2^3 (7 Fano cells + the absorbed point).   *)
(*  The Fourier transform on that group is the WALSH-HADAMARD         *)
(*  transform.  Unlike every other "spectral" file in the repo, this  *)
(*  is an ACTUAL transform (a linear operator), not a comment: we     *)
(*  define it and prove its defining properties with real proofs.     *)
(*                                                                    *)
(*  What this file buys, as theorems (all Qed, no Admitted):          *)
(*    * WH is symmetric and a self-inverse-up-to-scale involution:    *)
(*        WH (WH f) = 8 . f          (H^2 = 8 I)                       *)
(*      -> WH is a genuine self-adjoint "Fourier involution", the     *)
(*         finite Hamiltonian-flavoured object the repo was missing.  *)
(*    * SHIFT THEOREM: translating the signal by a group element a    *)
(*      becomes, in the transform domain, multiplication by the       *)
(*      character sign chi(a,.) in {+1,-1}:                           *)
(*        WH (translate a f) y = chi a y * WH f y                     *)
(*    * CONVOLUTION THEOREM: xor-convolution becomes pointwise product *)
(*        WH (conv f g) = WH f * WH g   (pointwise)                   *)
(*    * APEX / STANDING-WAVE COROLLARY: the prism apex involution      *)
(*      "reflect by DIAG" (f |-> f o (xor DIAG)) acts in the Fourier   *)
(*      domain as the SIGN FLIP chi(DIAG,.).  The +1 eigenspace = the  *)
(*      NODES, the -1 eigenspace = the ANTINODES of StandingWave.v.    *)
(*                                                                    *)
(*  This says nothing about RH.  It is a finite, fully verified model *)
(*  in which the "standing wave / self-dual reflection" slogans of    *)
(*  StandingWave.v become statements about a real Fourier transform.  *)
(* ================================================================= *)

From Stdlib Require Import ZArith List Bool Ring.
Import ListNotations.
Open Scope Z_scope.

(* ----------------------------------------------------------------- *)
(* SECTION 1 — The group F_2^3 (the 8-point Boolean cube)            *)
(* ----------------------------------------------------------------- *)

Record P3 : Type := mkP { c0 : bool; c1 : bool; c2 : bool }.

(* group operation: componentwise xor (this is the repo's "xb") *)
Definition xor3 (a b : P3) : P3 :=
  mkP (xorb (c0 a) (c0 b)) (xorb (c1 a) (c1 b)) (xorb (c2 a) (c2 b)).

Definition zero3 : P3 := mkP false false false.

(* the 8 points, enumerated once and for all *)
Definition allP : list P3 :=
  [ mkP false false false ; mkP false false true ;
    mkP false true  false ; mkP false true  true ;
    mkP true  false false ; mkP true  false true ;
    mkP true  true  false ; mkP true  true  true ].

(* ----------------------------------------------------------------- *)
(* SECTION 2 — Characters:  chi a y = (-1)^<a,y>                      *)
(* ----------------------------------------------------------------- *)

(* the bilinear form <a,y> in F_2 : parity of the coordinatewise AND *)
Definition dot (a y : P3) : bool :=
  xorb (xorb (andb (c0 a) (c0 y)) (andb (c1 a) (c1 y)))
       (andb (c2 a) (c2 y)).

(* the sign of a bit: false |-> +1, true |-> -1 *)
Definition signb (b : bool) : Z := if b then -1 else 1.

(* the character value in {+1,-1} *)
Definition chi (a y : P3) : Z := signb (dot a y).

(* ----------------------------------------------------------------- *)
(* SECTION 3 — The Walsh-Hadamard transform                          *)
(* ----------------------------------------------------------------- *)

Definition Signal := P3 -> Z.

(* WH f (y) = sum_x chi(x,y) f(x)  — the 8x8 Hadamard matrix acting  *)
Definition WH (f : Signal) : Signal :=
  fun y => fold_right Z.add 0 (map (fun x => chi x y * f x) allP).

(* translation of a signal by a group element *)
Definition translate (a : P3) (f : Signal) : Signal :=
  fun x => f (xor3 a x).

(* xor-convolution *)
Definition conv (f g : Signal) : Signal :=
  fun z => fold_right Z.add 0 (map (fun x => f x * g (xor3 x z)) allP).

(* ----------------------------------------------------------------- *)
(* SECTION 4 — Elementary algebra of the character                   *)
(* ----------------------------------------------------------------- *)

Lemma signb_xorb : forall p q, signb (xorb p q) = signb p * signb q.
Proof. intros [] []; reflexivity. Qed.

Lemma dot_sym : forall a y, dot a y = dot y a.
Proof.
  intros [a0 a1 a2] [y0 y1 y2]; unfold dot; cbn.
  now rewrite (andb_comm a0 y0), (andb_comm a1 y1), (andb_comm a2 y2).
Qed.

Lemma chi_sym : forall a y, chi a y = chi y a.
Proof. intros a y; unfold chi; now rewrite dot_sym. Qed.

(* the key homomorphism: dot is additive in its first argument *)
Lemma dot_xor_l : forall a b y, dot (xor3 a b) y = xorb (dot a y) (dot b y).
Proof.
  intros [a0 a1 a2] [b0 b1 b2] [y0 y1 y2]; unfold dot, xor3; cbn.
  destruct a0,a1,a2,b0,b1,b2,y0,y1,y2; reflexivity.
Qed.

Lemma chi_xor_l : forall a b y, chi (xor3 a b) y = chi a y * chi b y.
Proof.
  intros a b y; unfold chi; rewrite dot_xor_l; apply signb_xorb.
Qed.

(* ----------------------------------------------------------------- *)
(* SECTION 5 — THE MAIN THEOREMS                                     *)
(* ----------------------------------------------------------------- *)

(* WH is symmetric: the matrix chi x y is symmetric in (x,y). *)
Theorem WH_symmetric : forall x y, chi x y = chi y x.
Proof. exact chi_sym. Qed.

(* H^2 = 8 I : the Walsh-Hadamard transform is an involution up to    *)
(* the scale 8 = |F_2^3|.  This is the self-adjoint Fourier           *)
(* involution: applying it twice returns the signal times 8.          *)
Theorem WH_involution : forall (f : Signal) (y : P3),
  WH (WH f) y = 8 * f y.
Proof.
  intros f [y0 y1 y2].
  destruct y0, y1, y2;
    cbv [WH allP chi dot signb xor3 c0 c1 c2 andb orb xorb map fold_right]; ring.
Qed.

(* SHIFT THEOREM: translation in the space domain becomes a character *)
(* sign multiplication in the transform domain. *)
Theorem WH_shift : forall (a : P3) (f : Signal) (y : P3),
  WH (translate a f) y = chi a y * WH f y.
Proof.
  intros [a0 a1 a2] f [y0 y1 y2].
  destruct a0,a1,a2,y0,y1,y2;
    cbv [WH translate allP chi dot signb xor3 c0 c1 c2 andb orb xorb map fold_right]; ring.
Qed.

(* CONVOLUTION THEOREM: xor-convolution becomes a pointwise product. *)
Theorem WH_conv : forall (f g : Signal) (y : P3),
  WH (conv f g) y = WH f y * WH g y.
Proof.
  intros f g [y0 y1 y2].
  destruct y0, y1, y2;
    cbv [WH conv allP chi dot signb xor3 c0 c1 c2 andb orb xorb map fold_right]; ring.
Qed.

(* ----------------------------------------------------------------- *)
(* SECTION 6 — THE APEX INVOLUTION AS A FOURIER SIGN FLIP            *)
(*                                                                    *)
(*  StandingWave.v reflects the observer square "through the apex" by *)
(*  xoring with a fixed diagonal element DIAG.  As an operator on     *)
(*  signals this is  apex f = f o (xor DIAG) = translate DIAG f.      *)
(*  By the shift theorem, in the Fourier domain apex is exactly       *)
(*  multiplication by chi(DIAG, .) in {+1,-1}:                        *)
(*    - points y with chi(DIAG,y) = +1  are FIXED   (the NODES)       *)
(*    - points y with chi(DIAG,y) = -1  are NEGATED (the ANTINODES)   *)
(*  i.e. the reflection is diagonalised by WH, its eigenvalues +/-1   *)
(*  splitting the spectrum into nodes and antinodes.                  *)
(* ----------------------------------------------------------------- *)

(* pick a concrete diagonal element (the "DIAG" cell of the square) *)
Definition DIAG : P3 := mkP true true true.

Definition apex (f : Signal) : Signal := translate DIAG f.

(* apex is diagonalised by WH, eigenvalue chi(DIAG, y) in {+1,-1}. *)
Corollary apex_is_sign_flip : forall (f : Signal) (y : P3),
  WH (apex f) y = chi DIAG y * WH f y.
Proof. intros f y; apply WH_shift. Qed.

(* the eigenvalue is always +1 or -1 : a genuine reflection spectrum *)
Corollary apex_eigenvalue_pm1 : forall y,
  chi DIAG y = 1 \/ chi DIAG y = -1.
Proof. intro y; unfold chi, signb; destruct (dot DIAG y); [right|left]; reflexivity. Qed.

(* applying apex twice is the identity (it is an involution), so in    *)
(* the Fourier domain its eigenvalues square to 1. *)
Corollary apex_involutive_spectrum : forall y,
  chi DIAG y * chi DIAG y = 1.
Proof. intro y; destruct (apex_eigenvalue_pm1 y) as [H|H]; rewrite H; reflexivity. Qed.

(* ----------------------------------------------------------------- *)
(* SECTION 7 — A CONCRETE SPECTRUM (illustrative, computable)        *)
(*                                                                    *)
(*  Take a sample signal on the cube and read off its Walsh spectrum. *)
(*  We use the "delta at zero" signal, whose transform is the         *)
(*  all-ones (flat) spectrum — the discrete analogue of: a point in   *)
(*  space is a flat wave in frequency.  All values checked by         *)
(*  computation.                                                      *)
(* ----------------------------------------------------------------- *)

Definition delta0 : Signal := fun x => if andb (c0 x) (orb (c1 x) (c2 x))
                                        then 0 else (if orb (c0 x) (orb (c1 x) (c2 x)) then 0 else 1).
(* delta0 is 1 at zero3 and 0 elsewhere *)

Example delta0_at_zero : delta0 zero3 = 1.  Proof. reflexivity. Qed.

(* its Walsh spectrum is flat = 1 at every frequency *)
Example WH_delta0_flat : map (WH delta0) allP = [1;1;1;1;1;1;1;1].
Proof. vm_compute; reflexivity. Qed.

(* dually, the flat signal transforms to 8 * delta0 (a single spike) *)
Definition flat : Signal := fun _ => 1.
Example WH_flat_spike : map (WH flat) allP = [8;0;0;0;0;0;0;0].
Proof. vm_compute; reflexivity. Qed.

(* ----------------------------------------------------------------- *)
(* MASTER THEOREM — the Fourier transform, packaged                  *)
(* ----------------------------------------------------------------- *)

Theorem walsh_hadamard_is_a_fourier_transform :
  (* symmetric kernel *)
  (forall x y, chi x y = chi y x) /\
  (* self-inverse up to the scale 8 (H^2 = 8 I) *)
  (forall f y, WH (WH f) y = 8 * f y) /\
  (* translation <-> character multiplication *)
  (forall a f y, WH (translate a f) y = chi a y * WH f y) /\
  (* convolution <-> pointwise product *)
  (forall f g y, WH (conv f g) y = WH f y * WH g y) /\
  (* the apex reflection is a +/-1 sign flip in the transform domain *)
  (forall f y, WH (apex f) y = chi DIAG y * WH f y) /\
  (forall y, chi DIAG y = 1 \/ chi DIAG y = -1).
Proof.
  repeat split.
  - exact WH_symmetric.
  - exact WH_involution.
  - exact WH_shift.
  - exact WH_conv.
  - exact apex_is_sign_flip.
  - exact apex_eigenvalue_pm1.
Qed.

(* Show it depends on no axioms. *)
Print Assumptions walsh_hadamard_is_a_fourier_transform.

(* ================================================================= *)
(*  END WalshHadamard.v — the first genuine transform in the repo.   *)
(*  ZERO Admitted.  ALL PROOFS CLOSED.                               *)
(* ================================================================= *)
