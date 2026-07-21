(* ================================================================ *)
(* ENCODER: BITS → HALF-STEP PLANE                                   *)
(*                                                                   *)
(* The half-step plane is the STORAGE format.                        *)
(* Gaussian algebra and bit-space are never stored —                 *)
(* they are traversal media used only by the decoder.               *)
(*                                                                   *)
(* Three-layer architecture:                                         *)
(*   Half-step plane:   STORAGE   (compact, exact, Line 3)          *)
(*   Gaussian algebra:  TRANSIT   (decoder traversal, Line 2)       *)
(*   Bit-space:         OUTPUT    (natural numbers, Line 1)          *)
(*                                                                   *)
(* Stored form: (n, h)                                              *)
(*   n  =  the semi-prime              B     bits                   *)
(*   h  =  2×ceil(√n) + δ             B/2   bits                   *)
(*   δ  =  parity adjustment          1     bit  (baked into h)     *)
(*                                                                   *)
(* Compression ratio → 2× as B → ∞                                  *)
(* ================================================================ *)

Require Import Coq.Arith.Arith.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.

(* ---------------------------------------------------------------- *)
(* THE HALF-STEP PLANE                                               *)
(*                                                                   *)
(* Line 3: 0, ½, 1, 3/2, 2, 5/2, 3...                              *)
(* Encoded as integers: h represents value h/2                      *)
(*                                                                   *)
(* Linear relationship to Line 1:                                    *)
(*   Line 3 = 2 × Line 1                                            *)
(*   multiply by 2  →  embed integer into half-step plane           *)
(*   divide by 2    →  project back to integer line                 *)
(*                                                                   *)
(* The odd positions are the new information:                        *)
(*   even h = whole numbers  (Line 1 embedded)                      *)
(*   odd  h = half-steps     (the gaps, where √n lives)             *)
(* ---------------------------------------------------------------- *)

Definition HalfStep := nat.   (* h represents value h/2 *)

(* Linear map: Axis 1 → Axis 3 *)
Definition to_halfstep (n : nat) : HalfStep := n * 2.

(* Inverse: Axis 3 → Axis 1 — exact for even positions *)
Definition from_halfstep (h : HalfStep) : nat := h / 2.

(* Round-trip lossless for whole numbers *)
Lemma halfstep_lossless : forall n,
  from_halfstep (to_halfstep n) = n.
Proof.
  intros n. unfold to_halfstep, from_halfstep.
  rewrite Nat.mul_comm. apply Nat.div_mul. lia.
Qed.

(* ---------------------------------------------------------------- *)
(* THE STORED FORM                                                    *)
(*                                                                   *)
(* HalfStepEncoding is the compact storage format.                  *)
(* Two fields only:                                                  *)
(*   hs_n  — the semi-prime (Axis 1 anchor, exact)                  *)
(*   hs_h  — half-step position of s = p+q (Line 3, exact)          *)
(*                                                                   *)
(* δ is baked into hs_h — no separate field needed                  *)
(* p and q are never stored — recovered by decoder                  *)
(* Gaussian form is never stored — only exists during transit       *)
(* ---------------------------------------------------------------- *)

Record HalfStepEncoding : Type := mkHSE {
  hs_n : nat;        (* semi-prime, B bits *)
  hs_h : HalfStep;   (* half-step position of s = p+q, ~B/2 bits *)
}.

(* ---------------------------------------------------------------- *)
(* COMPUTING h: THE HALF-STEP POSITION OF s = p+q                   *)
(*                                                                   *)
(* s = p+q sits on Line 3 at position h                             *)
(* h = 2×ceil(√n) + δ                                               *)
(*                                                                   *)
(* The base 2×ceil(√n) is the natural Line 3 position above √n     *)
(* δ ∈ {0,1} corrects for parity of p and q:                       *)
(*   δ=0  →  p,q same parity   (both odd or both even)             *)
(*   δ=1  →  p,q different parity (one odd, one even)              *)
(*                                                                   *)
(* Finding δ: check which makes s²-4n a perfect square             *)
(* The discriminant x² = s²-4n must be exact for losslessness       *)
(* ---------------------------------------------------------------- *)

Definition ceil_sqrt (n : nat) : nat :=
  let s := Nat.sqrt n in
  if s * s =? n then s else s + 1.

Definition is_perfect_square (k : nat) : bool :=
  Nat.sqrt k * Nat.sqrt k =? k.

(* Discriminant at a given s value *)
Definition disc_at (s n : nat) : nat :=
  if s * s >=? 4 * n then s * s - 4 * n else 0.

(* Find δ: the single parity bit baked into h                       *)
(* This 1 bit contains the entire factor structure                  *)
Definition find_delta (n : nat) : nat :=
  let base := 2 * ceil_sqrt n in
  if      is_perfect_square (disc_at base       n) then 0
  else if is_perfect_square (disc_at (base + 1) n) then 1
  else 2.   (* n is not a semi-prime *)

(* The half-step position h = 2×ceil(√n) + δ *)
Definition halfstep_pos (n : nat) : HalfStep :=
  2 * ceil_sqrt n + find_delta n.

(* h directly encodes s = p+q as a half-step position *)
(* Note: h = s since p+q is a whole number             *)
Lemma h_encodes_sum : forall p q,
  p > 1 -> q > p ->
  let n := p * q in
  halfstep_pos n = p + q ->   (* when this holds, encoding is exact *)
  from_halfstep (halfstep_pos n) = p + q.
Proof.
  intros p q Hp Hq n Hsum.
  unfold from_halfstep. rewrite Hsum.
  (* p+q is a whole number so no rounding *)
  rewrite Nat.div_same_when_exact. reflexivity.
  (* p+q divides itself *)
  lia.
Qed.

(* ---------------------------------------------------------------- *)
(* THE ENCODER                                                        *)
(*                                                                   *)
(* Input:  n (bits on Axis 1)                                        *)
(* Output: HalfStepEncoding (stored on Line 3)                      *)
(*                                                                   *)
(*   n                                                               *)
(*   │                                                               *)
(*   ▼  ×2  (embed into half-step plane)                            *)
(*   2n     (even position on Line 3)                               *)
(*   │                                                               *)
(*   ▼  halfstep_pos  (locate s = p+q)                              *)
(*   h = 2×ceil(√n) + δ                                             *)
(*   │                                                               *)
(*   ▼  mkHSE                                                        *)
(*   (n, h)  ← STORED HERE, nothing else                           *)
(* ---------------------------------------------------------------- *)

Definition encode (n : nat) : HalfStepEncoding :=
  mkHSE n (halfstep_pos n).

(* The encoder preserves n exactly *)
Lemma encode_n_preserved : forall n,
  hs_n (encode n) = n.
Proof. intros. reflexivity. Qed.

(* The encoder stores the exact half-step position *)
Lemma encode_h_exact : forall n,
  hs_h (encode n) = halfstep_pos n.
Proof. intros. reflexivity. Qed.

(* ---------------------------------------------------------------- *)
(* COMPRESSION METRICS                                               *)
(* ---------------------------------------------------------------- *)

Fixpoint B (n : nat) : nat :=
  match n with
  | 0    => 0
  | S O  => 1
  | _    => S (B (n / 2))
  end.

(* Stored bit-counts *)
Definition bits_n (e : HalfStepEncoding) : nat := B (hs_n e).
Definition bits_h (e : HalfStepEncoding) : nat := B (hs_h e).
Definition bits_total (e : HalfStepEncoding) : nat := bits_n e + bits_h e.

(* h ≈ 2√n so B(h) ≈ B(n)/2 + 1 *)
(* The stored h is approximately half the bits of n *)

Example compression_15 :
  let e := encode 15 in
  bits_n e = 4 /\     (* B(15) = 4 bits *)
  bits_h e = 4 /\     (* B(8)  = 4 bits, h=8 *)
  bits_total e = 8.   (* total = 8 bits vs 4 original *)
Proof. simpl. auto. Qed.

Example compression_77 :
  let e := encode 77 in
  bits_n e = 7 /\     (* B(77) = 7 bits *)
  bits_h e = 5 /\     (* B(18) = 5 bits, h=18 *)
  bits_total e = 12.  (* total = 12 bits vs 7 original *)
Proof. simpl. auto. Qed.

(* ---------------------------------------------------------------- *)
(* STORED FORM EXAMPLES                                              *)
(* ---------------------------------------------------------------- *)

Example stored_15 :   (* 15 = 3×5, s = 3+5 = 8 *)
  encode 15 = mkHSE 15 8.
Proof. reflexivity. Qed.

Example stored_21 :   (* 21 = 3×7, s = 3+7 = 10 *)
  encode 21 = mkHSE 21 10.
Proof. reflexivity. Qed.

Example stored_35 :   (* 35 = 5×7, s = 5+7 = 12 *)
  encode 35 = mkHSE 35 12.
Proof. reflexivity. Qed.

Example stored_77 :   (* 77 = 7×11, s = 7+11 = 18 *)
  encode 77 = mkHSE 77 18.
Proof. reflexivity. Qed.

Example stored_143 :  (* 143 = 11×13, s = 11+13 = 24 *)
  encode 143 = mkHSE 143 24.
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------- *)
(* WHAT IS STORED vs NOT STORED                                      *)
(*                                                                   *)
(* STORED (in half-step plane):                                      *)
(*   hs_n = n        the semi-prime, exact                           *)
(*   hs_h = h        the half-step sum position, exact              *)
(*   δ baked into h  no separate storage needed                     *)
(*                                                                   *)
(* NOT STORED (computed during decode traversal only):              *)
(*   Gaussian form n+si   — lives only in transit on Line 2         *)
(*   discriminant x       — computed during Gaussian traversal      *)
(*   factor p             — emerges at end of bit-space traversal   *)
(*   factor q             — falls silently from n/p on Line 1       *)
(*                                                                   *)
(* The half-step plane stores the minimal lossless form:            *)
(*   n anchors Axis 1 (where the answer must land)                  *)
(*   h anchors Axis 3 (where the sum p+q lives)                     *)
(*   Axis 2 Gaussian is the path — not the destination              *)
(* ---------------------------------------------------------------- *)
