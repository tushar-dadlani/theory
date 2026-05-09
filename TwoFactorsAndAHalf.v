(* ============================================================ *)
(*  TwoFactorsAndAHalf.v                                        *)
(*                                                              *)
(*  THE OBSERVATION:                                            *)
(*    Every position on the half-step line decomposes into     *)
(*    THREE ingredients, each recovered separately:             *)
(*                                                              *)
(*       position = 2 * rank + info_bit                         *)
(*       │          │     │      │                              *)
(*       │          │     │      └── the half-step (0 or 1)    *)
(*       │          │     └────────  factor 1 (the rank)        *)
(*       │          └──────────────  factor 2 (the doubling)    *)
(*       └─────────────────────────  total encoding              *)
(*                                                              *)
(*  TWO FACTORS AND HALF A STEP:                                *)
(*    Factor 1: rank      — which symbol/number it is          *)
(*    Factor 2: 2         — the axis-doubling (multiplicative) *)
(*    Half-step: info_bit — phase / orthogonal-axis selector   *)
(*                                                              *)
(*  EACH IS RECOVERED INDEPENDENTLY:                            *)
(*    rank     = position / 2                                   *)
(*    factor 2 = position - info_bit  (always divisible by 2)  *)
(*    info_bit = position mod 2                                 *)
(*                                                              *)
(*  This is the COMPLETE encoding theorem of the framework.    *)
(*  The half-step is perpendicular to (and independent of)     *)
(*  the rank — they are recovered by orthogonal projections.    *)
(*                                                              *)
(*  Axiom count: 0.                                             *)
(* ============================================================ *)

From Coq Require Import Arith Lia.

(* ============================================================ *)
(*  PART 1 — THE THREE INGREDIENTS                              *)
(* ============================================================ *)

(* The encoding: position = 2 * rank + info_bit. *)
Definition encode (rank info_bit : nat) : nat :=
  2 * rank + info_bit.

(* The three independent decoders. *)
Definition decode_rank (pos : nat) : nat := pos / 2.
Definition decode_info (pos : nat) : nat := pos mod 2.
Definition decode_doubled (pos : nat) : nat := pos - (pos mod 2).

(* ============================================================ *)
(*  PART 2 — RECOVERY: EACH FACTOR INDEPENDENTLY                *)
(* ============================================================ *)

(* Recovery 1: the rank (factor 1). *)
Theorem recover_rank : forall r i,
  i <= 1 -> decode_rank (encode r i) = r.
Proof.
  intros r i Hi. unfold decode_rank, encode.
  destruct i.
  - replace (2 * r + 0) with (r * 2) by lia.
    rewrite Nat.div_mul by lia. reflexivity.
  - destruct i; [|lia].
    replace (2 * r + 1) with (1 + r * 2) by lia.
    rewrite Nat.div_add by lia.
    simpl. reflexivity.
Qed.

(* Recovery 2: the half-step (info_bit). *)
Theorem recover_info : forall r i,
  i <= 1 -> decode_info (encode r i) = i.
Proof.
  intros r i Hi. unfold decode_info, encode.
  destruct i.
  - replace (2 * r + 0) with (r * 2) by lia.
    rewrite Nat.mod_mul by lia. reflexivity.
  - destruct i; [|lia].
    replace (2 * r + 1) with (1 + r * 2) by lia.
    rewrite Nat.mod_add by lia.
    simpl. reflexivity.
Qed.

(* Recovery 3: the doubled component (factor 2). *)
Theorem recover_doubled : forall r i,
  i <= 1 -> decode_doubled (encode r i) = 2 * r.
Proof.
  intros r i Hi. unfold decode_doubled, encode.
  destruct i.
  - replace (2 * r + 0) with (r * 2) by lia.
    rewrite Nat.mod_mul by lia. lia.
  - destruct i; [|lia].
    replace (2 * r + 1) with (1 + r * 2) by lia.
    rewrite Nat.mod_add by lia.
    simpl. lia.
Qed.

(* ============================================================ *)
(*  PART 3 — INDEPENDENCE: THE THREE PROJECTIONS DON'T MIX     *)
(*                                                              *)
(*  The rank is independent of the info_bit:                   *)
(*  changing info_bit doesn't change the rank, and vice versa. *)
(* ============================================================ *)

(* The half-step doesn't affect the rank. *)
Theorem half_step_doesnt_affect_rank : forall r,
  decode_rank (encode r 0) = decode_rank (encode r 1).
Proof.
  intro r.
  rewrite (recover_rank r 0) by lia.
  rewrite (recover_rank r 1) by lia.
  reflexivity.
Qed.

(* The rank doesn't affect the half-step. *)
Theorem rank_doesnt_affect_half_step : forall r1 r2 i,
  i <= 1 -> decode_info (encode r1 i) = decode_info (encode r2 i).
Proof.
  intros r1 r2 i Hi.
  rewrite (recover_info r1 i Hi).
  rewrite (recover_info r2 i Hi).
  reflexivity.
Qed.

(* ============================================================ *)
(*  PART 4 — RECONSTRUCTION FROM THE THREE PARTS                *)
(*                                                              *)
(*  Given the rank and the half-step, you reconstruct the      *)
(*  position. No information is lost.                           *)
(* ============================================================ *)

Theorem reconstruct : forall pos,
  pos = encode (decode_rank pos) (decode_info pos).
Proof.
  intro pos. unfold encode, decode_rank, decode_info.
  pose proof (Nat.div_mod pos 2 ltac:(lia)) as H.
  lia.
Qed.

(* ============================================================ *)
(*  PART 5 — INJECTIVITY: THE ENCODING IS LOSSLESS              *)
(* ============================================================ *)

Theorem encoding_injective : forall r1 r2 i1 i2,
  i1 <= 1 -> i2 <= 1 ->
  encode r1 i1 = encode r2 i2 ->
  r1 = r2 /\ i1 = i2.
Proof.
  intros r1 r2 i1 i2 H1 H2 Heq.
  unfold encode in Heq.
  split; lia.
Qed.

(* ============================================================ *)
(*  PART 6 — THE GRAND THEOREM                                  *)
(*                                                              *)
(*  Two factors and half a step — the complete decomposition. *)
(*                                                              *)
(*  Every position pos on the half-step line has:              *)
(*    - rank      r = pos / 2          (factor 1)              *)
(*    - doubling  d = 2                (factor 2 — the axis)   *)
(*    - half-step b = pos mod 2        (the ½)                 *)
(*                                                              *)
(*  Each is recovered by an independent integer operation.     *)
(*  Together they reconstruct pos exactly.                      *)
(* ============================================================ *)

Theorem two_factors_and_a_half_step : forall pos,
  let r := decode_rank pos in
  let b := decode_info pos in
  (* Three pieces, recovered independently: *)
  pos = 2 * r + b /\
  (* The rank lives on the factor-1 axis: *)
  r = pos / 2 /\
  (* The half-step is the orthogonal coordinate: *)
  b = pos mod 2 /\
  (* The half-step takes only two values: *)
  (b = 0 \/ b = 1) /\
  (* The reconstruction is exact: *)
  pos = encode r b.
Proof.
  intro pos. simpl.
  split; [|split; [|split; [|split]]].
  - unfold decode_rank, decode_info.
    pose proof (Nat.div_mod pos 2 ltac:(lia)). lia.
  - reflexivity.
  - reflexivity.
  - unfold decode_info.
    pose proof (Nat.mod_upper_bound pos 2 ltac:(lia)). lia.
  - apply reconstruct.
Qed.

(* ============================================================ *)
(*  PART 7 — INTERPRETATION                                     *)
(*                                                              *)
(*  Every value in the framework decomposes into:              *)
(*                                                              *)
(*    1. WHICH (rank)      — the I-axis coordinate             *)
(*    2. SCALE (factor 2)  — the doubling that puts the         *)
(*                            two perpendicular axes onto       *)
(*                            the same number line              *)
(*    3. WHICH AXIS (½)    — the orthogonal selector            *)
(*                            (info_bit ∈ {0, 1})               *)
(*                                                              *)
(*  The first two are continuous (multiplicative).              *)
(*  The third is a single bit (additive, ½ of a unit step).    *)
(*  Together: 2 factors + ½ step.                               *)
(*                                                              *)
(*  Each is recovered by a SEPARATE integer operation:          *)
(*    /, *, mod                                                 *)
(*                                                              *)
(*  And those three operations span the framework.             *)
(* ============================================================ *)

Print Assumptions two_factors_and_a_half_step.
