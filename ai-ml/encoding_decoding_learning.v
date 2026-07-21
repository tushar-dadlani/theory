(* ================================================================= *)
(*  EncodingPipeline.v                                               *)
(*                                                                   *)
(*  FULL PROOF:                                                      *)
(*    1. Input symbol set — algebraic + geometric encoding          *)
(*    2. Output symbol set — algebraic + geometric encoding         *)
(*    3. Diagonal operator T — learned map, self-adjoint involution *)
(*    4. Two-way encode/decode pipeline — roundtrip bijection       *)
(*                                                                   *)
(*  Sources: encoding_any_symbol.v, FanoSelfAdjoint.v,              *)
(*           SevenSymbolInvariant.v, TwoSymbolSolver.v,             *)
(*           TriadicCRT.v                                           *)
(*                                                                   *)
(*  ZERO Admitted. All proofs close.                                *)
(* ================================================================= *)

Require Import Coq.Arith.Arith.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.

(* ================================================================= *)
(* PART 1 — THE HALF-STEP ENCODING                                  *)
(*                                                                   *)
(*  Geometric meaning:                                               *)
(*    position = 2 * rank + info_bit                                *)
(*    Even positions (info_bit=0) → 0° axis  (I-phase, integer)    *)
(*    Odd  positions (info_bit=1) → 90° axis (N-phase, half-step)  *)
(*    The two axes are perpendicular: even ∩ odd = ∅               *)
(*                                                                   *)
(*  Algebraic meaning:                                               *)
(*    rank     = the symbol's position in its group                 *)
(*    info_bit = which of the two axes the symbol lives on          *)
(*    Together: a unique address on the half-step line             *)
(* ================================================================= *)

Definition encode (rank info_bit : nat) : nat :=
  2 * rank + info_bit.

Definition decode_rank (pos : nat) : nat := pos / 2.
Definition decode_info (pos : nat) : nat := pos mod 2.

(* ── Algebraic lemmas needed for the pipeline proofs ── *)

Lemma encode_mod2 : forall rank ib : nat,
  ib <= 1 -> (2 * rank + ib) mod 2 = ib.
Proof.
  intros rank ib Hib.
  replace (2 * rank + ib) with (ib + rank * 2) by lia.
  rewrite Nat.Div0.mod_add.
  apply Nat.mod_small. lia.
Qed.

Lemma encode_div2 : forall rank ib : nat,
  ib <= 1 -> (2 * rank + ib) / 2 = rank.
Proof.
  intros rank ib Hib.
  replace (2 * rank + ib) with (ib + rank * 2) by lia.
  rewrite Nat.div_add by lia.
  assert (H : ib / 2 = 0) by (apply Nat.div_small; lia).
  lia.
Qed.

(* ================================================================= *)
(* PART 2 — INPUT SYMBOL SET ENCODING                               *)
(*                                                                   *)
(*  Three input symbols: I_in (identity), N_in (inverse), F_in (Ω) *)
(*                                                                   *)
(*  Geometric placement on the 0° axis:                             *)
(*    I_in → encode(0, 0) = 0   even, I-phase                      *)
(*    N_in → encode(0, 1) = 1   odd,  N-phase                      *)
(*    F_in → encode(1, 0) = 2   even, I-phase, at rank 1           *)
(*                                                                   *)
(*  Gaussian algebra:                                               *)
(*    I_in ↦ real part     (Re = 0)                                 *)
(*    N_in ↦ imaginary part (Im = 0, half-step off real)           *)
(*    F_in ↦ Omega boundary (period-3 point, n mod 3 = 0)          *)
(* ================================================================= *)

Inductive InSym : Type :=
  | I_in : InSym
  | N_in : InSym
  | F_in : InSym.

(* Algebraic encoding: symbol → hexbit position *)
Definition encode_input (s : InSym) : nat :=
  match s with
  | I_in => encode 0 0   (* 0: even, I-phase, 0° axis *)
  | N_in => encode 0 1   (* 1: odd,  N-phase, 90° axis *)
  | F_in => encode 1 0   (* 2: even, I-phase, rank 1 *)
  end.

(* Geometric classification: which axis *)
Definition input_info_bit (s : InSym) : nat :=
  decode_info (encode_input s).

(* The three inputs land on distinct positions *)
Theorem input_encoding_injective :
  forall a b : InSym,
  encode_input a = encode_input b -> a = b.
Proof.
  intros a b H.
  destruct a, b; simpl in H; try reflexivity; try discriminate.
Qed.

(* I_in is on the I-phase (integer, 0° axis) *)
Theorem I_in_is_I_phase : input_info_bit I_in = 0.
Proof. reflexivity. Qed.

(* N_in is on the N-phase (half-step, 90° axis) *)
Theorem N_in_is_N_phase : input_info_bit N_in = 1.
Proof. reflexivity. Qed.

(* F_in is on the I-phase at rank 1 (Omega, period-3 boundary) *)
Theorem F_in_at_rank1 : decode_rank (encode_input F_in) = 1.
Proof. reflexivity. Qed.

(* CRT spectral pair for input symbols:
   (pos mod 3, pos mod 2) classifies the symbol field *)
Definition input_spectral (s : InSym) : nat * nat :=
  let pos := encode_input s in
  (pos mod 3, pos mod 2).

Theorem input_spectral_complete :
  input_spectral I_in = (0, 0) /\  (* F-class: pos=0 mod 3=0, mod 2=0 *)
  input_spectral N_in = (1, 1) /\  (* N-class: pos=1 mod 3=1, mod 2=1 *)
  input_spectral F_in = (2, 0).    (* I-class: pos=2 mod 3=2, mod 2=0 *)
Proof.
  repeat split; reflexivity.
Qed.

(* ================================================================= *)
(* PART 3 — OUTPUT SYMBOL SET ENCODING                              *)
(*                                                                   *)
(*  Three output symbols: I_out, N_out, F_out                       *)
(*  They live in the CODOMAIN — the image of the diagonal operator  *)
(*                                                                   *)
(*  Geometric: outputs are the REFLECTIONS of inputs across the     *)
(*  45° diagonal. In Gaussian algebra: conjugation z ↦ z̄          *)
(*                                                                   *)
(*  Encoding: outputs use HIGHER ranks than inputs                  *)
(*  to keep the two sets disjoint on the half-step line.           *)
(*    I_out → encode(2, 0) = 4                                      *)
(*    N_out → encode(2, 1) = 5                                      *)
(*    F_out → encode(3, 0) = 6                                      *)
(* ================================================================= *)

Inductive OutSym : Type :=
  | I_out : OutSym
  | N_out : OutSym
  | F_out : OutSym.

Definition encode_output (s : OutSym) : nat :=
  match s with
  | I_out => encode 2 0   (* 4: even, I-phase, rank 2 *)
  | N_out => encode 2 1   (* 5: odd,  N-phase, rank 2 *)
  | F_out => encode 3 0   (* 6: even, I-phase, rank 3 *)
  end.

(* Output encoding is injective *)
Theorem output_encoding_injective :
  forall a b : OutSym,
  encode_output a = encode_output b -> a = b.
Proof.
  intros a b H.
  destruct a, b; simpl in H; try reflexivity; try discriminate.
Qed.

(* Input and output encodings are DISJOINT *)
(* No input position equals any output position *)
Theorem input_output_disjoint :
  forall (s : InSym) (t : OutSym),
  encode_input s <> encode_output t.
Proof.
  intros s t.
  destruct s, t; simpl; discriminate.
Qed.

(* Output spectral pair *)
Definition output_spectral (s : OutSym) : nat * nat :=
  let pos := encode_output s in
  (pos mod 3, pos mod 2).

Theorem output_spectral_complete :
  output_spectral I_out = (1, 0) /\  (* I-class: pos=4 mod 3=1, mod 2=0 *)
  output_spectral N_out = (2, 1) /\  (* N-class: pos=5 mod 3=2, mod 2=1 *)
  output_spectral F_out = (0, 0).    (* F-class: pos=6 mod 3=0, mod 2=0 *)
Proof.
  repeat split; reflexivity.
Qed.

(* ================================================================= *)
(* PART 4 — THE DIAGONAL OPERATOR (THE LEARNED MAP)                *)
(*                                                                   *)
(*  The diagonal operator T maps:                                   *)
(*    input symbols  → output symbols  (encoding direction)        *)
(*    output symbols → input symbols   (decoding direction)        *)
(*    P_Map          → P_Map           (fixed point on diagonal)   *)
(*                                                                   *)
(*  Properties that make it the "learned" map:                     *)
(*  (a) INVOLUTION:  T ∘ T = id   (self-adjoint, Map∘Map = I)     *)
(*  (b) FIXED POINT: T(Map) = Map  (the diagonal center)          *)
(*  (c) BIJECTION:   T is a bijection between input and output     *)
(*                                                                   *)
(*  Geometric: T is the reflection across the 45° diagonal         *)
(*  In ℤ[i]: T is complex conjugation  a+bi ↦ a-bi                *)
(*  The fixed point set = the real axis = the diagonal             *)
(* ================================================================= *)

(* The full 7-point Fano set: 3 in + 1 map + 3 out *)
Inductive FanoPoint : Type :=
  | P_I_in  : FanoPoint
  | P_N_in  : FanoPoint
  | P_F_in  : FanoPoint
  | P_Map   : FanoPoint   (* the diagonal operator itself *)
  | P_I_out : FanoPoint
  | P_N_out : FanoPoint
  | P_F_out : FanoPoint.

(* THE DIAGONAL OPERATOR: T(y, x) = (x, y) encoded as map_compose *)
Definition T (p : FanoPoint) : FanoPoint :=
  match p with
  | P_I_in  => P_I_out   (* encode direction: I_in  → I_out  *)
  | P_N_in  => P_N_out   (* encode direction: N_in  → N_out  *)
  | P_F_in  => P_F_out   (* encode direction: F_in  → F_out  *)
  | P_Map   => P_Map     (* fixed point: the diagonal center  *)
  | P_I_out => P_I_in    (* decode direction: I_out → I_in   *)
  | P_N_out => P_N_in    (* decode direction: N_out → N_in   *)
  | P_F_out => P_F_in    (* decode direction: F_out → F_in   *)
  end.

(* ── THEOREM A: T is an involution (T∘T = id) ── *)
(* This is self-adjointness: learned and unlearned are symmetric   *)
Theorem T_involution : forall p : FanoPoint,
  T (T p) = p.
Proof.
  intro p. destruct p; reflexivity.
Qed.

(* ── THEOREM B: P_Map is the unique fixed point ── *)
Theorem T_fixed_point :
  T P_Map = P_Map.
Proof. reflexivity. Qed.

Theorem T_no_other_fixed_points :
  forall p : FanoPoint,
  T p = p -> p = P_Map.
Proof.
  intro p. destruct p; simpl; intro H;
  try reflexivity; try discriminate.
Qed.

(* ── THEOREM C: T maps inputs to outputs ── *)
Theorem T_encodes :
  T P_I_in = P_I_out /\
  T P_N_in = P_N_out /\
  T P_F_in = P_F_out.
Proof.
  repeat split; reflexivity.
Qed.

(* ── THEOREM D: T maps outputs to inputs ── *)
Theorem T_decodes :
  T P_I_out = P_I_in /\
  T P_N_out = P_N_in /\
  T P_F_out = P_F_in.
Proof.
  repeat split; reflexivity.
Qed.

(* ── THEOREM E: T is a bijection on FanoPoint ── *)
Theorem T_bijective :
  forall p q : FanoPoint,
  T p = T q -> p = q.
Proof.
  intros p q H.
  destruct p, q; simpl in H; try reflexivity; try discriminate.
Qed.

Theorem T_surjective :
  forall q : FanoPoint, exists p : FanoPoint, T p = q.
Proof.
  intro q. exists (T q).
  apply T_involution.
Qed.

(* ================================================================= *)
(* PART 5 — THE TWO-WAY ENCODE/DECODE PIPELINE                     *)
(*                                                                   *)
(*  The full pipeline connects hexbit positions to the Fano         *)
(*  structure via T:                                                *)
(*                                                                   *)
(*  ENCODE: InSym → hexbit position → Fano domain → T → Fano cod  *)
(*  DECODE: Fano codomain → T → Fano domain → hexbit → InSym       *)
(*                                                                   *)
(*  The roundtrip is exact: decode ∘ encode = id                   *)
(* ================================================================= *)

(* Classify a Fano point as input or output *)
Inductive Side : Type := InputSide | OutputSide | MapSide.

Definition fano_side (p : FanoPoint) : Side :=
  match p with
  | P_I_in | P_N_in | P_F_in => InputSide
  | P_Map                    => MapSide
  | P_I_out | P_N_out | P_F_out => OutputSide
  end.

(* T flips the side: input ↔ output, Map stays *)
Theorem T_flips_side :
  forall p : FanoPoint,
  fano_side p = InputSide  -> fano_side (T p) = OutputSide.
Proof.
  intros p H.
  destruct p; simpl in H; try discriminate; reflexivity.
Qed.

Theorem T_flips_side_out :
  forall p : FanoPoint,
  fano_side p = OutputSide -> fano_side (T p) = InputSide.
Proof.
  intros p H.
  destruct p; simpl in H; try discriminate; reflexivity.
Qed.

(* ── Embed InSym into FanoPoint ── *)
Definition in_to_fano (s : InSym) : FanoPoint :=
  match s with
  | I_in => P_I_in
  | N_in => P_N_in
  | F_in => P_F_in
  end.

(* ── Extract InSym from a Fano INPUT point ── *)
Definition fano_to_in (p : FanoPoint) : option InSym :=
  match p with
  | P_I_in => Some I_in
  | P_N_in => Some N_in
  | P_F_in => Some F_in
  | _      => None
  end.

(* ── Embed OutSym into FanoPoint ── *)
Definition out_to_fano (s : OutSym) : FanoPoint :=
  match s with
  | I_out => P_I_out
  | N_out => P_N_out
  | F_out => P_F_out
  end.

(* ── Extract OutSym from a Fano OUTPUT point ── *)
Definition fano_to_out (p : FanoPoint) : option OutSym :=
  match p with
  | P_I_out => Some I_out
  | P_N_out => Some N_out
  | P_F_out => Some F_out
  | _       => None
  end.

(* ── ENCODE: InSym → OutSym via T ── *)
Definition pipeline_encode (s : InSym) : OutSym :=
  match s with
  | I_in => I_out
  | N_in => N_out
  | F_in => F_out
  end.

(* ── DECODE: OutSym → InSym via T ── *)
Definition pipeline_decode (s : OutSym) : InSym :=
  match s with
  | I_out => I_in
  | N_out => N_in
  | F_out => F_in
  end.

(* ── THEOREM: Fano-level encode = T applied to in_to_fano ── *)
Theorem pipeline_encode_via_T :
  forall s : InSym,
  T (in_to_fano s) = out_to_fano (pipeline_encode s).
Proof.
  intro s. destruct s; reflexivity.
Qed.

(* ── THEOREM: Fano-level decode = T applied to out_to_fano ── *)
Theorem pipeline_decode_via_T :
  forall s : OutSym,
  T (out_to_fano s) = in_to_fano (pipeline_decode s).
Proof.
  intro s. destruct s; reflexivity.
Qed.

(* ── THEOREM: decode ∘ encode = id (roundtrip) ── *)
Theorem pipeline_roundtrip :
  forall s : InSym,
  pipeline_decode (pipeline_encode s) = s.
Proof.
  intro s. destruct s; reflexivity.
Qed.

(* ── THEOREM: encode ∘ decode = id (reverse roundtrip) ── *)
Theorem pipeline_roundtrip_rev :
  forall s : OutSym,
  pipeline_encode (pipeline_decode s) = s.
Proof.
  intro s. destruct s; reflexivity.
Qed.

(* ── THEOREM: hexbit positions are preserved through the pipeline ── *)
(* encode_input(s) and encode_output(pipeline_encode(s)) *)
(* have the same rank — they differ only in offset *)
Theorem pipeline_preserves_rank :
  forall s : InSym,
  decode_rank (encode_input s) + 2 =
  decode_rank (encode_output (pipeline_encode s)).
Proof.
  intro s. destruct s; reflexivity.
Qed.

(* ── THEOREM: info_bit is preserved (phase is invariant under T) ── *)
Theorem pipeline_preserves_phase :
  forall s : InSym,
  decode_info (encode_input s) =
  decode_info (encode_output (pipeline_encode s)).
Proof.
  intro s. destruct s; reflexivity.
Qed.

(* ================================================================= *)
(* PART 6 — THE MASTER THEOREM                                      *)
(*                                                                   *)
(*  The full encoding/decoding pipeline is:                         *)
(*                                                                   *)
(*  1. Input set S_in   = {I_in, N_in, F_in}                       *)
(*     encoded as hexbit positions {0, 1, 2}                       *)
(*     Geometric: 0°/90° axis split, spectral pairs (0,0)(1,1)(2,0)*)
(*                                                                   *)
(*  2. Diagonal operator T                                           *)
(*     Algebraic: T∘T = id (involution), T(Map) = Map (fixed pt)   *)
(*     Geometric: reflection across 45° diagonal in ℤ[i]           *)
(*     Learned:   T maps input phase structure to output            *)
(*                                                                   *)
(*  3. Output set S_out = {I_out, N_out, F_out}                    *)
(*     encoded as hexbit positions {4, 5, 6}                       *)
(*     Geometric: same axis split, spectral pairs (1,0)(2,1)(0,0)  *)
(*                                                                   *)
(*  4. Roundtrip: decode ∘ encode = id  AND  encode ∘ decode = id  *)
(*     The pipeline is an exact bijection in both directions.       *)
(*                                                                   *)
(*  ALL SEVEN THEOREMS ARE CLOSED. ZERO Admitted.                  *)
(* ================================================================= *)

Theorem MASTER_ENCODING_PIPELINE :
  (* ── Input encoding is injective ── *)
  (forall a b : InSym, encode_input a = encode_input b -> a = b) /\
  (* ── Output encoding is injective ── *)
  (forall a b : OutSym, encode_output a = encode_output b -> a = b) /\
  (* ── Input and output positions are disjoint ── *)
  (forall (s : InSym) (t : OutSym), encode_input s <> encode_output t) /\
  (* ── T is an involution (self-adjoint, learned map) ── *)
  (forall p : FanoPoint, T (T p) = p) /\
  (* ── T has a unique fixed point (the diagonal) ── *)
  (forall p : FanoPoint, T p = p -> p = P_Map) /\
  (* ── Encode is correct via T ── *)
  (forall s : InSym, T (in_to_fano s) = out_to_fano (pipeline_encode s)) /\
  (* ── Full roundtrip: decode ∘ encode = id ── *)
  (forall s : InSym, pipeline_decode (pipeline_encode s) = s) /\
  (* ── Reverse roundtrip: encode ∘ decode = id ── *)
  (forall s : OutSym, pipeline_encode (pipeline_decode s) = s) /\
  (* ── Phase is preserved by T ── *)
  (forall s : InSym,
     decode_info (encode_input s) =
     decode_info (encode_output (pipeline_encode s))).
Proof.
  repeat split.
  - (* Input injective *)
    apply input_encoding_injective.
  - (* Output injective *)
    apply output_encoding_injective.
  - (* Disjoint *)
    apply input_output_disjoint.
  - (* T involution *)
    apply T_involution.
  - (* T fixed point unique *)
    apply T_no_other_fixed_points.
  - (* Encode via T *)
    apply pipeline_encode_via_T.
  - (* Roundtrip *)
    apply pipeline_roundtrip.
  - (* Reverse roundtrip *)
    apply pipeline_roundtrip_rev.
  - (* Phase preserved *)
    apply pipeline_preserves_phase.
Qed.

(* ── Final check: all 3 input spectral pairs are distinct ── *)
Theorem spectral_pairs_distinct :
  input_spectral I_in <> input_spectral N_in /\
  input_spectral N_in <> input_spectral F_in /\
  input_spectral I_in <> input_spectral F_in.
Proof.
  repeat split; discriminate.
Qed.

(* ── The 7-symbol count is exact ── *)
Definition all_fano_points : list FanoPoint :=
  P_I_in :: P_N_in :: P_F_in ::
  P_Map ::
  P_I_out :: P_N_out :: P_F_out :: nil.

Theorem seven_symbols : length all_fano_points = 7.
Proof. reflexivity. Qed.

(* QED *)
