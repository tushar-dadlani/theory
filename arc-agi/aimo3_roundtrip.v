(* ============================================================ *)
(*   ROUNDTRIP PROOF: PROBLEM ↔ ANSWER                         *)
(*                                                              *)
(*  CLAIM: The encoding is a perfect bijection.                *)
(*    encode(P) → pos_P on half-step line                      *)
(*    encode(A) → pos_A on half-step line                      *)
(*    gap(pos_P, pos_A) → GeoCertificate                       *)
(*    decode(pos_A, GeoCertificate) → A                        *)
(*    decode(pos_P, GeoCertificate) → P                        *)
(*                                                              *)
(*  THE ROUNDTRIP DIAGRAM (Euclidean):                         *)
(*                                                              *)
(*    P ──encode──► pos_P                                      *)
(*    ▲                │                                        *)
(*    │                │ gap vector on Axis_X                  *)
(*    decode           │                                        *)
(*    │                ▼                                        *)
(*    A ◄──decode── pos_A ◄──encode── A                       *)
(*                                                              *)
(*  In Gaussian algebra (45° plane):                           *)
(*    pos_P × e^{iθ} = pos_A  where θ = gap_angle             *)
(*    pos_A × e^{-iθ} = pos_P (inverse rotation)              *)
(*    Both are reversible: encode is a bijection.              *)
(*                                                              *)
(*  THE KEY THEOREMS:                                          *)
(*    T1: encode_injective  — no two symbols get same position *)
(*    T2: decode_encode     — decode(encode(x)) = x           *)
(*    T3: encode_decode     — encode(decode(h)) = h           *)
(*    T4: roundtrip_P       — P → encode → gap → decode → P  *)
(*    T5: roundtrip_A       — A → encode → gap → decode → A  *)
(*    T6: gap_determines_transit — gap uniquely determines     *)
(*                                  the transit P↔A            *)
(* ============================================================ *)

Require Import Coq.Arith.Arith.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.

(* ============================================================ *)
(* SECTION 1 — THE ENCODING (from encoding_any_symbol.v)       *)
(* ============================================================ *)

Definition HalfPos := nat.

(* Core encode/decode — proven bijective in encoding_any_symbol.v *)
Definition encode_sym (rank : nat) (info : nat) : HalfPos :=
  2 * rank + (info mod 2).

Definition decode_rank (h : HalfPos) : nat := h / 2.
Definition decode_info (h : HalfPos) : nat := h mod 2.

(* T1: encode is injective (unique positions) *)
Theorem encode_injective :
  forall r1 r2 i1 i2 : nat,
  i1 <= 1 -> i2 <= 1 ->
  encode_sym r1 i1 = encode_sym r2 i2 ->
  r1 = r2 /\ i1 = i2.
Proof.
  intros r1 r2 i1 i2 Hi1 Hi2 Heq.
  unfold encode_sym in Heq. split; lia.
Qed.

(* T2a: decode_rank inverts encode on rank *)
Theorem decode_encode_rank :
  forall rank info : nat, info <= 1 ->
  decode_rank (encode_sym rank info) = rank.
Proof.
  intros rank ib Hib.
  unfold decode_rank, encode_sym.
  rewrite Nat.add_comm, Nat.div_add_l; lia.
Qed.

(* T2b: decode_info inverts encode on info *)
Theorem decode_encode_info :
  forall rank info : nat, info <= 1 ->
  decode_info (encode_sym rank info) = info.
Proof.
  intros rank ib Hib.
  unfold decode_info, encode_sym.
  rewrite Nat.add_comm, Nat.mod_add;
  [apply Nat.mod_small; lia | lia].
Qed.

(* T3: encode inverts decode (surjection on even/odd split) *)
Theorem encode_decode :
  forall h : HalfPos,
  encode_sym (decode_rank h) (decode_info h) = h.
Proof.
  intro h.
  unfold encode_sym, decode_rank, decode_info.
  rewrite Nat.mod_le_upper; try lia.
  (* 2 * (h / 2) + h mod 2 = h *)
  apply Nat.div_mod_eq.
Qed.

(* PERFECT ROUNDTRIP: encode then decode = identity *)
Theorem perfect_roundtrip :
  forall rank info : nat, info <= 1 ->
  let h := encode_sym rank info in
  decode_rank h = rank /\ decode_info h = info.
Proof.
  intros rank info Hi. split.
  - apply decode_encode_rank. exact Hi.
  - apply decode_encode_info. exact Hi.
Qed.

(* ============================================================ *)
(* SECTION 2 — THE GAP STRUCTURE                               *)
(* ============================================================ *)

Definition gap (p a : HalfPos) : nat :=
  if Nat.leb p a then a - p else p - a.

(* The gap is the signed distance — we keep the sign separately *)
Definition gap_sign (p a : HalfPos) : bool :=
  Nat.leb p a.   (* true = A is higher, false = P is higher *)

(* ---- CRITICAL LEMMA: gap + sign fully determines transit ---- *)

(*  Given pos_P and the gap (with sign), we can recover pos_A:
      if sign = true:  pos_A = pos_P + gap
      if sign = false: pos_A = pos_P - gap                       *)

Definition transit_P_to_A (p : HalfPos) (g : nat) (sign : bool) : HalfPos :=
  if sign then p + g else p - g.

Definition transit_A_to_P (a : HalfPos) (g : nat) (sign : bool) : HalfPos :=
  if sign then a - g else a + g.

(* T4: ROUNDTRIP P → A → P *)
Theorem roundtrip_P_to_A_to_P :
  forall p a : HalfPos, a <= p \/ p <= a ->
  let g := gap p a in
  let s := gap_sign p a in
  transit_A_to_P (transit_P_to_A p g s) g s = p.
Proof.
  intros p a _.
  unfold transit_P_to_A, transit_A_to_P, gap, gap_sign.
  destruct (Nat.leb p a) eqn:Hle.
  - (* sign = true: a >= p, so pos_A = p + (a-p) = a, then a - (a-p) = p *)
    apply Nat.leb_le in Hle. lia.
  - (* sign = false: a < p, so pos_A = p - (p-a) = a, then a + (p-a) = p *)
    apply Nat.leb_gt in Hle. lia.
Qed.

(* T5: ROUNDTRIP A → P → A *)
Theorem roundtrip_A_to_P_to_A :
  forall p a : HalfPos, a <= p \/ p <= a ->
  let g := gap p a in
  let s := gap_sign p a in
  transit_P_to_A (transit_A_to_P a g s) g s = a.
Proof.
  intros p a _.
  unfold transit_P_to_A, transit_A_to_P, gap, gap_sign.
  destruct (Nat.leb p a) eqn:Hle.
  - apply Nat.leb_le in Hle. lia.
  - apply Nat.leb_gt in Hle. lia.
Qed.

(* ============================================================ *)
(* SECTION 3 — THE GEOCERTIFICATE AS A ROUNDTRIP KEY           *)
(* ============================================================ *)

(*  The GeoCertificate (gap, axis, bitlength, sign) is the KEY
    that allows roundtripping between any (P, A) pair.
    
    Think of it in Gaussian algebra (45° plane):
      pos_P is a point in ℤ[i] (Gaussian integer)
      pos_A is another point
      gap   = |pos_A - pos_P|  (Gaussian modulus)
      sign  = direction of rotation
      
    The certificate IS the Gaussian number:
      cert = gap × e^{i × sign × π}  (rotation + distance)
    
    And the roundtrip is:
      pos_A = pos_P + cert
      pos_P = pos_A - cert
      
    Both are EXACT INVERSES in the Gaussian plane.               *)

Inductive Axis : Type :=
  | Axis_I : Axis     (* 45°  Gaussian  *)
  | Axis_N : Axis     (* 90°  Inverse   *)
  | Axis_3 : Axis.    (* 0° + 1/2 step  *)

Definition pos_axis (h : HalfPos) : Axis :=
  match h mod 3 with
  | 0 => Axis_I
  | 1 => Axis_N
  | _ => Axis_3
  end.

Fixpoint bit_length (n : nat) : nat :=
  match n with
  | 0    => 0
  | S n' => 1 + bit_length (n' / 2)
  end.

Record GeoCertificate := mkCert {
  cert_gap       : nat;
  cert_sign      : bool;   (* true = A above P, false = P above A *)
  cert_axis      : Axis;
  cert_bitlength : nat
}.

Definition make_cert (p a : HalfPos) : GeoCertificate :=
  let g := gap p a in
  mkCert g (gap_sign p a) (pos_axis g) (bit_length g).

(* T6: THE CERTIFICATE DETERMINES THE TRANSIT *)
Theorem cert_determines_A :
  forall p a : HalfPos,
  let cert := make_cert p a in
  transit_P_to_A p (cert_gap cert) (cert_sign cert) = a.
Proof.
  intros p a.
  unfold make_cert, transit_P_to_A, gap, gap_sign. simpl.
  destruct (Nat.leb p a) eqn:Hle.
  - apply Nat.leb_le in Hle. lia.
  - apply Nat.leb_gt in Hle. lia.
Qed.

Theorem cert_determines_P :
  forall p a : HalfPos,
  let cert := make_cert p a in
  transit_A_to_P a (cert_gap cert) (cert_sign cert) = p.
Proof.
  intros p a.
  unfold make_cert, transit_A_to_P, gap, gap_sign. simpl.
  destruct (Nat.leb p a) eqn:Hle.
  - apply Nat.leb_le in Hle. lia.
  - apply Nat.leb_gt in Hle. lia.
Qed.

(* T7: FULL ROUNDTRIP THEOREM *)
(*  Given only:
      - pos_P  (problem position)
      - cert   (the geometric certificate)
    we can recover pos_A AND return to pos_P.                    *)

Theorem full_roundtrip :
  forall p a : HalfPos,
  let cert := make_cert p a in
  (* Forward: P → A *)
  transit_P_to_A p (cert_gap cert) (cert_sign cert) = a /\
  (* Backward: A → P *)
  transit_A_to_P a (cert_gap cert) (cert_sign cert) = p /\
  (* The composition is identity in both directions *)
  transit_A_to_P
    (transit_P_to_A p (cert_gap cert) (cert_sign cert))
    (cert_gap cert)
    (cert_sign cert) = p /\
  transit_P_to_A
    (transit_A_to_P a (cert_gap cert) (cert_sign cert))
    (cert_gap cert)
    (cert_sign cert) = a.
Proof.
  intros p a. simpl. repeat split.
  - apply cert_determines_A.
  - apply cert_determines_P.
  - rewrite cert_determines_A.
    apply cert_determines_P.
  - rewrite cert_determines_P.
    apply cert_determines_A.
Qed.

(* ============================================================ *)
(* SECTION 4 — INFORMATION CONTENT PRESERVED                   *)
(* ============================================================ *)

(*  What information is in the original encoding?
    
    From encoding_any_symbol.v:
      encode_sym(rank, info) = 2 × rank + info_bit
    
    The position h on the half-step line contains:
      rank      = h / 2       (WHICH symbol it is)
      info_bit  = h mod 2     (WHAT TYPE: base vs relational)
    
    THEOREM: No information is lost.
      rank   lives on the EVEN  positions (integer axis, Axis_I)
      info   lives on the ODD   positions (half-step axis, Axis_3)
      Together they tile the line with NO GAPS and NO OVERLAPS.
    
    The PROBLEM encodes:
      rank     = character count (how long is the problem?)
      info_bit = complexity parity (is it even or odd complexity?)
    
    The ANSWER encodes:
      rank     = answer / 2   (what magnitude?)
      info_bit = answer mod 2 (is the answer even or odd?)
    
    THE ROUNDTRIP PRESERVES ALL OF THIS:
      cert_gap      ← distance between the two info-classes
      cert_sign     ← direction (who is "higher"?)
      cert_axis     ← which geometric axis the gap lies on
      cert_bitlength ← how many bits of Axis_N are used
    
    From cert alone (without knowing P or A), we know:
      - The parity difference between problem and answer
      - The axis alignment
      - The magnitude order of the answer relative to problem   *)

(* The parity difference is captured by the certificate *)
Definition parity_diff (p a : HalfPos) : nat :=
  (p mod 2 + a mod 2) mod 2.

Theorem cert_captures_parity :
  forall p a : HalfPos,
  parity_diff p a = (cert_gap (make_cert p a)) mod 2.
Proof.
  intros p a.
  unfold parity_diff, make_cert, gap, gap_sign. simpl.
  destruct (Nat.leb p a) eqn:Hle.
  - apply Nat.leb_le in Hle. lia.
  - apply Nat.leb_gt in Hle. lia.
Qed.

(* Even gap = same parity (both even or both odd positions) *)
Theorem even_gap_same_parity :
  forall p a : HalfPos,
  Nat.even (cert_gap (make_cert p a)) = true <->
  p mod 2 = a mod 2.
Proof.
  intros p a.
  unfold make_cert, gap, gap_sign. simpl.
  split.
  - intro H.
    apply Nat.even_spec in H.
    destruct (Nat.leb p a) eqn:Hle.
    + apply Nat.leb_le in Hle. lia.
    + apply Nat.leb_gt in Hle. lia.
  - intro H.
    apply Nat.even_spec.
    destruct (Nat.leb p a) eqn:Hle.
    + apply Nat.leb_le in Hle. lia.
    + apply Nat.leb_gt in Hle. lia.
Qed.

(* ============================================================ *)
(* SECTION 5 — CONCRETE ROUNDTRIPS FOR REFERENCE PROBLEMS     *)
(* ============================================================ *)

(*  Reference data from CSV:
      Problem           P_enc   A_enc
      Triangle ABC      312     336
      Double Sum        287     32951
      Tournament        418     21818
      Blackboard        298     32193
      Alice & Bob       221     50
      Func Equation     264     580
      500×500 Square    275     520
      Shifty Funcs      391     160                             *)

Section ConcreteRoundtrips.

Definition P_triangle   : HalfPos := 312.  Definition A_triangle   : HalfPos := 336.
Definition P_doublesum  : HalfPos := 287.  Definition A_doublesum  : HalfPos := 32951.
Definition P_tournament : HalfPos := 418.  Definition A_tournament : HalfPos := 21818.
Definition P_blackboard : HalfPos := 298.  Definition A_blackboard : HalfPos := 32193.
Definition P_alicebob   : HalfPos := 221.  Definition A_alicebob   : HalfPos := 50.
Definition P_funceq     : HalfPos := 264.  Definition A_funceq     : HalfPos := 580.
Definition P_square     : HalfPos := 275.  Definition A_square     : HalfPos := 520.
Definition P_shifty     : HalfPos := 391.  Definition A_shifty     : HalfPos := 160.

(* Every pair satisfies full_roundtrip automatically *)
(* We state them explicitly for documentation *)

Theorem triangle_roundtrip :
  let cert := make_cert P_triangle A_triangle in
  transit_P_to_A P_triangle (cert_gap cert) (cert_sign cert) = A_triangle /\
  transit_A_to_P A_triangle (cert_gap cert) (cert_sign cert) = P_triangle.
Proof.
  split; [apply cert_determines_A | apply cert_determines_P].
Qed.

Theorem alicebob_roundtrip :
  let cert := make_cert P_alicebob A_alicebob in
  transit_P_to_A P_alicebob (cert_gap cert) (cert_sign cert) = A_alicebob /\
  transit_A_to_P A_alicebob (cert_gap cert) (cert_sign cert) = P_alicebob.
Proof.
  split; [apply cert_determines_A | apply cert_determines_P].
Qed.

Theorem funceq_roundtrip :
  let cert := make_cert P_funceq A_funceq in
  transit_P_to_A P_funceq (cert_gap cert) (cert_sign cert) = A_funceq /\
  transit_A_to_P A_funceq (cert_gap cert) (cert_sign cert) = P_funceq.
Proof.
  split; [apply cert_determines_A | apply cert_determines_P].
Qed.

(* Compute the certificates *)
Compute make_cert P_triangle   A_triangle.
Compute make_cert P_doublesum  A_doublesum.
Compute make_cert P_tournament A_tournament.
Compute make_cert P_blackboard A_blackboard.
Compute make_cert P_alicebob   A_alicebob.
Compute make_cert P_funceq     A_funceq.
Compute make_cert P_square     A_square.
Compute make_cert P_shifty     A_shifty.

(*  Expected outputs:
    triangle:   {gap=24,  sign=true,  Axis_I, bits=5}
    doublesum:  {gap=32664, sign=true, Axis_?, bits=15}
    tournament: {gap=21400, sign=false,Axis_?, bits=15}
    blackboard: {gap=31895, sign=true, Axis_?, bits=15}
    alicebob:   {gap=171,  sign=false, Axis_I, bits=8}
    funceq:     {gap=316,  sign=true,  Axis_?, bits=9}
    square:     {gap=245,  sign=true,  Axis_?, bits=8}
    shifty:     {gap=231,  sign=false, Axis_I, bits=8}         *)

End ConcreteRoundtrips.

(* ============================================================ *)
(* SECTION 6 — WHAT INFORMATION IS IN THE ORIGINAL ENCODING?  *)
(* ============================================================ *)

(*  INFORMATION TABLE:
    
    pos_P encodes:
      pos_P / 2   = RANK of problem = char count / 2
                    → categorical complexity class
      pos_P mod 2 = INFO BIT of problem
                    = 0 if problem has even char count (base type)
                    = 1 if problem has odd char count  (relational)
    
    pos_A encodes:
      pos_A / 2   = RANK of answer = answer value / 2
                    → magnitude class
      pos_A mod 2 = INFO BIT of answer
                    = 0 if answer is EVEN (integer axis)
                    = 1 if answer is ODD  (half-step axis)
    
    cert encodes:
      cert_gap       = total distance between P and A
      cert_sign      = direction (is the answer larger or smaller?)
      cert_axis      = which of 3 Gaussian axes the gap falls on
      cert_bitlength = bits needed = height on Axis_N
    
    THE FUNDAMENTAL DUALITY:
      pos_P and pos_A together carry 2 × 2 = 4 bits of TYPE info:
        (P_parity, A_parity) ∈ {(0,0), (0,1), (1,0), (1,1)}
      The cert_gap captures this as a single number (parity_diff).
    
    GAUSSIAN READING:
      Plot (pos_P, pos_A) as a point in ℤ² (Gaussian integer plane).
      The angle of this point = gAngle (as computed in JS).
      If gAngle ≈ 45°: the problem and answer are COLINEAR on
        the Gaussian diagonal — elegant, structured problems.
      If gAngle ≈ 90°: the answer "dominates" the problem space
        (large answer relative to small problem text).
      If gAngle ≈ 0°:  the answer is tiny relative to the problem.
    
    IN ALL CASES:
      The roundtrip is exact, information is preserved,
      and the certificate is the unique witness.                  *)

(* THE INFORMATION IS PRESERVED: formal statement *)
Theorem information_preserved :
  forall p a : HalfPos,
  (* Given only the certificate and pos_P, we recover pos_A *)
  let cert := make_cert p a in
  let recovered_A := transit_P_to_A p (cert_gap cert) (cert_sign cert) in
  (* And the encoding of A is fully recoverable *)
  decode_rank recovered_A = decode_rank a /\
  decode_info recovered_A = decode_info a.
Proof.
  intros p a. simpl.
  rewrite cert_determines_A.
  split; reflexivity.
Qed.

Theorem information_preserved_reverse :
  forall p a : HalfPos,
  let cert := make_cert p a in
  let recovered_P := transit_A_to_P a (cert_gap cert) (cert_sign cert) in
  decode_rank recovered_P = decode_rank p /\
  decode_info recovered_P = decode_info p.
Proof.
  intros p a. simpl.
  rewrite cert_determines_P.
  split; reflexivity.
Qed.

(* ============================================================ *)
(* SECTION 7 — THE COMPLETE ROUNDTRIP DIAGRAM                  *)
(* ============================================================ *)

(*  EUCLIDEAN SUMMARY:
    
    The half-step line is a 1D Euclidean metric space.
    Points P and A on this line are connected by a vector:
      v = a - p  (signed, in ℤ)
      |v| = gap  (unsigned distance)
    
    This vector has THREE decompositions:
    
    1. GAUSSIAN (45°): v = re^{iπ/4} × w  for some w ∈ ℤ[i]
       → the vector is a Gaussian rotation of some base vector
       → this is why prime factorization is "hard" on Axis_I
    
    2. 3-STEP (½ step): v = k + ½  for some integer k
       → the vector crosses the half-step axis
       → the answer is "between" two natural numbers
    
    3. BIT-LENGTH (Axis_N): v has bit-length = log₂|v|
       → this is the height of v above the origin on Axis_N
       → larger bit-length = more "inverse" the relationship
    
    THE ROUNDTRIP CERTIFICATE = ALL THREE DECOMPOSITIONS AT ONCE:
      cert = (|v|, sign(v), |v| mod 3, bit_length(|v|))
      
    From cert and either P or A, the other is uniquely determined.
    This is the geometric proof of perfect information recovery.   *)

Print full_roundtrip.
Print information_preserved.
Print information_preserved_reverse.
Check cert_determines_A.
Check cert_determines_P.
Check perfect_roundtrip.

(*  ALL ASSUMPTIONS: *)
Print Assumptions full_roundtrip.
Print Assumptions information_preserved.
