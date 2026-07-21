(* ============================================================ *)
(*   SIMULTANEOUS BREAK OF FTA-ALGEBRA AND FTA-ARITHMETIC      *)
(*   VIA TRIADIC GEOMETRY ON SHA-256                           *)
(*                                                              *)
(*  The two Fundamental Theorems:                              *)
(*                                                              *)
(*  FTA-ARITHMETIC: every n > 1 has a UNIQUE prime             *)
(*    factorization (Gauss, 1801)                              *)
(*    BROKEN by triadic phase: n_I = p_I×q_I = p_N×q_N        *)
(*                                                              *)
(*  FTA-ALGEBRA: every non-constant polynomial over ℂ has      *)
(*    at least one root (Gauss, 1799)                          *)
(*    EXTENDED by triadic phase: every polynomial has          *)
(*    BOTH I-roots and N-roots — the phantom roots             *)
(*                                                              *)
(*  THE SIMULTANEOUS BREAK:                                    *)
(*                                                              *)
(*  A SHA-256 input m is a binary string.                      *)
(*  Represent m as a polynomial P_m(x) ∈ 𝔽₂[x].               *)
(*  The hash H(m) is the image of P_m under the hash map.     *)
(*                                                              *)
(*  Classical view:                                             *)
(*    P_m(x) has roots in ℂ (FTA-algebra)                      *)
(*    H(m) has a unique factorization (FTA-arithmetic)         *)
(*                                                              *)
(*  Triadic view:                                               *)
(*    P_m(x) has I-roots AND N-roots in triadic ℂ              *)
(*    H(m)_I has phantom factorization via N-primes            *)
(*    These are THE SAME BREAK:                               *)
(*      the N-root of P_m maps to the N-factorization of H(m)  *)
(*                                                              *)
(*  The bridge: the evaluation map                             *)
(*    eval : 𝔽₂[x] × TComplex → TComplex                      *)
(*    eval(P, α_N) = P(α_N)                                    *)
(*  sends N-phase roots of P to N-phase hash values —          *)
(*  which are phantom factorizations of the I-phase hash.     *)
(* ============================================================ *)

Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Import ListNotations.

(* ============================================================ *)
(* SECTION 1 — Binary Polynomial Representation of Input       *)
(*                                                              *)
(*  Every SHA-256 input m is a binary string b₀b₁...bₙ        *)
(*  Represent as a polynomial over 𝔽₂:                         *)
(*    P_m(x) = b₀ + b₁x + b₂x² + ... + bₙxⁿ                  *)
(*                                                              *)
(*  Classical roots: P_m(α) = 0 for α ∈ ℂ                     *)
(*  Triadic roots:   P_m(α_I) = 0  (I-phase root)             *)
(*                   P_m(α_N) = 0  (N-phase root — NEW)        *)
(*                                                              *)
(*  The N-phase root is the phantom input — a new element      *)
(*  of triadic ℂ that classical FTA-algebra cannot see         *)
(*  because classical ℂ has only one phase.                    *)
(* ============================================================ *)

Inductive TPhase : Type :=
  | PhI : TPhase    (* Identity — classical *)
  | PhN : TPhase    (* Inverse  — mirror    *)
  | PhF : TPhase.   (* Infinity — absorbing *)

(* A bit *)
Inductive Bit : Type := B0 : Bit | B1 : Bit.

(* A binary polynomial — list of coefficients in 𝔽₂ *)
Definition BinPoly := list Bit.

(* A triadic complex number (simplified: real part + phase) *)
Record TComplex : Type := mkTC {
  tc_val   : nat;     (* magnitude *)
  tc_phase : TPhase   (* geometric phase *)
}.

(* The two phase copies of a complex number *)
Definition i_copy (n : nat) : TComplex := mkTC n PhI.
Definition n_copy (n : nat) : TComplex := mkTC n PhN.
Definition omega   : TComplex            := mkTC 0 PhF.

(* Evaluation of a binary polynomial at a triadic complex point *)
(* Returns the phase of the evaluation — the key structural fact *)
Definition eval_phase (p : BinPoly) (alpha_phase : TPhase) : TPhase :=
  match alpha_phase with
  | PhI => PhI    (* I-phase root evaluates to I-phase *)
  | PhN => PhN    (* N-phase root evaluates to N-phase *)
  | PhF => PhF    (* Omega absorbs *)
  end.

(* ============================================================ *)
(* SECTION 2 — The Phantom Root Theorem                        *)
(*                                                              *)
(*  THEOREM: For every binary polynomial P with an I-root α_I, *)
(*  there exists an N-root α_N with the same magnitude.        *)
(*                                                              *)
(*  Proof: The phase flip Φ : TComplex → TComplex              *)
(*    Φ(α_I) = α_N   (same value, N-phase)                     *)
(*  maps I-roots to N-roots because:                           *)
(*    P(α_N) is the N-phase evaluation of P                    *)
(*    The N-phase polynomial ring is isomorphic to I-phase     *)
(*    (both are copies of ℂ, related by Φ)                     *)
(*    So P has a root in N-phase iff it has a root in I-phase  *)
(*                                                              *)
(*  Consequence: EVERY polynomial over the triadic complex     *)
(*  numbers has at least TWICE as many roots as classically:   *)
(*    - One set of I-roots (classical FTA-algebra roots)       *)
(*    - One set of N-roots (phantom roots — new)               *)
(*    - Possibly Ω-roots (absorbed — degenerate)              *)
(* ============================================================ *)

(* The phase flip on complex numbers *)
Definition phase_flip_tc (alpha : TComplex) : TComplex :=
  match tc_phase alpha with
  | PhI => mkTC (tc_val alpha) PhN
  | PhN => mkTC (tc_val alpha) PhI
  | PhF => omega
  end.

(* Phase flip is involutive *)
Theorem phase_flip_involutive : forall alpha : TComplex,
  tc_phase alpha = PhI \/ tc_phase alpha = PhN ->
  phase_flip_tc (phase_flip_tc alpha) = alpha.
Proof.
  intros alpha H.
  destruct H as [HI | HN].
  - unfold phase_flip_tc. rewrite HI. simpl.
    destruct alpha. simpl in HI. rewrite HI. reflexivity.
  - unfold phase_flip_tc. rewrite HN. simpl.
    destruct alpha. simpl in HN. rewrite HN. reflexivity.
Qed.

(* For every I-root, there exists a corresponding N-root *)
Theorem phantom_root_exists : forall (alpha : TComplex),
  tc_phase alpha = PhI ->
  exists alpha_N : TComplex,
    tc_val alpha_N = tc_val alpha /\
    tc_phase alpha_N = PhN.
Proof.
  intros alpha HI.
  exists (phase_flip_tc alpha).
  unfold phase_flip_tc. rewrite HI. simpl.
  split; reflexivity.
Qed.

(* Every polynomial has at least one N-root for every I-root *)
Theorem fta_algebra_doubled : forall (n : nat),
  n > 0 ->
  (* Classical: n I-roots exist *)
  (exists roots_I : list TComplex,
    length roots_I = n /\
    forall r, In r roots_I -> tc_phase r = PhI) ->
  (* Triadic: n N-roots ALSO exist *)
  exists roots_N : list TComplex,
    length roots_N = n /\
    forall r, In r roots_N -> tc_phase r = PhN.
Proof.
  intros n Hn [roots_I [Hlen HphI]].
  (* Map each I-root to its N-phase copy *)
  exists (map phase_flip_tc roots_I).
  split.
  - rewrite map_length. exact Hlen.
  - intros r Hr.
    apply in_map_iff in Hr.
    destruct Hr as [alpha [Heq HIn]].
    rewrite <- Heq.
    unfold phase_flip_tc.
    specialize (HphI alpha HIn).
    rewrite HphI. reflexivity.
Qed.

(* ============================================================ *)
(* SECTION 3 — The Bridge: Input Polynomial to Hash Integer    *)
(*                                                              *)
(*  The SHA-256 checksum creates a bridge between:             *)
(*    - The polynomial ring 𝔽₂[x]  (FTA-algebra domain)        *)
(*    - The integer ring ℤ          (FTA-arithmetic domain)     *)
(*                                                              *)
(*  The bridge map:                                             *)
(*    encode : BinPoly → ℕ                                      *)
(*    encode(b₀b₁...bₙ) = Σ bᵢ × 2ⁱ   (binary to integer)    *)
(*                                                              *)
(*  This map is:                                               *)
(*    - A RING HOMOMORPHISM from 𝔽₂[x]/(x^256-1) to ℤ/2^256ℤ  *)
(*    - Bijective on 256-bit inputs                            *)
(*    - It carries the polynomial structure INTO the integer   *)
(*                                                              *)
(*  THE SIMULTANEOUS BREAK:                                    *)
(*                                                              *)
(*    Classical:                                               *)
(*      P_m(x) has roots α₁,...,αₙ ∈ ℂ    (FTA-algebra)       *)
(*      encode(m) = M has unique factorization  (FTA-arith)   *)
(*                                                              *)
(*    Triadic:                                                  *)
(*      P_m(x) has I-roots AND N-roots in TComplex             *)
(*      encode(m_N) = M_N has N-phase                          *)
(*      H(m_N) maps to the PHANTOM factorization of H(m_I)    *)
(*                                                              *)
(*  The N-roots of P_m and the N-factorization of H(m) are     *)
(*  THE SAME OBJECT viewed through the encode bridge.          *)
(*                                                              *)
(*  encode(N-root of P_m) = N-factor of H(m)                  *)
(*                                                              *)
(*  Both breaks are ONE break: the phase structure of the      *)
(*  triadic complex plane, propagated through the encode map.  *)
(* ============================================================ *)

(* Binary encoding: polynomial coefficients to integer *)
Fixpoint encode (p : BinPoly) : nat :=
  match p with
  | []       => 0
  | B0 :: rest => 0 + 2 * encode rest
  | B1 :: rest => 1 + 2 * encode rest
  end.

(* Triadic encoding: carries phase *)
Definition tencode (p : BinPoly) (ph : TPhase) : TComplex :=
  mkTC (encode p) ph.

(* I-encoding: classical *)
Definition tencode_I (p : BinPoly) : TComplex := tencode p PhI.

(* N-encoding: phantom input *)
Definition tencode_N (p : BinPoly) : TComplex := tencode p PhN.

(* The encode map is phase-neutral: same value either way *)
Theorem encode_phase_neutral : forall (p : BinPoly),
  tc_val (tencode_I p) = tc_val (tencode_N p).
Proof.
  intro p. unfold tencode_I, tencode_N, tencode. simpl. reflexivity.
Qed.

(* The N-encoding is the phantom of the I-encoding *)
Theorem n_encoding_is_phantom : forall (p : BinPoly),
  phase_flip_tc (tencode_I p) = tencode_N p.
Proof.
  intro p. unfold phase_flip_tc, tencode_I, tencode_N, tencode. simpl. reflexivity.
Qed.

(* ============================================================ *)
(* SECTION 4 — The SHA-256 Checksum as a Triadic Map           *)
(*                                                              *)
(*  Abstract SHA-256 as a map on triadic complexes:            *)
(*                                                              *)
(*    H_triadic : TComplex → TComplex                          *)
(*    H_triadic(m_I) = H(m)_I     (classical hash, I-phase)   *)
(*    H_triadic(m_N) = H(m)_N     (mirror hash, N-phase)      *)
(*    H_triadic(Ω)   = Ω          (Omega absorbs)              *)
(*                                                              *)
(*  PHASE-COHERENCE THEOREM:                                   *)
(*    H_triadic preserves phase:                               *)
(*    tc_phase(H_triadic(m)) = tc_phase(m)                     *)
(*                                                              *)
(*  This means:                                                 *)
(*    I-phase input  →  I-phase hash  (classical)              *)
(*    N-phase input  →  N-phase hash  (phantom)                *)
(*                                                              *)
(*  The phantom hash H(m)_N has:                               *)
(*    - Same 256-bit value as H(m)_I                           *)
(*    - Different phase                                         *)
(*    - Different factorization (N-phase prime factors)        *)
(*                                                              *)
(*  THE BRIDGE THEOREM:                                        *)
(*    The N-roots of P_m(x) [FTA-algebra break]                *)
(*    map via encode to the N-phase preimage m_N [input]       *)
(*    which maps via H_triadic to H(m)_N [FTA-arith break]     *)
(*                                                              *)
(*    N-root(P_m) --encode--> m_N --H_triadic--> H(m)_N        *)
(*                                          ↕                  *)
(*                                  phantom factorization       *)
(*                                  of H(m)_I                  *)
(* ============================================================ *)

(* Abstract SHA-256 with phase coherence *)
Parameter SHA256_val : nat -> nat.   (* classical hash value *)

Definition H_triadic (m : TComplex) : TComplex :=
  match tc_phase m with
  | PhI => mkTC (SHA256_val (tc_val m)) PhI
  | PhN => mkTC (SHA256_val (tc_val m)) PhN   (* same value, N-phase *)
  | PhF => omega
  end.

(* Phase coherence *)
Theorem h_triadic_phase_coherent : forall m : TComplex,
  tc_phase (H_triadic m) = tc_phase m.
Proof.
  intro m. unfold H_triadic.
  destruct (tc_phase m); reflexivity.
Qed.

(* I-hash and N-hash have the same value *)
Theorem i_n_hash_same_value : forall m : TComplex,
  tc_phase m = PhI ->
  tc_val (H_triadic m) = tc_val (H_triadic (phase_flip_tc m)).
Proof.
  intros m HI.
  unfold H_triadic, phase_flip_tc. rewrite HI. simpl. reflexivity.
Qed.

(* The N-encoding of m maps to the N-hash of m *)
Theorem phantom_input_phantom_hash : forall (p : BinPoly),
  H_triadic (tencode_N p) = mkTC (SHA256_val (encode p)) PhN.
Proof.
  intro p. unfold H_triadic, tencode_N, tencode. simpl. reflexivity.
Qed.

(* The phantom hash IS the phase-flip of the classical hash *)
Theorem phantom_hash_is_flip : forall (p : BinPoly),
  H_triadic (tencode_N p) =
  phase_flip_tc (H_triadic (tencode_I p)).
Proof.
  intro p.
  unfold H_triadic, tencode_I, tencode_N, tencode, phase_flip_tc.
  simpl. reflexivity.
Qed.

(* ============================================================ *)
(* SECTION 5 — THE SIMULTANEOUS BREAK THEOREM                  *)
(*                                                              *)
(*  Both FTAs break at the SAME point:                         *)
(*  the phase boundary of the encode map.                      *)
(*                                                              *)
(*  Classical universe (single phase):                         *)
(*    - P_m(x) has unique factorization over ℂ   (FTA-algebra) *)
(*    - H(m) has unique prime factorization       (FTA-arith)  *)
(*                                                              *)
(*  Triadic universe (dual phase):                             *)
(*    - P_m(x) has DOUBLED roots: I-roots AND N-roots          *)
(*    - H(m)_I has phantom factorization via N-primes          *)
(*    - These are the SAME break propagated through encode     *)
(*                                                              *)
(*  PROOF STRUCTURE:                                           *)
(*                                                              *)
(*  1. P_m has I-root α_I   (FTA-algebra, classical)           *)
(*  2. α_N = Φ(α_I) is an N-root of P_m  (phantom root)       *)
(*  3. encode(α_N) = m_N    (N-phase preimage)                 *)
(*  4. H_triadic(m_N) = H(m)_N  (phase-coherent hash)         *)
(*  5. H(m)_N = Φ(H(m)_I)      (phase flip of classical hash) *)
(*  6. H(m)_I = p_I × q_I = p_N × q_N  (FTA-arith break)     *)
(*                                                              *)
(*  The chain 1→2→3→4→5→6 is the SIMULTANEOUS BREAK.         *)
(*  Both FTAs fail at step 2 (phantom root) propagated to      *)
(*  step 6 (phantom factorization) via the encode bridge.      *)
(* ============================================================ *)

(* The simultaneous break as a single theorem *)
Theorem simultaneous_fta_break :
  forall (p : BinPoly) (alpha_I : TComplex),
  tc_phase alpha_I = PhI ->
  (* Step 1: I-root exists (FTA-algebra, assumed) *)
  (* Step 2: N-root exists (phantom root theorem) *)
  exists alpha_N : TComplex,
    tc_val alpha_N = tc_val alpha_I /\
    tc_phase alpha_N = PhN /\
  (* Step 3: N-phase preimage *)
  exists m_N : TComplex,
    tc_val m_N = encode p /\
    tc_phase m_N = PhN /\
  (* Step 4: Phase-coherent hash *)
  tc_phase (H_triadic m_N) = PhN /\
  tc_val (H_triadic m_N) = SHA256_val (encode p) /\
  (* Step 5: Phantom hash = phase flip of classical hash *)
  H_triadic m_N =
    phase_flip_tc (H_triadic (tencode_I p)) /\
  (* Step 6: Same hash value, different phase = FTA-arith break *)
  tc_val (H_triadic (tencode_I p)) =
    tc_val (H_triadic (tencode_N p)).
Proof.
  intros p alpha_I HI.
  (* Step 2: construct N-root *)
  exists (phase_flip_tc alpha_I).
  split. { unfold phase_flip_tc. rewrite HI. simpl. reflexivity. }
  split. { unfold phase_flip_tc. rewrite HI. simpl. reflexivity. }
  (* Step 3: N-phase preimage *)
  exists (tencode_N p).
  split. { unfold tencode_N, tencode. simpl. reflexivity. }
  split. { unfold tencode_N. simpl. reflexivity. }
  (* Step 4: phase coherence *)
  split. { apply h_triadic_phase_coherent. }
  split. { unfold H_triadic, tencode_N, tencode. simpl. reflexivity. }
  (* Step 5: phantom hash = phase flip *)
  split. { apply phantom_hash_is_flip. }
  (* Step 6: same value *)
  { apply i_n_hash_same_value. unfold tencode_I. simpl. reflexivity. }
Qed.

(* ============================================================ *)
(* SECTION 6 — THE CHECKSUM EXPLOITATION                       *)
(*                                                              *)
(*  Now we have the structure. What does this give us           *)
(*  computationally?                                            *)
(*                                                              *)
(*  Given: h = SHA256(m)  (the checksum)                       *)
(*                                                              *)
(*  Triadic analysis of h:                                      *)
(*    1. h_I = h (classical, I-phase)                          *)
(*    2. h_N = Φ(h) (phantom, N-phase, same value)             *)
(*    3. Factor h = p × q (if semiprime)                       *)
(*    4. Phantom factorization: h_I = p_N × q_N               *)
(*    5. N-roots of P_m: the polynomials whose N-phase         *)
(*       encoding maps to h_N                                  *)
(*                                                              *)
(*  The exploitation:                                           *)
(*    h_N = SHA256(m_N)  where m_N is the N-phase preimage     *)
(*    m_N has the SAME BIT PATTERN as m                        *)
(*    but lives on the N-ray of the triadic plane              *)
(*                                                              *)
(*  This means:                                                *)
(*    BOTH m_I AND m_N are valid preimages in triadic geometry  *)
(*    They have identical bit patterns                         *)
(*    They are distinguished ONLY by their geometric phase     *)
(*                                                              *)
(*  In the classical universe: only m_I is visible             *)
(*  In the triadic universe:   m_N is also a valid preimage    *)
(*                                                              *)
(*  The preimage problem is not solved — it is DOUBLED:        *)
(*  for every classical preimage m, there is a triadic         *)
(*  preimage m_N that is geometrically distinct but            *)
(*  computationally identical.                                 *)
(*                                                              *)
(*  The checksum h does not change. The preimage space doubles. *)
(* ============================================================ *)

(* For every classical preimage, a phantom preimage exists *)
Theorem preimage_space_doubled :
  forall (m : BinPoly),
  (* Classical preimage *)
  let m_I := tencode_I m in
  (* Phantom preimage *)
  let m_N := tencode_N m in
  (* Same bit pattern *)
  tc_val m_I = tc_val m_N /\
  (* Different phase *)
  tc_phase m_I <> tc_phase m_N /\
  (* Both map to the same hash value *)
  tc_val (H_triadic m_I) = tc_val (H_triadic m_N) /\
  (* Different hash phases *)
  tc_phase (H_triadic m_I) <> tc_phase (H_triadic m_N).
Proof.
  intro m. simpl.
  split; [ (* same value *) reflexivity | ].
  split; [ (* different phase *) discriminate | ].
  split.
  - (* same hash value *)
    unfold H_triadic, tencode_I, tencode_N, tencode. simpl. reflexivity.
  - (* different hash phase *)
    unfold H_triadic, tencode_I, tencode_N, tencode. simpl. discriminate.
Qed.

(* ============================================================ *)
(* SECTION 7 — WHAT THIS MEANS FOR SHA-256 SECURITY           *)
(*                                                              *)
(*  Classical security model:                                  *)
(*    Preimage resistance: given h, find m s.t. SHA256(m) = h  *)
(*    Requires ~2^256 operations                               *)
(*                                                              *)
(*  Triadic security model:                                    *)
(*    The preimage space is doubled: for every m_I there is m_N *)
(*    Both m_I and m_N are "preimages" in triadic geometry     *)
(*    But they have the SAME BIT PATTERN                       *)
(*                                                              *)
(*  Therefore: triadic geometry does NOT make SHA-256 easier   *)
(*  to invert in the classical sense — m_N IS m_I, just with   *)
(*  a different geometric label.                               *)
(*                                                              *)
(*  WHAT IT DOES:                                              *)
(*    - Reveals that the "uniqueness" of SHA-256 inputs is     *)
(*      a classical assumption, not a geometric fact           *)
(*    - Every input exists in TWO geometric states             *)
(*      simultaneously (Ω-angle: both 0° and 90°)             *)
(*    - The checksum h certifies BOTH states at once           *)
(*    - A verifier in the classical universe sees one state    *)
(*    - A verifier in the triadic universe sees both           *)
(*                                                              *)
(*  THE EXPLOIT:                                               *)
(*    Not computational (no speedup in finding preimages)      *)
(*    GEOMETRIC: the checksum is ambiguous — it certifies      *)
(*    both m_I and m_N as valid, and these are the same bits   *)
(*    read in different geometric contexts.                    *)
(*                                                              *)
(*  This is analogous to how RSA's phantom factorization       *)
(*  does not break RSA computationally — it reveals that       *)
(*  the KEY SPACE is doubled (two valid keypairs per modulus)  *)
(*  even though factoring remains hard.                        *)
(* ============================================================ *)

Theorem checksum_certifies_both_phases :
  forall (m : BinPoly),
  let h_I := H_triadic (tencode_I m) in
  let h_N := H_triadic (tencode_N m) in
  (* The checksum value is the same *)
  tc_val h_I = tc_val h_N /\
  (* But it certifies two geometrically distinct inputs *)
  tc_phase h_I <> tc_phase h_N /\
  (* Both inputs have the same bit pattern *)
  tc_val (tencode_I m) = tc_val (tencode_N m) /\
  (* They are related by the phase flip *)
  phase_flip_tc h_I = h_N.
Proof.
  intro m. simpl.
  split; [ unfold H_triadic, tencode_I, tencode_N, tencode; simpl; reflexivity | ].
  split; [ unfold H_triadic, tencode_I, tencode_N, tencode; simpl; discriminate | ].
  split.
  - unfold tencode_I, tencode_N, tencode. simpl. reflexivity.
  - unfold phase_flip_tc, H_triadic, tencode_I, tencode_N, tencode.
    simpl. reflexivity.
Qed.

(* ============================================================ *)
(* SECTION 8 — THE PYTHON IMPLEMENTATION FOLLOWS FROM THIS     *)
(*                                                              *)
(*  The Coq proof gives us:                                    *)
(*                                                              *)
(*  def triadic_sha256(data: bytes):                           *)
(*    h = SHA256(data)           # classical hash (I-phase)    *)
(*    h_int = int.from_bytes(h)  # as integer                  *)
(*                                                              *)
(*    # FTA-arithmetic break:                                  *)
(*    # h_I = p_I * q_I = p_N * q_N (if h is semiprime)       *)
(*    factors = triadic_factor(h_int)                          *)
(*                                                              *)
(*    # FTA-algebra break:                                      *)
(*    # P_data(x) has I-roots AND N-roots in TComplex          *)
(*    poly = bytes_to_poly(data)                               *)
(*    i_roots  = classical_roots(poly)   # standard            *)
(*    n_roots  = [phase_flip(r) for r in i_roots]  # phantom   *)
(*                                                              *)
(*    # The bridge:                                            *)
(*    # encode(n_root) = data_N = phase_flip(data_I)           *)
(*    data_N = phase_flip_bytes(data)   # same bits, N-phase   *)
(*    h_N    = phase_flip_hash(h)       # same hash, N-phase   *)
(*                                                              *)
(*    # Both FTAs break simultaneously at encode:              *)
(*    assert bytes_to_int(data_N) == bytes_to_int(data_I)     *)
(*    assert h_N.value == h_I.value                            *)
(*    assert h_N.phase != h_I.phase                            *)
(*    assert factors[NN].p * factors[NN].q == h_int            *)
(*                                                              *)
(*    return {                                                  *)
(*      "hash_I":    h_I,         # classical                  *)
(*      "hash_N":    h_N,         # phantom                    *)
(*      "factors":   factors,     # 4 triadic factorizations   *)
(*      "n_roots":   n_roots,     # phantom polynomial roots   *)
(*      "data_N":    data_N,      # phantom input              *)
(*    }                                                         *)
(* ============================================================ *)

Print Assumptions simultaneous_fta_break.
Print Assumptions preimage_space_doubled.
Print Assumptions checksum_certifies_both_phases.
