(** * Content-Addressed Computation: A Minimal Core

    Self-contained formalization of the central idea:

        F(X) = Y

    where F, X, and Y are all identified by their content hash,
    and every application is signed cryptographically.

    No imports from the DIM project — this file compiles standalone
    with Coq/Rocq 8.18+.

    Five results are proved:

      T1 (Identity Binding)              — equal hashes imply equal results
      T2 (Non-Repudiation)               — a valid receipt proves key ownership
      T3 (Cross-Party Reproducibility)   — same H(F) + H(X) → same H(Y)
      T4 (Seeded Is Deterministic)       — a seeded receipt is a valid receipt
      T5 (Seeded Reproducibility)        — same H(F), H(X), H(seed) → same H(Y)

    T4–T5 establish that probabilistic computation (LLM inference,
    sampling, Monte Carlo) reduces to deterministic computation under
    Definition 1 once the seed is fixed and content-addressed.
*)

(* ════════════════════════════════════════════════════════
   Section 1: Primitive Types
   ════════════════════════════════════════════════════════ *)

(** We represent hashes as natural numbers so the file needs no
    external axioms for equality decidability.  The exact type is
    immaterial; what matters is the axioms below. *)
Definition Hash := nat.

Parameter Data       : Type.
Parameter PublicKey  : Type.
Parameter PrivateKey : Type.
Parameter Signature  : Type.

(** A keypair relation: (pk, sk) are a matching public/private pair. *)
Parameter KeyPair : PublicKey -> PrivateKey -> Prop.

(* ════════════════════════════════════════════════════════
   Section 2: Content-Addressing
   ════════════════════════════════════════════════════════ *)

(** Hash algorithm identifiers — standalone copy for cas_core. *)
Inductive HashAlg := SHA256 | SHA3_256 | BLAKE3.

(** Hash function family. H_alg alg d is the hash of d under algorithm alg. *)
Parameter H_alg : HashAlg -> Data -> Hash.

(** H is SHA-256 — backward-compatible alias for all existing proofs. *)
Definition H : Data -> Hash := H_alg SHA256.

(** Per-algorithm collision resistance: for each HashAlg, no two distinct
    inputs share a hash. Stated per-algorithm so the system remains sound
    under any single algorithm, regardless of the status of others. *)
Axiom collision_resistant :
  forall (alg : HashAlg) (x y : Data),
    H_alg alg x = H_alg alg y -> x = y.

(* ════════════════════════════════════════════════════════
   Section 3: Content-Addressed Function Application
   ════════════════════════════════════════════════════════ *)

(** apply_cas hf hx = hy
    Apply the function whose hash is hf to the input whose hash is hx
    and return the hash of the result.

    Being a Coq function, apply_cas is *pure and deterministic*:
    the same arguments always yield the same result.  This is the
    key property exploited by T3. *)
Parameter apply_cas : Hash -> Hash -> Hash.

(* ════════════════════════════════════════════════════════
   Section 4: Cryptographic Signatures
   ════════════════════════════════════════════════════════ *)

(** Sign sk m — produce a signature over message m with private key sk.
    Models Ed25519 deterministic signing. *)
Parameter Sign   : PrivateKey -> Hash -> Signature.

(** Verify pk m s — check that signature s on message m was made by
    the holder of the private key matching pk. *)
Parameter Verify : PublicKey  -> Hash -> Signature -> bool.

(** To sign a triple (H(F), H(X), H(Y)) we hash it first. *)
Parameter hash_triple : Hash -> Hash -> Hash -> Hash.

(** Unforgeability (extractive EUF-CMA):
    if Verify accepts a signature, then it was produced by the holder
    of the corresponding private key.
    Models Ed25519 at 2^128 classical / 2^64 quantum security. *)
Axiom sign_unforgeable :
  forall (pk : PublicKey) (m : Hash) (s : Signature),
    Verify pk m s = true ->
    exists sk, KeyPair pk sk /\ s = Sign sk m.

(* ════════════════════════════════════════════════════════
   Section 5: Receipt
   A Receipt is a signed claim: "I (r_operator) applied H(F) to H(X)
   and obtained H(Y)."
   ════════════════════════════════════════════════════════ *)

Record Receipt := mkReceipt {
  r_function : Hash;      (** H(F) — content hash of the function *)
  r_input    : Hash;      (** H(X) — content hash of the input    *)
  r_output   : Hash;      (** H(Y) — content hash of the output   *)
  r_operator : PublicKey; (** who performed the computation        *)
  r_sig      : Signature; (** signature over (H(F), H(X), H(Y))   *)
  r_hash_alg : HashAlg;  (** algorithm used to hash function, input, output *)
}.

(** A receipt is valid when:
    (a) the signature checks out, AND
    (b) apply_cas confirms the functional relationship. *)
Definition receipt_valid (r : Receipt) : Prop :=
  Verify (r_operator r)
         (hash_triple (r_function r) (r_input r) (r_output r))
         (r_sig r) = true
  /\
  apply_cas (r_function r) (r_input r) = r_output r.

(* ════════════════════════════════════════════════════════
   T1: Identity Binding
   If two function-input pairs share the same hashes, they produce
   the same output hash.  Proof: collision resistance collapses the
   Data objects; apply_cas then has identical arguments.
   ════════════════════════════════════════════════════════ *)

Theorem identity_binding :
  forall (alg : HashAlg) (f1 f2 x1 x2 : Data),
    H_alg alg f1 = H_alg alg f2 ->
    H_alg alg x1 = H_alg alg x2 ->
    apply_cas (H_alg alg f1) (H_alg alg x1) =
    apply_cas (H_alg alg f2) (H_alg alg x2).
Proof.
  intros alg f1 f2 x1 x2 Hf Hx.
  apply (collision_resistant alg) in Hf.
  apply (collision_resistant alg) in Hx.
  subst. reflexivity.
Qed.

(* ════════════════════════════════════════════════════════
   T2: Non-Repudiation
   A valid receipt proves that the signing operator's private key
   was used.  The operator cannot deny having performed the
   computation.
   ════════════════════════════════════════════════════════ *)

Theorem non_repudiation :
  forall (r : Receipt),
    receipt_valid r ->
    exists sk,
      KeyPair (r_operator r) sk /\
      r_sig r = Sign sk (hash_triple (r_function r) (r_input r) (r_output r)).
Proof.
  intros r [Hverify _].
  apply sign_unforgeable in Hverify.
  destruct Hverify as [sk [Hkp Hsig]].
  exists sk. exact (conj Hkp Hsig).
Qed.

(* ════════════════════════════════════════════════════════
   T3: Cross-Party Reproducibility
   Any two parties who each hold a valid receipt for the same
   H(F) applied to the same H(X) must agree on H(Y).
   Proof: apply_cas is a pure Coq function; congruence closes the goal.
   ════════════════════════════════════════════════════════ *)

Theorem cross_party_reproducibility :
  forall (r1 r2 : Receipt),
    receipt_valid r1 ->
    receipt_valid r2 ->
    r_function r1 = r_function r2 ->
    r_input    r1 = r_input    r2 ->
    r_output   r1 = r_output   r2.
Proof.
  intros r1 r2 [_ Happly1] [_ Happly2] Hfn Hin.
  congruence.
Qed.

(* ════════════════════════════════════════════════════════
   Section 6: Seeded (Probabilistic) Computation

   Probabilistic functions — LLM inference, sampling, Monte Carlo —
   draw randomness from a seed.  If the seed is fixed and
   content-addressed alongside X, the computation becomes
   observationally deterministic: F(X ∥ seed) = Y.

   A seeded computation is NOT a new primitive.  It is an ordinary
   Receipt whose input field is H(concat X seed).  T4 makes this
   precise; T5 gives cross-party reproducibility for free.
   ════════════════════════════════════════════════════════ *)

(** Seeds are data objects, drawn once and fixed before the call. *)
Definition Seed := Data.

(** Byte-level concatenation of a data object and a seed. *)
Parameter concat : Data -> Seed -> Data.

(** A seeded receipt is a standard Receipt together with a witness
    that its input field equals H(concat X seed). *)
Definition seeded_receipt_valid (r : Receipt) (x : Data) (seed : Seed) : Prop :=
  r_input r = H (concat x seed) /\
  receipt_valid r.

(* ════════════════════════════════════════════════════════
   T4: Seeded Is Deterministic
   A seeded computation is a valid content-addressed computation.
   Proof: immediate — seeded_receipt_valid includes receipt_valid.
   ════════════════════════════════════════════════════════ *)

Theorem seeded_is_deterministic :
  forall (r : Receipt) (x : Data) (seed : Seed),
    seeded_receipt_valid r x seed ->
    receipt_valid r.
Proof.
  intros r x seed [_ Hreceipt].
  exact Hreceipt.
Qed.

(* ════════════════════════════════════════════════════════
   T5: Seeded Cross-Party Reproducibility
   Two operators who applied the same F to the same X with the same
   seed must agree on H(Y).

   The seed is fixed and content-addressed; collision resistance
   collapses equal hash witnesses to equal Data objects, so the
   combined inputs H(concat X seed) are identical.  T3 then closes
   the goal.
   ════════════════════════════════════════════════════════ *)

Theorem seeded_cross_party_reproducibility :
  forall (r1 r2 : Receipt) (x1 x2 : Data) (s1 s2 : Seed),
    seeded_receipt_valid r1 x1 s1 ->
    seeded_receipt_valid r2 x2 s2 ->
    r_function r1 = r_function r2 ->
    H x1 = H x2 ->
    H s1 = H s2 ->
    r_output r1 = r_output r2.
Proof.
  intros r1 r2 x1 x2 s1 s2 [Hin1 Hv1] [Hin2 Hv2] Hfn Hx Hs.
  apply collision_resistant in Hx.
  apply collision_resistant in Hs.
  subst x2. subst s2.
  apply (cross_party_reproducibility r1 r2 Hv1 Hv2 Hfn).
  rewrite Hin1, Hin2. reflexivity.
Qed.
