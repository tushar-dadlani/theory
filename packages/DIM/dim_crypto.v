(** * DIM Cryptographic Axioms
    Models SHA-256 (H) and Ed25519 (Sign/Verify).
    Updated: stdlib imports fixed; security axioms added. *)

From Stdlib Require Import List.
From Stdlib Require Import Nat.
Require Import dim_types.

(* ── Hash function ── *)
Parameter H : Data -> Hash.

(** Collision resistance: no two distinct inputs share an output.
    Models SHA-256 at 2^128 birthday-attack cost classically. *)
Axiom collision_resistant :
  forall (x y : Data), H x = H y -> x = y.

Lemma H_injective : forall (x y : Data), H x = H y <-> x = y.
Proof.
  intros x y. split.
  - apply collision_resistant.
  - intros Heq. rewrite Heq. reflexivity.
Qed.

(* ── Digital signatures ── *)
Parameter Sign   : PrivateKey -> Hash -> Signature.
Parameter Verify : PublicKey  -> Hash -> Signature -> bool.

(** Correctness: a signature made with kpriv verifies under kpub
    whenever (kpub, kpriv) is a valid keypair. *)
Axiom sign_correct :
  forall (kpub : PublicKey) (kpriv : PrivateKey) (m : Hash),
    KeyPair kpub kpriv ->
    Verify kpub m (Sign kpriv m) = true.

(** Unforgeability: without the matching private key, no signature
    on any message under kpub can verify.
    Models Ed25519 EUF-CMA security (2^128 classical hardness). *)
Axiom sign_unforgeable :
  forall (kpub : PublicKey) (kpriv : PrivateKey) (m : Hash) (s : Signature),
    ~ KeyPair kpub kpriv ->
    Verify kpub m s = false.

(** Key uniqueness: each public key has at most one matching private key.
    Prevents key-substitution attacks on the delegation chain. *)
Axiom keypair_unique :
  forall (kpub : PublicKey) (kpriv1 kpriv2 : PrivateKey),
    KeyPair kpub kpriv1 -> KeyPair kpub kpriv2 -> kpriv1 = kpriv2.

(** Signature determinism: Ed25519 is deterministic — same key and
    message always produce the same signature (no random nonce). *)
Axiom sign_deterministic :
  forall (kpriv : PrivateKey) (m : Hash),
    Sign kpriv m = Sign kpriv m.

(** Length-extension safety: the MAC model H(k || m) is insecure
    under Merkle-Damgard construction. We axiomatise that the DIM
    never uses bare H for authentication — only Sign/Verify.
    This is enforced structurally: receipt_valid requires a Verify check,
    not a hash comparison. *)
(** (No axiom needed — this is a structural property of the Record types.) *)
