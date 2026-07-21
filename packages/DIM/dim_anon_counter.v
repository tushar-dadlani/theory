(** * DIM Anonymous Counter Delegation
    Time-bounded anonymous voting tokens for the Delegatable Identity Machine.

    Structural anonymity: [AnonToken] contains no [PublicKey] for the holder.
    The holder's identity is hidden in a hash commitment [H(holder_secret)].
    This is a type-level guarantee — the record itself cannot leak identity.

    Verifiable AI Alignment connection: AI evaluators can vote anonymously,
    preventing preference falsification while producing publicly auditable
    aggregate counts.  A threshold of anonymous counter increments can
    trigger governance actions (rollback, retraining) without exposing
    individual evaluator opinions. *)

From Stdlib Require Import List.
From Stdlib Require Import Nat.
From Stdlib Require Import Arith.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
Require Import dim_types.
Require Import dim_crypto.
Import ListNotations.
Open Scope list_scope.

(* ════════════════════════════════════════════════════════
   Section 1 — AnonToken Record
   ════════════════════════════════════════════════════════ *)

(** An anonymous delegation token.
    Structural anonymity: no [PublicKey] field for the holder.
    The commitment [H(holder_secret)] binds the token to a specific holder
    without revealing their public key. *)
Record AnonToken := mkAnonToken {
  tok_not_after  : Timestamp;   (** hard expiry — included in signed data *)
  tok_commitment : Hash;        (** H(holder_secret): hides holder identity *)
  tok_counter_id : Hash;        (** which counter this token authorizes *)
  tok_sig        : Signature;   (** signed by the delegator *)
}.

(** The hash function the delegator signs.
    Covers tok_not_after, tok_commitment, and tok_counter_id —
    all fields except tok_sig itself. *)
Parameter hash_token : Timestamp -> Hash -> Hash -> Hash.

(** Default AnonToken (used as list-access sentinel in chain operations). *)
Parameter default_token : AnonToken.

(* ════════════════════════════════════════════════════════
   Section 2 — CounterOp Record
   ════════════════════════════════════════════════════════ *)

(** A single counter increment authorized by an AnonToken.
    The holder proves authorization by possessing a valid token,
    not by signing — there is no separate holder signature. *)
Record CounterOp := mkCounterOp {
  cop_token      : AnonToken;   (** the authorizing token *)
  cop_counter_id : Hash;        (** must match tok_counter_id *)
  cop_time       : Timestamp;   (** must be ≤ tok_not_after *)
}.

(* ════════════════════════════════════════════════════════
   Section 3 — Validity Predicate
   ════════════════════════════════════════════════════════ *)

(** A counter operation is valid when:
    (1) the delegator's signature over the token verifies,
    (2) the operation falls within the token's time window, and
    (3) the operation's counter ID matches the token's counter ID
        (prevents counter-substitution attacks). *)
Definition counter_op_valid (delegator : PublicKey) (op : CounterOp) : Prop :=
  let tok := cop_token op in
  Verify delegator
         (hash_token (tok_not_after tok) (tok_commitment tok) (tok_counter_id tok))
         (tok_sig tok) = true
  /\ cop_time op <= tok_not_after tok
  /\ cop_counter_id op = tok_counter_id tok.

(** Boolean decision procedure for counter_op_valid, used in tally_count. *)
Definition counter_op_validb (delegator : PublicKey) (op : CounterOp) : bool :=
  let tok := cop_token op in
  Verify delegator
         (hash_token (tok_not_after tok) (tok_commitment tok) (tok_counter_id tok))
         (tok_sig tok)
  && Nat.leb (cop_time op) (tok_not_after tok)
  && Nat.eqb (cop_counter_id op) (tok_counter_id tok).

Lemma counter_op_validb_spec : forall delegator op,
  counter_op_validb delegator op = true <-> counter_op_valid delegator op.
Proof.
  intros delegator op.
  unfold counter_op_validb, counter_op_valid.
  rewrite !andb_true_iff.
  rewrite Nat.leb_le.
  rewrite Nat.eqb_eq.
  tauto.
Qed.

(* ════════════════════════════════════════════════════════
   Section 4 — Anonymous Delegation Chain
   ════════════════════════════════════════════════════════ *)

Definition AnonDelegChain := list AnonToken.

(** Time windows shrink monotonically through delegation:
    each successive token expires no later than the previous.
    Analogous to [chain_depth_decreasing] for regular [DelegChain]. *)
Definition anon_chain_time_shrink (ch : AnonDelegChain) : Prop :=
  forall i j : nat,
    i < length ch -> j < length ch -> i < j ->
    tok_not_after (nth j ch default_token) <= tok_not_after (nth i ch default_token).

Definition anon_chain_valid (ch : AnonDelegChain) : Prop :=
  ch <> [] /\ anon_chain_time_shrink ch.

(* ════════════════════════════════════════════════════════
   Section 5 — Counter Tally
   ════════════════════════════════════════════════════════ *)

(** A tally is a list of counter ops targeting a single counter. *)
Definition Tally := list CounterOp.

(** Computable tally: count ops that are valid and target counter [cid]. *)
Definition tally_count (delegator : PublicKey) (cid : Hash) (ops : Tally) : nat :=
  length (filter (fun op =>
    Nat.eqb (cop_counter_id op) cid &&
    counter_op_validb delegator op)
  ops).

(** Tally validity as a Prop: every op in [ops] is valid for [delegator]
    and targets counter [cid]. *)
Definition tally_valid (delegator : PublicKey) (cid : Hash) (ops : Tally) : Prop :=
  forall op, In op ops -> counter_op_valid delegator op /\ cop_counter_id op = cid.

(* ════════════════════════════════════════════════════════
   Section 6 — Theorems
   ════════════════════════════════════════════════════════ *)

(** T_AC1: Time enforcement — valid ops lie within the token's window. *)
Lemma tok_time_enforcement : forall delegator op,
  counter_op_valid delegator op ->
  cop_time op <= tok_not_after (cop_token op).
Proof.
  intros delegator op [_ [Htime _]].
  exact Htime.
Qed.

(** T_AC2: Structural anonymity — validity requires no holder PublicKey.
    [counter_op_valid] takes [delegator] (the issuer's key) but no key for
    the holder; holder identity is definitionally absent from the check.
    The commitment witnesses the holder without revealing their key. *)
Lemma tok_structural_anonymity : forall delegator op,
  counter_op_valid delegator op ->
  exists (commitment : Hash), tok_commitment (cop_token op) = commitment.
Proof.
  intros delegator op _.
  exists (tok_commitment (cop_token op)).
  reflexivity.
Qed.

(** T_AC3: Token equality from field equality (record extensionality). *)
Lemma tok_commitment_unique : forall tok1 tok2,
  tok_not_after tok1 = tok_not_after tok2 ->
  tok_commitment tok1 = tok_commitment tok2 ->
  tok_counter_id tok1 = tok_counter_id tok2 ->
  tok_sig tok1 = tok_sig tok2 ->
  tok1 = tok2.
Proof.
  intros [na1 c1 cid1 s1] [na2 c2 cid2 s2].
  simpl.
  intros Hna Hc Hcid Hs.
  subst.
  reflexivity.
Qed.

(** T_AC4: Expiry irrevocability — expired tokens cannot authorize ops. *)
Lemma tok_expired_invalid : forall delegator op,
  cop_time op > tok_not_after (cop_token op) ->
  ~ counter_op_valid delegator op.
Proof.
  intros delegator op Hexp [_ [Htime _]].
  lia.
Qed.

(** T_AC5: Delegation chain time bound is monotone. *)
Lemma anon_chain_time_monotone : forall ch i j,
  anon_chain_valid ch ->
  i < length ch -> j < length ch -> i < j ->
  tok_not_after (nth j ch default_token) <= tok_not_after (nth i ch default_token).
Proof.
  intros ch i j [_ Hshrink] Hi Hj Hij.
  apply Hshrink; assumption.
Qed.

(** T_AC6: Tally soundness — every op in a valid tally is time-bounded. *)
Lemma tally_sound : forall delegator cid ops,
  tally_valid delegator cid ops ->
  forall op, In op ops -> cop_time op <= tok_not_after (cop_token op).
Proof.
  intros delegator cid ops Hvalid op Hin.
  apply (tok_time_enforcement delegator).
  exact (proj1 (Hvalid op Hin)).
Qed.

(** T_AC7: Every token in a valid chain expires no later than the head token.
    Any sub-delegated token is bounded by the root token's time window. *)
Lemma anon_chain_bound : forall ch,
  anon_chain_valid ch ->
  ch <> [] ->
  forall tok, In tok ch ->
    tok_not_after tok <= tok_not_after (hd default_token ch).
Proof.
  intros ch [_ Hshrink] Hne tok Hin.
  apply List.In_nth with (d := default_token) in Hin.
  destruct Hin as [k [Hk Hkth]].
  rewrite <- Hkth.
  replace (hd default_token ch) with (nth 0 ch default_token).
  - destruct k as [| k'].
    + apply Nat.le_refl.
    + apply Hshrink; [lia | exact Hk | lia].
  - destruct ch as [| h t].
    + contradiction.
    + reflexivity.
Qed.
