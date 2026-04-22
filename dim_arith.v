(** * DIM Arithmetic Precision — Layer 2 Reproducibility
    Refines Layer 1's opaque [compute] by making the arithmetic mode
    (Int8, Posit8, Float32, Float64) explicit.

    Theorem inventory:
      T26 arith_determinism              — fixed mode + input + RNG ⟹ same output
      T27 arith_mode_divergence          — different modes can diverge (IEEE 754)
      T28 arith_mode_binding             — same operator+sig ⟹ same data hash
      T29 arith_chain_replay_determinism — linked chain equals pure replay
      T30 layer1_is_fixed_mode           — Layer 1 = Layer 2 at default mode

    New axioms: 4.
    New parameters: 3.
    All hash-level injectivity is derived, not postulated.
*)

From Stdlib Require Import List.
From Stdlib Require Import Nat.
From Stdlib Require Import Bool.
Require Import DIM.dim_types.
Require Import DIM.dim_crypto.
Require Import DIM.dim_capability.
Require Import DIM.dim_reproducibility.
Import ListNotations.
Open Scope list_scope.

(* ════════════════════════════════════════════════════════
   Section 1: ArithMode Type
   ════════════════════════════════════════════════════════ *)

Inductive ArithMode : Type :=
  | Int8    : ArithMode
  | Posit8  : ArithMode
  | Float32 : ArithMode
  | Float64 : ArithMode.

Lemma arith_mode_eq_dec : forall (m1 m2 : ArithMode), {m1 = m2} + {m1 <> m2}.
Proof. decide equality. Defined.

(* ════════════════════════════════════════════════════════
   Section 2: ArithMode as CAS Object
   ════════════════════════════════════════════════════════ *)

Parameter encode_arith_mode : ArithMode -> Data.
Axiom encode_arith_mode_injective :
  forall m1 m2, encode_arith_mode m1 = encode_arith_mode m2 -> m1 = m2.

Definition hash_arith_mode (m : ArithMode) : Hash := H (encode_arith_mode m).

Lemma hash_arith_mode_injective :
  forall m1 m2, hash_arith_mode m1 = hash_arith_mode m2 -> m1 = m2.
Proof.
  intros m1 m2 Heq.
  unfold hash_arith_mode in Heq.
  apply collision_resistant in Heq.
  apply encode_arith_mode_injective.
  exact Heq.
Qed.

(* ════════════════════════════════════════════════════════
   Section 3: Mode-Parameterized Computation + Bridge
   ════════════════════════════════════════════════════════ *)

Parameter compute_arith : ArithMode -> Hash -> RNGLog -> Hash.

Definition default_arith_mode : ArithMode := Int8.

(** Bridge to Layer 1: the opaque compute is compute_arith at default mode. *)
Axiom compute_is_default_mode :
  forall (h : Hash) (log : RNGLog),
    compute h log = compute_arith default_arith_mode h log.

(* ════════════════════════════════════════════════════════
   Section 4: Divergence Axiom
   ════════════════════════════════════════════════════════ *)

(** Different ArithModes can produce different outputs — IEEE 754 non-associativity. *)
Axiom arith_impl_may_diverge :
  exists (h : Hash) (log : RNGLog) (m1 m2 : ArithMode),
    m1 <> m2 /\
    compute_arith m1 h log <> compute_arith m2 h log.

(* ════════════════════════════════════════════════════════
   Section 5: ArithProbReceipt Record & Hashing
   ════════════════════════════════════════════════════════ *)

Parameter encode_arith_prob_receipt :
  Hash -> Hash -> DelegChain -> Hash -> Hash -> Data.
Axiom encode_arith_prob_receipt_injective :
  forall i1 o1 ch1 rh1 ah1 i2 o2 ch2 rh2 ah2,
    encode_arith_prob_receipt i1 o1 ch1 rh1 ah1 =
    encode_arith_prob_receipt i2 o2 ch2 rh2 ah2 ->
    i1 = i2 /\ o1 = o2 /\ ch1 = ch2 /\ rh1 = rh2 /\ ah1 = ah2.

Definition hash_arith_prob_receipt (i o : Hash) (ch : DelegChain) (rh ah : Hash) : Hash :=
  H (encode_arith_prob_receipt i o ch rh ah).

Lemma hash_arith_prob_receipt_injective :
  forall i1 o1 ch1 rh1 ah1 i2 o2 ch2 rh2 ah2,
    hash_arith_prob_receipt i1 o1 ch1 rh1 ah1 =
    hash_arith_prob_receipt i2 o2 ch2 rh2 ah2 ->
    i1 = i2 /\ o1 = o2 /\ ch1 = ch2 /\ rh1 = rh2 /\ ah1 = ah2.
Proof.
  intros i1 o1 ch1 rh1 ah1 i2 o2 ch2 rh2 ah2 Heq.
  unfold hash_arith_prob_receipt in Heq.
  apply collision_resistant in Heq.
  apply encode_arith_prob_receipt_injective.
  exact Heq.
Qed.

Record ArithProbReceipt := mkArithProbReceipt {
  apr_input      : Hash;
  apr_output     : Hash;
  apr_operator   : PublicKey;
  apr_chain      : DelegChain;
  apr_time       : Timestamp;
  apr_rng_log    : RNGLog;
  apr_rng_hash   : Hash;
  apr_arith_mode : ArithMode;
  apr_arith_hash : Hash;
  apr_sig        : Signature;
}.

Definition arith_prob_receipt_valid (apr : ArithProbReceipt) : Prop :=
  Verify (apr_operator apr)
         (hash_arith_prob_receipt (apr_input apr) (apr_output apr)
            (apr_chain apr) (apr_rng_hash apr) (apr_arith_hash apr))
         (apr_sig apr) = true
  /\ chain_sigs_valid  (apr_chain apr)
  /\ chain_linked      (apr_chain apr)
  /\ chain_caps_shrink (apr_chain apr)
  /\ apr_rng_hash apr = hash_rng_log (apr_rng_log apr)
  /\ apr_arith_hash apr = hash_arith_mode (apr_arith_mode apr).

Definition arith_prob_receipt_faithful (apr : ArithProbReceipt) : Prop :=
  apr_output apr = compute_arith (apr_arith_mode apr) (apr_input apr) (apr_rng_log apr).

(* ════════════════════════════════════════════════════════
   T26: Arithmetic Determinism
   ════════════════════════════════════════════════════════ *)

Theorem arith_determinism :
  forall (m : ArithMode) (h1 h2 : Hash) (log1 log2 : RNGLog),
    h1 = h2 -> log1 = log2 ->
    compute_arith m h1 log1 = compute_arith m h2 log2.
Proof.
  intros m h1 h2 log1 log2 Hh Hlog.
  subst. reflexivity.
Qed.

(* ════════════════════════════════════════════════════════
   T27: Arithmetic Mode Divergence
   ════════════════════════════════════════════════════════ *)

Theorem arith_mode_divergence :
  exists (h : Hash) (log : RNGLog) (m1 m2 : ArithMode),
    m1 <> m2 /\
    compute_arith m1 h log <> compute_arith m2 h log.
Proof.
  exact arith_impl_may_diverge.
Qed.

(* ════════════════════════════════════════════════════════
   T28: ArithMode Binding (Auditability)
   ════════════════════════════════════════════════════════ *)

Theorem arith_mode_binding :
  forall apr1 apr2,
    arith_prob_receipt_valid apr1 -> arith_prob_receipt_valid apr2 ->
    apr_operator apr1 = apr_operator apr2 ->
    apr_sig apr1 = apr_sig apr2 ->
    apr_input apr1 = apr_input apr2 /\
    apr_output apr1 = apr_output apr2 /\
    apr_chain apr1 = apr_chain apr2 /\
    apr_rng_hash apr1 = apr_rng_hash apr2 /\
    apr_arith_hash apr1 = apr_arith_hash apr2.
Proof.
  intros apr1 apr2 Hv1 Hv2 Hop Hsig.
  destruct Hv1 as [Hver1 _]. destruct Hv2 as [Hver2 _].
  apply sign_unforgeable in Hver1. apply sign_unforgeable in Hver2.
  destruct Hver1 as [kp1 [Hkp1 Hs1]]. destruct Hver2 as [kp2 [Hkp2 Hs2]].
  rewrite Hop in Hkp1.
  pose proof (keypair_unique _ _ _ Hkp1 Hkp2) as Hkeq. subst.
  assert (Hmeq : hash_arith_prob_receipt (apr_input apr1) (apr_output apr1)
                    (apr_chain apr1) (apr_rng_hash apr1) (apr_arith_hash apr1) =
                  hash_arith_prob_receipt (apr_input apr2) (apr_output apr2)
                    (apr_chain apr2) (apr_rng_hash apr2) (apr_arith_hash apr2)).
  { apply (sign_injective kp2). congruence. }
  apply hash_arith_prob_receipt_injective in Hmeq.
  destruct Hmeq as [Hi [Ho [Hc [Hr Ha]]]].
  exact (conj Hi (conj Ho (conj Hc (conj Hr Ha)))).
Qed.

(* ════════════════════════════════════════════════════════
   T29: Chain Replay under Fixed ArithMode
   ════════════════════════════════════════════════════════ *)

Fixpoint arith_replay (m : ArithMode) (init : Hash) (logs : list RNGLog) : Hash :=
  match logs with
  | []          => init
  | log :: rest => arith_replay m (compute_arith m init log) rest
  end.

Inductive arith_prob_linked : ArithMode -> Hash -> list ArithProbReceipt -> Hash -> Prop :=
  | APL_base : forall m x y apr,
      arith_prob_receipt_valid apr -> arith_prob_receipt_faithful apr ->
      apr_arith_mode apr = m -> apr_input apr = x -> apr_output apr = y ->
      arith_prob_linked m x [apr] y
  | APL_step : forall m x y z apr aprs,
      arith_prob_receipt_valid apr -> arith_prob_receipt_faithful apr ->
      apr_arith_mode apr = m -> apr_input apr = x -> apr_output apr = y ->
      arith_prob_linked m y aprs z ->
      arith_prob_linked m x (apr :: aprs) z.

Theorem arith_chain_replay_determinism :
  forall (m : ArithMode) (x z : Hash) (aprs : list ArithProbReceipt),
    arith_prob_linked m x aprs z ->
    z = arith_replay m x (map apr_rng_log aprs).
Proof.
  intros m x z aprs Hlink.
  induction Hlink as
    [ m' x' y' apr Hvalid Hfaith Hmode Hin Hout
    | m' x' y' z' apr aprs' Hvalid Hfaith Hmode Hin Hout Hrest IH ].
  - (* Base: single receipt *)
    simpl. subst.
    unfold arith_prob_receipt_faithful in Hfaith.
    rewrite Hfaith.
    reflexivity.
  - (* Step: apr :: aprs' *)
    subst x'. subst y'.
    simpl.
    unfold arith_prob_receipt_faithful in Hfaith.
    rewrite Hmode in Hfaith.
    rewrite Hfaith in IH.
    exact IH.
Qed.

(* ════════════════════════════════════════════════════════
   T30: Layer 1 Recovery
   ════════════════════════════════════════════════════════ *)

Lemma replay_is_arith_replay :
  forall (init : Hash) (logs : list RNGLog),
    replay init logs = arith_replay default_arith_mode init logs.
Proof.
  intros init logs.
  generalize dependent init.
  induction logs as [| log rest IH]; intros init.
  - simpl. reflexivity.
  - simpl. rewrite compute_is_default_mode. apply IH.
Qed.

Theorem layer1_is_fixed_mode :
  forall (x z : Hash) (prs : list ProbReceipt),
    prob_linked x prs z ->
    z = arith_replay default_arith_mode x (map pr_rng_log prs).
Proof.
  intros x z prs Hlink.
  apply prob_chain_matches_replay in Hlink.
  rewrite Hlink.
  apply replay_is_arith_replay.
Qed.
