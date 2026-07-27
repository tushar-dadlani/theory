(* ================================================================= *)
(*  PadicUncountable.v  —  THE 2-ADIC INTEGERS ARE A CANTOR SET.      *)
(*                                                                    *)
(*  This wires together two things the repo already builds:           *)
(*   • the p-adic integers as coherent residue sequences              *)
(*     (`PadicIntegers.Zp` — the inverse limit lim ℤ/pⁿ), and         *)
(*   • Cantor's diagonal argument (the `¬ f x x` obstruction, proved  *)
(*     abstractly on `A → Prop` in `category-topos/CategoryInterval.  *)
(*     cantor`).                                                       *)
(*                                                                    *)
(*  At p = 2 the p-adic integers ARE the Cantor space: a binary       *)
(*  stream `nat → bool` is exactly a coherent 2-adic residue          *)
(*  sequence.  We build that injection `{0,1}^ℕ ↪ ℤ₂` (`ofbits`,      *)
(*  `ofbits_inj`) together with its digit-reading retraction (`bit`,  *)
(*  `bit_ofbits`), and then run Cantor's diagonal on the 2-adic       *)
(*  DIGITS to get the repo's first genuine CONTINUUM-cardinality      *)
(*  statement:                                                        *)
(*                                                                    *)
(*     Zp2_uncountable : no map  ℕ → ℤ₂  is surjective.               *)
(*                                                                    *)
(*  i.e. |ℤ₂| > ℵ₀ = |ℚ|.  This is the cardinality shadow of the      *)
(*  repo's discrete↔continuous quarantine wall: the archimedean       *)
(*  completion ℝ = ℚ_∞ and the 2-adic completion ℤ₂ both jump from    *)
(*  the countable ℚ to the continuum 2^ℵ₀, and Cantor's diagonal is   *)
(*  the theorem that forces that jump to be genuine.                  *)
(*                                                                    *)
(*  AXIOM-FREE: the diagonal is run POINTWISE, so no functional       *)
(*  extensionality (or any classical axiom) is used.  `Print          *)
(*  Assumptions` = Closed under the global context.                  *)
(* ================================================================= *)

From Stdlib Require Import Arith Lia Bool.
Require Import PadicIntegers.

(* ----------------------------------------------------------------- *)
(*  Cantor's diagonal, the Boolean (Turing/halting) instance —        *)
(*  the concrete form of `CategoryInterval.cantor` (there B = Prop;   *)
(*  here B = bool).  No stream `nat → bool` enumerates all streams.   *)
(* ----------------------------------------------------------------- *)
Theorem stream_uncountable : forall g : nat -> (nat -> bool),
  ~ (forall s, exists n, g n = s).
Proof.
  intros g Hsurj.
  destruct (Hsurj (fun m => negb (g m m))) as [n Hn].
  pose proof (f_equal (fun f => f n) Hn) as Hd; cbn beta in Hd.
  exact (no_fixpoint_negb (g n n) (eq_sym Hd)).
Qed.

(* ----------------------------------------------------------------- *)
(*  The injection  {0,1}^ℕ ↪ ℤ₂ :  a binary stream is a coherent      *)
(*  2-adic residue sequence.  bits_to_nat s n = the number whose      *)
(*  low n bits are s(0..n−1).                                         *)
(* ----------------------------------------------------------------- *)
Fixpoint bits_to_nat (s : nat -> bool) (n : nat) : nat :=
  match n with
  | O => 0
  | S k => bits_to_nat s k + (if s k then 2 ^ k else 0)
  end.

Lemma bits_lt : forall s n, bits_to_nat s n < 2 ^ n.
Proof.
  intros s n; induction n as [|n IH]; cbn [bits_to_nat].
  - cbn [Nat.pow]; lia.
  - rewrite Nat.pow_succ_r'; destruct (s n); lia.
Qed.

Lemma redcoh_bits : forall s, redcoh 2 (bits_to_nat s).
Proof.
  intros s n; cbn [bits_to_nat].
  replace (if s n then 2 ^ n else 0) with ((if s n then 1 else 0) * 2 ^ n)
    by (destruct (s n); lia).
  rewrite Nat.Div0.mod_add, Nat.mod_small by (apply bits_lt); reflexivity.
Qed.

Definition ofbits (s : nat -> bool) : Zp 2 := exist _ (bits_to_nat s) (redcoh_bits s).

(* the digit-reading retraction  ℤ₂ → {0,1}^ℕ *)
Definition bit (z : Zp 2) (n : nat) : bool :=
  Nat.eqb ((proj1_sig z (S n) / 2 ^ n) mod 2) 1.

Lemma bit_ofbits : forall s n, bit (ofbits s) n = s n.
Proof.
  intros s n; unfold bit, ofbits; cbn [proj1_sig]; cbn [bits_to_nat].
  replace (if s n then 2 ^ n else 0) with ((if s n then 1 else 0) * 2 ^ n)
    by (destruct (s n); lia).
  rewrite Nat.div_add by (apply Nat.pow_nonzero; lia).
  rewrite (Nat.div_small (bits_to_nat s n) (2 ^ n)) by (apply bits_lt).
  destruct (s n); reflexivity.
Qed.

(* the injection is genuine (proved pointwise — no funext) *)
Lemma ofbits_inj : forall s t, ofbits s = ofbits t -> forall n, s n = t n.
Proof.
  intros s t Heq n.
  rewrite <- (bit_ofbits s n), <- (bit_ofbits t n), Heq; reflexivity.
Qed.

(* ----------------------------------------------------------------- *)
(*  CANTOR'S DIAGONAL ON THE 2-ADIC DIGITS:  ℤ₂ is uncountable.       *)
(* ----------------------------------------------------------------- *)
Theorem Zp2_uncountable : forall g : nat -> Zp 2, ~ (forall z, exists n, g n = z).
Proof.
  intros g Hsurj.
  (* the anti-diagonal 2-adic integer: flip the n-th digit of g(n) *)
  destruct (Hsurj (ofbits (fun n => negb (bit (g n) n)))) as [n Hn].
  pose proof (f_equal (fun z => bit z n) Hn) as Hd; cbn beta in Hd.
  rewrite bit_ofbits in Hd.
  (* Hd : bit (g n) n = negb (bit (g n) n) *)
  exact (no_fixpoint_negb (bit (g n) n) (eq_sym Hd)).
Qed.

Print Assumptions Zp2_uncountable.

(* ================================================================= *)
(*  END PadicUncountable.v                                           *)
(*  ℤ₂ = lim ℤ/2ⁿ (PadicIntegers.Zp at p=2) contains {0,1}^ℕ         *)
(*  (`ofbits`, injective) and no ℕ → ℤ₂ is onto (`Zp2_uncountable`,  *)
(*  Cantor's diagonal on the digits) — the repo's first continuum-    *)
(*  cardinality (2^ℵ₀) result, axiom-free.                           *)
(* ================================================================= *)
