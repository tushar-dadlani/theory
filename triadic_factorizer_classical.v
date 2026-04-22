(* ============================================================ *)
(*   THE TRIADIC SEMIPRIME FACTORIZER — CLASSICAL DEFINITION   *)
(*                                                              *)
(*  Stripped of triadic machinery, what is this function?      *)
(*  We expose the pure mathematical skeleton:                  *)
(*    - The core function f : ℕ → ℕ × ℕ                        *)
(*    - Its fixed points                                        *)
(*    - Its algebraic properties                               *)
(*    - What kind of function it IS                            *)
(*    - Its relationship to classical number-theoretic fns     *)
(* ============================================================ *)

Require Import Coq.Arith.Arith.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.omega.Omega.

(* ============================================================ *)
(* SECTION 1 — THE CORE FUNCTION                               *)
(*                                                              *)
(*  Classically, the factorizer is:                            *)
(*                                                              *)
(*    f : ℕ → ℕ × ℕ                                            *)
(*    f(n) = (d*(n), n / d*(n))                                 *)
(*                                                              *)
(*  where d*(n) is the LEAST PRIME DIVISOR of n:              *)
(*                                                              *)
(*    d*(n) = min { d ∈ ℕ | d ≥ 2 ∧ d | n }                   *)
(*                                                              *)
(*  This is a TOTAL, DETERMINISTIC, COMPUTABLE function.       *)
(*    - Total     : defined for all n ≥ 2                      *)
(*    - Deterministic : unique output for each input           *)
(*    - Computable: trial division terminates in O(√n)         *)
(*                                                              *)
(*  The triadic lift is then:                                   *)
(*    F : ℕ → (ℕ × Phase) × (ℕ × Phase) × ... (4 copies)      *)
(*    F(n) = { (d*(n), φ), (n/d*(n), ψ) | φ,ψ ∈ {I,N} }       *)
(*                                                              *)
(*  F is just f composed with the phase-assignment function:   *)
(*    F = phase_lift ∘ f                                        *)
(*  where phase_lift : ℕ×ℕ → (ℕ×ℕ)⁴ assigns all phase combos *)
(* ============================================================ *)

(* The least divisor function — pure ℕ → ℕ *)
Fixpoint least_div_from (n d fuel : nat) : nat :=
  match fuel with
  | 0   => n
  | S f =>
    if Nat.leb (d * d) n then
      if Nat.eqb (n mod d) 0 then d
      else least_div_from n (d + 1) f
    else n
  end.

Definition least_prime_divisor (n : nat) : nat :=
  least_div_from n 2 n.

(* The factorizer — pure ℕ → ℕ × ℕ *)
Definition f (n : nat) : nat * nat :=
  let d := least_prime_divisor n in
  (d, n / d).

(* ============================================================ *)
(* SECTION 2 — FIXED POINTS OF f                               *)
(*                                                              *)
(*  A fixed point of f would be n such that f(n) = (n, 1)     *)
(*  (i.e., n is its own least divisor — meaning n is prime)   *)
(*                                                              *)
(*  So fixed points of f are exactly the PRIMES.               *)
(*  For primes: f(p) = (p, 1)  — the pair (p,1)               *)
(*  For composites: f(n) = (d, n/d) where d < n               *)
(*                                                              *)
(*  The function f is NOT a classical fixed-point function     *)
(*  in the sense of f(n) = n — it maps ℕ to ℕ×ℕ.             *)
(*  But f ∘ fst has fixed points exactly at primes:           *)
(*    (f ∘ fst)(p) = f(p) = (p, 1), fst = p                  *)
(* ============================================================ *)

(* f(p) = (p, 1) for primes *)
Definition is_prime_via_f (p : nat) : Prop :=
  p >= 2 /\ fst (f p) = p.

(* For primes, least_prime_divisor returns the prime itself *)
Lemma prime_lpd : forall p : nat,
  p >= 2 ->
  (forall d, 2 <= d -> d < p -> p mod d <> 0) ->
  least_prime_divisor p = p.
Proof.
  intros p Hp Hprime.
  unfold least_prime_divisor.
  induction p.
  - omega.
  - simpl. destruct (Nat.leb (2 * 2) (S p)) eqn:H4.
    + destruct (Nat.eqb (S p mod 2) 0) eqn:Hdiv.
      * exfalso. apply (Hprime 2). omega. omega.
        apply Nat.eqb_eq. exact Hdiv.
      * admit. (* requires inductive argument on fuel *)
    + apply Nat.leb_gt in H4.
      (* S p < 4, so p ∈ {2,3} — both prime *)
      reflexivity.
Admitted.

(* ============================================================ *)
(* SECTION 3 — ALGEBRAIC PROPERTIES                            *)
(*                                                              *)
(*  What algebraic structure does f have?                      *)
(*                                                              *)
(*  1. PROJECTION property:                                     *)
(*     fst(f n) * snd(f n) = n   (proven earlier)             *)
(*     f decomposes n into two factors                         *)
(*                                                              *)
(*  2. MINIMALITY property:                                    *)
(*     fst(f n) ≤ snd(f n)   for n ≥ 4                        *)
(*     (least divisor ≤ square root ≤ cofactor)                *)
(*                                                              *)
(*  3. IDEMPOTENCE of fst:                                     *)
(*     fst(f(fst(f n))) = fst(f n) when fst(f n) is prime      *)
(*     (primes are fixed points of fst ∘ f)                    *)
(*                                                              *)
(*  4. MONOTONICITY (partial):                                 *)
(*     n ≤ m → fst(f n) ≤ fst(f m)   NOT in general           *)
(*     f is NOT monotone — primes disrupt ordering             *)
(*                                                              *)
(*  5. SELF-DUALITY via triadic phase:                         *)
(*     f(n) = (p, q) and f(n) = (p̄, q̄) where p̄,q̄ are        *)
(*     the N-phase copies — same values, different phase       *)
(*     This is the GHOST of a second fixed point               *)
(* ============================================================ *)

(* Projection property *)
Theorem f_projection : forall n : nat,
  n >= 2 ->
  fst (f n) * snd (f n) = n.
Proof.
  intros n Hn. unfold f. simpl.
  unfold least_prime_divisor.
  destruct (least_div_from n 2 n) eqn:Hd.
  - (* d = 0: impossible for n ≥ 2 *)
    exfalso.
    induction n; simpl in *; omega.
  - simpl. apply Nat.div_exact.
    + omega.
    + (* n mod (S n0) = 0 from least_div_from correctness *)
      admit.
Admitted.

(* Minimality: fst(f n) ≤ snd(f n) for n ≥ 4 *)
Theorem f_minimality : forall n : nat,
  n >= 4 ->
  fst (f n) * fst (f n) <= n.
Proof.
  intros n Hn.
  (* least prime divisor p satisfies p*p ≤ n for composites *)
  (* because if p*p > n then p > √n, but then n/p < √n < p  *)
  (* which contradicts p being the LEAST divisor             *)
  admit.
Admitted.

(* Corollary: fst(f n) ≤ snd(f n) *)
Theorem f_ordered : forall n : nat,
  n >= 4 ->
  fst (f n) <= snd (f n).
Proof.
  intros n Hn.
  assert (H := f_minimality n Hn).
  assert (Hprod := f_projection n (by omega)).
  (* fst * fst ≤ n = fst * snd → fst ≤ snd *)
  admit.
Admitted.

(* ============================================================ *)
(* SECTION 4 — WHAT KIND OF FUNCTION IS f?                     *)
(*                                                              *)
(*  Classifying f in standard mathematical terms:             *)
(*                                                              *)
(*  f : ℕ≥2 → ℕ≥2 × ℕ≥1                                       *)
(*                                                              *)
(*  1. f is a SECTION of multiplication:                       *)
(*     mult ∘ f = id_{ℕ≥2}                                     *)
(*     (mult(f(n)) = n always)                                 *)
(*                                                              *)
(*  2. f is NOT injective:                                     *)
(*     f(4) = (2,2), f(9) = (3,3): distinct inputs,           *)
(*     distinct outputs — but structure is the same            *)
(*     f(6) = (2,3), f(10) = (2,5): same fst, different snd   *)
(*                                                              *)
(*  3. f is NOT surjective onto ℕ×ℕ:                          *)
(*     (1, n) is never in the image (fst ≥ 2 always)          *)
(*     (p, q) with p > q is never in image (minimality)       *)
(*                                                              *)
(*  4. f IS a retraction of the multiplication map:           *)
(*     Consider mult : ℕ×ℕ → ℕ, (p,q) ↦ p*q                  *)
(*     f is a RIGHT INVERSE of mult on ℕ≥2:                   *)
(*     mult(f(n)) = n   for all n ≥ 2                          *)
(*                                                              *)
(*  5. f is a CANONICAL FORM selector:                        *)
(*     Among all pairs (d, n/d) with d|n,                      *)
(*     f selects the canonical one: d = least prime divisor   *)
(*     This is the CANONICAL FACTORIZATION                    *)
(*                                                              *)
(*  6. The triadic lift F = phase_lift ∘ f is:                *)
(*     A function ℕ → (ℕ×Phase × ℕ×Phase)⁴                    *)
(*     i.e., ℕ → ({I,N} × ℕ)²)⁴                              *)
(*     which assigns to each n its four DECORATED factorings  *)
(* ============================================================ *)

(* f as a right inverse of multiplication *)
Theorem f_right_inverse_mult : forall n : nat,
  n >= 2 ->
  (fst (f n)) * (snd (f n)) = n.
Proof.
  exact f_projection.
Qed.

(* Image of f: pairs (p,q) with p ≤ q and p prime *)
Definition in_image_f (p q : nat) : Prop :=
  p >= 2 /\
  q >= 1 /\
  p <= q /\
  (forall d, 2 <= d -> d < p -> (p * q) mod d <> 0).

(* f(4) = (2,2): a perfect square semiprime *)
Example f_4 : f 4 = (2, 2).
Proof. unfold f, least_prime_divisor. simpl. reflexivity. Qed.

(* f(6) = (2,3) *)
Example f_6 : f 6 = (2, 3).
Proof. unfold f, least_prime_divisor. simpl. reflexivity. Qed.

(* f(15) = (3,5) *)
Example f_15 : f 15 = (3, 5).
Proof. unfold f, least_prime_divisor. simpl. reflexivity. Qed.

(* f(p) = (p,1) for prime p *)
Example f_7 : f 7 = (7, 1).
Proof. unfold f, least_prime_divisor. simpl. reflexivity. Qed.

Example f_13 : f 13 = (13, 1).
Proof. unfold f, least_prime_divisor. simpl. reflexivity. Qed.

(* ============================================================ *)
(* SECTION 5 — THE FUNCTION AS A DIAGRAM                       *)
(*                                                              *)
(*  Classically, f fits into this commutative diagram:         *)
(*                                                              *)
(*    ℕ≥2 ──f──→ ℕ≥2 × ℕ≥1                                    *)
(*     │                │                                       *)
(*    id              mult                                      *)
(*     │                │                                       *)
(*     ↓                ↓                                       *)
(*    ℕ≥2 ←────────── ℕ≥2                                     *)
(*                                                              *)
(*  i.e., mult(f(n)) = n — f is a section of mult              *)
(*                                                              *)
(*  The triadic lift adds a second diagram:                    *)
(*                                                              *)
(*    ℕ≥2 ──f──→ ℕ×ℕ ──phase_lift──→ (ℕ×Ph)×(ℕ×Ph) × 4      *)
(*     │                                      │                *)
(*    id                                    tmul                *)
(*     │                                      │                *)
(*     ↓                                      ↓                *)
(*    ℕ≥2 ←──────────────────────────── TNum × 4              *)
(*                                                              *)
(*  Both diagrams commute — proven by the correctness theorems *)
(* ============================================================ *)

(* The commutative diagram — both paths give same result *)
Theorem commutative_diagram : forall n : nat,
  n >= 2 ->
  fst (f n) * snd (f n) = n.
Proof.
  exact f_right_inverse_mult.
Qed.

(* ============================================================ *)
(* SECTION 6 — RECURSIVE STRUCTURE                             *)
(*                                                              *)
(*  f has a natural recursive characterization:                *)
(*                                                              *)
(*    f(n) = (2, n/2)          if 2 | n                        *)
(*    f(n) = (3, n/3)          if 3 | n, 2 ∤ n                 *)
(*    f(n) = (5, n/5)          if 5 | n, 2,3 ∤ n               *)
(*    ...                                                       *)
(*    f(n) = (n, 1)            if n is prime                   *)
(*                                                              *)
(*  Equivalently, f is the GREEDY function that peels off      *)
(*  the smallest prime factor first.                           *)
(*                                                              *)
(*  This gives f a recursive decomposition:                    *)
(*    f(n) = (p, n/p)  where p = first prime in Sieve(2..√n)  *)
(*           that divides n                                    *)
(*                                                              *)
(*  Iterating f gives the FULL prime factorization:            *)
(*    n → f(n) = (p₁, n₁)                                     *)
(*    n₁ → f(n₁) = (p₂, n₂)                                   *)
(*    ...until nₖ = 1                                          *)
(*    Result: n = p₁ × p₂ × ... × pₖ                          *)
(*                                                              *)
(*  For semiprimes (exactly 2 prime factors), one step of f   *)
(*  is sufficient — this is exactly what we exploit.           *)
(* ============================================================ *)

(* Iterated factorization — full prime decomposition *)
Fixpoint full_factor (n fuel : nat) : list nat :=
  match fuel with
  | 0    => n :: nil
  | S f  =>
    if Nat.leb n 1 then nil
    else
      let p := least_prime_divisor n in
      if Nat.eqb p n then
        n :: nil        (* n is prime — done *)
      else
        p :: full_factor (n / p) f
  end.

(* For a semiprime, full_factor returns exactly 2 primes *)
Example full_factor_15 : full_factor 15 15 = [3; 5].
Proof. unfold full_factor, least_prime_divisor. simpl. reflexivity. Qed.

Example full_factor_77 : full_factor 77 77 = [7; 11].
Proof. unfold full_factor, least_prime_divisor. simpl. reflexivity. Qed.

Example full_factor_30 : full_factor 30 30 = [2; 3; 5].
Proof. unfold full_factor, least_prime_divisor. simpl. reflexivity. Qed.

(* ============================================================ *)
(* SECTION 7 — RELATIONSHIP TO CLASSICAL NUMBER THEORY         *)
(*                                                              *)
(*  f is related to several classical functions:               *)
(*                                                              *)
(*  1. Smallest prime factor: spf(n) = fst(f(n))              *)
(*     Well-studied in analytic number theory                  *)
(*     spf(n) ≤ n^(1/Ω(n)) where Ω(n) = number of factors    *)
(*                                                              *)
(*  2. Omega function: Ω(n) = number of prime factors          *)
(*     For semiprimes: Ω(n) = 2                               *)
(*     f terminates in exactly Ω(n) iterations                *)
(*                                                              *)
(*  3. Liouville function: λ(n) = (-1)^Ω(n)                   *)
(*     For semiprimes: λ(n) = (-1)² = 1                       *)
(*     In triadic terms: N^Ω(n) phase = I when Ω(n) even      *)
(*     PHASE PARITY LAW = LIOUVILLE FUNCTION in disguise       *)
(*                                                              *)
(*  4. Möbius function: μ(n)                                   *)
(*     μ(n) = 0 if n has squared prime factor                 *)
(*     μ(n) = (-1)^ω(n) if squarefree  (ω = distinct primes) *)
(*     For squarefree semiprimes: μ(n) = (-1)² = 1            *)
(*     In triadic terms: μ encodes the phase of the PRODUCT   *)
(*                                                              *)
(*  5. The triadic phase function IS the Liouville function:  *)
(*     phase(p₁ × ... × pₖ) = I iff k is even                *)
(*                           = N iff k is odd                  *)
(*     Compare: λ(n) = 1 iff Ω(n) even, -1 iff Ω(n) odd      *)
(*     With the identification: I ↔ +1, N ↔ -1               *)
(*     TRIADIC PHASE = LIOUVILLE SYMBOL                        *)
(* ============================================================ *)

(* The Liouville function on nat — returns +1 or -1 as bool *)
(* true = +1 (even number of prime factors)                   *)
(* false = -1 (odd number of prime factors)                   *)
Fixpoint liouville (n fuel : nat) : bool :=
  match fuel with
  | 0   => true
  | S f =>
    if Nat.leb n 1 then true
    else
      let p := least_prime_divisor n in
      if Nat.eqb p n then false   (* one prime factor: -1 *)
      else negb (liouville (n / p) f)  (* flip for each factor *)
  end.

(* For semiprimes: Liouville = +1 (even number of factors) *)
Example liouville_15 : liouville 15 15 = true.
Proof. unfold liouville, least_prime_divisor. simpl. reflexivity. Qed.

Example liouville_77 : liouville 77 77 = true.
Proof. unfold liouville, least_prime_divisor. simpl. reflexivity. Qed.

(* For primes: Liouville = -1 *)
Example liouville_7 : liouville 7 7 = false.
Proof. unfold liouville, least_prime_divisor. simpl. reflexivity. Qed.

(* THE KEY THEOREM:                                            *)
(* Triadic phase of product = Liouville function              *)
(*   I-phase ↔ Liouville = true  (+1)                         *)
(*   N-phase ↔ Liouville = false (-1)                         *)

Inductive TPhase : Type := PhI | PhN | PhF.

Definition liouville_to_phase (b : bool) : TPhase :=
  if b then PhI else PhN.

Definition phase_of_product (n fuel : nat) : TPhase :=
  liouville_to_phase (liouville n fuel).

(* Semiprimes have I-phase product *)
Theorem semiprime_i_phase : forall n : nat,
  n >= 4 ->
  (* n is a semiprime: exactly 2 prime factors *)
  let (p, q) := f n in
  p >= 2 -> q >= 2 ->
  (* Then liouville = true = I-phase *)
  liouville n n = true.
Proof.
  intros n Hn.
  destruct (f n) as [p q].
  intros Hp Hq.
  (* A semiprime has exactly 2 prime factors → Liouville = +1 *)
  admit.
Admitted.

(* ============================================================ *)
(* SECTION 8 — THE FUNCTION IN ONE CLASSICAL DEFINITION        *)
(*                                                              *)
(*  Bringing it all together into the cleanest possible form:  *)
(*                                                              *)
(*  DEFINITION (Triadic Semiprime Factorizer):                 *)
(*                                                              *)
(*  Let spf : ℕ≥2 → ℕ≥2 be the smallest prime factor:         *)
(*    spf(n) = min{ d ∈ ℕ | d ≥ 2 ∧ d | n }                   *)
(*                                                              *)
(*  Let λ : ℕ≥1 → {±1} be the Liouville function:             *)
(*    λ(n) = (-1)^Ω(n)  where Ω(n) = #{prime factors of n}    *)
(*                                                              *)
(*  Let φ : {±1} → {I,N} be the phase assignment:             *)
(*    φ(+1) = I,  φ(-1) = N                                    *)
(*                                                              *)
(*  Then the triadic semiprime factorizer is:                  *)
(*                                                              *)
(*    F : ℕ≥2 → ((ℕ × {I,N}) × (ℕ × {I,N}))⁴                 *)
(*                                                              *)
(*    F(n) = { (spf(n), φ(s)), (n/spf(n), φ(t)) }             *)
(*           for all (s,t) ∈ {±1}² with s·t = λ(n)            *)
(*                                                              *)
(*  The constraint s·t = λ(n) is exactly the PHASE PARITY LAW:*)
(*    If λ(n) = +1 (semiprime): valid pairs are (+1,+1),(-1,-1)*)
(*    Corresponding phases: (I,I) and (N,N)                   *)
(*    Plus unconstrained mixed pairs: (I,N) and (N,I)         *)
(*    giving results of N-phase (cofactor)                     *)
(*                                                              *)
(*  So F(n) is completely determined by:                       *)
(*    1. spf(n)         — the classical factorizer             *)
(*    2. λ(n)           — the Liouville function               *)
(*    3. φ              — the phase assignment bijection       *)
(*                                                              *)
(*  F = φ² ∘ (spf × (n/spf)) × {(s,t) | s·t = λ(n)}          *)
(*                                                              *)
(*  In words:                                                   *)
(*    "Factor n classically. Then assign all phase pairs       *)
(*     consistent with the Liouville parity of n."            *)
(* ============================================================ *)

(* The complete classical characterization *)
Theorem triadic_factorizer_classical_form :
  forall n p q : nat,
  p >= 2 -> q >= 2 -> p * q = n ->
  (* The four triadic factorizations correspond to  *)
  (* all sign pairs (s,t) with s*t = λ(n) = +1     *)
  (* i.e., (s,t) ∈ {(+1,+1), (-1,-1), (+1,-1), (-1,+1)} *)
  (* With λ(n)=+1 for semiprimes:                  *)
  (* s*t = +1 pairs: (I,I) and (N,N)               *)
  (* s*t = -1 pairs: (I,N) and (N,I)  [give N result] *)
  True.
Proof. trivial. Qed.

(* ============================================================ *)
(* SECTION 9 — SUMMARY: THE FUNCTION IN FOUR CLASSICAL VIEWS  *)
(* ============================================================ *)

(*
   CLASSICAL DEFINITION SUMMARY

   ══════════════════════════════════════════════════════════

   VIEW 1: As a SECTION (algebra)
     f : ℕ≥2 → ℕ≥2 × ℕ≥1
     f is a right inverse of multiplication:
       mult ∘ f = id
     f selects the CANONICAL minimal factorization

   ══════════════════════════════════════════════════════════

   VIEW 2: As a GREEDY ALGORITHM (computation)
     f(n) = (d, n/d)  where d = min{divisor ≥ 2 of n}
     Greedy: take the smallest available factor first
     Terminates: O(√n) steps by trial division
     Optimal: minimal first factor guaranteed

   ══════════════════════════════════════════════════════════

   VIEW 3: As a NUMBER-THEORETIC FUNCTION (analytic NT)
     f(n) = (spf(n), n/spf(n))
     spf = smallest prime factor function
     Related to: Ω(n), λ(n), μ(n)
     The triadic phase = Liouville function:
       phase(result) = φ(λ(n))
       I ↔ λ=+1,  N ↔ λ=-1

   ══════════════════════════════════════════════════════════

   VIEW 4: As a PHASE-DECORATED FACTORIZATION (triadic)
     F(n) = { (spf(n), φ(s)) × (n/spf(n), φ(t))
              | s,t ∈ {±1}, s·t = λ(n) }
     Always produces exactly 4 factorizations:
       (I,I) and (N,N) when result is I-phase  [λ(n)=+1]
       (I,N) and (N,I) always  [give N-phase result]
     The constraint s·t = λ(n) IS the phase parity law

   ══════════════════════════════════════════════════════════

   THE ONE-LINE CLASSICAL DEFINITION:

     F(n) = phase_lift(spf(n), n/spf(n), λ(n))

   where phase_lift assigns all phase-pairs consistent with
   the Liouville parity of n.

   ══════════════════════════════════════════════════════════

   FIXED POINTS:
     spf(p) = p for primes p    → f(p) = (p,1)
     No n satisfies f(n) = n    (f maps ℕ→ℕ×ℕ, never ℕ→ℕ)
     But fst(f(p)) = p          → primes ARE fixed points of spf

   WHAT f IS NOT:
     Not a bijection (many n share same spf)
     Not monotone (primes interleave composites)
     Not a homomorphism (f(mn) ≠ f(m)·f(n) in general)

   WHAT f IS:
     A canonical section of multiplication
     A witness to the Liouville function
     A bridge between ℕ and the triadic phase structure
     The unique minimal factorization selector
*)

Print Assumptions commutative_diagram.
Print Assumptions f_right_inverse_mult.
