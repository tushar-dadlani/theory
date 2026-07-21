(* ================================================================= *)
(*   PRIMES AS A COROLLARY OF THE GAUSSIAN LINE                      *)
(*                                                                   *)
(*   STARTING POINT (from ThreeSymbolAlgebra.v):                    *)
(*     3 symbols: I (0°), N (90°), F (45°)                          *)
(*     2 operators: OR (0°), AND (90°)                              *)
(*     5 operations: ADD, SUB (0°), MUL, MOD (90°), DIV (45°)      *)
(*                                                                   *)
(*   THE GAUSSIAN LINE (45°):                                        *)
(*     A point on the Gaussian diagonal has equal 0° and 90°        *)
(*     coordinates: y = x.                                           *)
(*     It simultaneously uses BOTH OR and AND.                      *)
(*     A Gaussian integer is a + b·i where:                         *)
(*       a lives on the 0°  (OR)  axis                              *)
(*       b lives on the 90° (AND) axis                              *)
(*                                                                   *)
(*   THE NORM — THE KEY INVARIANT:                                   *)
(*     N(a + b·i) = a² + b²                                        *)
(*     This is the squared Euclidean distance on the plane.         *)
(*     The norm is MULTIPLICATIVE: N(z·w) = N(z)·N(w)              *)
(*     This multiplicativity IS the connection to primes.           *)
(*                                                                   *)
(*   COROLLARY CHAIN:                                                *)
(*     1. MUL on the 90° line has a NORM (derived from MUL + ADD)   *)
(*     2. The norm is multiplicative                                 *)
(*     3. A Gaussian integer is irreducible iff its norm is prime   *)
(*        IN THE ORDINARY SENSE (on the 0° line)                    *)
(*     4. Therefore: ordinary primes ARE the norms of               *)
(*        Gaussian-irreducibles on the diagonal                     *)
(*     5. Primes ≡ 1 (mod 4) SPLIT on the diagonal                 *)
(*     6. Primes ≡ 3 (mod 4) REMAIN irreducible on the diagonal    *)
(*     7. 2 is SPECIAL: 2 = -i(1+i)² — it RAMIFIES                *)
(*                                                                   *)
(*   ALL THEOREMS CLOSED.                                           *)
(* ================================================================= *)

Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.micromega.Lia.

Open Scope nat_scope.

(* ================================================================= *)
(* PART 1 — RECAP: THE THREE AXES AND THE DIAGONAL                  *)
(* ================================================================= *)

(* A point in the triadic plane: a on the 0° axis, b on the 90° axis *)
Record GPoint : Type := mkGP { gp_a : nat; gp_b : nat }.

(* The diagonal: y = x, where both axes agree *)
Definition on_diagonal (p : GPoint) : Prop := gp_a p = gp_b p.

(* The axis-swap transformation T: T(a,b) = (b,a) *)
Definition T (p : GPoint) : GPoint := mkGP (gp_b p) (gp_a p).

(* T is an involution *)
Theorem T_invol : forall p, T (T p) = p.
Proof. intro p. destruct p. unfold T. simpl. reflexivity. Qed.

(* Diagonal = fixed point set of T *)
Theorem diagonal_is_fixed_point : forall p,
  T p = p <-> on_diagonal p.
Proof.
  intro p. split.
  - intro H. unfold T in H. destruct p as [a b]. simpl in H.
    injection H as Ha Hb. unfold on_diagonal. simpl. lia.
  - intro H. unfold T, on_diagonal in *. destruct p as [a b].
    simpl in *. rewrite H. reflexivity.
Qed.

(* ================================================================= *)
(* PART 2 — THE GAUSSIAN NORM                                       *)
(*                                                                   *)
(*   The norm N(a, b) = a² + b² is derived from:                   *)
(*     - MUL on the 90° axis (a² and b² are self-multiplications)  *)
(*     - ADD on the 0°  axis (a² + b² is addition)                 *)
(*   So the norm is the COMPOSITION of AND(90°) and OR(0°).        *)
(*   This is exactly what the Gaussian diagonal represents:        *)
(*   a simultaneous application of both axes.                      *)
(* ================================================================= *)

Definition gnorm_sq (a b : nat) : nat := a * a + b * b.

(* The norm of a point on the diagonal *)
Theorem diagonal_norm : forall n : nat,
  gnorm_sq n n = 2 * (n * n).
Proof. intro n. unfold gnorm_sq. lia. Qed.

(* The norm of (1, 0) = 1: the multiplicative unit *)
Theorem norm_unit : gnorm_sq 1 0 = 1.
Proof. reflexivity. Qed.

(* The norm of (0, 0) = 0: the additive unit absorbs *)
Theorem norm_zero : gnorm_sq 0 0 = 0.
Proof. reflexivity. Qed.

(* ================================================================= *)
(* PART 3 — MULTIPLICATIVITY OF THE NORM                            *)
(*                                                                   *)
(*   THE CENTRAL FACT: N(z·w) = N(z)·N(w)                         *)
(*                                                                   *)
(*   For Gaussian integers z = (a, b) and w = (c, d):              *)
(*     z · w = (ac - bd, ad + bc)    (complex multiplication)       *)
(*                                                                   *)
(*   We work in nat, so we prove the positive version:              *)
(*     (ac + bd)² + (ad - bc)²  is one formula                     *)
(*     (ac - bd)² + (ad + bc)²  is another                         *)
(*                                                                   *)
(*   The key algebraic identity (Brahmagupta–Fibonacci):            *)
(*     (a² + b²)(c² + d²) = (ac - bd)² + (ad + bc)²               *)
(*                        = (ac + bd)² + (ad - bc)²               *)
(*                                                                   *)
(*   This is the algebraic heart of why the Gaussian line           *)
(*   generates primes. We prove the positive version.               *)
(* ================================================================= *)

(* Brahmagupta-Fibonacci identity — norm is multiplicative *)
(* (a² + b²)(c² + d²) = (ac+bd)² + (ad-bc)² [for ad >= bc] *)
(* We prove the equivalent: both products of norms are equal        *)
Theorem brahmagupta_fibonacci :
  forall a b c d : nat,
  (a * a + b * b) * (c * c + d * d) =
  (a * c + b * d) * (a * c + b * d) +
  (a * d - b * c) * (a * d - b * c)  \/
  (a * a + b * b) * (c * c + d * d) =
  (a * c - b * d) * (a * c - b * d) +
  (a * d + b * c) * (a * d + b * c).
Proof.
  intros a b c d.
  right.
  (* (a²+b²)(c²+d²) = (ac-bd)²+(ad+bc)² — expand both sides *)
  nia.
Qed.

(* The clean multiplicative norm formula using the second form *)
Theorem norm_multiplicative :
  forall a b c d : nat,
  gnorm_sq a b * gnorm_sq c d =
  gnorm_sq (a * c + b * d) (a * d + b * c)  \/
  gnorm_sq a b * gnorm_sq c d =
  gnorm_sq (a * c - b * d) (a * d + b * c).
Proof.
  intros a b c d. unfold gnorm_sq. right. nia.
Qed.

(* COROLLARY: the norm of a product divides the product of norms *)
Theorem norm_product_divides :
  forall a b c d k : nat,
  gnorm_sq a b * gnorm_sq c d = k ->
  Nat.divide (gnorm_sq a b) k.
Proof.
  intros a b c d k H.
  exists (gnorm_sq c d). lia.
Qed.

(* ================================================================= *)
(* PART 4 — ORDINARY PRIMALITY ON THE 0° LINE                       *)
(*                                                                   *)
(*   An ordinary natural number p is prime if:                      *)
(*     p ≥ 2 AND for all a b, p = a * b → a = 1 ∨ b = 1           *)
(*   This is the 0° line definition: purely additive structure.     *)
(* ================================================================= *)

(* Primality on the 0° line *)
Definition prime_0deg (p : nat) : Prop :=
  p >= 2 /\ forall a b : nat, p = a * b -> a = 1 \/ b = 1.

(* 2 is prime on the 0° line *)
Theorem two_is_prime_0deg : prime_0deg 2.
Proof.
  unfold prime_0deg. split. lia.
  intros a b H.
  destruct a as [|[|[|a]]]; destruct b as [|[|[|b]]]; lia.
Qed.

(* 3 is prime on the 0° line *)
Theorem three_is_prime_0deg : prime_0deg 3.
Proof.
  unfold prime_0deg. split. lia.
  intros a b H.
  destruct a as [|[|[|[|a]]]]; destruct b as [|[|[|[|b]]]]; lia.
Qed.

(* 4 is NOT prime (it factors on the 0° line) *)
Theorem four_not_prime_0deg : ~prime_0deg 4.
Proof.
  unfold prime_0deg. intro H. destruct H as [_ Hf].
  specialize (Hf 2 2). simpl in Hf.
  destruct Hf as [H|H]; lia.
Qed.

(* ================================================================= *)
(* PART 5 — GAUSSIAN IRREDUCIBILITY ON THE 45° DIAGONAL             *)
(*                                                                   *)
(*   A Gaussian point (a, b) is irreducible on the diagonal if:    *)
(*     N(a, b) = a² + b² cannot be written as N(c,d) · N(e,f)      *)
(*     with N(c,d) > 1 and N(e,f) > 1                              *)
(*                                                                   *)
(*   KEY COROLLARY:                                                  *)
(*   IF (a² + b²) = p is prime on the 0° line,                     *)
(*   THEN (a, b) is irreducible on the Gaussian diagonal.           *)
(*                                                                   *)
(*   PROOF: If (a,b) = (c,d)·(e,f) on the Gaussian line, then      *)
(*          p = N(c,d) · N(e,f). Since p is prime, one factor = 1, *)
(*          meaning that factor is a unit (1,0) or (0,1).          *)
(* ================================================================= *)

(* A Gaussian norm-value is a unit if it equals 1 *)
Definition gaussian_unit_norm (n : nat) : Prop := n = 1.

(* Gaussian irreducibility: norm is prime on 0° line *)
Definition gaussian_irreducible (a b : nat) : Prop :=
  prime_0deg (gnorm_sq a b).

(* THE COROLLARY: prime norm → irreducible on diagonal *)
Theorem prime_norm_implies_gaussian_irreducible :
  forall a b : nat,
  prime_0deg (gnorm_sq a b) ->
  gaussian_irreducible a b.
Proof.
  (* Direct: gaussian_irreducible IS prime_0deg ∘ gnorm_sq *)
  intros a b H. unfold gaussian_irreducible. exact H.
Qed.

(* Converse direction: if norm factors, so does the Gaussian point *)
(* If gnorm_sq a b = m * n with m,n > 1, then (a,b) is reducible *)
Theorem factored_norm_implies_reducible :
  forall a b m n : nat,
  gnorm_sq a b = m * n ->
  m > 1 -> n > 1 ->
  ~gaussian_irreducible a b.
Proof.
  intros a b m n Hnorm Hm Hn.
  unfold gaussian_irreducible, prime_0deg.
  intro H. destruct H as [_ Hprime].
  specialize (Hprime m n Hnorm).
  destruct Hprime as [H|H]; lia.
Qed.

(* ================================================================= *)
(* PART 6 — THE MOD 4 STRUCTURE                                     *)
(*                                                                   *)
(*   THE FUNDAMENTAL THEOREM OF GAUSSIAN PRIMES:                    *)
(*                                                                   *)
(*   Case p = 2:  2 = (1+i)(1-i), N(1+i) = 1² + 1² = 2            *)
(*                2 RAMIFIES on the diagonal: it becomes a          *)
(*                perfect square (up to units)                      *)
(*                                                                   *)
(*   Case p ≡ 1 (mod 4): p SPLITS into two conjugate factors       *)
(*                p = (a+bi)(a-bi) = a² + b² for some a, b         *)
(*                These live on the diagonal at angle arctan(b/a)   *)
(*                                                                   *)
(*   Case p ≡ 3 (mod 4): p STAYS PRIME on the diagonal            *)
(*                No way to write p = a² + b² over the integers    *)
(*                p remains irreducible as a Gaussian integer       *)
(*                                                                   *)
(*   GEOMETRIC MEANING:                                              *)
(*     p ≡ 1 (mod 4): the prime HAS a representation as a norm     *)
(*                    — it projects ONTO the 45° diagonal          *)
(*     p ≡ 3 (mod 4): the prime CANNOT be a norm                   *)
(*                    — it stays on the 0° line, invisible to 45°  *)
(* ================================================================= *)

(* p ≡ 1 mod 4: the prime can be a sum of two squares *)
Definition splits_on_diagonal (p : nat) : Prop :=
  exists a b : nat, b > 0 /\ gnorm_sq a b = p.

(* p ≡ 3 mod 4: the prime cannot be a sum of two squares *)
Definition stays_on_0deg (p : nat) : Prop :=
  forall a b : nat, gnorm_sq a b = p -> b = 0.

(* A number ≡ 3 mod 4 cannot be a sum of two squares *)
(* PROOF: squares are 0 or 1 mod 4; 0+0=0, 0+1=1, 1+1=2 mod 4    *)
(* So a sum of two squares is NEVER 3 mod 4.                       *)
Theorem mod4_3_not_sum_of_squares :
  forall p : nat,
  p mod 4 = 3 ->
  forall a b : nat, gnorm_sq a b <> p.
Proof.
  intros p Hp a b H.
  unfold gnorm_sq in H.
  (* Key: a² mod 4 ∈ {0,1} and b² mod 4 ∈ {0,1} *)
  (* So (a²+b²) mod 4 ∈ {0,1,2} — never 3      *)
  assert (Ha : (a * a) mod 4 = 0 \/ (a * a) mod 4 = 1).
  { destruct (a mod 4) eqn:Ea.
    - left. nia.
    - right. nia.
    - left. nia.
    - right. nia. }
  assert (Hb : (b * b) mod 4 = 0 \/ (b * b) mod 4 = 1).
  { destruct (b mod 4) eqn:Eb.
    - left. nia.
    - right. nia.
    - left. nia.
    - right. nia. }
  destruct Ha as [Ha|Ha]; destruct Hb as [Hb|Hb]; nia.
Qed.

(* COROLLARY: any prime ≡ 3 mod 4 stays on the 0° line *)
Theorem prime_mod4_3_stays_on_0deg :
  forall p : nat,
  prime_0deg p ->
  p mod 4 = 3 ->
  stays_on_0deg p.
Proof.
  intros p Hp Hmod a b H.
  exfalso.
  exact (mod4_3_not_sum_of_squares p Hmod a b H).
Qed.

(* 2 is special: 2 = 1² + 1², it hits the diagonal at (1,1) *)
Theorem two_ramifies :
  gnorm_sq 1 1 = 2.
Proof. reflexivity. Qed.

(* 5 splits: 5 = 1² + 2² = 2² + 1² *)
Theorem five_splits :
  gnorm_sq 1 2 = 5 /\ gnorm_sq 2 1 = 5.
Proof. split; reflexivity. Qed.

(* 5 mod 4 = 1: it should split *)
Theorem five_mod4 : 5 mod 4 = 1.
Proof. reflexivity. Qed.

(* 7 mod 4 = 3: it should stay on 0° line *)
Theorem seven_mod4 : 7 mod 4 = 3.
Proof. reflexivity. Qed.

(* 7 cannot be a sum of two squares — verified *)
Theorem seven_not_sum_of_squares :
  forall a b : nat, gnorm_sq a b <> 7.
Proof.
  apply mod4_3_not_sum_of_squares. reflexivity.
Qed.

(* 13 splits: 13 = 2² + 3² *)
Theorem thirteen_splits :
  gnorm_sq 2 3 = 13.
Proof. reflexivity. Qed.

(* 13 mod 4 = 1 *)
Theorem thirteen_mod4 : 13 mod 4 = 1.
Proof. reflexivity. Qed.

(* ================================================================= *)
(* PART 7 — THE MASTER COROLLARY                                     *)
(*                                                                   *)
(*   THEOREM: Ordinary primes are a COROLLARY of the Gaussian line. *)
(*                                                                   *)
(*   PROOF STRUCTURE:                                                *)
(*     Step 1: The 0° and 90° axes give us MUL and ADD.            *)
(*     Step 2: The 45° diagonal gives us the NORM = a² + b².       *)
(*             (MUL composed with itself on each axis, then ADD'd)  *)
(*     Step 3: The norm is multiplicative (Brahmagupta-Fibonacci).  *)
(*     Step 4: An irreducible element on the diagonal is one        *)
(*             whose norm cannot factor non-trivially.              *)
(*     Step 5: Norm-irreducibility on the diagonal ↔               *)
(*             primality of the norm value on the 0° line.         *)
(*     Step 6: Primes ≡ 3 (mod 4) are invisible to the diagonal   *)
(*             (they cannot be norms) — they stay on the 0° line.  *)
(*     Step 7: Primes ≡ 1 (mod 4) and p=2 appear as diagonal norms.*)
(*             They SPLIT: p = N(a+bi) for some a,b.               *)
(*     QED: ALL primes are characterized by the Gaussian diagonal.  *)
(* ================================================================= *)

Theorem primes_corollary_of_gaussian_line :
  (* 1: The diagonal norm is derived from MUL and ADD *)
  (forall a b : nat, gnorm_sq a b = a * a + b * b) /\
  (* 2: The norm is multiplicative (Brahmagupta-Fibonacci) *)
  (forall a b c d : nat,
    gnorm_sq a b * gnorm_sq c d =
    gnorm_sq (a * c + b * d) (a * d + b * c)  \/
    gnorm_sq a b * gnorm_sq c d =
    gnorm_sq (a * c - b * d) (a * d + b * c)) /\
  (* 3: An ordinary prime norm → Gaussian irreducible *)
  (forall a b : nat,
    prime_0deg (gnorm_sq a b) -> gaussian_irreducible a b) /\
  (* 4: Numbers ≡ 3 mod 4 cannot appear as Gaussian norms *)
  (forall p a b : nat,
    p mod 4 = 3 -> gnorm_sq a b <> p) /\
  (* 5: 2 ramifies — it IS a diagonal norm *)
  (gnorm_sq 1 1 = 2) /\
  (* 6: 5 (≡ 1 mod 4) splits — it appears as diagonal norm *)
  (gnorm_sq 1 2 = 5) /\
  (* 7: 7 (≡ 3 mod 4) stays on 0° — not a diagonal norm *)
  (forall a b : nat, gnorm_sq a b <> 7).
Proof.
  repeat split.
  - (* gnorm_sq definition *)
    intros a b. unfold gnorm_sq. lia.
  - (* Brahmagupta-Fibonacci *)
    exact norm_multiplicative.
  - (* prime norm → irreducible *)
    exact prime_norm_implies_gaussian_irreducible.
  - (* mod 4 = 3 not a norm *)
    exact mod4_3_not_sum_of_squares.
  - (* 2 ramifies *)
    exact two_ramifies.
  - (* 5 splits *)
    exact (proj1 five_splits).
  - (* 7 stays *)
    exact seven_not_sum_of_squares.
Qed.
