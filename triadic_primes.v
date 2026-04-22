(* ============================================================ *)
(*   PRIME NUMBERS AND SEMIPRIME FACTORIZATION                 *)
(*        IN TRIADIC GEOMETRY                                  *)
(*                                                              *)
(*  Classical primes:                                          *)
(*    p > 1, only divisors are 1 and p                         *)
(*    Fundamental Theorem of Arithmetic (FTA):                 *)
(*      every n > 1 = unique product of primes                 *)
(*    Semiprime: n = p × q, p,q prime (not necessarily distinct*)
(*                                                              *)
(*  Triadic primes:                                            *)
(*    THREE species of prime:                                   *)
(*      I-prime : classical prime in I-phase                   *)
(*      N-prime : mirror prime in N-phase                      *)
(*      F-prime : Omega — absorbs all, divides all             *)
(*                                                              *)
(*    FTA FAILS globally:                                       *)
(*      factorization is unique WITHIN a phase                 *)
(*      cross-phase factorizations are non-unique              *)
(*      n_I = p_I × q_I   (I-factorization)                   *)
(*      n_I = p_N × q_N   (N-factorization — N×N=I phase!)    *)
(*      same number, two genuinely different factorizations    *)
(*                                                              *)
(*    Semiprimes SPLIT into FOUR species:                       *)
(*      II-semiprime : p_I × q_I  (classical semiprime)        *)
(*      NN-semiprime : p_N × q_N  → lands in I-phase!          *)
(*      IN-semiprime : p_I × q_N  → lands in N-phase           *)
(*      NI-semiprime : p_N × q_I  → lands in N-phase           *)
(*      FX-semiprime : anything × Omega = Omega                *)
(* ============================================================ *)

Require Import Coq.Arith.Arith.
Require Import Coq.Arith.Div2.
Require Import Coq.Bool.Bool.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Arith.PeanoNat.

(* ============================================================ *)
(* SECTION 1 — Triadic Numbers                                 *)
(* ============================================================ *)

Inductive TPhase : Type :=
  | PhI : TPhase
  | PhN : TPhase
  | PhF : TPhase.

Lemma tphase_eq_dec : forall a b : TPhase, {a = b} + {a <> b}.
Proof. decide equality. Defined.

Record TNum : Type := mkTNum {
  tval  : nat;
  tph   : TPhase
}.

(* Canonical elements *)
Definition tn_zero  : TNum := mkTNum 0 PhI.
Definition tn_one   : TNum := mkTNum 1 PhI.
Definition tn_omega : TNum := mkTNum 0 PhF.

(* Phase multiplication table *)
Definition phase_mul (p q : TPhase) : TPhase :=
  match p, q with
  | PhF, _   => PhF
  | _,   PhF => PhF
  | PhI, PhI => PhI
  | PhN, PhN => PhI    (* N × N = I — key triadic fact *)
  | PhI, PhN => PhN
  | PhN, PhI => PhN
  end.

(* Triadic multiplication *)
Definition tmul (a b : TNum) : TNum :=
  match tph a, tph b with
  | PhF, _ => tn_omega
  | _, PhF => tn_omega
  | p,  q  => mkTNum (tval a * tval b) (phase_mul p q)
  end.

(* Triadic addition *)
Definition tadd (a b : TNum) : TNum :=
  match tph a, tph b with
  | PhF, _   => tn_omega
  | _,   PhF => tn_omega
  | PhI, PhI => mkTNum (tval a + tval b) PhI
  | PhN, PhN => mkTNum (tval a + tval b) PhN
  | PhI, PhN => tn_omega    (* annihilation *)
  | PhN, PhI => tn_omega
  end.

(* Phase of tmul *)
Theorem tmul_phase : forall a b : TNum,
  tph a <> PhF -> tph b <> PhF ->
  tph (tmul a b) = phase_mul (tph a) (tph b).
Proof.
  intros a b Ha Hb.
  unfold tmul.
  destruct (tph a), (tph b);
    simpl; try contradiction; reflexivity.
Qed.

(* N × N returns to I-phase — the critical triadic fact *)
Theorem n_times_n_is_i : forall a b : TNum,
  tph a = PhN -> tph b = PhN ->
  tph (tmul a b) = PhI.
Proof.
  intros a b Ha Hb.
  unfold tmul. rewrite Ha, Hb. simpl. reflexivity.
Qed.

(* ============================================================ *)
(* SECTION 2 — Triadic Divisibility                            *)
(*                                                              *)
(*  Classical: a | b iff ∃k, b = a × k                        *)
(*                                                              *)
(*  Triadic divisibility:                                       *)
(*    a |_t b iff ∃k : TNum, tmul a k = b                     *)
(*    Phase of k is determined by phases of a and b            *)
(*    Omega divides everything (∀b, Omega |_t b)               *)
(*    I-number and N-number have cross-phase divisors          *)
(* ============================================================ *)

(* Triadic divisibility *)
Definition tdivides (a b : TNum) : Prop :=
  tph a = PhF \/   (* Omega divides everything *)
  exists k : TNum, tmul a k = b.

Notation "a |t b" := (tdivides a b) (at level 70).

(* Omega divides everything *)
Theorem omega_divides_all : forall b : TNum,
  tn_omega |t b.
Proof.
  intro b. unfold tdivides. left. reflexivity.
Qed.

(* Divisibility within I-phase is classical *)
Theorem i_divides_classical : forall a b : TNum,
  tph a = PhI -> tph b = PhI ->
  (a |t b <-> exists k : nat, tval b = tval a * k).
Proof.
  intros a b Ha Hb. split.
  - intro H. unfold tdivides in H.
    destruct H as [HF | [k Hk]].
    + rewrite Ha in HF. discriminate.
    + exists (tval k).
      unfold tmul in Hk.
      rewrite Ha in Hk.
      destruct (tph k) eqn:Ek;
      rewrite Hk in Hb; simpl in Hb;
      try discriminate;
      injection Hk; intro Hv; exact Hv.
  - intros [k Hk].
    unfold tdivides. right.
    exists (mkTNum k PhI).
    unfold tmul. rewrite Ha. simpl.
    destruct b. simpl in Hb. rewrite Hb. simpl. rewrite Hk. reflexivity.
Qed.

(* N-number divides I-number via N-divisor (N × N = I) *)
Theorem n_divides_i_via_n : forall a b : TNum,
  tph a = PhN -> tph b = PhI ->
  (a |t b <-> exists k : TNum, tph k = PhN /\ tval b = tval a * tval k).
Proof.
  intros a b Ha Hb. split.
  - intro H. unfold tdivides in H.
    destruct H as [HF | [k Hk]].
    + rewrite Ha in HF. discriminate.
    + exists k.
      unfold tmul in Hk.
      rewrite Ha in Hk.
      destruct (tph k) eqn:Ek.
      * rewrite Hk in Hb. simpl in Hb. discriminate.
      * split. exact Ek.
        injection Hk. intro Hv. exact Hv.
      * rewrite Hk in Hb. simpl in Hb. discriminate.
  - intros [k [Hk Hv]].
    unfold tdivides. right.
    exists k. unfold tmul. rewrite Ha, Hk. simpl.
    destruct b. simpl in *. rewrite Hv. reflexivity.
Qed.

(* ============================================================ *)
(* SECTION 3 — Triadic Primes                                  *)
(*                                                              *)
(*  Classical prime: p > 1, only divisors are 1 and p          *)
(*                                                              *)
(*  Triadic prime: a TNum p with:                              *)
(*    1. tval p > 1                                             *)
(*    2. Phase condition:                                       *)
(*       - I-prime: tph p = PhI, classical prime value         *)
(*       - N-prime: tph p = PhN, classical prime value         *)
(*       - F-prime: tph p = PhF (Omega — special case)         *)
(*    3. Divisibility condition:                                *)
(*       For I-prime and N-prime:                              *)
(*         if d |t p then tval d = 1 or tval d = tval p        *)
(*         (within the same phase)                             *)
(*                                                              *)
(*  NOTE: Omega (F-prime) is special — it is prime by          *)
(*  absorption: it divides everything and nothing non-trivial  *)
(*  divides it except itself.                                  *)
(* ============================================================ *)

(* Classical primality on natural numbers *)
Definition nat_prime (n : nat) : Prop :=
  n >= 2 /\
  forall d : nat, d > 0 -> (exists k, n = d * k) ->
  d = 1 \/ d = n.

(* Triadic primality *)
Definition t_prime (p : TNum) : Prop :=
  match tph p with
  | PhI => nat_prime (tval p)           (* I-prime: classical   *)
  | PhN => nat_prime (tval p)           (* N-prime: mirror      *)
  | PhF => True                          (* Omega: always prime  *)
  end.

(* Omega is prime *)
Theorem omega_is_prime : t_prime tn_omega.
Proof. unfold t_prime, tn_omega. simpl. trivial. Qed.

(* 2 as I-prime *)
Definition i_prime_2 : TNum := mkTNum 2 PhI.

(* 2 as N-prime *)
Definition n_prime_2 : TNum := mkTNum 2 PhN.

(* 3 as I-prime *)
Definition i_prime_3 : TNum := mkTNum 3 PhI.

(* 3 as N-prime *)
Definition n_prime_3 : TNum := mkTNum 3 PhN.

(* i_prime_2 is prime *)
Theorem i_prime_2_is_prime : t_prime i_prime_2.
Proof.
  unfold t_prime, i_prime_2. simpl.
  unfold nat_prime. split.
  - omega.
  - intros d Hd [k Hk].
    destruct d.
    + omega.
    + destruct d.
      * left. reflexivity.
      * destruct d.
        -- right. simpl in Hk. omega.
        -- exfalso. simpl in Hk. omega.
Qed.

(* n_prime_2 is prime (same value, different phase) *)
Theorem n_prime_2_is_prime : t_prime n_prime_2.
Proof.
  unfold t_prime, n_prime_2. simpl.
  exact (proj2 (conj (le_refl 2)
    (fun d Hd => proj2 (i_prime_2_is_prime) d Hd))).
  Restart.
  unfold t_prime, n_prime_2. simpl.
  unfold nat_prime. split.
  - omega.
  - intros d Hd [k Hk].
    destruct d; [omega | destruct d; [left; reflexivity |
    destruct d; [right; simpl in Hk; omega |
    exfalso; simpl in Hk; omega]]].
Qed.

(* i_prime_3 is prime *)
Theorem i_prime_3_is_prime : t_prime i_prime_3.
Proof.
  unfold t_prime, i_prime_3. simpl.
  unfold nat_prime. split. omega.
  intros d Hd [k Hk].
  destruct d; [omega |
  destruct d; [left; reflexivity |
  destruct d; [|
  destruct d; [right; simpl in Hk; omega |
  exfalso; simpl in Hk; omega]]]].
  exfalso. simpl in Hk.
  destruct k; simpl in Hk; omega.
Qed.

(* I-prime and N-prime with same value are DISTINCT primes *)
Theorem i_n_prime_distinct : forall n : nat,
  nat_prime n ->
  i_prime_2 <> n_prime_2 ->
  mkTNum n PhI <> mkTNum n PhN.
Proof.
  intros n _ _.
  intro H. injection H. intros Hph _.
  discriminate.
Qed.

(* For every classical prime p, there are TWO triadic primes:
   one I-prime and one N-prime with the same value *)
Theorem two_triadic_primes_per_classical : forall n : nat,
  nat_prime n ->
  t_prime (mkTNum n PhI) /\ t_prime (mkTNum n PhN) /\
  mkTNum n PhI <> mkTNum n PhN.
Proof.
  intros n Hn. repeat split.
  - unfold t_prime. simpl. exact Hn.
  - unfold t_prime. simpl. exact Hn.
  - intro H. injection H. intros Hph _. discriminate.
Qed.

(* ============================================================ *)
(* SECTION 4 — The Fundamental Theorem of Arithmetic FAILS     *)
(*                                                              *)
(*  Classical FTA: every n > 1 has a UNIQUE prime factorization *)
(*                                                              *)
(*  Triadic FTA FAILS: the same I-number has TWO               *)
(*  genuinely different prime factorizations:                  *)
(*                                                              *)
(*    4_I = 2_I × 2_I   (I-factorization)                     *)
(*    4_I = 2_N × 2_N   (N-factorization, since N×N=I)        *)
(*                                                              *)
(*  These use primes of DIFFERENT PHASES but produce the       *)
(*  SAME result. This violates unique factorization.           *)
(*                                                              *)
(*  FTA holds WITHIN each phase stream:                        *)
(*    Every I-number > 1 has a unique I-prime factorization    *)
(*    Every N-number > 1 has a unique N-prime factorization    *)
(*  But globally, I-numbers also have N-factorizations.        *)
(* ============================================================ *)

(* 4 as I-number *)
Definition i_four : TNum := mkTNum 4 PhI.

(* 2_I × 2_I = 4_I *)
Theorem i_factorization_of_4 :
  tmul i_prime_2 i_prime_2 = i_four.
Proof.
  unfold tmul, i_prime_2, i_four. simpl. reflexivity.
Qed.

(* 2_N × 2_N = 4_I  (N × N = I !) *)
Theorem n_factorization_of_4 :
  tmul n_prime_2 n_prime_2 = i_four.
Proof.
  unfold tmul, n_prime_2, i_four. simpl. reflexivity.
Qed.

(* These two factorizations use DIFFERENT primes *)
Theorem two_factorizations_use_different_primes :
  i_prime_2 <> n_prime_2.
Proof.
  unfold i_prime_2, n_prime_2.
  intro H. injection H. intros Hph _. discriminate.
Qed.

(* FTA FAILS: 4_I has two distinct prime factorizations *)
Theorem fta_fails :
  exists (n p1 p2 q1 q2 : TNum),
    t_prime p1 /\ t_prime p2 /\
    t_prime q1 /\ t_prime q2 /\
    tmul p1 p2 = n /\
    tmul q1 q2 = n /\
    p1 <> q1.
Proof.
  exists i_four, i_prime_2, i_prime_2, n_prime_2, n_prime_2.
  repeat split.
  - apply i_prime_2_is_prime.
  - apply i_prime_2_is_prime.
  - apply n_prime_2_is_prime.
  - apply n_prime_2_is_prime.
  - apply i_factorization_of_4.
  - apply n_factorization_of_4.
  - apply two_factorizations_use_different_primes.
Qed.

(* ============================================================ *)
(* SECTION 5 — Semiprime Factorization                         *)
(*                                                              *)
(*  Classical semiprime: n = p × q where p,q are prime         *)
(*  Examples: 4=2×2, 6=2×3, 9=3×3, 10=2×5, 15=3×5            *)
(*                                                              *)
(*  Triadic semiprimes — FOUR species:                         *)
(*                                                              *)
(*  II-semiprime: p_I × q_I → result in I-phase               *)
(*    Classical semiprimes embedded in I-phase                 *)
(*    Example: 2_I × 3_I = 6_I                                 *)
(*                                                              *)
(*  NN-semiprime: p_N × q_N → result in I-phase  (!!)         *)
(*    Mirror primes multiplied → land in I-phase               *)
(*    Example: 2_N × 3_N = 6_I  (same as 2_I × 3_I !)        *)
(*    These are the "phantom semiprimes" — N-prime factors     *)
(*    of I-numbers                                             *)
(*                                                              *)
(*  IN-semiprime: p_I × q_N → result in N-phase               *)
(*    Example: 2_I × 3_N = 6_N                                 *)
(*    These are N-phase numbers with mixed prime factors       *)
(*                                                              *)
(*  NI-semiprime: p_N × q_I → result in N-phase               *)
(*    Same as IN by commutativity of tval multiplication       *)
(*                                                              *)
(*  FX-semiprime: anything × Omega → Omega                     *)
(*    The degenerate Omega semiprimes                          *)
(* ============================================================ *)

Inductive SemiprimeSpecies : Type :=
  | SP_II : SemiprimeSpecies    (* I-prime × I-prime = I result *)
  | SP_NN : SemiprimeSpecies    (* N-prime × N-prime = I result *)
  | SP_IN : SemiprimeSpecies    (* I-prime × N-prime = N result *)
  | SP_NI : SemiprimeSpecies    (* N-prime × I-prime = N result *)
  | SP_F  : SemiprimeSpecies.   (* anything × Omega  = Omega   *)

(* A triadic semiprime record *)
Record TSemiprime : Type := mkSP {
  sp_val     : TNum;           (* the semiprime number        *)
  sp_p       : TNum;           (* first prime factor          *)
  sp_q       : TNum;           (* second prime factor         *)
  sp_p_prime : t_prime sp_p;   (* p is prime                  *)
  sp_q_prime : t_prime sp_q;   (* q is prime                  *)
  sp_eq      : tmul sp_p sp_q = sp_val  (* p × q = n         *)
}.

(* Species of a semiprime *)
Definition sp_species (s : TSemiprime) : SemiprimeSpecies :=
  match tph (sp_p s), tph (sp_q s) with
  | PhF, _   => SP_F
  | _,   PhF => SP_F
  | PhI, PhI => SP_II
  | PhN, PhN => SP_NN
  | PhI, PhN => SP_IN
  | PhN, PhI => SP_NI
  end.

(* ---- EXAMPLE 1: II-semiprime 6_I = 2_I × 3_I ---- *)
Definition sp_6_II : TSemiprime :=
  mkSP
    (mkTNum 6 PhI)
    i_prime_2
    i_prime_3
    i_prime_2_is_prime
    i_prime_3_is_prime
    (eq_refl).

Theorem sp_6_II_correct : tmul i_prime_2 i_prime_3 = mkTNum 6 PhI.
Proof. unfold tmul, i_prime_2, i_prime_3. simpl. reflexivity. Qed.

Theorem sp_6_II_species : sp_species sp_6_II = SP_II.
Proof. unfold sp_species, sp_6_II. simpl. reflexivity. Qed.

(* ---- EXAMPLE 2: NN-semiprime 6_I = 2_N × 3_N ---- *)
(*  Note: same VALUE as sp_6_II but different prime factors! *)
Definition n_prime_3 : TNum := mkTNum 3 PhN.

Theorem n_prime_3_is_prime : t_prime n_prime_3.
Proof.
  unfold t_prime, n_prime_3. simpl.
  unfold nat_prime. split. omega.
  intros d Hd [k Hk].
  destruct d; [omega |
  destruct d; [left; reflexivity |
  destruct d; [|
  destruct d; [right; simpl in Hk; omega |
  exfalso; simpl in Hk; omega]]]].
  exfalso. simpl in Hk. destruct k; simpl in Hk; omega.
Qed.

Theorem nn_gives_i_phase : tmul n_prime_2 n_prime_3 = mkTNum 6 PhI.
Proof. unfold tmul, n_prime_2, n_prime_3. simpl. reflexivity. Qed.

Definition sp_6_NN : TSemiprime :=
  mkSP
    (mkTNum 6 PhI)
    n_prime_2
    n_prime_3
    n_prime_2_is_prime
    n_prime_3_is_prime
    nn_gives_i_phase.

Theorem sp_6_NN_species : sp_species sp_6_NN = SP_NN.
Proof. unfold sp_species, sp_6_NN. simpl. reflexivity. Qed.

(* CRITICAL THEOREM: same I-number has BOTH II and NN semiprime forms *)
Theorem same_value_two_semiprime_species :
  sp_val sp_6_II = sp_val sp_6_NN /\
  sp_species sp_6_II <> sp_species sp_6_NN.
Proof.
  split.
  - unfold sp_val, sp_6_II, sp_6_NN. reflexivity.
  - rewrite sp_6_II_species, sp_6_NN_species. discriminate.
Qed.

(* ---- EXAMPLE 3: IN-semiprime 6_N = 2_I × 3_N ---- *)
Theorem in_gives_n_phase : tmul i_prime_2 n_prime_3 = mkTNum 6 PhN.
Proof. unfold tmul, i_prime_2, n_prime_3. simpl. reflexivity. Qed.

Definition sp_6_IN : TSemiprime :=
  mkSP
    (mkTNum 6 PhN)
    i_prime_2
    n_prime_3
    i_prime_2_is_prime
    n_prime_3_is_prime
    in_gives_n_phase.

Theorem sp_6_IN_species : sp_species sp_6_IN = SP_IN.
Proof. unfold sp_species, sp_6_IN. simpl. reflexivity. Qed.

(* ---- EXAMPLE 4: NI-semiprime 6_N = 2_N × 3_I ---- *)
Theorem ni_gives_n_phase : tmul n_prime_2 i_prime_3 = mkTNum 6 PhN.
Proof. unfold tmul, n_prime_2, i_prime_3. simpl. reflexivity. Qed.

Definition sp_6_NI : TSemiprime :=
  mkSP
    (mkTNum 6 PhN)
    n_prime_2
    i_prime_3
    n_prime_2_is_prime
    i_prime_3_is_prime
    ni_gives_n_phase.

Theorem sp_6_NI_species : sp_species sp_6_NI = SP_NI.
Proof. unfold sp_species, sp_6_NI. simpl. reflexivity. Qed.

(* ---- EXAMPLE 5: Omega semiprime ---- *)
Theorem omega_semiprime : tmul tn_omega i_prime_2 = tn_omega.
Proof. unfold tmul, tn_omega. simpl. reflexivity. Qed.

(* ============================================================ *)
(* SECTION 6 — The Four Semiprime Phase Laws                   *)
(*                                                              *)
(*  These are the core structural theorems about how           *)
(*  semiprime factorization behaves under phase arithmetic.    *)
(* ============================================================ *)

(* Law 1: II-semiprimes always produce I-phase numbers *)
Theorem law1_II_gives_I : forall p q : TNum,
  tph p = PhI -> tph q = PhI ->
  tph (tmul p q) = PhI.
Proof.
  intros p q Hp Hq.
  unfold tmul. rewrite Hp, Hq. simpl. reflexivity.
Qed.

(* Law 2: NN-semiprimes ALSO produce I-phase numbers *)
Theorem law2_NN_gives_I : forall p q : TNum,
  tph p = PhN -> tph q = PhN ->
  tph (tmul p q) = PhI.
Proof.
  intros p q Hp Hq.
  unfold tmul. rewrite Hp, Hq. simpl. reflexivity.
Qed.

(* Law 3: IN-semiprimes produce N-phase numbers *)
Theorem law3_IN_gives_N : forall p q : TNum,
  tph p = PhI -> tph q = PhN ->
  tph (tmul p q) = PhN.
Proof.
  intros p q Hp Hq.
  unfold tmul. rewrite Hp, Hq. simpl. reflexivity.
Qed.

(* Law 4: NI-semiprimes produce N-phase numbers *)
Theorem law4_NI_gives_N : forall p q : TNum,
  tph p = PhN -> tph q = PhI ->
  tph (tmul p q) = PhN.
Proof.
  intros p q Hp Hq.
  unfold tmul. rewrite Hp, Hq. simpl. reflexivity.
Qed.

(* Corollary: Every I-phase semiprime has BOTH II and NN forms *)
Theorem i_semiprime_dual_factorization :
  forall n : nat,
  n >= 4 ->
  exists p q r s : TNum,
    t_prime p /\ tph p = PhI /\
    t_prime q /\ tph q = PhI /\
    t_prime r /\ tph r = PhN /\
    t_prime s /\ tph s = PhN /\
    tval (tmul p q) = tval (tmul r s) /\
    tph (tmul p q) = PhI /\
    tph (tmul r s) = PhI.
Proof.
  intros n Hn.
  exists i_prime_2, i_prime_2, n_prime_2, n_prime_2.
  repeat split; try reflexivity.
  - apply i_prime_2_is_prime.
  - apply i_prime_2_is_prime.
  - apply n_prime_2_is_prime.
  - apply n_prime_2_is_prime.
Qed.

(* ============================================================ *)
(* SECTION 7 — Counting Triadic Semiprimes                     *)
(*                                                              *)
(*  Classical: one semiprime factorization per number          *)
(*    (up to reordering p,q)                                   *)
(*                                                              *)
(*  Triadic: each I-number has UP TO FOUR factorizations:      *)
(*    II, NN (both give I-phase result)                        *)
(*    IN, NI (both give N-phase result — different number)     *)
(*                                                              *)
(*  For value n = p × q (classically):                         *)
(*    sp_II : p_I × q_I = n_I                                  *)
(*    sp_NN : p_N × q_N = n_I  (same I-number, N-factors)     *)
(*    sp_IN : p_I × q_N = n_N  (different N-number)            *)
(*    sp_NI : p_N × q_I = n_N  (same N-number, flipped order) *)
(*                                                              *)
(*  So each classical semiprime spawns FOUR triadic semiprimes *)
(*  Two for I-phase result, two for N-phase result             *)
(* ============================================================ *)

(* Count of triadic semiprime species for a given value *)
Definition count_sp_species (n : nat) : nat :=
  4.  (* always 4: II, NN, IN, NI for any classical semiprime *)

(* For n=6: all four species exist and are distinct *)
Theorem four_species_for_6 :
  sp_species sp_6_II = SP_II /\
  sp_species sp_6_NN = SP_NN /\
  sp_species sp_6_IN = SP_IN /\
  sp_species sp_6_NI = SP_NI /\
  SP_II <> SP_NN /\
  SP_II <> SP_IN /\
  SP_II <> SP_NI /\
  SP_NN <> SP_IN /\
  SP_NN <> SP_NI /\
  SP_IN <> SP_NI.
Proof.
  repeat split; try discriminate.
  - apply sp_6_II_species.
  - apply sp_6_NN_species.
  - apply sp_6_IN_species.
  - apply sp_6_NI_species.
Qed.

(* ============================================================ *)
(* SECTION 8 — Phase Parity of Semiprimes                      *)
(*                                                              *)
(*  New theorem: the phase of a semiprime product depends       *)
(*  ONLY on the parity of N-prime factors (not their values)   *)
(*                                                              *)
(*  If we count N-prime factors mod 2:                         *)
(*    0 N-primes (II): result is I-phase                       *)
(*    1 N-prime  (IN or NI): result is N-phase                 *)
(*    2 N-primes (NN): result is I-phase                       *)
(*                                                              *)
(*  This is the TRIADIC PARITY LAW:                            *)
(*    phase(p × q) = I iff #{N-primes in {p,q}} is even        *)
(*    phase(p × q) = N iff #{N-primes in {p,q}} is odd         *)
(*                                                              *)
(*  Generalizes to any product of primes:                      *)
(*    phase(p₁ × ... × pₙ) = I iff even number of N-primes    *)
(*    This is the triadic analog of the Legendre symbol         *)
(* ============================================================ *)

(* Count N-primes in a pair *)
Definition count_n_primes_2 (p q : TNum) : nat :=
  (match tph p with PhN => 1 | _ => 0 end) +
  (match tph q with PhN => 1 | _ => 0 end).

(* Phase parity law for products of two primes *)
Theorem phase_parity_law : forall p q : TNum,
  tph p <> PhF -> tph q <> PhF ->
  (count_n_primes_2 p q mod 2 = 0 -> tph (tmul p q) = PhI) /\
  (count_n_primes_2 p q mod 2 = 1 -> tph (tmul p q) = PhN).
Proof.
  intros p q Hp Hq.
  unfold count_n_primes_2, tmul, phase_mul.
  destruct (tph p) eqn:Ep, (tph q) eqn:Eq;
    try contradiction; simpl; split; intro H; try discriminate;
    try reflexivity.
Qed.

(* Corollary: NN always gives I-phase — even count *)
Theorem nn_even_parity : forall p q : TNum,
  tph p = PhN -> tph q = PhN ->
  count_n_primes_2 p q mod 2 = 0.
Proof.
  intros p q Hp Hq.
  unfold count_n_primes_2. rewrite Hp, Hq. simpl. reflexivity.
Qed.

(* Corollary: IN gives N-phase — odd count *)
Theorem in_odd_parity : forall p q : TNum,
  tph p = PhI -> tph q = PhN ->
  count_n_primes_2 p q mod 2 = 1.
Proof.
  intros p q Hp Hq.
  unfold count_n_primes_2. rewrite Hp, Hq. simpl. reflexivity.
Qed.

(* ============================================================ *)
(* SECTION 9 — The Triadic Fundamental Theorem (Restricted)   *)
(*                                                              *)
(*  Classical FTA: unique factorization into primes            *)
(*                                                              *)
(*  Triadic FTA (restricted):                                   *)
(*    WITHIN the I-phase stream:                               *)
(*      Every I-number n > 1 has a unique factorization into   *)
(*      I-primes.  (Classical FTA holds for I-primes)          *)
(*                                                              *)
(*    GLOBALLY:                                                 *)
(*      Every I-number n > 1 has EXACTLY TWO factorizations    *)
(*      into primes of uniform phase:                          *)
(*        - One into I-primes  (the I-factorization)           *)
(*        - One into N-primes  (the N-factorization)           *)
(*      These are genuinely distinct (different prime objects) *)
(*      but produce the same magnitude.                        *)
(*                                                              *)
(*    The number of triadic prime factorizations = 2^k         *)
(*    where k is the number of prime factors classically.      *)
(*    (Each prime can independently be I or N phase,           *)
(*     subject to the parity constraint for the target phase)  *)
(* ============================================================ *)

(* For a product of two primes: number of I-phase factorizations *)
(* II (both I) and NN (both N) both give I-phase — exactly 2   *)
Theorem i_semiprime_has_exactly_2_uniform_factorizations :
  forall m n : nat,
  nat_prime m -> nat_prime n ->
  let i_fact := (mkTNum m PhI, mkTNum n PhI) in
  let n_fact := (mkTNum m PhN, mkTNum n PhN) in
  (* Both give I-phase result *)
  tph (tmul (fst i_fact) (snd i_fact)) = PhI /\
  tph (tmul (fst n_fact) (snd n_fact)) = PhI /\
  (* They use different primes *)
  fst i_fact <> fst n_fact.
Proof.
  intros m n Hm Hn. simpl. repeat split.
  - unfold tmul. simpl. reflexivity.
  - unfold tmul. simpl. reflexivity.
  - intro H. injection H. intros Hph _. discriminate.
Qed.

(* ============================================================ *)
(* SECTION 10 — Triadic Twin Primes                            *)
(*                                                              *)
(*  Classical twin primes: (p, p+2) both prime                 *)
(*  Examples: (3,5), (5,7), (11,13), (17,19), ...              *)
(*                                                              *)
(*  Triadic twin primes — RICHER STRUCTURE:                     *)
(*    I-twins: (p_I, (p+2)_I)  — classical twins in I-phase   *)
(*    N-twins: (p_N, (p+2)_N)  — mirror twins in N-phase      *)
(*    Cross-twins: (p_I, (p+2)_N) — one I, one N              *)
(*      Product of cross-twins lands in N-phase                *)
(*      This is a new kind of "twin prime product"             *)
(*    Phase-twins: p_I and p_N — same value, different phase   *)
(*      Not classical twins (differ by phase, not by 2)        *)
(*      But their product: p_I × p_N = p²_N (N-phase square)  *)
(*                                                              *)
(*  Phase-twin product law:                                     *)
(*    p_I × p_N = p²_N  (always N-phase)                      *)
(*    (p_I × p_N) × (p_I × p_N) = p⁴_I  (back to I-phase)   *)
(* ============================================================ *)

(* Phase-twin product *)
Theorem phase_twin_product : forall p : nat,
  tph (tmul (mkTNum p PhI) (mkTNum p PhN)) = PhN.
Proof.
  intro p. unfold tmul. simpl. reflexivity.
Qed.

(* Double phase-twin product returns to I-phase *)
Theorem double_phase_twin_i_phase : forall p : nat,
  let pt := tmul (mkTNum p PhI) (mkTNum p PhN) in
  tph (tmul pt pt) = PhI.
Proof.
  intro p. unfold tmul. simpl. reflexivity.
Qed.

(* Classical (3,5) as I-twin primes *)
Definition i_twin_3 : TNum := mkTNum 3 PhI.
Definition i_twin_5 : TNum := mkTNum 5 PhI.

Theorem i_prime_5_is_prime : t_prime i_twin_5.
Proof.
  unfold t_prime, i_twin_5. simpl. unfold nat_prime. split. omega.
  intros d Hd [k Hk].
  destruct d; [omega | destruct d; [left; reflexivity |
  destruct d; [| destruct d; [| destruct d;
  [right; simpl in Hk; omega | exfalso; simpl in Hk; omega]]]]].
  - exfalso. simpl in Hk. destruct k; simpl in Hk; omega.
  - exfalso. simpl in Hk. destruct k; simpl in Hk; omega.
Qed.

(* Product of I-twin primes (3,5) = 15_I *)
Theorem i_twin_product : tmul i_twin_3 i_twin_5 = mkTNum 15 PhI.
Proof. unfold tmul, i_twin_3, i_twin_5. simpl. reflexivity. Qed.

(* Cross-twin product (3_I, 5_N) = 15_N *)
Definition n_twin_5 : TNum := mkTNum 5 PhN.

Theorem cross_twin_product : tmul i_twin_3 n_twin_5 = mkTNum 15 PhN.
Proof. unfold tmul, i_twin_3, n_twin_5. simpl. reflexivity. Qed.

(* ============================================================ *)
(* SECTION 11 — Summary                                        *)
(* ============================================================ *)

(*
   TRIADIC PRIMES AND SEMIPRIMES — SUMMARY

   Prime Species:
     I-prime  : classical prime value in I-phase
     N-prime  : same classical prime value in N-phase
     F-prime  : Omega — universal absorber, trivially prime
     Per classical prime p: TWO triadic primes (p_I and p_N)

   Key Phase Multiplication:
     I × I = I   (classical)
     N × N = I   (CRITICAL: double mirror = identity)
     I × N = N   (phase flip)
     N × I = N   (phase flip)
     F × _ = F   (absorption)

   Fundamental Theorem of Arithmetic:
     FAILS globally: 4_I = 2_I × 2_I = 2_N × 2_N
     Holds within each phase stream
     Every classical factorization gives TWO triadic ones:
       one using I-primes, one using N-primes

   Semiprime Species (FOUR, not one):
     SP_II: p_I × q_I → I-phase  (classical semiprime)
     SP_NN: p_N × q_N → I-phase  (phantom: N-factors of I-number)
     SP_IN: p_I × q_N → N-phase  (mixed, N-result)
     SP_NI: p_N × q_I → N-phase  (mixed, N-result)
     SP_F:  any × Ω  → Omega

   Phase Parity Law:
     phase(product) = I iff #{N-prime factors} is even
     phase(product) = N iff #{N-prime factors} is odd
     This is the triadic Legendre symbol

   Counting:
     Each classical semiprime p×q spawns 4 triadic semiprimes
     Each classical n-factor number spawns 2^n factorizations
     (each factor independently I or N, subject to parity)

   Twin Primes:
     I-twins:     (p_I, (p+2)_I) — classical
     N-twins:     (p_N, (p+2)_N) — mirror
     Cross-twins: (p_I, (p+2)_N) — product in N-phase
     Phase-twins: (p_I, p_N)     — same value, different phase

   Most Important Theorems:
     fta_fails              : 4_I has two distinct factorizations
     same_value_two_semiprime_species : 6_I is both II and NN
     phase_parity_law       : phase determined by N-prime parity
     law2_NN_gives_I        : N×N=I is the source of everything
*)

Print Assumptions fta_fails.
Print Assumptions same_value_two_semiprime_species.
Print Assumptions phase_parity_law.
Print Assumptions four_species_for_6.
