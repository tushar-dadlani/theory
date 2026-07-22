(* ================================================================= *)
(*  PrimeFactorizationN.v                                             *)
(*                                                                    *)
(*  UNIQUE FACTORIZATION OVER THE FIRST n PRIMES, AS A BIJECTION.      *)
(*                                                                    *)
(*  Generalizes FreeDivMeetIso (2 primes) to a list ps of n DISTINCT   *)
(*  primes.  The coding map                                            *)
(*                                                                    *)
(*     code ps ks = prod_i (ps_i) ^ (ks_i)   (occupation vector -> N)   *)
(*                                                                    *)
(*  sends an exponent tuple to the {ps}-smooth number it factors.  We  *)
(*  prove it is:                                                       *)
(*                                                                    *)
(*    - an ORDER EMBEDDING  (code_order_iso_N):                        *)
(*        code ps as | code ps bs  <->  Forall2 (<=) as bs             *)
(*      (divisibility of the coded numbers = pointwise order of the     *)
(*       exponent tuples), generalizing FreeDivMeetIso.code_order_iso;  *)
(*                                                                    *)
(*    - INJECTIVE  (code_inj):                                         *)
(*        code ps as = code ps bs  ->  as = bs                         *)
(*      i.e. the exponent tuple is UNIQUE -- the "unique" of unique     *)
(*      factorization.  So code is a BIJECTION of the first-n-primes    *)
(*      exponent tuples onto the {first n primes}-smooth numbers they   *)
(*      generate.                                                      *)
(*                                                                    *)
(*  This is the injective (uniqueness) half of the crux deferred in     *)
(*  PrimorialZeta / LEDGER.  The core is prime_pow_cancel: from         *)
(*  p^a * X = p^b * Y with X,Y coprime to a prime p, we get a=b and     *)
(*  X=Y (the p-adic valuation is well-defined) -- peeling one prime at   *)
(*  a time, exactly the FreeDivMeetIso Gauss argument iterated.         *)
(*                                                                    *)
(*  Axiom-free: constructive Z/nat, Znumtheory (no classical logic).   *)
(* ================================================================= *)

Require Import FreeDivMeet FreeDivMeetIso.
From Stdlib Require Import ZArith Znumtheory Lia List.
Import ListNotations.

(* the coding map: prod ps_i ^ ks_i over the paired lists *)
Fixpoint code (ps : list Z) (ks : list nat) : Z :=
  match ps, ks with
  | p :: ps', k :: ks' => p ^ Z.of_nat k * code ps' ks'
  | _, _ => 1
  end.

(* ----------------------------------------------------------------- *)
(*  Coprimality plumbing                                             *)
(* ----------------------------------------------------------------- *)

(* a prime is coprime to any OTHER prime (like FreeDivMeet.pq_coprime) *)
Lemma distinct_primes_coprime : forall p q,
  prime p -> prime q -> p <> q -> rel_prime p q.
Proof.
  intros p q Hp Hq Hpq. apply prime_rel_prime; [ exact Hp | ]. intro Hdiv.
  destruct (prime_divisors q Hq p Hdiv) as [H | [H | [H | H]]];
    destruct Hp as [Hp1 _]; destruct Hq as [Hq1 _]; lia.
Qed.

(* a prime coprime to every prime in ps is coprime to code ps ks *)
Lemma coprime_code : forall p ps ks,
  prime p -> Forall prime ps -> ~ In p ps ->
  length ps = length ks ->
  rel_prime p (code ps ks).
Proof.
  intros p ps; induction ps as [|q ps' IH]; intros ks Hp Hpr Hnin Hlen.
  - destruct ks; simpl; [ apply rel_prime_sym, rel_prime_1 | simpl in Hlen; lia ].
  - destruct ks as [|k ks']; [ simpl in Hlen; lia | ].
    inversion Hpr as [| ? ? Hq Hpr']; subst.
    assert (Hpq : p <> q) by (intro; subst; apply Hnin; left; reflexivity).
    simpl. apply rel_prime_mult.
    + apply rp_r, distinct_primes_coprime; assumption.
    + apply IH; [ assumption | assumption
                | intro Hin; apply Hnin; right; exact Hin | simpl in Hlen; lia ].
Qed.

(* a prime does not divide anything coprime to it *)
Lemma rel_prime_ndvd : forall p X, 1 < p -> rel_prime p X -> ~ (p | X).
Proof.
  intros p X Hp Hrp Hdvd. destruct Hrp as [_ _ Hg].
  assert (Hd1 : (p | 1)) by (apply Hg; [ apply Z.divide_refl | exact Hdvd ]).
  pose proof (Z.divide_pos_le p 1 ltac:(lia) Hd1); lia.
Qed.

(* ----------------------------------------------------------------- *)
(*  The p-adic cancellation core                                     *)
(* ----------------------------------------------------------------- *)

(* if p^a * X = p^b * Y and X is coprime to p, then b <= a *)
Lemma no_extra_p : forall p X Y a b, 1 < p -> rel_prime p X ->
  p ^ Z.of_nat a * X = p ^ Z.of_nat b * Y -> (b <= a)%nat.
Proof.
  intros p X Y a b Hp Hrp Heq.
  destruct (le_gt_dec b a) as [Hle | Hgt]; [ exact Hle | exfalso ].
  assert (Hpa : 0 < p ^ Z.of_nat a) by (apply Z.pow_pos_nonneg; lia).
  assert (Hsplit : Z.of_nat b = Z.of_nat a + Z.of_nat (b - a)) by lia.
  rewrite Hsplit, Z.pow_add_r in Heq by lia.
  assert (HX : X = p ^ Z.of_nat (b - a) * Y).
  { apply (Z.mul_reg_l X (p ^ Z.of_nat (b - a) * Y) (p ^ Z.of_nat a));
      [ lia | rewrite Heq; ring ]. }
  assert (Hpp : (p | p ^ Z.of_nat (b - a))).
  { exists (p ^ Z.of_nat (b - a - 1)).
    replace (Z.of_nat (b - a)) with (Z.of_nat (b - a - 1) + 1) by lia.
    rewrite Z.pow_add_r by lia; rewrite Z.pow_1_r; ring. }
  assert (Hpdvd : (p | X)).
  { rewrite HX; apply Z.divide_trans with (p ^ Z.of_nat (b - a));
      [ exact Hpp | exists Y; ring ]. }
  apply (rel_prime_ndvd p X Hp Hrp Hpdvd).
Qed.

(* CANCELLATION: p^a*X = p^b*Y with X,Y coprime to p forces a=b and X=Y *)
Lemma prime_pow_cancel : forall p X Y a b, 1 < p ->
  rel_prime p X -> rel_prime p Y ->
  p ^ Z.of_nat a * X = p ^ Z.of_nat b * Y -> a = b /\ X = Y.
Proof.
  intros p X Y a b Hp HrX HrY Heq.
  assert (Hba : (b <= a)%nat) by (apply (no_extra_p p X Y a b Hp HrX Heq)).
  assert (Hab : (a <= b)%nat).
  { apply (no_extra_p p Y X b a Hp HrY); symmetry; exact Heq. }
  assert (Hab_eq : a = b) by lia. subst b.
  assert (Hpa : 0 < p ^ Z.of_nat a) by (apply Z.pow_pos_nonneg; lia).
  split; [ reflexivity | apply (Z.mul_reg_l X Y (p ^ Z.of_nat a)); [ lia | exact Heq ] ].
Qed.

(* ----------------------------------------------------------------- *)
(*  INJECTIVITY -- uniqueness of factorization over the first n primes *)
(* ----------------------------------------------------------------- *)

Theorem code_inj : forall ps as_ bs,
  Forall prime ps -> NoDup ps ->
  length ps = length as_ -> length ps = length bs ->
  code ps as_ = code ps bs -> as_ = bs.
Proof.
  induction ps as [|p ps' IH]; intros as_ bs Hpr Hnd Hla Hlb Heq.
  - destruct as_; [ | simpl in Hla; lia ].
    destruct bs; [ reflexivity | simpl in Hlb; lia ].
  - destruct as_ as [|a as'']; [ simpl in Hla; lia | ].
    destruct bs as [|b bs']; [ simpl in Hlb; lia | ].
    inversion Hpr as [| ? ? Hpp Hpr']; subst.
    inversion Hnd as [| ? ? Hnin Hnd']; subst.
    assert (Hp1 : 1 < p) by (destruct Hpp; lia).
    assert (HrX : rel_prime p (code ps' as''))
      by (apply coprime_code; [ exact Hpp | exact Hpr' | exact Hnin | simpl in Hla; lia ]).
    assert (HrY : rel_prime p (code ps' bs'))
      by (apply coprime_code; [ exact Hpp | exact Hpr' | exact Hnin | simpl in Hlb; lia ]).
    simpl in Heq.
    destruct (prime_pow_cancel p (code ps' as'') (code ps' bs') a b Hp1 HrX HrY Heq)
      as [Hab Hcode].
    subst b.
    assert (as'' = bs')
      by (apply IH; [ exact Hpr' | exact Hnd' | simpl in Hla; lia
                    | simpl in Hlb; lia | exact Hcode ]).
    subst; reflexivity.
Qed.

(* ----------------------------------------------------------------- *)
(*  THE ORDER EMBEDDING -- divisibility = pointwise order             *)
(* ----------------------------------------------------------------- *)

Lemma mul_dvd : forall a b c d : Z, (a | b) -> (c | d) -> (a * c | b * d).
Proof. intros a b c d [x Hx] [y Hy]; exists (x * y); subst; ring. Qed.

(* forward: pointwise order -> divisibility *)
Lemma code_mono_N : forall ps as_ bs,
  length ps = length as_ -> Forall2 le as_ bs ->
  (code ps as_ | code ps bs).
Proof.
  induction ps as [|p ps' IH]; intros as_ bs Hlen Hf2.
  - simpl. apply Z.divide_refl.
  - destruct as_ as [|a as'']; [ simpl in Hlen; lia | ].
    inversion Hf2 as [| ? ? ? ? Hab Hf2']; subst.
    simpl. apply mul_dvd; [ apply pow_dvd; exact Hab
                         | apply IH; [ simpl in Hlen; lia | exact Hf2' ] ].
Qed.

(* reverse: divisibility -> pointwise order (the substantive direction) *)
Lemma code_faithful_N : forall ps as_ bs,
  Forall prime ps -> NoDup ps ->
  length ps = length as_ -> length ps = length bs ->
  (code ps as_ | code ps bs) -> Forall2 le as_ bs.
Proof.
  induction ps as [|p ps' IH]; intros as_ bs Hpr Hnd Hla Hlb Hdvd.
  - destruct as_; [ | simpl in Hla; lia ].
    destruct bs; [ constructor | simpl in Hlb; lia ].
  - destruct as_ as [|a as'']; [ simpl in Hla; lia | ].
    destruct bs as [|b bs']; [ simpl in Hlb; lia | ].
    inversion Hpr as [| ? ? Hpp Hpr']; subst.
    inversion Hnd as [| ? ? Hnin Hnd']; subst.
    assert (Hp2 : 2 <= p) by (destruct Hpp; lia).
    assert (Hp1 : 1 < p) by lia.
    assert (HrX : rel_prime p (code ps' as''))
      by (apply coprime_code; [ exact Hpp | exact Hpr' | exact Hnin | simpl in Hla; lia ]).
    assert (HrY : rel_prime p (code ps' bs'))
      by (apply coprime_code; [ exact Hpp | exact Hpr' | exact Hnin | simpl in Hlb; lia ]).
    simpl in Hdvd.
    (* a <= b : peel the prime p via Gauss (p^a coprime to Y) *)
    assert (Hab : (a <= b)%nat).
    { apply (pow_dvd_le p a b Hp2).
      apply (Gauss (p ^ Z.of_nat a) (code ps' bs') (p ^ Z.of_nat b)).
      - rewrite (Z.mul_comm (code ps' bs') (p ^ Z.of_nat b)).
        apply Z.divide_trans with (p ^ Z.of_nat a * code ps' as'');
          [ exists (code ps' as''); ring | exact Hdvd ].
      - apply rp_l; exact HrY. }
    (* the tails divide, so recurse : X | Y via Gauss (X coprime to p^b) *)
    assert (HXY : (code ps' as'' | code ps' bs')).
    { apply (Gauss (code ps' as'') (p ^ Z.of_nat b) (code ps' bs')).
      - apply Z.divide_trans with (p ^ Z.of_nat a * code ps' as'');
          [ exists (p ^ Z.of_nat a); ring | exact Hdvd ].
      - apply rp_r, rel_prime_sym; exact HrX. }
    constructor;
      [ exact Hab
      | apply (IH as'' bs' Hpr' Hnd');
          [ simpl in Hla; lia | simpl in Hlb; lia | exact HXY ] ].
Qed.

Theorem code_order_iso_N : forall ps as_ bs,
  Forall prime ps -> NoDup ps ->
  length ps = length as_ -> length ps = length bs ->
  ((code ps as_ | code ps bs) <-> Forall2 le as_ bs).
Proof.
  intros ps as_ bs Hpr Hnd Hla Hlb; split.
  - apply code_faithful_N; assumption.
  - apply code_mono_N; assumption.
Qed.

(* ----------------------------------------------------------------- *)
(*  MASTER THEOREM                                                   *)
(* ----------------------------------------------------------------- *)

Theorem unique_factorization_first_n_primes : forall ps as_ bs,
  Forall prime ps -> NoDup ps ->
  length ps = length as_ -> length ps = length bs ->
  (* code is an order embedding ... *)
  ((code ps as_ | code ps bs) <-> Forall2 le as_ bs)
  (* ... hence injective: the exponent tuple is unique *)
  /\ (code ps as_ = code ps bs -> as_ = bs).
Proof.
  intros ps as_ bs Hpr Hnd Hla Hlb; split.
  - apply code_order_iso_N; assumption.
  - apply code_inj; assumption.
Qed.

Print Assumptions unique_factorization_first_n_primes.

(* ================================================================= *)
(*  END PrimeFactorizationN.v                                        *)
(*  code ps : exponent-tuples -> {ps}-smooth numbers is an order       *)
(*  embedding and injective (unique factorization over the first n     *)
(*  primes).  This is the injectivity/uniqueness half of the crux      *)
(*  deferred in PrimorialZeta; surjectivity onto ALL {ps}-smooth        *)
(*  numbers (factorization EXISTENCE) remains the other half.          *)
(*  ZERO Admitted; Closed under the global context.                    *)
(* ================================================================= *)
