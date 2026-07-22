(* ================================================================= *)
(*  PrimeFactorizationExists.v                                       *)
(*                                                                    *)
(*  FACTORIZATION EXISTENCE -- the surjective half of the crux.        *)
(*                                                                    *)
(*  PrimeFactorizationN proved the coding map                          *)
(*     code ps ks = prod_i (ps_i) ^ (ks_i)                             *)
(*  INJECTIVE (unique factorization over the first n primes).  Here we  *)
(*  prove it SURJECTIVE onto the {ps}-smooth numbers: every m > 0 all   *)
(*  of whose prime divisors lie in ps HAS an exponent tuple ks with     *)
(*  code ps ks = m (code_surj).  Together with code_inj this makes      *)
(*  code a genuine BIJECTION                                           *)
(*                                                                    *)
(*     {exponent tuples of length n}  <->  {ps}-smooth positive numbers *)
(*                                                                    *)
(*  (code_bijection_smooth).                                          *)
(*                                                                    *)
(*  The engine is padic_val: every m > 0 splits as p^v * m' with        *)
(*  p not dividing m' (the p-adic valuation is total), proved by        *)
(*  well-founded recursion on 0 <= . < m; and has_prime_divisor: every  *)
(*  m > 1 has a prime divisor (well-founded recursion via stdlib's       *)
(*  not_prime_divide).  Peeling p_0, then p_1, ... down the prime list   *)
(*  reconstructs the tuple.                                            *)
(*                                                                    *)
(*  Axiom-free: constructive Z/nat, Znumtheory (no classical logic).   *)
(* ================================================================= *)

Require Import PrimeFactorizationN.
From Stdlib Require Import ZArith Znumtheory Lia List Wellfounded.
Import ListNotations.

(* ----------------------------------------------------------------- *)
(*  p-adic valuation is total: m = p^v * m' with p not dividing m'    *)
(* ----------------------------------------------------------------- *)

Lemma padic_val : forall p, 2 <= p -> forall m, 0 < m ->
  exists v m', m = p ^ Z.of_nat v * m' /\ ~ (p | m') /\ 0 < m'.
Proof.
  intros p Hp2 m. pattern m; revert m.
  apply (well_founded_induction (Z.lt_wf 0)).
  intros m IH Hm.
  assert (Hp0 : p <> 0) by lia.
  destruct (Z.eq_dec (m mod p) 0) as [Hmod | Hmod].
  - (* p | m : peel one factor of p and recurse on the quotient *)
    assert (Hpm : (p | m)) by (apply Zmod_divide; [ exact Hp0 | exact Hmod ]).
    destruct Hpm as [c Hc].                       (* m = c * p *)
    assert (Hc0 : 0 < c) by nia.
    assert (Hcm : 0 <= c < m) by nia.
    destruct (IH c Hcm Hc0) as [v1 [m' [Hval [Hnd Hpos]]]].
    exists (S v1), m'. split; [ | split; [ exact Hnd | exact Hpos ] ].
    rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
    rewrite Hc, Hval; ring.
  - (* p does not divide m : valuation is 0 *)
    exists 0%nat, m. rewrite Z.pow_0_r, Z.mul_1_l.
    split; [ reflexivity | split; [ | exact Hm ] ].
    intro Hdiv. apply Hmod. apply (proj2 (Z.mod_divide m p Hp0)); exact Hdiv.
Qed.

(* ----------------------------------------------------------------- *)
(*  every m > 1 has a prime divisor                                  *)
(* ----------------------------------------------------------------- *)

Lemma has_prime_divisor : forall m, 1 < m -> exists q, prime q /\ (q | m).
Proof.
  intros m. pattern m; revert m.
  apply (well_founded_induction (Z.lt_wf 0)).
  intros m IH Hm.
  destruct (prime_dec m) as [Hpr | Hnpr].
  - exists m; split; [ exact Hpr | apply Z.divide_refl ].
  - destruct (not_prime_divide m Hm Hnpr) as [n [[Hn1 Hn2] Hdvd]].
    assert (Hn0 : 0 <= n < m) by lia.
    destruct (IH n Hn0 Hn1) as [q [Hq Hqn]].
    exists q; split; [ exact Hq | apply Z.divide_trans with n; assumption ].
Qed.

(* ----------------------------------------------------------------- *)
(*  SURJECTIVITY onto the {ps}-smooth numbers                        *)
(* ----------------------------------------------------------------- *)

Theorem code_surj : forall ps, Forall prime ps -> NoDup ps ->
  forall m, 0 < m ->
    (forall q, prime q -> (q | m) -> In q ps) ->
    exists ks, length ps = length ks /\ code ps ks = m.
Proof.
  induction ps as [|p ps' IH]; intros Hpr Hnd m Hm Hsm.
  - (* ps = [] : m has no prime divisor, so m = 1 = code [] [] *)
    assert (Hm1 : m = 1).
    { destruct (Z.eq_dec m 1) as [He | Hne]; [ exact He | exfalso ].
      assert (H1m : 1 < m) by lia.
      destruct (has_prime_divisor m H1m) as [q [Hq Hqm]].
      exact (Hsm q Hq Hqm). }
    exists []; split; [ reflexivity | cbn [code]; rewrite Hm1; reflexivity ].
  - (* ps = p :: ps' : extract the p-valuation, recurse on the quotient *)
    inversion Hpr as [| ? ? Hpp Hpr']; subst.
    inversion Hnd as [| ? ? Hnin Hnd']; subst.
    assert (Hp2 : 2 <= p) by (destruct Hpp; lia).
    destruct (padic_val p Hp2 m Hm) as [a [m1 [Heq [Hndvd Hm1pos]]]].
    (* the quotient m1 is {ps'}-smooth *)
    assert (Hm1sm : forall q, prime q -> (q | m1) -> In q ps').
    { intros q Hq Hqm1.
      assert (Hqm : (q | m)).
      { apply Z.divide_trans with m1;
          [ exact Hqm1 | rewrite Heq; exists (p ^ Z.of_nat a); ring ]. }
      destruct (Hsm q Hq Hqm) as [Hpe | Hin]; [ exfalso | exact Hin ].
      rewrite <- Hpe in Hqm1; exact (Hndvd Hqm1). }
    destruct (IH Hpr' Hnd' m1 Hm1pos Hm1sm) as [ks' [Hlen Hcode]].
    exists (a :: ks'); split.
    + cbn [length]; rewrite Hlen; reflexivity.
    + cbn [code]; rewrite Hcode; symmetry; exact Heq.
Qed.

(* ----------------------------------------------------------------- *)
(*  THE BIJECTION: code is a bijection between exponent tuples and     *)
(*  {ps}-smooth positive numbers                                      *)
(* ----------------------------------------------------------------- *)

Theorem code_bijection_smooth : forall ps, Forall prime ps -> NoDup ps ->
  (* SURJECTIVE onto {ps}-smooth positives *)
  (forall m, 0 < m -> (forall q, prime q -> (q | m) -> In q ps) ->
     exists ks, length ps = length ks /\ code ps ks = m)
  /\
  (* INJECTIVE (PrimeFactorizationN.code_inj) *)
  (forall as_ bs, length ps = length as_ -> length ps = length bs ->
     code ps as_ = code ps bs -> as_ = bs).
Proof.
  intros ps Hpr Hnd; split.
  - apply code_surj; assumption.
  - intros as_ bs; apply code_inj; assumption.
Qed.

Print Assumptions code_bijection_smooth.

(* ================================================================= *)
(*  END PrimeFactorizationExists.v                                   *)
(*  code ps is SURJECTIVE onto the {ps}-smooth positive numbers        *)
(*  (factorization existence) and, with PrimeFactorizationN.code_inj,   *)
(*  a genuine BIJECTION exponent-tuples <-> {ps}-smooth positives.      *)
(*  This closes BOTH halves of the unique-factorization crux deferred   *)
(*  in PrimorialZeta.  ZERO Admitted; Closed under the global context. *)
(* ================================================================= *)
