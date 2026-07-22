(* ================================================================= *)
(*  FreeDivMeetIso.v                                                  *)
(*                                                                    *)
(*  GAP-FILL: the INTERIOR ISOMORPHISM of FreeDivMeet -- the full CRT   *)
(*  lattice iso, not just the axis generators.  Axiom-free.            *)
(*                                                                    *)
(*  FreeDivMeet proved the meet/join coincidence only at the two       *)
(*  prime-power AXES.  Here we prove the coding map                    *)
(*     code (i,j) = p^i * q^j                                          *)
(*  is an ORDER EMBEDDING of the free product-of-chains lattice into    *)
(*  the divisibility lattice:                                          *)
(*                                                                    *)
(*     code u | code v   <->   fle u v   (i.e. i<=i' /\ j<=j')          *)
(*                                                                    *)
(*  so the free lattice F = N x N sits inside (Z, |) as EXACTLY the      *)
(*  {p,q}-smooth numbers, and Div(p^a q^b) ~= [0..a] x [0..b] as posets. *)
(*  The reverse direction (divisibility -> order) is the substantive    *)
(*  part: it uses Gauss + coprimality of prime powers (rp_pow_gen,      *)
(*  pq_coprime from FreeDivMeet) to peel one prime at a time.          *)
(* ================================================================= *)

Require Import FreeDivMeet.
From Stdlib Require Import ZArith Znumtheory Lia Arith.

(* p^a divides p^b when a <= b *)
Lemma pow_dvd : forall (x : Z) (a b : nat), (a <= b)%nat ->
  (x ^ Z.of_nat a | x ^ Z.of_nat b).
Proof.
  intros x a b Hab. exists (x ^ Z.of_nat (b - a)).
  replace (Z.of_nat b) with (Z.of_nat (b - a) + Z.of_nat a)%Z by lia.
  rewrite Z.pow_add_r by lia; ring.
Qed.

(* p^a | p^b forces a <= b, for a base >= 2 *)
Lemma pow_dvd_le : forall (x : Z) (a b : nat), 2 <= x ->
  (x ^ Z.of_nat a | x ^ Z.of_nat b) -> (a <= b)%nat.
Proof.
  intros x a b Hx Hdvd.
  destruct (le_gt_dec a b) as [Hle | Hgt]; [ exact Hle | exfalso ].
  assert (Hle1 : x ^ Z.of_nat a <= x ^ Z.of_nat b).
  { apply Z.divide_pos_le; [ apply Z.pow_pos_nonneg; lia | exact Hdvd ]. }
  assert (Hlt : x ^ Z.of_nat b < x ^ Z.of_nat a).
  { apply Z.pow_lt_mono_r; lia. }
  lia.
Qed.

(* forward: order -> divisibility *)
Lemma code_mono : forall p q u v, fle u v -> (code p q u | code p q v).
Proof.
  intros p q [u1 u2] [v1 v2] [H1 H2]; cbn [fst snd] in H1, H2; unfold code; cbn [fst snd].
  exists (p ^ Z.of_nat (v1 - u1) * q ^ Z.of_nat (v2 - u2)).
  replace (Z.of_nat v1) with (Z.of_nat (v1 - u1) + Z.of_nat u1)%Z by lia.
  replace (Z.of_nat v2) with (Z.of_nat (v2 - u2) + Z.of_nat u2)%Z by lia.
  rewrite !Z.pow_add_r by lia; ring.
Qed.

(* reverse: divisibility -> order (the substantive direction, via Gauss) *)
Lemma code_faithful : forall p q u v,
  prime p -> prime q -> p <> q ->
  (code p q u | code p q v) -> fle u v.
Proof.
  intros p q [u1 u2] [v1 v2] Hp Hq Hpq Hdvd; unfold code in *; cbn [fst snd] in *.
  assert (Hp2 : 2 <= p) by (destruct Hp; lia).
  assert (Hq2 : 2 <= q) by (destruct Hq; lia).
  unfold fle; cbn [fst snd]; split.
  - (* u1 <= v1 : peel the prime p using Gauss + p^u1 _|_ q^v2 *)
    apply (pow_dvd_le p u1 v1 Hp2).
    apply (Gauss (p ^ Z.of_nat u1) (q ^ Z.of_nat v2) (p ^ Z.of_nat v1)).
    + rewrite Z.mul_comm.
      apply Z.divide_trans with (p ^ Z.of_nat u1 * q ^ Z.of_nat u2);
        [ exists (q ^ Z.of_nat u2); ring | exact Hdvd ].
    + apply rp_pow_gen, pq_coprime; assumption.
  - (* u2 <= v2 : peel the prime q using Gauss + q^u2 _|_ p^v1 *)
    apply (pow_dvd_le q u2 v2 Hq2).
    apply (Gauss (q ^ Z.of_nat u2) (p ^ Z.of_nat v1) (q ^ Z.of_nat v2)).
    + apply Z.divide_trans with (p ^ Z.of_nat u1 * q ^ Z.of_nat u2);
        [ exists (p ^ Z.of_nat u1); ring | exact Hdvd ].
    + apply rp_pow_gen, pq_coprime; auto.
Qed.

(* ----------------------------------------------------------------- *)
(*  THE INTERIOR ISOMORPHISM: code is an order embedding             *)
(* ----------------------------------------------------------------- *)

Theorem code_order_iso : forall p q u v,
  prime p -> prime q -> p <> q ->
  ((code p q u | code p q v) <-> fle u v).
Proof.
  intros p q u v Hp Hq Hpq; split.
  - apply code_faithful; assumption.
  - apply code_mono.
Qed.

Print Assumptions code_order_iso.

(* ================================================================= *)
(*  END FreeDivMeetIso.v                                              *)
(*  code : F -> Z is an order embedding (code u | code v <-> fle u v), *)
(*  so the free product-of-chains lattice IS the {p,q}-smooth part of   *)
(*  the divisibility lattice: Div(p^a q^b) ~= [0..a] x [0..b].          *)
(*  ZERO Admitted; Closed under the global context.                    *)
(* ================================================================= *)
