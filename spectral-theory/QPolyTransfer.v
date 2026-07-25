(* ================================================================= *)
(*  QPolyTransfer.v                                                  *)
(*                                                                    *)
(*  TRANSFERRING ℤ[X] FACTS TO ℚ[X] (brick 6b, bridge + gcd).      *)
(*                                                                    *)
(*  Key bridge `qeval_ext_Z`: two ℚ polynomials that agree at every   *)
(*  integer point Z2Qc a agree everywhere (a ℚ polynomial is pinned   *)
(*  by its values on ℤ, since ℚ is infinite — via poly_roots_eval).   *)
(*  Consequences: divisibility transfers (`pdivides_emb`), X^m−1 ∣    *)
(*  X^n−1 in ℚ[X] (`qXn1_dvd`), the Bézout identity for X^a−1 over ℚ  *)
(*  (`qxn1_bezout`), and hence common divisors of X^i−1, X^j−1 divide *)
(*  X^{gcd(i,j)}−1 (`qdiv_gcd`).  AXIOM-FREE.                        *)
(* ================================================================= *)

From Stdlib Require Import QArith Qcanon List Lia Arith ZArith.
Import ListNotations.
Require Import IntPoly Xn1Bezout QPoly QPolyDiv QPolyGcd QPolyCoeffPIT QPolyPIT
        QPolyDeriv QPolyEmbed.
Open Scope Qc_scope.

(* ----------------------------------------------------------------- *)
(*  The transfer bridge                                              *)
(* ----------------------------------------------------------------- *)
Theorem qeval_ext_Z : forall p q,
  (forall a : Z, qeval p (Z2Qc a) = qeval q (Z2Qc a)) -> forall x, qeval p x = qeval q x.
Proof.
  intros p q H x.
  assert (Hzero : forall y, qeval (qsub p q) y = 0).
  { apply (poly_roots_eval (length (qsub p q)) (qsub p q) (qdegle_length _)
             (map (fun k => qnat k) (seq 0 (S (length (qsub p q)))))).
    - apply NoDup_map_inj;
        [ intros a b _ _ Hab; apply qnat_inj in Hab; lia | apply seq_NoDup ].
    - rewrite length_map, length_seq; lia.
    - intros pt Hpt; apply in_map_iff in Hpt; destruct Hpt as [k [Hk _]]; subst pt.
      change (qnat k) with (Z2Qc (Z.of_nat k)); rewrite qeval_sub, (H (Z.of_nat k)); ring. }
  specialize (Hzero x); rewrite qeval_sub in Hzero.
  replace (qeval p x) with (qeval p x - qeval q x + qeval q x) by ring.
  rewrite Hzero; ring.
Qed.

(* ----------------------------------------------------------------- *)
(*  Powers and X^a−1 under Z2Qc                                      *)
(* ----------------------------------------------------------------- *)
Lemma Z2Qc_pow : forall a i, Z2Qc (a ^ Z.of_nat i) = (Z2Qc a) ^ i.
Proof.
  intros a i; induction i as [|i IH].
  - change (Z.of_nat 0) with 0%Z; rewrite Z.pow_0_r, Z2Qc_1; reflexivity.
  - rewrite Znat.Nat2Z.inj_succ, Z.pow_succ_r by lia.
    rewrite Z2Qc_mul, IH; reflexivity.
Qed.

Lemma Z2Qc_sub1 : forall y, Z2Qc (y - 1) = Z2Qc y - 1.
Proof.
  intro y; replace (y - 1)%Z with (y + - (1))%Z by ring.
  rewrite Z2Qc_add, (Z2Qc_opp 1), Z2Qc_1; ring.
Qed.

Lemma Z2Qc_Xn1val : forall a i, Z2Qc (a ^ Z.of_nat i - 1) = (Z2Qc a) ^ i - 1.
Proof. intros a i; rewrite Z2Qc_sub1, Z2Qc_pow; reflexivity. Qed.

(* ----------------------------------------------------------------- *)
(*  Divisibility transfers                                           *)
(* ----------------------------------------------------------------- *)
Theorem pdivides_emb : forall p q, pdivides p q -> qdivides (emb p) (emb q).
Proof.
  intros p q [r Hr]; exists (emb r).
  cut (forall x, qeval (emb q) x = qeval (qmul (emb p) (emb r)) x).
  { intros Hc x; rewrite (Hc x), qeval_mul; reflexivity. }
  apply qeval_ext_Z; intro a.
  rewrite qeval_emb, qeval_mul, !qeval_emb, <- Z2Qc_mul, <- (Hr a); reflexivity.
Qed.

Theorem qXn1_dvd : forall i j, Nat.divide i j -> qdivides (qXn1 i) (qXn1 j).
Proof.
  intros i j Hij; rewrite <- (emb_Xn1 i), <- (emb_Xn1 j).
  apply pdivides_emb, Xn1_dvd, Hij.
Qed.

(* ----------------------------------------------------------------- *)
(*  Bézout for X^a−1 over ℚ, and common divisors → gcd               *)
(* ----------------------------------------------------------------- *)
Theorem qxn1_bezout : forall i j, exists u v : qpoly,
  forall x, qeval u x * (x ^ i - 1) + qeval v x * (x ^ j - 1) = x ^ (Nat.gcd i j) - 1.
Proof.
  intros i j; destruct (xn1_bezout i j) as [u [v Huv]].
  exists (emb u), (emb v); intro x.
  transitivity (qeval (qadd (qmul (emb u) (qXn1 i)) (qmul (emb v) (qXn1 j))) x).
  { rewrite qeval_add, !qeval_mul, !qeval_Xn1; ring. }
  transitivity (qeval (qXn1 (Nat.gcd i j)) x); [ | rewrite qeval_Xn1; ring ].
  apply qeval_ext_Z; intro a.
  rewrite qeval_add, !qeval_mul, !qeval_emb, !qeval_Xn1.
  rewrite <- !Z2Qc_Xn1val, <- !Z2Qc_mul, <- Z2Qc_add, (Huv a); reflexivity.
Qed.

Theorem qdiv_gcd : forall g i j,
  qdivides g (qXn1 i) -> qdivides g (qXn1 j) -> qdivides g (qXn1 (Nat.gcd i j)).
Proof.
  intros g i j [ri Hri] [rj Hrj]; destruct (qxn1_bezout i j) as [u [v Huv]].
  exists (qadd (qmul u ri) (qmul v rj)); intro x.
  specialize (Hri x); specialize (Hrj x); rewrite qeval_Xn1 in Hri, Hrj.
  rewrite qeval_Xn1, qeval_add, !qeval_mul, <- (Huv x), Hri, Hrj; ring.
Qed.

Print Assumptions qeval_ext_Z.
Print Assumptions qdiv_gcd.

(* ================================================================= *)
(*  END QPolyTransfer.v                                              *)
(*  ℤ[X] eval-identities transfer to ℚ[X] ∀-identities; hence         *)
(*  divisibility, X^m−1∣X^n−1, Bézout, and gcd of X^a−1 over ℚ.       *)
(*  Closed under the global context (axiom-free).                    *)
(* ================================================================= *)
