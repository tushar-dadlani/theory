(* ================================================================= *)
(*  CRealCharPos.v  --  positivity of f = 1 * chi for a REAL chi.     *)
(*                                                                    *)
(*  This is the arithmetic half of the elementary (hyperbola) proof   *)
(*  of L(1,chi) <> 0 for a real character -- the case where the        *)
(*  3-4-1 argument degenerates because chi^2 = chi_0.                  *)
(*                                                                    *)
(*  The whole point is that f is nonnegative and is at least 1 on      *)
(*  squares.  Then sum_{n<=x} f(n)/sqrt n diverges (it dominates       *)
(*  sum_{m<=sqrt x} 1/m), while the hyperbola method evaluates the     *)
(*  same sum as 2 sqrt x L(1,chi) + O(1), which is bounded if          *)
(*  L(1,chi) = 0.  Contradiction.                                      *)
(*                                                                    *)
(*  Everything here is Z-valued: CRealChar.chz is the {-1,0,1} avatar  *)
(*  of chi, so the repo's Dirichlet convolution machinery applies.     *)
(*                                                                    *)
(*    f (q^k) = sum_{j=0}^{k} chi(q)^j                                 *)
(*                                                                    *)
(*  and that geometric sum is 1, k+1, or 1-or-0-by-parity according    *)
(*  as chi(q) is 0, 1, or -1.  Nonnegative in every case, and at       *)
(*  least 1 when k is even.  mult_ind lifts both to all n.             *)
(* ================================================================= *)

From Stdlib Require Import ZArith Znumtheory Arith Lia List.
Require Import ComplexField Cmodulus RootsOfUnity ZmodOrder ZmodPStar
        DirichletModP HopfGroupTensor Totient DirichletConv DirichletMult
        DirichletDivisor DirichletPPow DirichletPeel DirichletVonMangoldtGen
        CRealChar.
Import ListNotations.
Open Scope Z_scope.

(* ----------------------------------------------------------------- *)
(*  Part A -- the three geometric sums, over Z, no characters yet.     *)
(* ----------------------------------------------------------------- *)

Lemma pow_m1 : forall j, (-1) ^ Z.of_nat j = (if Nat.even j then 1 else -1).
Proof.
  induction j as [| j IH]; [ reflexivity | ].
  rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. rewrite IH.
  rewrite Nat.even_succ, <- Nat.negb_even.
  destruct (Nat.even j); cbn; ring.
Qed.

Lemma gsum_0 : forall k, sumf (seq 0 (S k)) (fun j => 0 ^ Z.of_nat j) = 1.
Proof.
  induction k as [| k IH]; [ reflexivity | ].
  rewrite (sumf_seq_last (S k)), IH, Z.pow_0_l by lia. ring.
Qed.

Lemma gsum_1 : forall k, sumf (seq 0 (S k)) (fun j => 1 ^ Z.of_nat j) = Z.of_nat (S k).
Proof.
  induction k as [| k IH]; [ reflexivity | ].
  rewrite (sumf_seq_last (S k)), IH, Z.pow_1_l by lia. lia.
Qed.

Lemma gsum_m1 : forall k,
  sumf (seq 0 (S k)) (fun j => (-1) ^ Z.of_nat j) = (if Nat.even k then 1 else 0).
Proof.
  induction k as [| k IH]; [ reflexivity | ].
  rewrite (sumf_seq_last (S k)), IH, pow_m1.
  rewrite Nat.even_succ, <- Nat.negb_even.
  destruct (Nat.even k); cbn; ring.
Qed.

Section RealCharPos.

Variable p g A : nat.
Hypothesis Hp : prime (Z.of_nat p).
Hypothesis Hg : (1 <= g <= p - 1)%nat.
Hypothesis Hord : ord p g = (p - 1)%nat.
Hypothesis Hreal : forall n, Cconj (dchar p g A n) = dchar p g A n.

Notation ch := (chz p g A).
Notation f  := (fchi p g A).

Lemma fmult : multiplicative f.
Proof. exact (fchi_mult p g A Hp Hg Hord Hreal). Qed.

(* ----------------------------------------------------------------- *)
(*  Part B -- chi is completely multiplicative on prime powers.        *)
(* ----------------------------------------------------------------- *)

Lemma chz_ppow : forall q j, ch (q ^ j)%nat = (ch q) ^ Z.of_nat j.
Proof.
  intros q j. induction j as [| j IH].
  - change (q ^ 0)%nat with 1%nat.
    rewrite (chz_one p g A Hp Hg Hord Hreal).
    change (Z.of_nat 0) with 0. rewrite Z.pow_0_r. reflexivity.
  - change (q ^ S j)%nat with (q * q ^ j)%nat.
    rewrite (chz_mul p g A Hp Hg Hord Hreal q (q ^ j)%nat), IH.
    rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. reflexivity.
Qed.

(* ----------------------------------------------------------------- *)
(*  Part C -- f as a divisor sum, and its value at a prime power.      *)
(* ----------------------------------------------------------------- *)

Lemma fchi_div_sum : forall n, (1 <= n)%nat -> f n = sumf (divisors n) ch.
Proof.
  intros n Hn. unfold fchi.
  rewrite (dconv_as_div (chz p g A) done n Hn).
  apply sumf_ext. intros d _. unfold done. ring.
Qed.

Theorem fchi_ppow : forall q k, prime (Z.of_nat q) ->
  f (q ^ k)%nat = sumf (seq 0 (S k)) (fun j => (ch q) ^ Z.of_nat j).
Proof.
  intros q k Hq.
  rewrite (fchi_div_sum (q ^ k)%nat (ppow_pos q k Hq)).
  rewrite (divisors_ppow_sum q k ch Hq).
  apply sumf_ext. intros j _. apply chz_ppow.
Qed.

(* ----------------------------------------------------------------- *)
(*  Part D -- nonnegativity, and >= 1 at even exponents.               *)
(* ----------------------------------------------------------------- *)

Lemma fchi_ppow_nonneg : forall q k, prime (Z.of_nat q) -> 0 <= f (q ^ k)%nat.
Proof.
  intros q k Hq. rewrite (fchi_ppow q k Hq).
  destruct (chz_values p g A q) as [E | [E | E]]; rewrite E.
  - rewrite gsum_0; lia.
  - rewrite gsum_1; lia.
  - rewrite gsum_m1. destruct (Nat.even k); lia.
Qed.

Lemma fchi_ppow_even_ge1 : forall q k, prime (Z.of_nat q) ->
  Nat.even k = true -> 1 <= f (q ^ k)%nat.
Proof.
  intros q k Hq He. rewrite (fchi_ppow q k Hq).
  destruct (chz_values p g A q) as [E | [E | E]]; rewrite E.
  - rewrite gsum_0; lia.
  - rewrite gsum_1; lia.
  - rewrite gsum_m1, He; lia.
Qed.

(* ----------------------------------------------------------------- *)
(*  Part E -- lift to all n by peeling prime powers.                   *)
(* ----------------------------------------------------------------- *)

Theorem fchi_nonneg : forall n, (1 <= n)%nat -> 0 <= f n.
Proof.
  apply (mult_ind (fun n => 0 <= f n)).
  - rewrite (proj1 fmult). lia.
  - intros q v m Hq Hqm Hv Hm IH.
    assert (Hgc : Nat.gcd (q ^ v) m = 1%nat) by (apply gcd_ppow_coprime; assumption).
    rewrite (proj2 fmult (q ^ v)%nat m (ppow_pos q v Hq) Hm Hgc).
    apply Z.mul_nonneg_nonneg; [ apply fchi_ppow_nonneg; exact Hq | exact IH ].
Qed.

Theorem fchi_sq_ge1 : forall n, (1 <= n)%nat -> 1 <= f (n * n)%nat.
Proof.
  apply (mult_ind (fun n => 1 <= f (n * n)%nat)).
  - change (1 * 1)%nat with 1%nat. rewrite (proj1 fmult). lia.
  - intros q v m Hq Hqm Hv Hm IH.
    assert (Hsplit : (q ^ v * m * (q ^ v * m))%nat = (q ^ (v + v) * (m * m))%nat)
      by (rewrite Nat.pow_add_r; ring).
    rewrite Hsplit.
    assert (Hmm : (1 <= m * m)%nat) by nia.
    assert (Hqmm : ~ Nat.divide q (m * m)).
    { intro Hd. destruct (prime_mult_nat q m m Hq Hd); contradiction. }
    assert (Hgc : Nat.gcd (q ^ (v + v)) (m * m) = 1%nat)
      by (apply gcd_ppow_coprime; assumption).
    rewrite (proj2 fmult (q ^ (v + v))%nat (m * m)%nat
               (ppow_pos q (v + v) Hq) Hmm Hgc).
    assert (He : Nat.even (v + v)%nat = true)
      by (apply Nat.even_spec; exists v; lia).
    apply Z.le_trans with (1 * 1); [ lia | ].
    apply Z.mul_le_mono_nonneg;
      [ lia | apply fchi_ppow_even_ge1; assumption | lia | exact IH ].
Qed.

End RealCharPos.

Print Assumptions fchi_nonneg.
Print Assumptions fchi_sq_ge1.

(* ================================================================= *)
(*  END CRealCharPos.v                                                *)
(* ================================================================= *)
