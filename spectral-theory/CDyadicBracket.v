(* ================================================================= *)
(*  CDyadicBracket.v  —  bracketing a real between consecutive        *)
(*  powers of two.                                                    *)
(*                                                                    *)
(*    dyadic_bracket : 1 <= x  ==>  exists K, x <= 2^K < 2x.          *)
(*                                                                    *)
(*  Pow_x_infinity gives only the UPPER side -- 2^n eventually       *)
(*  exceeds x -- and that is all the repo has ever needed            *)
(*  (CDyadicSum.dyadic_sum_bound, CPeelBound).  A minimum-modulus     *)
(*  split needs both sides at once: the near/far cut has to be a      *)
(*  power of two, because the two dyadic sum bounds are stated at     *)
(*  powers of two, AND it has to sit within a bounded factor of the   *)
(*  circle radius, because the near factors are divided by it.        *)
(*                                                                    *)
(*  The least such K is what does it.  least_pow2 finds it by         *)
(*  induction on the upper witness, using Rle_dec at each level --    *)
(*  monotonicity of 2^n is what makes the induction go through, since *)
(*  failing at N then rules out every j <= N at once.  Minimality      *)
(*  gives 2^(K-1) < x, hence 2^K < 2x; K = 0 is the x <= 1 boundary.  *)
(*  Axiom-clean.                                                      *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Open Scope R_scope.

Lemma pow2_mono : forall m n : nat, (m <= n)%nat -> 2 ^ m <= 2 ^ n.
Proof.
  intros m n H. induction H as [| n H IH]; [ lra | ].
  cbn [pow]. pose proof (pow_le 2 m ltac:(lra)). lra.
Qed.

(* the LEAST power of two above x, given any one *)
Lemma least_pow2 : forall (x : R) (N : nat), x <= 2 ^ N ->
  exists K, x <= 2 ^ K /\ forall j, (j < K)%nat -> 2 ^ j < x.
Proof.
  intros x N. induction N as [| N IH]; intro HN.
  - exists 0%nat. split; [ exact HN | intros j Hj; lia ].
  - destruct (Rle_dec x (2 ^ N)) as [Hy | Hn]; [ apply IH; exact Hy | ].
    exists (S N). split; [ exact HN | ].
    intros j Hj.
    assert (Hjn : (j <= N)%nat) by lia.
    pose proof (pow2_mono j N Hjn). lra.
Qed.

Theorem dyadic_bracket : forall x, 1 <= x ->
  exists K, x <= 2 ^ K /\ 2 ^ K < 2 * x.
Proof.
  intros x Hx.
  assert (Habs2 : Rabs 2 > 1) by (rewrite Rabs_pos_eq; lra).
  destruct (Pow_x_infinity 2 Habs2 x) as [N HN].
  pose proof (HN N (le_n N)) as HNn.
  rewrite Rabs_pos_eq in HNn by (apply pow_le; lra).
  destruct (least_pow2 x N ltac:(lra)) as [K [HK Hmin]].
  exists K. split; [ exact HK | ].
  destruct K as [| K']; [ cbn [pow]; lra | ].
  pose proof (Hmin K' ltac:(lia)) as H. cbn [pow]. lra.
Qed.

Print Assumptions dyadic_bracket.
