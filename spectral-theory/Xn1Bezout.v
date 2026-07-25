(* ================================================================= *)
(*  Xn1Bezout.v                                                      *)
(*                                                                    *)
(*  A BÉZOUT IDENTITY FOR X^a − 1 in ℤ[X]:                          *)
(*                                                                    *)
(*      ∃ u v ∈ ℤ[X],                                               *)
(*        u·(X^a − 1) + v·(X^b − 1) = X^{gcd(a,b)} − 1.              *)
(*                                                                    *)
(*  Proved by the Euclidean algorithm on the exponents, mirrored on  *)
(*  the polynomials via                                              *)
(*      X^b − 1 = X^{b mod m}·(X^m − 1)·(1+X^m+…) + (X^{b mod m} − 1),*)
(*  i.e. one division step X^b = X^{m·(b/m)}·X^{b mod m}.  No ℚ[X]    *)
(*  machinery — everything stays in ℤ[X].  This gives the greatest   *)
(*  common "X^d − 1" as an integer combination, the key to the       *)
(*  coprimality of the cyclotomic factors behind ∏_{d|n}Φ_d = X^n−1. *)
(*  AXIOM-FREE.                                                       *)
(* ================================================================= *)

From Stdlib Require Import ZArith List Lia Arith.
Import ListNotations.
Require Import IntPoly PolyDiv.
Open Scope Z_scope.

Theorem xn1_bezout : forall a b, exists u v : poly,
  forall x, eval u x * (x ^ Z.of_nat a - 1) + eval v x * (x ^ Z.of_nat b - 1)
            = x ^ Z.of_nat (Nat.gcd a b) - 1.
Proof.
  intro a; induction a as [a IH] using lt_wf_ind; intro b.
  destruct a as [|a'].
  - (* gcd 0 b = b : take u = 0, v = 1 *)
    exists (pconst 0), (pconst 1); intro x.
    rewrite !eval_const; change (Nat.gcd 0 b) with b; ring.
  - remember (S a') as m eqn:Em.
    assert (Hm : (0 < m)%nat) by lia.
    set (r := (b mod m)%nat).
    set (q := (b / m)%nat).
    assert (Hr : (r < m)%nat) by (unfold r; apply Nat.mod_upper_bound; lia).
    assert (Hb : b = (m * q + r)%nat) by (unfold q, r; exact (Nat.div_mod_eq b m)).
    destruct (IH r ltac:(lia) m) as [u' [v' Huv]].
    exists (psub v' (pmul u' (pmul (pmonom r) (geo m q)))), u'.
    intro x.
    assert (Hgcd : Nat.gcd m b = Nat.gcd r m) by (unfold r; rewrite Em; reflexivity).
    rewrite Hgcd.
    (* one Euclidean division step, on the polynomials *)
    assert (Hbrel : x ^ Z.of_nat b - 1
                    = x ^ Z.of_nat r * eval (geo m q) x * (x ^ Z.of_nat m - 1)
                      + (x ^ Z.of_nat r - 1)).
    { pose proof (geo_telescope m q x) as Hgt.
      assert (Hxb : x ^ Z.of_nat b = x ^ Z.of_nat (m * q) * x ^ Z.of_nat r).
      { rewrite <- Z.pow_add_r by lia; f_equal; rewrite <- Nat2Z.inj_add; f_equal; exact Hb. }
      rewrite Hxb.
      assert (Hxmq : x ^ Z.of_nat (m * q) = (x ^ Z.of_nat m - 1) * eval (geo m q) x + 1) by lia.
      rewrite Hxmq; ring. }
    rewrite Hbrel, eval_sub, !eval_mul, eval_monom, <- Huv; ring.
Qed.

Print Assumptions xn1_bezout.

(* ================================================================= *)
(*  END Xn1Bezout.v                                                  *)
(*  u·(X^a−1) + v·(X^b−1) = X^{gcd(a,b)}−1 with integer-polynomial    *)
(*  u, v, by the Euclidean algorithm on exponents.  Foundation for   *)
(*  the coprimality of cyclotomic factors.  Closed under the global  *)
(*  context (axiom-free).                                            *)
(* ================================================================= *)
