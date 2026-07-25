(* ================================================================= *)
(*  Xn1Gcd.v                                                         *)
(*                                                                    *)
(*  COMMON DIVISORS OF X^a−1 AND X^b−1 DIVIDE X^{gcd(a,b)}−1.        *)
(*                                                                    *)
(*      pdivides g (X^a−1) → pdivides g (X^b−1)                     *)
(*        → pdivides g (X^{gcd(a,b)}−1).                            *)
(*                                                                    *)
(*  Immediate from the Bézout identity Xn1Bezout.xn1_bezout: writing  *)
(*  X^{gcd}−1 = u·(X^a−1) + v·(X^b−1), any g dividing both terms on   *)
(*  the right divides the left.  This is the first step toward the    *)
(*  coprimality of the cyclotomic factors: gcd(Φ_i,Φ_j) divides       *)
(*  X^{gcd(i,j)}−1.  AXIOM-FREE.                                     *)
(* ================================================================= *)

From Stdlib Require Import ZArith List Lia Arith.
Import ListNotations.
Require Import IntPoly PolyDiv Xn1Bezout.
Open Scope Z_scope.

Theorem pdiv_gcd : forall g a b,
  pdivides g (Xn1 a) -> pdivides g (Xn1 b) -> pdivides g (Xn1 (Nat.gcd a b)).
Proof.
  intros g a b [ra Hra] [rb Hrb].
  destruct (xn1_bezout a b) as [u [v Huv]].
  exists (padd (pmul u ra) (pmul v rb)); intro x.
  specialize (Hra x); specialize (Hrb x); rewrite eval_Xn1 in Hra, Hrb.
  rewrite eval_Xn1, eval_add, !eval_mul, <- Huv, Hra, Hrb; ring.
Qed.

Print Assumptions pdiv_gcd.

(* ================================================================= *)
(*  END Xn1Gcd.v                                                     *)
(*  Common divisors of X^a−1 and X^b−1 divide X^{gcd(a,b)}−1.        *)
(*  Closed under the global context (axiom-free).                    *)
(* ================================================================= *)
