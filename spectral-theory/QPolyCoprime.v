(* ================================================================= *)
(*  QPolyCoprime.v                                                   *)
(*                                                                    *)
(*  COPRIMALITY IN ℚ[X] AND "PRODUCT OF COPRIMES DIVIDES" (brick 4). *)
(*                                                                    *)
(*  `qcopr f g` : every common divisor of f and g is a nonzero       *)
(*  constant.  From the extended Euclid output (a common divisor h    *)
(*  with u·f + v·g = h), coprimality forces h constant, giving a       *)
(*  Bézout identity  u·f + v·g = 1  after scaling.  Hence             *)
(*                                                                    *)
(*      qcopr p q → p | M → q | M → (p·q) | M,                       *)
(*                                                                    *)
(*  the mechanism by which ∏_{d|n} Φ_d divides X^n−1 once the Φ_d are  *)
(*  shown pairwise coprime.  AXIOM-FREE.                             *)
(* ================================================================= *)

From Stdlib Require Import QArith Qcanon List Lia Arith.
Import ListNotations.
Require Import QPoly QPolyDiv QPolyDeg QPolyGcd.
Open Scope Qc_scope.

(* every common divisor of f and g is a nonzero constant *)
Definition qcopr (f g : qpoly) : Prop :=
  forall d, qdivides d f -> qdivides d g ->
    exists c, c <> 0 /\ (forall x, qeval d x = c).

(* coprimality yields a Bézout identity equal to 1 *)
Lemma coprime_bezout : forall f g, qcopr f g ->
  exists u v, forall x, qeval u x * qeval f x + qeval v x * qeval g x = 1.
Proof.
  intros f g Hco.
  pose proof (qeuclid_spec (S (qdeg g)) f g ltac:(lia)) as Hspec.
  destruct (qeuclid (S (qdeg g)) f g) as [[h u] v] eqn:E.
  destruct Hspec as [Hbez [Hhf Hhg]].
  destruct (Hco h Hhf Hhg) as [c [Hcnz Hhc]].
  exists (qscale (/ c) u), (qscale (/ c) v); intro x.
  rewrite !qeval_scale; specialize (Hbez x); specialize (Hhc x).
  transitivity (/ c * (qeval u x * qeval f x + qeval v x * qeval g x)); [ ring | ].
  rewrite Hbez, Hhc; field; exact Hcnz.
Qed.

(* coprime factors each dividing M : their product divides M *)
Theorem qcopr_product_divides : forall p q M,
  qcopr p q -> qdivides p M -> qdivides q M -> qdivides (qmul p q) M.
Proof.
  intros p q M Hco Hp Hq.
  destruct Hp as [m2 Hm2]; destruct Hq as [m1 Hm1].
  destruct (coprime_bezout p q Hco) as [u [v Huv]].
  exists (qadd (qmul u m1) (qmul v m2)); intro x.
  rewrite (qeval_mul p q), qeval_add, (qeval_mul u m1), (qeval_mul v m2).
  specialize (Huv x); specialize (Hm1 x); specialize (Hm2 x).
  replace (qeval p x * qeval q x * (qeval u x * qeval m1 x + qeval v x * qeval m2 x))
    with (qeval u x * qeval p x * (qeval q x * qeval m1 x)
          + qeval v x * qeval q x * (qeval p x * qeval m2 x)) by ring.
  rewrite <- Hm1, <- Hm2.
  transitivity (qeval M x * (qeval u x * qeval p x + qeval v x * qeval q x));
    [ rewrite Huv; ring | ring ].
Qed.

Print Assumptions qcopr_product_divides.

(* ================================================================= *)
(*  END QPolyCoprime.v                                               *)
(*  Coprimality (every common divisor is a nonzero constant) yields   *)
(*  Bézout = 1, hence coprime factors dividing M have their product   *)
(*  divide M.  Closed under the global context (axiom-free).         *)
(* ================================================================= *)
