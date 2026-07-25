(* ================================================================= *)
(*  QPolyRoot.v                                                      *)
(*                                                                    *)
(*  THE FACTOR THEOREM IN ℚ[X] (brick 5a, root theory).            *)
(*                                                                    *)
(*      qeval p a = 0  →  ∃ q, ∀x, qeval p x = (x − a)·qeval q x.    *)
(*                                                                    *)
(*  Divide p by the monic X − a (via QPolyDiv.qdivmod): the remainder *)
(*  is a constant equal to p(a) = 0, so the division is exact.  This  *)
(*  is the first step of the polynomial identity theorem (a nonzero   *)
(*  polynomial has finitely many roots), which the derivative-based   *)
(*  squarefreeness of X^n−1 needs.  AXIOM-FREE.                     *)
(* ================================================================= *)

From Stdlib Require Import QArith Qcanon List Lia Arith.
Import ListNotations.
Require Import QPoly QPolyDiv QPolyDeg QPolyGcd.
Open Scope Qc_scope.

Lemma qc_one_neq_zero : (1 : Qc) <> 0.
Proof. intro H; inversion H. Qed.

(* a polynomial of degree bound 0 is its constant coefficient *)
Lemma qeval_const_of_degle0 : forall p, qdegle p 0 -> forall x, qeval p x = qcoeff p 0.
Proof.
  intros p H x; destruct p as [|c p'].
  - reflexivity.
  - assert (Hp' : forall y, qeval p' y = 0).
    { intro y; apply qeval_all_zero; intro i.
      change (qcoeff p' i) with (qcoeff (c :: p') (S i)); apply H; lia. }
    simpl; rewrite Hp'; unfold qcoeff; simpl; ring.
Qed.

Theorem factor_theorem : forall p a, qeval p a = 0 ->
  exists q, forall x, qeval p x = (x - a) * qeval q x.
Proof.
  intros p a Ha.
  assert (Hg1 : qcoeff [Qcopp a; 1] 1 = 1) by reflexivity.
  assert (Hgdeg : qdegle [Qcopp a; 1] 1)
    by (intros i Hi; unfold qcoeff; apply nth_overflow; simpl; lia).
  assert (Hgx : forall y, qeval [Qcopp a; 1] y = y - a) by (intro y; simpl; ring).
  pose proof (qdivmod_spec [Qcopp a; 1] 1 1 ltac:(lia) qc_one_neq_zero
                Hg1 Hgdeg (length p) p (qdegle_length p)) as Hdm.
  destruct (qdivmod (length p) p [Qcopp a; 1] 1 1) as [q r] eqn:E.
  cbn [fst snd] in Hdm; destruct Hdm as [Hpqr [Hrdeg _]].
  assert (Hr0 : qcoeff r 0 = 0).
  { pose proof (Hpqr a) as Hpa; rewrite Hgx in Hpa.
    replace (a - a) with (0 : Qc) in Hpa by ring.
    rewrite (qeval_const_of_degle0 r Hrdeg a), Ha in Hpa.
    rewrite Qcmult_0_r, Qcplus_0_l in Hpa; symmetry; exact Hpa. }
  exists q; intro x.
  pose proof (Hpqr x) as Hpx; rewrite Hgx in Hpx.
  rewrite (qeval_const_of_degle0 r Hrdeg x), Hr0 in Hpx.
  rewrite Hpx; ring.
Qed.

Print Assumptions factor_theorem.

(* ================================================================= *)
(*  END QPolyRoot.v                                                  *)
(*  Factor theorem in ℚ[X]: a root a yields the factor (X − a).      *)
(*  First step of the polynomial identity theorem.  Closed under the  *)
(*  global context (axiom-free).                                     *)
(* ================================================================= *)
