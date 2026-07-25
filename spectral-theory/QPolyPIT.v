(* ================================================================= *)
(*  QPolyPIT.v                                                       *)
(*                                                                    *)
(*  THE POLYNOMIAL IDENTITY THEOREM in ℚ[X] (functional form),      *)
(*  brick 5b:                                                        *)
(*                                                                    *)
(*    a polynomial of degree ≤ n that vanishes at more than n        *)
(*    distinct points is identically zero (as a function).          *)
(*                                                                    *)
(*  Proof: peel one root a with the degree-bounded factor theorem    *)
(*  (p = (X−a)·q, deg q ≤ n−1); the other roots are roots of q (the  *)
(*  field ℚ has no zero divisors), so q vanishes everywhere by        *)
(*  induction, hence so does p.  This is the classical root-counting  *)
(*  identity theorem.  AXIOM-FREE.                                   *)
(* ================================================================= *)

From Stdlib Require Import QArith Qcanon List Lia Arith.
Import ListNotations.
Require Import QPoly QPolyDiv QPolyDeg QPolyGcd QPolyRoot.
Open Scope Qc_scope.

(* factor theorem with a degree bound on the quotient *)
Lemma factor_theorem_deg : forall p a m, qeval p a = 0 -> qdegle p (S m) ->
  exists q, (forall x, qeval p x = (x - a) * qeval q x) /\ qdegle q m.
Proof.
  intros p a m Ha Hp.
  assert (Hg1 : qcoeff [Qcopp a; 1] 1 = 1) by reflexivity.
  assert (Hgdeg : qdegle [Qcopp a; 1] 1)
    by (intros i Hi; unfold qcoeff; apply nth_overflow; simpl; lia).
  assert (Hgx : forall y, qeval [Qcopp a; 1] y = y - a) by (intro y; simpl; ring).
  pose proof (qdivmod_spec [Qcopp a; 1] 1 1 ltac:(lia) qc_one_neq_zero Hg1 Hgdeg (S m) p Hp) as Hdm.
  destruct (qdivmod (S m) p [Qcopp a; 1] 1 1) as [q r] eqn:E.
  cbn [fst snd] in Hdm; destruct Hdm as [Hpqr [Hrdeg Hqdeg]].
  assert (Hr0 : qcoeff r 0 = 0).
  { pose proof (Hpqr a) as Hpa; rewrite Hgx in Hpa.
    replace (a - a) with (0 : Qc) in Hpa by ring.
    rewrite (qeval_const_of_degle0 r Hrdeg a), Ha in Hpa.
    rewrite Qcmult_0_r, Qcplus_0_l in Hpa; symmetry; exact Hpa. }
  exists q; split.
  - intro x; pose proof (Hpqr x) as Hpx; rewrite Hgx in Hpx.
    rewrite (qeval_const_of_degle0 r Hrdeg x), Hr0 in Hpx; rewrite Hpx; ring.
  - replace m with (S m - 1)%nat by lia; exact Hqdeg.
Qed.

Theorem poly_roots_eval : forall n p, qdegle p n ->
  forall pts, NoDup pts -> (n < length pts)%nat ->
  (forall a, In a pts -> qeval p a = 0) -> forall x, qeval p x = 0.
Proof.
  induction n as [|m IH]; intros p H pts Hnd Hlen Hpts x.
  - destruct pts as [|a0 rest]; [ simpl in Hlen; lia | ].
    rewrite (qeval_const_of_degle0 p H x), <- (qeval_const_of_degle0 p H a0).
    apply Hpts; left; reflexivity.
  - destruct pts as [|a rest]; [ simpl in Hlen; lia | ].
    apply NoDup_cons_iff in Hnd; destruct Hnd as [Hanr Hndr].
    destruct (factor_theorem_deg p a m (Hpts a (or_introl eq_refl)) H) as [q [Hpq Hqd]].
    assert (Hqrest : forall b, In b rest -> qeval q b = 0).
    { intros b Hbr.
      assert (Hba : b <> a) by (intro Heq; subst b; contradiction).
      pose proof (Hpts b (or_intror Hbr)) as Hpb; rewrite (Hpq b) in Hpb.
      apply Qcmult_integral in Hpb; destruct Hpb as [Hz | Hz]; [ exfalso | exact Hz ].
      apply Hba; transitivity (b - a + a); [ ring | rewrite Hz; ring ]. }
    assert (Hrl : (m < length rest)%nat) by (simpl in Hlen; lia).
    pose proof (IH q Hqd rest Hndr Hrl Hqrest) as Hq0.
    rewrite (Hpq x), (Hq0 x); ring.
Qed.

Print Assumptions poly_roots_eval.

(* ================================================================= *)
(*  END QPolyPIT.v                                                   *)
(*  A degree-≤n polynomial with more than n distinct roots is         *)
(*  identically zero (functional polynomial identity theorem).       *)
(*  Closed under the global context (axiom-free).                    *)
(* ================================================================= *)
