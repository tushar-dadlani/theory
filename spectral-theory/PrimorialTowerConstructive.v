(* ================================================================= *)
(*  PrimorialTowerConstructive.v                                    *)
(*                                                                    *)
(*  Movement IV of the ζ arc — the PRIMORIAL EULER TOWER → ζ(2),      *)
(*  ported to Rocq's axiom-free constructive real.                    *)
(*                                                                    *)
(*  `cvQ_tower` is the constructive analogue of the classical         *)
(*  `PrimorialZeta.tower_is_zeta2`: a MONOTONE rational rung sequence  *)
(*  whose rungs are each ≤ ζ(2) and eventually dominate the ζ(2)       *)
(*  partial sums converges to ζ(2).  The concrete tower               *)
(*  `∏_{p ≤ n} 1/(1−p⁻²)` (the Euler factor product over a growing    *)
(*  prime set) is then shown to satisfy the three hypotheses, so it   *)
(*  converges to ζ(2) (`primorial_tower_zeta2`).  AXIOM-FREE.         *)
(* ================================================================= *)

From Stdlib Require Import Reals.Cauchy.ConstructiveCauchyReals
        Reals.Cauchy.ConstructiveCauchyRealsMult
        Reals.Cauchy.ConstructiveCauchyAbs
        Reals.Cauchy.ConstructiveRcomplete.
From Stdlib Require Import ZArith QArith Qabs Qround Lqa Lia List Arith Znumtheory.
Import ListNotations.
Require Import PrimonGas EulerReindex EulerProductZeta
        CRealCv ZetaConstructive ZetaSquareConstructive ZetaMasterConstructive
        EulerProductConstructive.
Local Open Scope Q_scope.

(* ================================================================= *)
(*  the constructive tower principle (port of tower_is_zeta2)         *)
(* ================================================================= *)
Lemma cvQ_tower : forall (E : nat -> Q),
  (forall m n, (m <= n)%nat -> E m <= E n) ->
  (forall n, (inject_Q (E n) <= zeta2c)%CReal) ->
  (forall N, exists n, (zpartQ N <= E n)%Q) ->
  cvQ E zeta2c.
Proof.
  intros E Hmono Hub Hdom p.
  destruct (zeta2c_cv p) as [M HM].
  destruct (Hdom M) as [n0 Hn0].
  exists n0; intros n Hn.
  apply CReal_abs_le; split.
  - apply CReal_le_trans with (inject_Q (zpartQ M) - zeta2c)%CReal.
    + apply abs_le_neg; exact (HM M (Nat.le_refl M)).
    + apply CReal_plus_le_compat; [ | apply CRealLe_refl ].
      apply inject_Q_le, Qle_trans with (E n0); [ exact Hn0 | apply Hmono; lia ].
  - apply CReal_le_trans with (inject_Q 0).
    + assert (E0 : (inject_Q 0 == zeta2c - zeta2c)%CReal) by ring; rewrite E0.
      apply CReal_plus_le_compat; [ apply Hub | apply CRealLe_refl ].
    + apply inject_Q_le; unfold Qle; simpl; lia.
Qed.

(* ================================================================= *)
(*  ℚ product helpers + monotonicity of the Euler factor product      *)
(* ================================================================= *)
Lemma qprod_app : forall l1 l2, qprod (l1 ++ l2) == qprod l1 * qprod l2.
Proof.
  induction l1 as [|a l1 IH]; intro l2; [ cbn; ring | ].
  cbn [app qprod]; rewrite IH; ring.
Qed.

Lemma qprod_ge1 : forall l, (forall x, In x l -> 1 <= x) -> 1 <= qprod l.
Proof.
  induction l as [|a l IH]; intro H; [ cbn; lra | ].
  cbn [qprod]; assert (1 <= a) by (apply H; left; auto).
  assert (1 <= qprod l) by (apply IH; intros x Hx; apply H; right; auto); nra.
Qed.

Lemma efacQ_ge1 : forall p, prime p -> 1 <= efacQ p.
Proof.
  intros p Hp; unfold efacQ.
  assert (H1 : / 1 == 1) by reflexivity; rewrite <- H1.
  apply Qinv_le; [ pose proof (fug_lt1 p Hp); lra | pose proof (fug_pos p Hp); lra ].
Qed.

Lemma ZfactorQ_app : forall a b, ZfactorQ (a ++ b) == ZfactorQ a * ZfactorQ b.
Proof. intros a b; unfold ZfactorQ; rewrite map_app, qprod_app; reflexivity. Qed.

Lemma ZfactorQ_ge1 : forall ps, Forall prime ps -> 1 <= ZfactorQ ps.
Proof.
  intros ps Hps; unfold ZfactorQ; apply qprod_ge1.
  intros x Hx; apply in_map_iff in Hx; destruct Hx as [p [Hp Hin]]; subst x.
  apply efacQ_ge1; rewrite Forall_forall in Hps; apply Hps; exact Hin.
Qed.

Lemma primes_upto_prefix : forall a b, (a <= b)%nat ->
  exists r, primes_upto b = primes_upto a ++ r /\ Forall prime r.
Proof.
  intros a b Hab; unfold primes_upto.
  replace (seq 0 (S b)) with (seq 0 (S a) ++ seq (S a) (S b - S a))%list.
  2:{ symmetry; replace (S b) with (S a + (S b - S a))%nat at 1 by lia; rewrite seq_app; reflexivity. }
  rewrite map_app, filter_app; eexists; split; [ reflexivity | ].
  rewrite Forall_forall; intros x Hx; apply filter_In in Hx; destruct Hx as [_ Hpx].
  destruct (prime_dec x); [ exact p | discriminate ].
Qed.

Lemma ZfactorQ_primes_mono : forall a b, (a <= b)%nat ->
  ZfactorQ (primes_upto (S a)) <= ZfactorQ (primes_upto (S b)).
Proof.
  intros a b Hab; destruct (primes_upto_prefix (S a) (S b) ltac:(lia)) as [r [Hr Hpr]].
  rewrite Hr, ZfactorQ_app.
  assert (1 <= ZfactorQ r) by (apply ZfactorQ_ge1; exact Hpr).
  assert (0 <= ZfactorQ (primes_upto (S a))) by (apply ZfactorQ_nonneg, primes_upto_Forall).
  nra.
Qed.

(* ================================================================= *)
(*  the concrete primorial Euler tower converges to ζ(2)             *)
(* ================================================================= *)
Theorem primorial_tower_zeta2 :
  cvQ (fun n => ZfactorQ (primes_upto (S n))) zeta2c.
Proof.
  apply cvQ_tower.
  - intros m n Hmn; apply ZfactorQ_primes_mono; exact Hmn.
  - intro n; apply ZfactorQ_le_zeta2c; [ apply primes_upto_Forall | apply primes_upto_nodup ].
  - intro N; exists N; apply zpartQ_le_ZfactorQ_primes.
Qed.

Print Assumptions cvQ_tower.
Print Assumptions primorial_tower_zeta2.

(* ================================================================= *)
(*  END PrimorialTowerConstructive.v                                *)
(*  The primorial Euler tower → ζ(2), axiom-free (movement IV):       *)
(*  the abstract tower principle `cvQ_tower` and its concrete         *)
(*  instance.  Closed under the global context.                      *)
(* ================================================================= *)
