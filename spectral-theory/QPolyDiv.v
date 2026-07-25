(* ================================================================= *)
(*  QPolyDiv.v                                                       *)
(*                                                                    *)
(*  EUCLIDEAN DIVISION IN ℚ[X] (by any polynomial with nonzero       *)
(*  leading coefficient).                                            *)
(*                                                                    *)
(*      f = q·g + r,    deg r < d,    deg q ≤ n − d,                *)
(*                                                                    *)
(*  where d is the degree of g and its leading coefficient cl ≠ 0.   *)
(*  Unlike ℤ[X] (which needs g MONIC), over the field ℚ we divide the *)
(*  leading coefficient, so division by ANY nonzero g works — the     *)
(*  basis for the ℚ[X] gcd/Bézout algorithm.  AXIOM-FREE.           *)
(* ================================================================= *)

From Stdlib Require Import QArith Qcanon List Lia Arith.
Import ListNotations.
Require Import QPoly.
Open Scope Qc_scope.

(* ----------------------------------------------------------------- *)
(*  Degree-bound helpers                                             *)
(* ----------------------------------------------------------------- *)
Lemma qdegle_nil : forall n, qdegle [] n.
Proof. intros n i Hi; unfold qcoeff; apply nth_overflow; simpl; lia. Qed.

Lemma qdegle_mono : forall p a b, qdegle p a -> (a <= b)%nat -> qdegle p b.
Proof. intros p a b H Hab i Hi; apply H; lia. Qed.

Lemma qdegle_add : forall p q n, qdegle p n -> qdegle q n -> qdegle (qadd p q) n.
Proof. intros p q n Hp Hq i Hi; rewrite qcoeff_add, Hp, Hq by lia; ring. Qed.

Lemma qdegle_scale : forall c p n, qdegle p n -> qdegle (qscale c p) n.
Proof. intros c p n Hp i Hi; rewrite qcoeff_scale, Hp by lia; ring. Qed.

Lemma qcoeff_monom_hi : forall k i, (k < i)%nat -> qcoeff (qmonom k) i = 0.
Proof.
  induction k as [|k IH]; intros i Hi.
  - destruct i as [|i]; [ lia | ].
    unfold qcoeff; simpl; destruct i; reflexivity.
  - destruct i as [|i]; [ lia | ].
    unfold qcoeff; cbn [qmonom nth].
    change (nth i (qmonom k) 0) with (qcoeff (qmonom k) i); apply IH; lia.
Qed.

Lemma qdegle_monom : forall k, qdegle (qmonom k) k.
Proof. intros k i Hi; apply qcoeff_monom_hi; exact Hi. Qed.

(* ----------------------------------------------------------------- *)
(*  The division function and its specification                     *)
(* ----------------------------------------------------------------- *)
Fixpoint qdivmod (n : nat) (f g : qpoly) (d : nat) (cl : Qc) : qpoly * qpoly :=
  match n with
  | O => ([], f)
  | S m =>
      if le_lt_dec d (S m) then
        let c := qcoeff f (S m) * / cl in
        let f' := qsub f (qscale c (qshiftk (S m - d) g)) in
        let (q', r) := qdivmod m f' g d cl in
        (qadd q' (qscale c (qmonom (S m - d))), r)
      else ([], f)
  end.

Lemma qdivmod_spec : forall g d cl, (1 <= d)%nat -> cl <> 0 ->
  qcoeff g d = cl -> qdegle g d ->
  forall n f, qdegle f n ->
    (forall x, qeval f x
               = qeval (fst (qdivmod n f g d cl)) x * qeval g x
                 + qeval (snd (qdivmod n f g d cl)) x)
    /\ qdegle (snd (qdivmod n f g d cl)) (Nat.pred d)
    /\ qdegle (fst (qdivmod n f g d cl)) (n - d).
Proof.
  intros g d cl Hd1 Hcl Hlead Hdegg n.
  induction n as [|n IH]; intros f Hf.
  - cbn [qdivmod fst snd]; split; [ | split ].
    + intro x; simpl; ring.
    + intros i Hi; apply Hf; lia.
    + apply qdegle_nil.
  - cbn [qdivmod]; destruct (le_lt_dec d (S n)) as [Hdn | Hdn].
    + set (c := qcoeff f (S n) * / cl).
      set (f' := qsub f (qscale c (qshiftk (S n - d) g))).
      assert (Hccl : c * cl = qcoeff f (S n)) by (unfold c; field; exact Hcl).
      assert (Hf' : qdegle f' n).
      { intros i Hi.
        unfold f'; rewrite qcoeff_sub, qcoeff_scale, qcoeff_shiftk.
        destruct (Nat.ltb_spec i (S n - d)) as [Hlt | Hge].
        - lia.
        - destruct (Nat.eq_dec i (S n)) as [-> | Hne].
          + replace (S n - (S n - d))%nat with d by lia.
            rewrite Hlead, Hccl; ring.
          + rewrite (Hf i ltac:(lia)).
            replace (qcoeff g (i - (S n - d))) with 0 by (symmetry; apply Hdegg; lia).
            ring. }
      destruct (IH f' Hf') as [Hev [Hr Hq]].
      destruct (qdivmod n f' g d cl) as [q' r] eqn:E.
      cbn [fst snd] in Hev, Hr, Hq |- *.
      split; [ | split ].
      * intro x; rewrite qeval_add, qeval_scale, qeval_monom.
        assert (Hfx : qeval f x
                      = qeval f' x + c * (x ^ (S n - d) * qeval g x))
          by (unfold f'; rewrite qeval_sub, qeval_scale, qeval_shiftk; ring).
        rewrite Hfx, (Hev x); ring.
      * exact Hr.
      * apply qdegle_add.
        -- apply (qdegle_mono q' (n - d)); [ exact Hq | lia ].
        -- apply qdegle_scale; apply (qdegle_mono _ (S n - d));
             [ apply qdegle_monom | lia ].
    + cbn [fst snd]; split; [ | split ].
      * intro x; simpl; ring.
      * intros i Hi; apply Hf; lia.
      * apply qdegle_nil.
Qed.

Print Assumptions qdivmod_spec.

(* ================================================================= *)
(*  END QPolyDiv.v                                                   *)
(*  Euclidean division in ℚ[X] by any nonzero-leading polynomial:    *)
(*  f = q·g + r with deg r < deg g.  Basis for the ℚ[X] gcd.  Closed  *)
(*  under the global context (axiom-free).                           *)
(* ================================================================= *)
