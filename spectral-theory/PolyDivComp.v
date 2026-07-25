(* ================================================================= *)
(*  PolyDivComp.v                                                    *)
(*                                                                    *)
(*  COMPUTABLE monic division in ℤ[X].                              *)
(*                                                                    *)
(*  PolyDiv.monic_div only asserts EXISTENCE of q, r.  To DEFINE the *)
(*  cyclotomic Φ_n as an actual quotient (axiom-free, no choice), we  *)
(*  need a division FUNCTION.  `pdivmod n f g d` computes (q, r) by   *)
(*  the same leading-term cancellation, and `pdivmod_spec` proves     *)
(*      f = q·g + r,   deg r < d,   deg q ≤ n − d                    *)
(*  (the quotient degree bound is what pins down that Φ_n is monic).  *)
(*  AXIOM-FREE.                                                       *)
(* ================================================================= *)

From Stdlib Require Import ZArith List Lia.
Import ListNotations.
Require Import IntPoly PolyDiv.
Open Scope Z_scope.

(* ----------------------------------------------------------------- *)
(*  Degree-bound helpers                                             *)
(* ----------------------------------------------------------------- *)
Lemma degle_nil : forall n, degle [] n.
Proof. intros n i Hi; unfold coeff; apply nth_overflow; simpl; lia. Qed.

Lemma degle_mono : forall p a b, degle p a -> (a <= b)%nat -> degle p b.
Proof. intros p a b H Hab i Hi; apply H; lia. Qed.

Lemma degle_padd : forall p q n, degle p n -> degle q n -> degle (padd p q) n.
Proof. intros p q n Hp Hq i Hi; rewrite coeff_padd, Hp, Hq by lia; ring. Qed.

Lemma degle_pscale : forall c p n, degle p n -> degle (pscale c p) n.
Proof. intros c p n Hp i Hi; rewrite coeff_pscale, Hp by lia; ring. Qed.

Lemma coeff_pmonom_hi : forall k i, (k < i)%nat -> coeff (pmonom k) i = 0.
Proof.
  induction k as [|k IH]; intros i Hi.
  - destruct i as [|i]; [ lia | ].
    unfold coeff; simpl; destruct i; reflexivity.
  - destruct i as [|i]; [ lia | ].
    unfold coeff; cbn [pmonom nth].
    change (nth i (pmonom k) 0) with (coeff (pmonom k) i); apply IH; lia.
Qed.

Lemma degle_pmonom : forall k, degle (pmonom k) k.
Proof. intros k i Hi; apply coeff_pmonom_hi; exact Hi. Qed.

(* ----------------------------------------------------------------- *)
(*  The division function and its specification                     *)
(* ----------------------------------------------------------------- *)
Fixpoint pdivmod (n : nat) (f g : poly) (d : nat) : poly * poly :=
  match n with
  | O => ([], f)
  | S m =>
      if le_lt_dec d (S m) then
        let c := coeff f (S m) in
        let f' := psub f (pscale c (pshiftk (S m - d) g)) in
        let (q', r) := pdivmod m f' g d in
        (padd q' (pscale c (pmonom (S m - d))), r)
      else ([], f)
  end.

Lemma pdivmod_spec : forall g d, (1 <= d)%nat -> monic g d ->
  forall n f, degle f n ->
    (forall x, eval f x
               = eval (fst (pdivmod n f g d)) x * eval g x
                 + eval (snd (pdivmod n f g d)) x)
    /\ degle (snd (pdivmod n f g d)) (Nat.pred d)
    /\ degle (fst (pdivmod n f g d)) (n - d).
Proof.
  intros g d Hd1 [Hlead Hdegg] n.
  induction n as [|n IH]; intros f Hf.
  - cbn [pdivmod fst snd]; split; [ | split ].
    + intro x; simpl; ring.
    + intros i Hi; apply Hf; lia.
    + apply degle_nil.
  - cbn [pdivmod]; destruct (le_lt_dec d (S n)) as [Hdn | Hdn].
    + set (c := coeff f (S n)).
      set (f' := psub f (pscale c (pshiftk (S n - d) g))).
      assert (Hf' : degle f' n).
      { intros i Hi.
        unfold f'; rewrite coeff_psub, coeff_pscale, coeff_pshiftk.
        destruct (Nat.ltb_spec i (S n - d)) as [Hlt | Hge].
        - lia.
        - destruct (Nat.eq_dec i (S n)) as [-> | Hne].
          + replace (S n - (S n - d))%nat with d by lia.
            unfold c; rewrite Hlead; ring.
          + rewrite (Hf i ltac:(lia)).
            replace (coeff g (i - (S n - d))) with 0 by (symmetry; apply Hdegg; lia).
            ring. }
      destruct (IH f' Hf') as [Hev [Hr Hq]].
      destruct (pdivmod n f' g d) as [q' r] eqn:E.
      cbn [fst snd] in Hev, Hr, Hq |- *.
      split; [ | split ].
      * intro x; rewrite eval_add, eval_scale, eval_monom.
        assert (Hfx : eval f x
                      = eval f' x + c * (x ^ Z.of_nat (S n - d) * eval g x))
          by (unfold f'; rewrite eval_sub, eval_scale, eval_pshiftk; ring).
        rewrite Hfx, (Hev x); ring.
      * exact Hr.
      * apply degle_padd.
        -- apply (degle_mono q' (n - d)); [ exact Hq | lia ].
        -- apply degle_pscale; apply (degle_mono _ (S n - d));
             [ apply degle_pmonom | lia ].
    + cbn [fst snd]; split; [ | split ].
      * intro x; simpl; ring.
      * intros i Hi; apply Hf; lia.
      * apply degle_nil.
Qed.

Print Assumptions pdivmod_spec.

(* ================================================================= *)
(*  END PolyDivComp.v                                                *)
(*  A computable monic-division function pdivmod with f = q·g + r,   *)
(*  deg r < d, deg q ≤ n − d.  Lets Φ_n be defined as an actual       *)
(*  integer-polynomial quotient.  Closed under the global context.   *)
(* ================================================================= *)
