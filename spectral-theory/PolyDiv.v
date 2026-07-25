(* ================================================================= *)
(*  PolyDiv.v                                                        *)
(*                                                                    *)
(*  EUCLIDEAN DIVISION BY A MONIC POLYNOMIAL in ℤ[X].               *)
(*                                                                    *)
(*  For any f and any MONIC g (leading coefficient 1, degree d ≥ 1), *)
(*  there are integer polynomials q, r with                          *)
(*      f = q·g + r      and      deg r < d.                         *)
(*                                                                    *)
(*  The quotient/remainder have INTEGER coefficients precisely       *)
(*  because g is monic: each step subtracts (lead f)·X^k·g, which     *)
(*  cancels the leading term of f with no coefficient division.       *)
(*  This is the reusable primitive for defining the cyclotomic Φ_n    *)
(*  (as the exact quotient of X^n−1 by ∏_{d|n,d<n} Φ_d) and for the   *)
(*  squarefreeness / gcd arguments behind ∏_{d|n} Φ_d = X^n−1.        *)
(*  AXIOM-FREE.                                                       *)
(* ================================================================= *)

From Stdlib Require Import ZArith List Lia.
Import ListNotations.
Require Import IntPoly.
Open Scope Z_scope.

(* the i-th coefficient (0 beyond the length) *)
Definition coeff (p : poly) (i : nat) : Z := nth i p 0.

(* ----------------------------------------------------------------- *)
(*  Negation / subtraction / shift-by-X^k, at eval and coeff level   *)
(* ----------------------------------------------------------------- *)
Definition pneg (p : poly) : poly := map Z.opp p.
Definition psub (p q : poly) : poly := padd p (pneg q).
Definition pshiftk (k : nat) (p : poly) : poly := repeat 0%Z k ++ p.

Lemma eval_neg : forall p x, eval (pneg p) x = - eval p x.
Proof.
  intros p x; induction p as [|a p IH]; simpl; [ ring | ].
  change (map Z.opp p) with (pneg p); rewrite IH; ring.
Qed.

Lemma eval_sub : forall p q x, eval (psub p q) x = eval p x - eval q x.
Proof. intros; unfold psub; rewrite eval_add, eval_neg; ring. Qed.

Lemma eval_pshiftk : forall k p x, eval (pshiftk k p) x = x ^ Z.of_nat k * eval p x.
Proof.
  induction k as [|k IH]; intros p x.
  - unfold pshiftk; cbn [repeat app]; cbn [Z.of_nat]; rewrite Z.pow_0_r; ring.
  - unfold pshiftk; cbn [repeat app eval].
    change (repeat 0%Z k ++ p) with (pshiftk k p); rewrite IH.
    rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia; ring.
Qed.

Lemma nth_repeat0 : forall k i, nth i (repeat 0%Z k) 0%Z = 0%Z.
Proof. intros k; induction k as [|k IH]; intros [|i]; simpl; auto. Qed.

(* ----------------------------------------------------------------- *)
(*  Coefficients of the operations                                   *)
(* ----------------------------------------------------------------- *)
Lemma coeff_padd : forall p q i, coeff (padd p q) i = coeff p i + coeff q i.
Proof.
  unfold coeff; induction p as [|a p IH]; intros q i.
  - cbn [padd]; destruct i; simpl; ring.
  - destruct q as [|b q]; simpl.
    + destruct i; simpl; ring.
    + destruct i; simpl; [ ring | apply IH ].
Qed.

Lemma coeff_pscale : forall c p i, coeff (pscale c p) i = c * coeff p i.
Proof.
  intros c p i; unfold coeff, pscale.
  replace 0%Z with (Z.mul c 0) at 1 by ring.
  rewrite map_nth; reflexivity.
Qed.

Lemma coeff_pneg : forall p i, coeff (pneg p) i = - coeff p i.
Proof.
  intros p i; unfold coeff, pneg.
  replace 0%Z with (Z.opp 0) at 1 by ring.
  rewrite map_nth; reflexivity.
Qed.

Lemma coeff_psub : forall p q i, coeff (psub p q) i = coeff p i - coeff q i.
Proof. intros; unfold psub; rewrite coeff_padd, coeff_pneg; ring. Qed.

Lemma coeff_pshiftk : forall k p i,
  coeff (pshiftk k p) i = if (i <? k)%nat then 0 else coeff p (i - k).
Proof.
  intros k p i; unfold coeff, pshiftk.
  destruct (Nat.ltb_spec i k) as [Hlt | Hge].
  - rewrite app_nth1 by (rewrite repeat_length; lia); apply nth_repeat0.
  - rewrite app_nth2 by (rewrite repeat_length; lia).
    rewrite repeat_length; reflexivity.
Qed.

(* ----------------------------------------------------------------- *)
(*  Degree bound and monic-ness                                      *)
(* ----------------------------------------------------------------- *)
Definition degle (p : poly) (n : nat) : Prop :=
  forall i, (n < i)%nat -> coeff p i = 0.

Definition monic (g : poly) (d : nat) : Prop := coeff g d = 1 /\ degle g d.

(* every polynomial has degree bounded by its length *)
Lemma degle_length : forall f, degle f (length f).
Proof. intros f i Hi; unfold coeff; apply nth_overflow; lia. Qed.

(* ----------------------------------------------------------------- *)
(*  The division, by induction on the degree bound of the dividend   *)
(* ----------------------------------------------------------------- *)
Lemma monic_div_aux : forall g d, (1 <= d)%nat -> monic g d ->
  forall n f, degle f n ->
  exists q r,
    (forall x, eval f x = eval q x * eval g x + eval r x)
    /\ degle r (Nat.pred d).
Proof.
  intros g d Hd1 [Hlead Hdegg] n.
  induction n as [|n IH]; intros f Hf.
  - (* deg f = 0 < d : quotient 0, remainder f *)
    exists [], f; split.
    + intro x; simpl; ring.
    + intros i Hi; apply Hf; lia.
  - destruct (le_lt_dec d (S n)) as [Hdn | Hdn].
    + (* d <= S n : cancel the top coefficient *)
      set (c := coeff f (S n)).
      set (f' := psub f (pscale c (pshiftk (S n - d) g))).
      assert (Hf' : degle f' n).
      { intros i Hi.
        unfold f'; rewrite coeff_psub, coeff_pscale, coeff_pshiftk.
        destruct (Nat.ltb_spec i (S n - d)) as [Hlt | Hge2].
        - lia.
        - destruct (Nat.eq_dec i (S n)) as [Hie | Hine].
          + subst i; replace (S n - (S n - d))%nat with d by lia.
            unfold c; rewrite Hlead; ring.
          + rewrite (Hf i ltac:(lia)).
            replace (coeff g (i - (S n - d))) with 0 by (symmetry; apply Hdegg; lia).
            ring. }
      destruct (IH f' Hf') as [q' [r [Hev Hr]]].
      exists (padd q' (pscale c (pmonom (S n - d)))), r; split.
      * intro x.
        rewrite eval_add, eval_scale, eval_monom.
        assert (Hfx : eval f x
                      = eval f' x + c * (x ^ Z.of_nat (S n - d) * eval g x))
          by (unfold f'; rewrite eval_sub, eval_scale, eval_pshiftk; ring).
        rewrite Hfx, Hev; ring.
      * exact Hr.
    + (* S n < d : deg f <= S n < d : quotient 0, remainder f *)
      exists [], f; split.
      * intro x; simpl; ring.
      * intros i Hi; apply Hf; lia.
Qed.

Theorem monic_div : forall f g d, (1 <= d)%nat -> monic g d ->
  exists q r,
    (forall x, eval f x = eval q x * eval g x + eval r x)
    /\ degle r (Nat.pred d).
Proof.
  intros f g d Hd1 Hmon.
  apply (monic_div_aux g d Hd1 Hmon (length f) f (degle_length f)).
Qed.

Print Assumptions monic_div.

(* ================================================================= *)
(*  END PolyDiv.v                                                    *)
(*  Euclidean division by a monic polynomial in ℤ[X]: f = q·g + r    *)
(*  with deg r < deg g, integer coefficients throughout.  The        *)
(*  reusable primitive for the cyclotomic Φ_n.  Closed under the      *)
(*  global context (axiom-free).                                     *)
(* ================================================================= *)
