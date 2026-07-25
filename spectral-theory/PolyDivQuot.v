(* ================================================================= *)
(*  PolyDivQuot.v                                                    *)
(*                                                                    *)
(*  THE QUOTIENT OF A MONIC BY A MONIC IS MONIC.                     *)
(*                                                                    *)
(*      monic f n → monic g d → 1 ≤ d ≤ n →                         *)
(*          monic (quotient of f by g) (n − d).                     *)
(*                                                                    *)
(*  This is what makes Φ_n = (X^n−1)/∏_{d|n,d<n}Φ_d monic of degree   *)
(*  φ(n).  It needs the COEFFICIENT-level division identity          *)
(*      coeff f i = coeff (q·g) i + coeff r i                        *)
(*  (the eval-level spec cannot pin a leading coefficient), which     *)
(*  rests on a little pmul coefficient algebra (distributivity over  *)
(*  padd, pulling out a scale, and X^k·g = pshiftk k g).  AXIOM-FREE.*)
(* ================================================================= *)

From Stdlib Require Import ZArith List Lia.
Import ListNotations.
Require Import IntPoly PolyDiv PolyMonic PolyDivComp.
Open Scope Z_scope.

(* ----------------------------------------------------------------- *)
(*  Coefficients of pmonom below / at its degree                    *)
(* ----------------------------------------------------------------- *)
Lemma pmonom_repeat : forall k, pmonom k = repeat 0%Z k ++ [1].
Proof. induction k as [|k IH]; simpl; [ reflexivity | rewrite IH; reflexivity ]. Qed.

Lemma coeff_pmonom_lo : forall k j, (j < k)%nat -> coeff (pmonom k) j = 0.
Proof.
  intros k j Hj; unfold coeff; rewrite pmonom_repeat, app_nth1
    by (rewrite repeat_length; lia); apply nth_repeat0.
Qed.

Lemma coeff_pmonom_eq : forall k, coeff (pmonom k) k = 1.
Proof.
  intro k; unfold coeff; rewrite pmonom_repeat, app_nth2
    by (rewrite repeat_length; lia).
  rewrite repeat_length, Nat.sub_diag; reflexivity.
Qed.

(* ----------------------------------------------------------------- *)
(*  pmul coefficient algebra (via the convolution of PolyMonic)     *)
(* ----------------------------------------------------------------- *)
Lemma fold_map_add : forall (l : list nat) (f h : nat -> Z),
  fold_right Z.add 0 (map f l) + fold_right Z.add 0 (map h l)
  = fold_right Z.add 0 (map (fun j => f j + h j) l).
Proof.
  induction l as [|a l IH]; intros f h; simpl; [ ring | rewrite <- IH; ring ].
Qed.

Lemma fold_map_scale : forall (l : list nat) (c : Z) (f : nat -> Z),
  c * fold_right Z.add 0 (map f l) = fold_right Z.add 0 (map (fun j => c * f j) l).
Proof.
  induction l as [|a l IH]; intros c f; simpl; [ ring | rewrite <- IH; ring ].
Qed.

Lemma coeff_pmul_padd_l : forall a b g i,
  coeff (pmul (padd a b) g) i = coeff (pmul a g) i + coeff (pmul b g) i.
Proof.
  intros a b g i; rewrite !coeff_pmul; unfold conv.
  rewrite fold_map_add; f_equal; apply map_ext; intro j.
  rewrite coeff_padd; ring.
Qed.

Lemma coeff_pmul_pscale_l : forall c a g i,
  coeff (pmul (pscale c a) g) i = c * coeff (pmul a g) i.
Proof.
  intros c a g i; rewrite !coeff_pmul; unfold conv.
  rewrite fold_map_scale; f_equal; apply map_ext; intro j.
  rewrite coeff_pscale; ring.
Qed.

Lemma coeff_pmul_pmonom_l : forall k g i,
  coeff (pmul (pmonom k) g) i = coeff (pshiftk k g) i.
Proof.
  intros k g i; rewrite coeff_pmul, coeff_pshiftk; unfold conv.
  destruct (Nat.ltb_spec i k) as [Hlt | Hge].
  - apply fold_add_zero; intros j Hj; rewrite in_seq in Hj.
    rewrite coeff_pmonom_lo by lia; ring.
  - replace (S i) with (k + S (i - k))%nat by lia.
    rewrite seq_app, map_app, fold_app.
    rewrite (fold_add_zero (seq 0 k)).
    2:{ intros j Hj; rewrite in_seq in Hj; rewrite coeff_pmonom_lo by lia; ring. }
    replace (0 + k)%nat with k by lia.
    cbn [seq map fold_right].
    rewrite (fold_add_zero (seq (S k) (i - k))).
    2:{ intros j Hj; rewrite in_seq in Hj; rewrite coeff_pmonom_hi by lia; ring. }
    rewrite coeff_pmonom_eq; ring.
Qed.

(* ----------------------------------------------------------------- *)
(*  Coefficient-level division identity  f = q·g + r                *)
(* ----------------------------------------------------------------- *)
Lemma pdivmod_coeff : forall g d, (1 <= d)%nat -> monic g d ->
  forall n f, degle f n ->
    forall i, coeff f i
              = coeff (pmul (fst (pdivmod n f g d)) g) i
                + coeff (snd (pdivmod n f g d)) i.
Proof.
  intros g d Hd1 Hmon n; destruct Hmon as [Hlead Hdegg].
  induction n as [|n IH]; intros f Hf i.
  - cbn [pdivmod fst snd]; cbn [pmul]; rewrite coeff_nil; ring.
  - cbn [pdivmod]; destruct (le_lt_dec d (S n)) as [Hdn | Hdn].
    + set (c := coeff f (S n)).
      set (f' := psub f (pscale c (pshiftk (S n - d) g))).
      assert (Hf' : degle f' n).
      { intros k Hk.
        unfold f'; rewrite coeff_psub, coeff_pscale, coeff_pshiftk.
        destruct (Nat.ltb_spec k (S n - d)) as [Hlt | Hge].
        - lia.
        - destruct (Nat.eq_dec k (S n)) as [-> | Hne].
          + replace (S n - (S n - d))%nat with d by lia.
            unfold c; rewrite Hlead; ring.
          + rewrite (Hf k ltac:(lia)).
            replace (coeff g (k - (S n - d))) with 0 by (symmetry; apply Hdegg; lia).
            ring. }
      specialize (IH f' Hf').
      destruct (pdivmod n f' g d) as [q' r] eqn:E.
      cbn [fst snd] in IH |- *.
      rewrite coeff_pmul_padd_l, coeff_pmul_pscale_l, coeff_pmul_pmonom_l.
      assert (Hfi : coeff f i = coeff f' i + c * coeff (pshiftk (S n - d) g) i)
        by (unfold f'; rewrite coeff_psub, coeff_pscale; ring).
      rewrite Hfi, (IH i); ring.
    + cbn [fst snd pmul]; rewrite coeff_nil; ring.
Qed.

(* ----------------------------------------------------------------- *)
(*  THE QUOTIENT OF A MONIC BY A MONIC IS MONIC                      *)
(* ----------------------------------------------------------------- *)
Theorem monic_div_monic : forall f n g d, (1 <= d <= n)%nat ->
  monic f n -> monic g d -> monic (fst (pdivmod n f g d)) (n - d).
Proof.
  intros f n g d [Hd1 Hdn] [Hfl Hfd] Hg.
  assert (Hgpair := Hg); destruct Hg as [Hgl Hgd].
  pose proof (pdivmod_spec g d Hd1 Hgpair n f Hfd) as [_ [_ Hq]].
  split; [ | exact Hq ].
  pose proof (pdivmod_coeff g d Hd1 Hgpair n f Hfd n) as Hn.
  assert (Hrn : coeff (snd (pdivmod n f g d)) n = 0)
    by (pose proof (pdivmod_spec g d Hd1 Hgpair n f Hfd) as [_ [Hr _]]; apply Hr; lia).
  pose proof (coeff_pmul_top (fst (pdivmod n f g d)) g (n - d) d Hq Hgd) as Htop.
  replace (n - d + d)%nat with n in Htop by lia.
  rewrite Hgl in Htop.
  rewrite Hfl, Htop, Hrn in Hn; lia.
Qed.

Print Assumptions monic_div_monic.

(* ================================================================= *)
(*  END PolyDivQuot.v                                                *)
(*  The quotient of a monic polynomial by a monic polynomial is      *)
(*  monic (degree subtracts).  Via the coefficient-level identity    *)
(*  f = q·g + r and the leading-coefficient formula.  This makes Φ_n  *)
(*  monic of degree φ(n).  Closed under the global context.          *)
(* ================================================================= *)
