(* ================================================================= *)
(*  RecipSquareBound.v                                               *)
(*                                                                    *)
(*  THE zeta(2) DOMINATION LEMMA -- the analytic crux of the Euler-     *)
(*  product bridge.                                                   *)
(*                                                                    *)
(*  Any FINITE set of DISTINCT positive integers contributes at most   *)
(*  zeta(2) worth of 1/m^2:                                            *)
(*                                                                    *)
(*     NoDup L  ->  (all m in L are >= 1)                              *)
(*         ->  sum_{m in L} 1/m^2  <=  zeta(2)         (recip_sq_nodup_bound)*)
(*                                                                    *)
(*  This is exactly what forces the primorial Euler rung EP n <= zeta(2)*)
(*  (tighter than the telescoping EP n <= 2, since zeta(2) < 2): via     *)
(*  EulerReindex, EP n is a sum of 1/m^2 over the DISTINCT {first n      *)
(*  primes}-smooth numbers, a subset of all of {1/m^2}, hence <= zeta(2).*)
(*                                                                    *)
(*  Proof: a NoDup list of positive integers included in [1..M] sums     *)
(*  (of any nonnegative g) to at most the full range sum (incl_sum_le,    *)
(*  by peeling elements with List.remove); the full range sum of 1/m^2   *)
(*  is the zeta partial sum zpart (M-1) (seqsum_zpart); and every zeta    *)
(*  partial sum is <= the limit (growing_ineq, ZetaConverge).           *)
(*                                                                    *)
(*  Uses the classical Reals axioms (quarantined, via ZetaConverge).   *)
(* ================================================================= *)

Require Import ZetaConverge.
From Stdlib Require Import Reals Lra Lia List.
Import ListNotations.
Open Scope R_scope.

Definition Rlsum (l : list R) : R := fold_right Rplus 0 l.

Lemma Rlsum_app : forall l1 l2, Rlsum (l1 ++ l2) = Rlsum l1 + Rlsum l2.
Proof.
  induction l1 as [|a l1 IH]; intro l2; unfold Rlsum in *; simpl;
    [ ring | rewrite IH; ring ].
Qed.

Lemma Rlsum_cons : forall x l, Rlsum (x :: l) = x + Rlsum l.
Proof. intros x l; unfold Rlsum; reflexivity. Qed.

(* ----------------------------------------------------------------- *)
(*  generic finite-sum facts for a nonnegative weight g              *)
(* ----------------------------------------------------------------- *)

Section GenSum.
Variable g : nat -> R.
Hypothesis Hg : forall x, 0 <= g x.

Lemma remove_nodup : forall x l, NoDup l -> NoDup (remove Nat.eq_dec x l).
Proof.
  intros x l; induction l as [|a l IH]; intro Hnd; simpl; [ constructor | ].
  inversion Hnd as [| ? ? Hnin Hnd']; subst.
  destruct (Nat.eq_dec x a) as [He | Hne]; [ apply IH; exact Hnd' | ].
  constructor;
    [ intro Hin; apply in_remove in Hin; destruct Hin as [Hin _]; contradiction
    | apply IH; exact Hnd' ].
Qed.

(* removing an element of a NoDup list drops its weight from the sum *)
Lemma sum_remove : forall r l, In r l -> NoDup l ->
  Rlsum (map g l) = g r + Rlsum (map g (remove Nat.eq_dec r l)).
Proof.
  intros r l; induction l as [|a l IH]; intros Hin Hnd; [ destruct Hin | ].
  inversion Hnd as [| ? ? Hnin Hnd']; subst.
  cbn [map remove]; rewrite Rlsum_cons.
  destruct (Nat.eq_dec r a) as [He | Hne].
  - subst a. rewrite (notin_remove Nat.eq_dec l r Hnin); reflexivity.
  - destruct Hin as [Ha | Hin]; [ symmetry in Ha; contradiction | ].
    cbn [map]; rewrite Rlsum_cons, (IH Hin Hnd'); ring.
Qed.

(* a NoDup list included in Rs sums to at most the sum over Rs *)
Lemma incl_sum_le : forall Rs L,
  NoDup L -> incl L Rs -> Rlsum (map g L) <= Rlsum (map g Rs).
Proof.
  induction Rs as [|r R' IH]; intros L Hnd Hincl.
  - assert (L = []).
    { destruct L as [|a L0]; [ reflexivity | ].
      exfalso; destruct (Hincl a (in_eq a L0)). }
    subst; unfold Rlsum; simpl; lra.
  - cbn [map]; rewrite Rlsum_cons.
    destruct (in_dec Nat.eq_dec r L) as [Hin | Hnin].
    + rewrite (sum_remove r L Hin Hnd).
      apply Rplus_le_compat_l.
      apply IH; [ apply remove_nodup; exact Hnd | ].
      intros x Hx; apply in_remove in Hx; destruct Hx as [Hx1 Hx2].
      destruct (Hincl x Hx1) as [He | Hin'];
        [ exfalso; apply Hx2; symmetry; exact He | exact Hin' ].
    + apply Rle_trans with (Rlsum (map g R')).
      * apply IH; [ exact Hnd | ].
        intros x Hx; destruct (Hincl x Hx) as [He | Hin'];
          [ subst r; contradiction | exact Hin' ].
      * pose proof (Hg r); lra.
Qed.

End GenSum.

(* ----------------------------------------------------------------- *)
(*  the concrete weight 1/m^2 and its zeta partial sums              *)
(* ----------------------------------------------------------------- *)

Definition rr (m : nat) : R := / (INR m) ^ 2.

Lemma rr_nonneg : forall m, 0 <= rr m.
Proof.
  intro m; unfold rr.
  destruct m as [|m].
  - simpl; rewrite Rmult_0_l, Rinv_0; lra.
  - apply Rlt_le, Rinv_0_lt_compat, pow_lt, lt_0_INR; lia.
Qed.

(* the full range sum of 1/m^2 over [1..S M] is the zeta partial sum *)
Lemma seqsum_zpart : forall M, Rlsum (map rr (seq 1 (S M))) = zpart M.
Proof.
  induction M as [|M IH].
  - unfold Rlsum, rr, zpart, zterm; simpl; lra.
  - rewrite seq_S, map_app, Rlsum_app, IH.
    change (zpart (S M)) with (zpart M + zterm (S M)).
    replace (1 + S M)%nat with (S (S M)) by lia.
    unfold Rlsum, rr, zterm; simpl; lra.
Qed.

Lemma Lz_nonneg : 0 <= proj1_sig zeta2_converges.
Proof.
  apply Rle_trans with (zpart 0);
    [ | apply (growing_ineq zpart (proj1_sig zeta2_converges)
                 zpart_growing (proj2_sig zeta2_converges)) ].
  unfold zpart; cbn [sum_f_R0]; apply Rlt_le, zterm_pos.
Qed.

(* helper: every element of a list is <= its list_max *)
Lemma in_le_list_max : forall x l, In x l -> (x <= list_max l)%nat.
Proof.
  intros x l Hin.
  pose proof (proj1 (list_max_le l (list_max l)) (le_n (list_max l))) as HF.
  rewrite Forall_forall in HF; apply HF; exact Hin.
Qed.

(* ----------------------------------------------------------------- *)
(*  THE zeta(2) DOMINATION LEMMA                                     *)
(* ----------------------------------------------------------------- *)

Theorem recip_sq_nodup_bound : forall L,
  NoDup L -> (forall m, In m L -> (1 <= m)%nat) ->
  Rlsum (map rr L) <= proj1_sig zeta2_converges.
Proof.
  intros L Hnd Hpos.
  destruct L as [|a L0].
  - unfold Rlsum; simpl; apply Lz_nonneg.
  - remember (list_max (a :: L0)) as M eqn:EM.
    assert (HM1 : (1 <= M)%nat).
    { subst M; pose proof (Hpos a (in_eq a L0));
        pose proof (in_le_list_max a (a :: L0) (in_eq a L0)); lia. }
    assert (Hincl : incl (a :: L0) (seq 1 M)).
    { intros x Hx; apply in_seq; split.
      - apply Hpos; exact Hx.
      - pose proof (in_le_list_max x (a :: L0) Hx); subst M; lia. }
    apply Rle_trans with (Rlsum (map rr (seq 1 M))).
    + apply (incl_sum_le rr rr_nonneg (seq 1 M) (a :: L0) Hnd Hincl).
    + destruct M as [|M']; [ lia | ].
      rewrite seqsum_zpart.
      apply (growing_ineq zpart (proj1_sig zeta2_converges)
               zpart_growing (proj2_sig zeta2_converges)).
Qed.

Print Assumptions recip_sq_nodup_bound.

(* ================================================================= *)
(*  END RecipSquareBound.v                                           *)
(*  Any finite set of distinct positive integers sums (of 1/m^2) to    *)
(*  at most zeta(2).  This is the domination that turns the primorial   *)
(*  Euler rung (a sum of 1/m^2 over distinct smooth numbers, via        *)
(*  EulerReindex) into the bound EP n <= zeta(2) = Hupper.              *)
(*  Uses the classical Reals axioms (quarantined).                    *)
(* ================================================================= *)
