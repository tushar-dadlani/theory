(* ================================================================= *)
(*  HyperbolaSplit.v  --  Dirichlet's hyperbola method, over R.       *)
(*                                                                    *)
(*  Two identities, both pure combinatorics -- no characters, no      *)
(*  analysis.  RS F X is sum_{n=1}^{X} F n.                            *)
(*                                                                    *)
(*  hyper_iter :  sum_{n<=X} sum_{d|n} a_d b_{n/d}                     *)
(*                  = sum_{d<=X} a_d sum_{e<=X/d} b_e                  *)
(*                                                                    *)
(*  hyper_split (at X = N*N, so that sqrt X is an integer and every    *)
(*  floor disappears):                                                 *)
(*                sum_{d<=X} a_d sum_{e<=X/d} b_e                      *)
(*                  = sum_{d<=N} a_d sum_{e<=X/d} b_e                  *)
(*                  + sum_{e<=N} b_e sum_{d<=X/e} a_d                  *)
(*                  - (sum_{d<=N} a_d)(sum_{e<=N} b_e)                 *)
(*                                                                    *)
(*  WHY THE SPLIT IS NEEDED.  Feeding sum_{e<=y} 1/sqrt e =            *)
(*  2 sqrt y + C + O(1/sqrt y) into the UNSPLIT sum leaves an error    *)
(*  sum_{d<=X} (1/sqrt d) O(sqrt d / sqrt X) of size X/sqrt X = sqrt X *)
(*  -- useless.  The split confines that error to d <= N, where it is  *)
(*  O(N/sqrt X) = O(1), and the far region is handled by the SECOND    *)
(*  form, whose x^{1/4}-sized main term cancels against the third      *)
(*  product exactly.                                                   *)
(*                                                                    *)
(*  Everything reduces to swapping two finite iterated sums over a     *)
(*  rectangle (RS_swap, an easy induction) plus two reindexings:       *)
(*  RS_indic_div for  [d | n], n = d e  and RS_indic_le for  d e <= X. *)
(*  No Permutation surgery on lists of pairs is needed anywhere.       *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia Arith List Bool.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  Part A -- RS: the 1-indexed partial sum, and its algebra.          *)
(* ----------------------------------------------------------------- *)

Fixpoint RS (F : nat -> R) (X : nat) : R :=
  match X with O => 0 | S X' => RS F X' + F (S X') end.

Lemma RS_ext : forall F G X,
  (forall n, (1 <= n <= X)%nat -> F n = G n) -> RS F X = RS G X.
Proof.
  intros F G X. induction X as [| X IH]; intro H; [ reflexivity | ].
  cbn [RS]. rewrite (H (S X)) by lia. f_equal. apply IH. intros n Hn. apply H. lia.
Qed.

Lemma RS_zero : forall X, RS (fun _ => 0) X = 0.
Proof. induction X as [| X IH]; [ reflexivity | cbn [RS]; rewrite IH; ring ]. Qed.

Lemma RS_plus : forall F G X, RS (fun n => F n + G n) X = RS F X + RS G X.
Proof. intros F G X. induction X as [| X IH]; [ cbn; ring | cbn [RS]; rewrite IH; ring ]. Qed.

Lemma RS_minus : forall F G X, RS (fun n => F n - G n) X = RS F X - RS G X.
Proof. intros F G X. induction X as [| X IH]; [ cbn; ring | cbn [RS]; rewrite IH; ring ]. Qed.

Lemma RS_scal : forall c F X, RS (fun n => c * F n) X = c * RS F X.
Proof. intros c F X. induction X as [| X IH]; [ cbn; ring | cbn [RS]; rewrite IH; ring ]. Qed.

Lemma RS_stab : forall F X Y, (X <= Y)%nat -> (forall n, (X < n)%nat -> F n = 0) ->
  RS F Y = RS F X.
Proof.
  intros F X Y HXY H. induction Y as [| Y IH].
  - replace X with 0%nat by lia. reflexivity.
  - destruct (Nat.eq_dec X (S Y)) as [E | E]; [ rewrite E; reflexivity | ].
    cbn [RS]. rewrite (H (S Y)) by lia. rewrite IH by lia. ring.
Qed.

Lemma RS_swap : forall (G : nat -> nat -> R) X Y,
  RS (fun d => RS (fun e => G d e) Y) X = RS (fun e => RS (fun d => G d e) X) Y.
Proof.
  intros G X Y. induction X as [| X IH].
  - cbn [RS]. symmetry.
    transitivity (RS (fun _ : nat => 0) Y);
      [ apply RS_ext; intros; reflexivity | apply RS_zero ].
  - cbn [RS]. rewrite IH, <- RS_plus. apply RS_ext. intros e _. reflexivity.
Qed.

Lemma RS_split : forall F N X, (N <= X)%nat ->
  RS F X = RS F N + RS (fun d => if (N <? d)%nat then F d else 0) X.
Proof.
  intros F N X. induction X as [| X IH]; intro HNX.
  - replace N with 0%nat by lia. cbn [RS]. ring.
  - destruct (Nat.eq_dec N (S X)) as [E | E].
    + rewrite E.
      rewrite (RS_ext (fun d => if (S X <? d)%nat then F d else 0) (fun _ => 0)).
      * rewrite RS_zero. ring.
      * intros n Hn. destruct (S X <? n)%nat eqn:Eb;
          [ apply Nat.ltb_lt in Eb; lia | reflexivity ].
    + cbn [RS]. rewrite (IH ltac:(lia)).
      replace (N <? S X)%nat with true by (symmetry; apply Nat.ltb_lt; lia). ring.
Qed.

(* ----------------------------------------------------------------- *)
(*  Part B -- the nat-division facts.                                  *)
(* ----------------------------------------------------------------- *)

Lemma div_unique_loc : forall a d q r, (1 <= d)%nat -> (r < d)%nat ->
  a = (d * q + r)%nat -> (a / d)%nat = q.
Proof.
  intros a d q r Hd Hr Ha. subst a.
  replace (d * q)%nat with (q * d)%nat by lia.
  rewrite Nat.div_add_l by lia. rewrite (Nat.div_small r d Hr). lia.
Qed.

Lemma mod_unique_loc : forall a d q r, (1 <= d)%nat -> (r < d)%nat ->
  a = (d * q + r)%nat -> (a mod d)%nat = r.
Proof.
  intros a d q r Hd Hr Ha.
  pose proof (Nat.div_mod_eq a d) as HE.
  rewrite (div_unique_loc a d q r Hd Hr Ha) in HE. lia.
Qed.

Lemma div_succ_cases : forall d X, (1 <= d)%nat ->
  ((S X mod d = 0)%nat /\ (S X / d = X / d + 1)%nat)
  \/ ((S X mod d <> 0)%nat /\ (S X / d = X / d)%nat).
Proof.
  intros d X Hd.
  pose proof (Nat.div_mod_eq X d) as HE.
  pose proof (Nat.mod_upper_bound X d ltac:(lia)) as Hr.
  destruct (Nat.eq_dec (X mod d + 1) d) as [E | E].
  - left. assert (Ha : S X = (d * (X / d + 1) + 0)%nat) by nia.
    assert (H0d : (0 < d)%nat) by lia.
    split; [ exact (mod_unique_loc _ _ _ _ Hd H0d Ha)
           | exact (div_unique_loc _ _ _ _ Hd H0d Ha) ].
  - right. assert (Hlt : (X mod d + 1 < d)%nat) by lia.
    assert (Ha : S X = (d * (X / d) + (X mod d + 1))%nat) by nia.
    rewrite (mod_unique_loc _ _ _ _ Hd Hlt Ha).
    split; [ lia | apply (div_unique_loc _ _ _ _ Hd Hlt Ha) ].
Qed.

Lemma le_div_iff : forall d e X, (1 <= d)%nat -> ((e <= X / d)%nat <-> (d * e <= X)%nat).
Proof.
  intros d e X Hd.
  pose proof (Nat.div_mod_eq X d) as HE.
  pose proof (Nat.mod_upper_bound X d ltac:(lia)) as Hr.
  split; intro H; nia.
Qed.

Lemma div_le_self : forall d X, (1 <= d)%nat -> (X / d <= X)%nat.
Proof.
  intros d X Hd. pose proof (Nat.div_mod_eq X d) as HE.
  pose proof (Nat.mod_upper_bound X d ltac:(lia)) as Hr. nia.
Qed.

(* ----------------------------------------------------------------- *)
(*  Part C -- the two reindexings.                                     *)
(* ----------------------------------------------------------------- *)

Lemma RS_indic_div : forall (h : nat -> R) d X, (1 <= d)%nat ->
  RS (fun n => if (n mod d =? 0)%nat then h n else 0) X
  = RS (fun e => h (d * e)%nat) (X / d).
Proof.
  intros h d X Hd. induction X as [| X IH].
  - rewrite (Nat.div_small 0 d ltac:(lia)). reflexivity.
  - cbn [RS]. rewrite IH.
    destruct (div_succ_cases d X Hd) as [[E2 E3] | [E2 E3]].
    + rewrite E3.
      replace (S X mod d =? 0)%nat with true by (symmetry; apply Nat.eqb_eq; exact E2).
      assert (Hmul : (d * S (X / d))%nat = S X).
      { pose proof (Nat.div_mod_eq (S X) d) as HE. rewrite E3, E2 in HE.
        replace (S (X / d)) with (X / d + 1)%nat by lia. nia. }
      replace (X / d + 1)%nat with (S (X / d)) by lia.
      cbn [RS]. rewrite Hmul. reflexivity.
    + rewrite E3.
      replace (S X mod d =? 0)%nat with false by (symmetry; apply Nat.eqb_neq; exact E2).
      ring.
Qed.

Lemma RS_indic_le : forall (b : nat -> R) d X, (1 <= d)%nat ->
  RS (fun e => if (d * e <=? X)%nat then b e else 0) X = RS b (X / d).
Proof.
  intros b d X Hd.
  transitivity (RS (fun e => if (d * e <=? X)%nat then b e else 0) (X / d)).
  - apply RS_stab; [ apply div_le_self; lia | ].
    intros n Hn. replace (d * n <=? X)%nat with false; [ reflexivity | ].
    symmetry. apply Nat.leb_nle. intro Hc.
    apply (le_div_iff d n X Hd) in Hc. lia.
  - apply RS_ext. intros e He.
    replace (d * e <=? X)%nat with true; [ reflexivity | ].
    symmetry. apply Nat.leb_le. apply (le_div_iff d e X Hd). lia.
Qed.

Lemma RS_indic_le' : forall (a : nat -> R) e X, (1 <= e)%nat ->
  RS (fun d => if (d * e <=? X)%nat then a d else 0) X = RS a (X / e).
Proof.
  intros a e X He. rewrite <- (RS_indic_le a e X He).
  apply RS_ext. intros d Hd. replace (e * d)%nat with (d * e)%nat by lia. reflexivity.
Qed.

(* ----------------------------------------------------------------- *)
(*  Part D -- the divisor sum as an iterated sum.                      *)
(* ----------------------------------------------------------------- *)

Theorem hyper_iter : forall (a b : nat -> R) X,
  RS (fun n => RS (fun d => if (n mod d =? 0)%nat then a d * b (n / d)%nat else 0) X) X
  = RS (fun d => a d * RS b (X / d)%nat) X.
Proof.
  intros a b X. rewrite RS_swap. apply RS_ext. intros d Hd.
  rewrite (RS_indic_div (fun n => a d * b (n / d)%nat) d X ltac:(lia)).
  rewrite <- RS_scal. apply RS_ext. intros e He.
  replace (d * e / d)%nat with e; [ reflexivity | ].
  symmetry. replace (d * e)%nat with (e * d)%nat by lia. apply Nat.div_mul. lia.
Qed.

(* ----------------------------------------------------------------- *)
(*  Part E -- the hyperbola split at X = N*N.                          *)
(* ----------------------------------------------------------------- *)

Theorem hyper_split : forall (a b : nat -> R) N,
  RS (fun d => a d * RS b (N * N / d)%nat) (N * N)
  = RS (fun d => a d * RS b (N * N / d)%nat) N
    + RS (fun e => b e * RS a (N * N / e)%nat) N
    - RS a N * RS b N.
Proof.
  intros a b N. set (X := (N * N)%nat).
  assert (HNX : (N <= X)%nat) by (unfold X; nia).
  rewrite (RS_split (fun d => a d * RS b (X / d)%nat) N X HNX).
  assert (Hkey : RS (fun d => if (N <? d)%nat then a d * RS b (X / d)%nat else 0) X
                 = RS (fun e => b e * RS a (X / e)%nat) N - RS a N * RS b N).
  { transitivity (RS (fun d => RS (fun e =>
        if ((N <? d) && (d * e <=? X))%nat then a d * b e else 0) X) X).
    { apply RS_ext. intros d Hd. destruct (N <? d)%nat eqn:Ed.
      - rewrite <- (RS_indic_le b d X ltac:(lia)), <- RS_scal.
        apply RS_ext. intros e He. cbn [andb].
        destruct (d * e <=? X)%nat; ring.
      - transitivity (RS (fun _ : nat => 0) X).
        + symmetry. apply RS_zero.
        + apply RS_ext. intros e He. reflexivity. }
    rewrite RS_swap.
    rewrite (RS_stab _ N X HNX).
    2: { intros e He.
         rewrite (RS_ext (fun d => if ((N <? d) && (d * e <=? X))%nat
                                   then a d * b e else 0) (fun _ => 0)).
         - apply RS_zero.
         - intros d Hd. destruct ((N <? d) && (d * e <=? X))%nat eqn:Eb;
             [ | reflexivity ].
           exfalso. apply andb_true_iff in Eb. destruct Eb as [E1 E2].
           apply Nat.ltb_lt in E1. apply Nat.leb_le in E2. unfold X in E2. nia. }
    transitivity (RS (fun e => b e * RS a (X / e)%nat - b e * RS a N) N).
    - apply RS_ext. intros e He.
      transitivity (RS (fun d => if (d * e <=? X)%nat then a d * b e else 0) X
                    - RS (fun d => if (d <=? N)%nat then a d * b e else 0) X).
      + rewrite <- RS_minus. apply RS_ext. intros d Hd.
        destruct (N <? d)%nat eqn:E1.
        * replace (d <=? N)%nat with false
            by (symmetry; apply Nat.leb_nle; apply Nat.ltb_lt in E1; lia).
          cbn [andb]. destruct (d * e <=? X)%nat; ring.
        * replace (d <=? N)%nat with true
            by (symmetry; apply Nat.leb_le; apply Nat.ltb_ge in E1; lia).
          replace (d * e <=? X)%nat with true.
          2: { symmetry. apply Nat.leb_le. apply Nat.ltb_ge in E1. unfold X. nia. }
          cbn [andb]. ring.
      + f_equal.
        * rewrite <- (RS_indic_le' a e X ltac:(lia)), <- RS_scal.
          apply RS_ext. intros d Hd. destruct (d * e <=? X)%nat; ring.
        * transitivity (RS (fun d => if (d <=? N)%nat then a d * b e else 0) N).
          -- apply RS_stab; [ exact HNX | ]. intros n Hn.
             replace (n <=? N)%nat with false
               by (symmetry; apply Nat.leb_nle; lia). reflexivity.
          -- rewrite <- RS_scal. apply RS_ext. intros d Hd.
             replace (d <=? N)%nat with true by (symmetry; apply Nat.leb_le; lia). ring.
    - rewrite RS_minus. f_equal.
      rewrite (RS_ext (fun e => b e * RS a N) (fun e => RS a N * b e))
        by (intros; ring).
      rewrite RS_scal. reflexivity. }
  rewrite Hkey. ring.
Qed.

Print Assumptions hyper_iter.
Print Assumptions hyper_split.

(* ================================================================= *)
(*  END HyperbolaSplit.v                                              *)
(* ================================================================= *)
