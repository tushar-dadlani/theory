(* ================================================================= *)
(*  CDyadicSum2.v  —  two more dyadic sums off the SAME counting        *)
(*  hypothesis, both needed for the minimum modulus of the product.     *)
(*                                                                    *)
(*    dyadic_sum_inv1 : SUM 1/|x| over the zeros of modulus < 2^K       *)
(*      is at most a . K(K+1)/2  --  i.e. O(ln^2 r).  The FIRST power   *)
(*      diverges, so unlike CDyadicSum this one has to be cut off; the  *)
(*      cut-off is exactly what the near-zero block of the product      *)
(*      needs.                                                         *)
(*                                                                    *)
(*    dyadic_sum_tail : SUM 1/|x|^2 over the zeros of modulus >= 2^K    *)
(*      is at most a . 2(K+2)/2^K  --  i.e. O(ln r / r).  This is the   *)
(*      far-zero block, where 1/|x|^2 is summable and only the RATE     *)
(*      matters.                                                       *)
(*                                                                    *)
(*  Neither needs a new counting input.  Both are the same regrouping   *)
(*  as dyadic_sum_bound against a different model series:               *)
(*    * for the first power the annulus 2^k <= |x| < 2^{k+1} gives      *)
(*      B(2^{k+1})/2^k <= a(k+1), an ARITHMETIC progression, summing to *)
(*      a K(K+1)/2 -- no geometric factor survives, which is exactly    *)
(*      why the first power diverges;                                  *)
(*    * for the tail it is Gser's own tail, and Gser_closed already     *)
(*      gives that in closed form: 4 - Gser K = 2(K+2)/2^K.             *)
(*                                                                    *)
(*  Working with 1/|x| rather than a fractional power 1/|x|^{3/2} is    *)
(*  deliberate: it keeps every constant rational and avoids Rpower      *)
(*  entirely.  The o(r^2) slack is wide enough to absorb the loss.      *)
(*  Axiom-clean.                                                       *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia List.
Require Import ComplexField Cmodulus CDyadicSum.
Open Scope R_scope.

Definition invmod (x : C) : R := / Cmod x.

(* the arithmetic model series  sum_{k<K} (k+1) *)
Fixpoint Aser (K : nat) : R :=
  match K with O => 0 | S k => Aser k + INR (S k) end.

Lemma Aser_closed : forall K : nat, Aser K = INR K * (INR K + 1) / 2.
Proof.
  induction K as [| K IH]; cbn [Aser].
  - change (INR 0) with 0. lra.
  - rewrite IH, !S_INR. field.
Qed.

Section Dyadic2.

Variable P : C -> Prop.
Variable B : R -> R.
Variable Q : list C -> Prop.
Hypothesis Qfilter : forall (p : C -> bool) (s : list C), Q s -> Q (filter p s).

Hypothesis Hcount : forall (r : R) (s : list C),
  0 < r -> Q s ->
  (forall x, In x s -> P x) ->
  (forall x, In x s -> Cmod x < r) ->
  INR (length s) <= B r.

Variable a : R.
Hypothesis Ha : 0 <= a.
Hypothesis Hgrow : forall k : nat, B (2 ^ (S k)) <= a * INR (S k) * 2 ^ k.

(* ----------------------------------------------------------------- *)
(*  A.  the first power, cut off at 2^K                                *)
(* ----------------------------------------------------------------- *)
Theorem dyadic_sum_inv1 : forall (K : nat) (s : list C),
  Q s ->
  (forall x, In x s -> P x) ->
  (forall x, In x s -> 1 <= Cmod x < 2 ^ K) ->
  sumlist invmod s <= a * Aser K.
Proof.
  induction K as [| K IH]; intros s Hq HP Hrange.
  - destruct s as [| x t]; [ cbn [sumlist Aser]; lra | exfalso ].
    destruct (Hrange x (or_introl eq_refl)) as [H1 H2]. cbn [pow] in H2. lra.
  - set (p := fun x : C => if Rlt_dec (Cmod x) (2 ^ K) then true else false).
    rewrite (sumlist_split invmod p s).
    pose proof (pow2_pos K) as H2.
    assert (Hin1 : sumlist invmod (filter p s) <= a * Aser K).
    { apply IH.
      - apply Qfilter; exact Hq.
      - intros x Hx. apply HP. exact (proj1 (proj1 (filter_In p x s) Hx)).
      - intros x Hx.
        destruct (proj1 (filter_In p x s) Hx) as [Hxs Hpx].
        split; [ exact (proj1 (Hrange x Hxs)) | ].
        unfold p in Hpx. destruct (Rlt_dec (Cmod x) (2 ^ K)) as [Hlt | _];
          [ exact Hlt | discriminate ]. }
    assert (Hin2 : sumlist invmod (filter (fun x => negb (p x)) s)
                   <= a * INR (S K)).
    { set (t := filter (fun x => negb (p x)) s).
      assert (Hmem : forall x, In x t -> In x s /\ 2 ^ K <= Cmod x).
      { intros x Hx. destruct (proj1 (filter_In _ x s) Hx) as [Hxs Hnp].
        split; [ exact Hxs | ]. unfold p in Hnp.
        destruct (Rlt_dec (Cmod x) (2 ^ K)) as [_ | Hge];
          [ discriminate | lra ]. }
      assert (Hterm : forall x, In x t -> invmod x <= / 2 ^ K).
      { intros x Hx. destruct (Hmem x Hx) as [_ Hge]. unfold invmod.
        apply Rinv_le_contravar; lra. }
      assert (Hlen : INR (length t) <= B (2 ^ (S K))).
      { apply (Hcount (2 ^ (S K))).
        - apply pow2_pos.
        - apply Qfilter; exact Hq.
        - intros x Hx. apply HP. exact (proj1 (Hmem x Hx)).
        - intros x Hx. exact (proj2 (Hrange x (proj1 (Hmem x Hx)))). }
      apply Rle_trans with (INR (length t) * / 2 ^ K).
      - apply sumlist_le_count; exact Hterm.
      - apply Rle_trans with (B (2 ^ (S K)) * / 2 ^ K).
        + apply Rmult_le_compat_r;
            [ left; apply Rinv_0_lt_compat; exact H2 | exact Hlen ].
        + apply Rle_trans with (a * INR (S K) * 2 ^ K * / 2 ^ K).
          * apply Rmult_le_compat_r;
              [ left; apply Rinv_0_lt_compat; exact H2 | apply Hgrow ].
          * apply Req_le. field. lra. }
    cbn [Aser]. lra.
Qed.

(* ----------------------------------------------------------------- *)
(*  B.  the square tail, from 2^K outwards                             *)
(* ----------------------------------------------------------------- *)
Lemma dyadic_tail_range : forall (K N : nat), (K <= N)%nat ->
  forall s : list C,
  Q s ->
  (forall x, In x s -> P x) ->
  (forall x, In x s -> 2 ^ K <= Cmod x < 2 ^ N) ->
  sumlist invsq s <= a * (Gser N - Gser K).
Proof.
  intros K N. revert K. induction N as [| N IH]; intros K HKN s Hq HP Hrange.
  - assert (HK : K = 0%nat) by lia. subst K.
    destruct s as [| x t]; [ cbn [sumlist]; lra | exfalso ].
    destruct (Hrange x (or_introl eq_refl)) as [H1 H2]. lra.
  - destruct (Nat.eq_dec K (S N)) as [HeqK | HneK].
    + subst K.
      destruct s as [| x t]; [ cbn [sumlist]; lra | exfalso ].
      destruct (Hrange x (or_introl eq_refl)) as [H1 H2]. lra.
    + assert (HKN' : (K <= N)%nat) by lia.
      set (p := fun x : C => if Rlt_dec (Cmod x) (2 ^ N) then true else false).
      rewrite (sumlist_split invsq p s).
      pose proof (pow2_pos N) as H2. pose proof (pow4_pos N) as H4.
      assert (Hin1 : sumlist invsq (filter p s) <= a * (Gser N - Gser K)).
      { apply IH; [ exact HKN' | apply Qfilter; exact Hq | | ].
        - intros x Hx. apply HP. exact (proj1 (proj1 (filter_In p x s) Hx)).
        - intros x Hx.
          destruct (proj1 (filter_In p x s) Hx) as [Hxs Hpx].
          split; [ exact (proj1 (Hrange x Hxs)) | ].
          unfold p in Hpx. destruct (Rlt_dec (Cmod x) (2 ^ N)) as [Hlt | _];
            [ exact Hlt | discriminate ]. }
      assert (Hin2 : sumlist invsq (filter (fun x => negb (p x)) s)
                     <= a * (INR (S N) * / 2 ^ N)).
      { set (t := filter (fun x => negb (p x)) s).
        assert (Hmem : forall x, In x t -> In x s /\ 2 ^ N <= Cmod x).
        { intros x Hx. destruct (proj1 (filter_In _ x s) Hx) as [Hxs Hnp].
          split; [ exact Hxs | ]. unfold p in Hnp.
          destruct (Rlt_dec (Cmod x) (2 ^ N)) as [_ | Hge];
            [ discriminate | lra ]. }
        assert (Hterm : forall x, In x t -> invsq x <= / 4 ^ N).
        { intros x Hx. destruct (Hmem x Hx) as [_ Hge]. unfold invsq.
          apply Rinv_le_contravar; [ lra | ].
          rewrite four_pow. replace (Cmod x ^ 2) with (Cmod x * Cmod x) by ring.
          apply Rmult_le_compat; lra. }
        assert (Hlen : INR (length t) <= B (2 ^ (S N))).
        { apply (Hcount (2 ^ (S N))).
          - apply pow2_pos.
          - apply Qfilter; exact Hq.
          - intros x Hx. apply HP. exact (proj1 (Hmem x Hx)).
          - intros x Hx. exact (proj2 (Hrange x (proj1 (Hmem x Hx)))). }
        apply Rle_trans with (INR (length t) * / 4 ^ N).
        - apply sumlist_le_count; exact Hterm.
        - apply Rle_trans with (B (2 ^ (S N)) * / 4 ^ N).
          + apply Rmult_le_compat_r;
              [ left; apply Rinv_0_lt_compat; exact H4 | exact Hlen ].
          + apply Rle_trans with (a * INR (S N) * 2 ^ N * / 4 ^ N).
            * apply Rmult_le_compat_r;
                [ left; apply Rinv_0_lt_compat; exact H4 | apply Hgrow ].
            * apply Req_le. rewrite four_pow. field. lra. }
      change (Gser (S N)) with (Gser N + INR (S N) * / 2 ^ N). lra.
Qed.

Theorem dyadic_sum_tail : forall (K N : nat), (K <= N)%nat ->
  forall s : list C,
  Q s ->
  (forall x, In x s -> P x) ->
  (forall x, In x s -> 2 ^ K <= Cmod x < 2 ^ N) ->
  sumlist invsq s <= a * (2 * (INR K + 2) / 2 ^ K).
Proof.
  intros K N HKN s Hq HP Hrange.
  apply Rle_trans with (a * (Gser N - Gser K));
    [ exact (dyadic_tail_range K N HKN s Hq HP Hrange) | ].
  apply Rmult_le_compat_l; [ exact Ha | ].
  pose proof (Gser_le4 N) as H4. rewrite (Gser_closed K). lra.
Qed.

End Dyadic2.

Print Assumptions dyadic_sum_inv1.
Print Assumptions dyadic_sum_tail.
