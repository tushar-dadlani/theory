(* ================================================================= *)
(*  CDyadicSum.v  —  from a zero-COUNTING bound to a SUMMABILITY        *)
(*  bound:  n(r) = O(r ln r)  ==>  sum 1/|rho|^2 bounded.              *)
(*                                                                    *)
(*    dyadic_sum_bound : if every ADMISSIBLE list of P-points of       *)
(*      < r has length <= B r, and B (2^(k+1)) <= a . (k+1) . 2^k,      *)
(*      then for EVERY admissible list s of P-points with 1 <= |x|,    *)
(*                                                                    *)
(*        sumlist (fun x => / |x|^2) s  <=  4 a.                        *)
(*                                                                    *)
(*  This is the genus-1 convergence input for the Hadamard product:     *)
(*  the product over zeros converges precisely because sum 1/|rho|^2    *)
(*  does, and that in turn is the dyadic regrouping                     *)
(*                                                                    *)
(*     sum_{2^k <= |x| < 2^{k+1}} 1/|x|^2  <=  B(2^{k+1}) . 4^{-k}      *)
(*                                        <=  a (k+1) 2^k . 4^{-k}      *)
(*                                         =  a (k+1) 2^{-k},           *)
(*                                                                    *)
(*  and sum_k (k+1) 2^{-k} = 4 exactly (Gser_closed below gives the     *)
(*  partial sums in closed form, 4 - 2(K+2)/2^K).                       *)
(*                                                                    *)
(*  Everything is stated for FINITE lists, with a bound uniform over    *)
(*  them.  That is deliberate: it avoids having to first enumerate the  *)
(*  zero set as a single sequence -- a global enumeration the           *)
(*  development does not yet have, and does not need for this step.     *)
(*  Axiom-clean.                                                       *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia List.
Require Import ComplexField Cmodulus.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  A.  sums over a list                                              *)
(* ----------------------------------------------------------------- *)
Fixpoint sumlist (f : C -> R) (l : list C) : R :=
  match l with
  | nil => 0
  | x :: t => f x + sumlist f t
  end.

Lemma sumlist_split : forall (f : C -> R) (p : C -> bool) (l : list C),
  sumlist f l
  = sumlist f (filter p l) + sumlist f (filter (fun x => negb (p x)) l).
Proof.
  intros f p l. induction l as [| x l' IH]; simpl.
  - ring.
  - destruct (p x); simpl; rewrite IH; ring.
Qed.

Lemma sumlist_le_count : forall (f : C -> R) (l : list C) (b : R),
  (forall x, In x l -> f x <= b) ->
  sumlist f l <= INR (length l) * b.
Proof.
  intros f l b Hb. induction l as [| x l' IH]; cbn [sumlist length].
  - change (INR 0) with 0. lra.
  - rewrite S_INR.
    assert (Hrest : sumlist f l' <= INR (length l') * b)
      by (apply IH; intros y Hy; apply Hb; right; exact Hy).
    pose proof (Hb x (or_introl eq_refl)). lra.
Qed.

(* the largest modulus occurring in a list *)
Fixpoint maxmod (l : list C) : R :=
  match l with
  | nil => 0
  | x :: t => Rmax (Cmod x) (maxmod t)
  end.

Lemma maxmod_ub : forall (l : list C) (x : C), In x l -> Cmod x <= maxmod l.
Proof.
  induction l as [| y l' IH]; intros x Hx; [ destruct Hx | ].
  simpl. destruct Hx as [E | Hx'].
  - subst y. apply Rmax_l.
  - apply Rle_trans with (maxmod l'); [ apply IH; exact Hx' | apply Rmax_r ].
Qed.

(* ----------------------------------------------------------------- *)
(*  B.  the model series  sum_{k<K} (k+1) 2^{-k}                       *)
(* ----------------------------------------------------------------- *)
Fixpoint Gser (K : nat) : R :=
  match K with
  | O => 0
  | S k => Gser k + INR (S k) * / 2 ^ k
  end.

Lemma pow2_pos : forall k : nat, 0 < 2 ^ k.
Proof. intro k; apply pow_lt; lra. Qed.

Lemma Gser_closed : forall K : nat, Gser K = 4 - 2 * (INR K + 2) / 2 ^ K.
Proof.
  induction K as [| K IH].
  - cbn [Gser pow]. change (INR 0) with 0. lra.
  - assert (HK : 0 < 2 ^ K) by apply pow2_pos.
    assert (Hp : 2 ^ S K = 2 * 2 ^ K) by (cbn [pow]; ring).
    cbn [Gser]. rewrite IH, Hp, !S_INR. field. lra.
Qed.

Lemma Gser_le4 : forall K : nat, Gser K <= 4.
Proof.
  intro K. rewrite Gser_closed.
  pose proof (pow2_pos K) as HK. pose proof (pos_INR K) as HN.
  assert (0 <= 2 * (INR K + 2) / 2 ^ K)
    by (apply Rle_mult_inv_pos; lra).
  lra.
Qed.

(* ----------------------------------------------------------------- *)
(*  C.  the dyadic regrouping                                          *)
(* ----------------------------------------------------------------- *)
Definition invsq (x : C) : R := / (Cmod x) ^ 2.

Section Dyadic.

Variable P : C -> Prop.
Variable B : R -> R.

(* The admissibility predicate on lists.  It was NoDup, but the Hadamard
   product repeats each zero according to MULTIPLICITY, so the counting
   input has to admit repeats.  All the dyadic argument ever needs of it
   is closure under filter -- exactly what NoDup_filter provided. *)
Variable Q : list C -> Prop.
Hypothesis Qfilter : forall (p : C -> bool) (s : list C), Q s -> Q (filter p s).

Hypothesis Hcount : forall (r : R) (s : list C),
  0 < r -> Q s ->
  (forall x, In x s -> P x) ->
  (forall x, In x s -> Cmod x < r) ->
  INR (length s) <= B r.

Fixpoint Dsum (K : nat) : R :=
  match K with
  | O => 0
  | S k => Dsum k + B (2 ^ (S k)) * / 4 ^ k
  end.

Lemma pow4_pos : forall k : nat, 0 < 4 ^ k.
Proof. intro k; apply pow_lt; lra. Qed.

Lemma four_pow : forall k : nat, 4 ^ k = 2 ^ k * 2 ^ k.
Proof.
  intro k. replace 4 with (2 * 2) by ring. apply Rpow_mult_distr.
Qed.

Lemma dyadic_bounded : forall (K : nat) (s : list C),
  Q s ->
  (forall x, In x s -> P x) ->
  (forall x, In x s -> 1 <= Cmod x < 2 ^ K) ->
  sumlist invsq s <= Dsum K.
Proof.
  induction K as [| K IH]; intros s Hnd HP Hrange.
  - (* 1 <= |x| < 1 is empty *)
    destruct s as [| x t]; [ simpl; lra | exfalso ].
    destruct (Hrange x (or_introl eq_refl)) as [H1 H2]. simpl in H2. lra.
  - set (p := fun x : C => if Rlt_dec (Cmod x) (2 ^ K) then true else false).
    rewrite (sumlist_split invsq p s).
    (* the inner bucket, by induction *)
    assert (Hin1 : sumlist invsq (filter p s) <= Dsum K).
    { apply IH.
      - apply Qfilter; exact Hnd.
      - intros x Hx. apply HP. exact (proj1 (proj1 (filter_In p x s) Hx)).
      - intros x Hx.
        destruct (proj1 (filter_In p x s) Hx) as [Hxs Hpx].
        split; [ exact (proj1 (Hrange x Hxs)) | ].
        unfold p in Hpx. destruct (Rlt_dec (Cmod x) (2 ^ K)) as [Hlt | _];
          [ exact Hlt | discriminate ]. }
    (* the outer bucket: every term is at most 4^{-K}, and there are few *)
    assert (Hin2 : sumlist invsq (filter (fun x => negb (p x)) s)
                   <= B (2 ^ (S K)) * / 4 ^ K).
    { pose proof (pow4_pos K) as H4. pose proof (pow2_pos K) as H2.
      set (t := filter (fun x => negb (p x)) s).
      assert (Hmem : forall x, In x t -> In x s /\ 2 ^ K <= Cmod x).
      { intros x Hx. destruct (proj1 (filter_In _ x s) Hx) as [Hxs Hnp].
        split; [ exact Hxs | ]. unfold p in Hnp.
        destruct (Rlt_dec (Cmod x) (2 ^ K)) as [_ | Hge];
          [ discriminate | lra ]. }
      assert (Hterm : forall x, In x t -> invsq x <= / 4 ^ K).
      { intros x Hx. destruct (Hmem x Hx) as [_ Hge]. unfold invsq.
        apply Rinv_le_contravar; [ lra | ].
        rewrite four_pow. replace (Cmod x ^ 2) with (Cmod x * Cmod x) by ring.
        apply Rmult_le_compat; lra. }
      assert (Hlen : INR (length t) <= B (2 ^ (S K))).
      { apply (Hcount (2 ^ (S K))).
        - apply pow2_pos.
        - apply Qfilter; exact Hnd.
        - intros x Hx. apply HP. exact (proj1 (Hmem x Hx)).
        - intros x Hx. exact (proj2 (Hrange x (proj1 (Hmem x Hx)))). }
      apply Rle_trans with (INR (length t) * / 4 ^ K).
      - apply sumlist_le_count; exact Hterm.
      - apply Rmult_le_compat_r; [ left; apply Rinv_0_lt_compat; exact H4
                                 | exact Hlen ]. }
    change (Dsum (S K)) with (Dsum K + B (2 ^ (S K)) * / 4 ^ K). lra.
Qed.

(* the growth hypothesis: B (2^{k+1}) grows like a . (k+1) . 2^k *)
Variable a : R.
Hypothesis Ha : 0 <= a.
Hypothesis Hgrow : forall k : nat, B (2 ^ (S k)) <= a * INR (S k) * 2 ^ k.

Lemma Dsum_le_aG : forall K : nat, Dsum K <= a * Gser K.
Proof.
  induction K as [| K IH].
  - simpl. lra.
  - change (Dsum (S K)) with (Dsum K + B (2 ^ (S K)) * / 4 ^ K).
    change (Gser (S K)) with (Gser K + INR (S K) * / 2 ^ K).
    pose proof (pow4_pos K) as H4. pose proof (pow2_pos K) as H2.
    assert (Hstep : B (2 ^ (S K)) * / 4 ^ K <= a * (INR (S K) * / 2 ^ K)).
    { apply Rle_trans with (a * INR (S K) * 2 ^ K * / 4 ^ K).
      - apply Rmult_le_compat_r;
          [ left; apply Rinv_0_lt_compat; exact H4 | apply Hgrow ].
      - rewrite four_pow. apply Req_le. field. lra. }
    lra.
Qed.

Theorem dyadic_sum_bound : forall s : list C,
  Q s ->
  (forall x, In x s -> P x) ->
  (forall x, In x s -> 1 <= Cmod x) ->
  sumlist invsq s <= 4 * a.
Proof.
  intros s Hnd HP Hlow.
  (* every list is inside SOME dyadic disk *)
  assert (Habs2 : Rabs 2 > 1) by (rewrite Rabs_pos_eq; lra).
  destruct (Pow_x_infinity 2 Habs2 (maxmod s + 1)) as [N HN].
  pose proof (HN N (le_n N)) as HNn.
  rewrite Rabs_pos_eq in HNn by (apply pow_le; lra).
  assert (Hrange : forall x, In x s -> 1 <= Cmod x < 2 ^ N).
  { intros x Hx. split; [ apply Hlow; exact Hx | ].
    pose proof (maxmod_ub s x Hx). lra. }
  apply Rle_trans with (Dsum N); [ apply dyadic_bounded; assumption | ].
  apply Rle_trans with (a * Gser N); [ apply Dsum_le_aG | ].
  pose proof (Gser_le4 N).
  apply Rle_trans with (a * 4); [ apply Rmult_le_compat_l; assumption | lra ].
Qed.

End Dyadic.

Print Assumptions dyadic_sum_bound.
