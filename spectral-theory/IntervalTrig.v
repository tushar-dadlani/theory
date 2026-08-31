(* ================================================================= *)
(*  IntervalTrig.v  --  cos and sin of an INTERVAL argument.          *)
(*                                                                    *)
(*  IntervalCos.Icos_pt already handles arbitrarily large rational     *)
(*  arguments by double-angle halving, so no reduction mod 2 pi is     *)
(*  needed.  What is missing is that the arguments we must feed it     *)
(*  (t * ln m) are themselves only known to an interval.               *)
(*                                                                    *)
(*  Since |cos' | <= 1 and |sin'| <= 1, one MVT gives the Lipschitz    *)
(*  bound |cos a - cos b| <= |a - b|, so evaluating at the midpoint    *)
(*  and widening by the radius is sound -- and costs nothing, because  *)
(*  the radius is already the accuracy we are carrying.                *)
(*                                                                    *)
(*  sin is then cos(x - pi/2), against the certified pi/2 of           *)
(*  IntervalAtan.                                                     *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia Qreals QArith.
Require Import IntervalArith IntervalCos IntervalAtan CertifiedPi.
Open Scope R_scope.

(* ---- Lipschitz ---- *)

Lemma cos_lip : forall a b, Rabs (cos a - cos b) <= Rabs (a - b).
Proof.
  intros a b.
  assert (Key : forall u v, u < v -> Rabs (cos u - cos v) <= Rabs (u - v)).
  { intros u v Huv.
    destruct (MVT_cor2 cos (fun x => - sin x) u v Huv
                (fun c _ => derivable_pt_lim_cos c)) as [c [Hc _]].
    assert (Hs : Rabs (- sin c) <= 1).
    { pose proof (SIN_bound c). apply Rabs_le. lra. }
    assert (E : Rabs (cos u - cos v) = Rabs (cos v - cos u))
      by (rewrite <- Rabs_Ropp; f_equal; ring).
    rewrite E, Hc, Rabs_mult.
    assert (Hp : 0 <= Rabs (v - u)) by apply Rabs_pos.
    assert (E2 : Rabs (v - u) = Rabs (u - v))
      by (rewrite <- Rabs_Ropp; f_equal; ring).
    rewrite E2 in *. nra. }
  destruct (Rtotal_order a b) as [H | [H | H]].
  - apply Key; exact H.
  - subst. replace (cos b - cos b) with 0 by ring.
    replace (b - b) with 0 by ring. rewrite Rabs_R0. apply Rle_refl.
  - assert (E : Rabs (cos a - cos b) = Rabs (cos b - cos a))
      by (rewrite <- Rabs_Ropp; f_equal; ring).
    assert (E2 : Rabs (a - b) = Rabs (b - a))
      by (rewrite <- Rabs_Ropp; f_equal; ring).
    rewrite E, E2. apply Key. lra.
Qed.

(* ---- midpoint and radius ---- *)

Definition Imid (j : Itv) : Q := (ilo j + ihi j) / 2.
Definition Irad (j : Itv) : Q := (ihi j - ilo j) / 2.

Lemma Q2R_Imid : forall j, Q2R (Imid j) = (Q2R (ilo j) + Q2R (ihi j)) / 2.
Proof.
  intro j. unfold Imid. rewrite Q2R_div by (apply Qne0_of_R; rewrite Q2R_two; lra).
  rewrite Q2R_plus, Q2R_two. reflexivity.
Qed.

Lemma Q2R_Irad : forall j, Q2R (Irad j) = (Q2R (ihi j) - Q2R (ilo j)) / 2.
Proof.
  intro j. unfold Irad. rewrite Q2R_div by (apply Qne0_of_R; rewrite Q2R_two; lra).
  rewrite Q2R_minus, Q2R_two. reflexivity.
Qed.

Lemma mid_rad : forall j x, Icontains j x ->
  Rabs (x - Q2R (Imid j)) <= Q2R (Irad j).
Proof.
  intros j x [H1 H2]. rewrite Q2R_Imid, Q2R_Irad.
  apply Rabs_le. lra.
Qed.

(* ---- cos of an interval ---- *)

Definition Icos_itv (p m n : nat) (j : Itv) : Itv :=
  Iadd (Icos_pt p m n (Imid j)) (mkI (Qopp (Irad j)) (Irad j)).

Theorem Icos_itv_sound : forall p m n j x,
  Icontains j x ->
  - PI / 2 <= Q2R (Imid j) / INR (2 ^ m) ->
  Q2R (Imid j) / INR (2 ^ m) <= PI / 2 ->
  Icontains (Icos_itv p m n j) (cos x).
Proof.
  intros p m n j x Hx Hlo Hhi. unfold Icos_itv.
  replace (cos x) with (cos (Q2R (Imid j)) + (cos x - cos (Q2R (Imid j))))
    by ring.
  apply Iadd_sound; [ apply Icos_pt_sound; assumption | ].
  assert (H : Rabs (cos x - cos (Q2R (Imid j))) <= Q2R (Irad j)).
  { eapply Rle_trans; [ apply cos_lip | apply mid_rad; exact Hx ]. }
  unfold Icontains; simpl. rewrite Q2R_opp.
  assert (H1 : cos x - cos (Q2R (Imid j)) <= Rabs (cos x - cos (Q2R (Imid j))))
    by apply Rle_abs.
  assert (H2 : - (cos x - cos (Q2R (Imid j)))
               <= Rabs (cos x - cos (Q2R (Imid j))))
    by (rewrite <- Rabs_Ropp; apply Rle_abs).
  lra.
Qed.

(* ---- sin of an interval, as cos(x - pi/2) ---- *)

Lemma sin_as_cos : forall x, sin x = cos (x - PI / 2).
Proof.
  intro x. replace (x - PI / 2) with (- (PI / 2 - x)) by ring.
  rewrite cos_neg, cos_shift. reflexivity.
Qed.

Definition Isin_itv (p m n : nat) (j : Itv) : Itv :=
  Icos_itv p m n (Isub j Ihalfpi).

Theorem Isin_itv_sound : forall p m n j x,
  Icontains j x ->
  - PI / 2 <= Q2R (Imid (Isub j Ihalfpi)) / INR (2 ^ m) ->
  Q2R (Imid (Isub j Ihalfpi)) / INR (2 ^ m) <= PI / 2 ->
  Icontains (Isin_itv p m n j) (sin x).
Proof.
  intros p m n j x Hx Hlo Hhi. unfold Isin_itv.
  rewrite sin_as_cos.
  apply Icos_itv_sound; [ | exact Hlo | exact Hhi ].
  apply Isub_sound; [ exact Hx | apply Ihalfpi_sound ].
Qed.
