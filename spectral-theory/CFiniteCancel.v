(* ================================================================= *)
(*  CFiniteCancel.v  —  cancelling a polynomial factor.                *)
(*                                                                    *)
(*    prodfac_cancel : prodfac l . A = prodfac l . B  pointwise, with  *)
(*      A and B continuous, forces A = B EVERYWHERE -- including at    *)
(*      the points of l, where the factor vanishes and the algebra     *)
(*      gives nothing.                                                 *)
(*                                                                    *)
(*  This is the missing link in the glue.  Two cofactors Gseq M and    *)
(*  Gseq N of the SAME xi are related only through xi, so extracting   *)
(*  their ratio means dividing by a product of linear factors -- legal *)
(*  off the zeros, silent at them.  Continuity closes the gap: a       *)
(*  finite list is nowhere dense, so every point of it is a limit of   *)
(*  points off it.                                                    *)
(*                                                                    *)
(*  The one geometric input is sep_exists: around any w, a finite list *)
(*  leaves a punctured ball free.  Proved by induction, with the       *)
(*  classical case split x = w or not -- fine, the statement is a Prop *)
(*  and no data is extracted from it.  The approach direction is the   *)
(*  real axis, which costs nothing: only the distance to w matters.    *)
(*  Axiom-clean.                                                       *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia List Classical_Prop.
Require Import ComplexField Cmodulus Holomorphic CDeriv
        JensenMultiZero CZeroListFactor CGoursatConv.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  A.  a finite list leaves a punctured ball free                     *)
(* ----------------------------------------------------------------- *)
Lemma Cmod_pos_ne : forall a b, a <> b -> 0 < Cmod (Cminus a b).
Proof.
  intros a b Hne.
  destruct (Rle_lt_or_eq_dec 0 (Cmod (Cminus a b)) (Cmod_nonneg _)) as [Hlt | Heq];
    [ exact Hlt | ].
  exfalso. apply Hne.
  assert (Hz : Cminus a b = C0) by (apply (proj1 (Cmod0 _)); lra).
  assert (Ha : a = Cadd (Cminus a b) b) by ring.
  rewrite Hz in Ha. rewrite Ha. ring.
Qed.

Lemma sep_exists : forall (l : list C) (w : C),
  exists d, 0 < d /\ forall x, In x l -> x <> w -> d <= Cmod (Cminus x w).
Proof.
  induction l as [| x l' IH]; intro w.
  - exists 1. split; [ lra | intros y Hy; destruct Hy ].
  - destruct (IH w) as [d' [Hd' Hb']].
    destruct (classic (x = w)) as [Hxw | Hxw].
    + exists d'. split; [ exact Hd' | ].
      intros y Hy Hyw. destruct Hy as [Hy | Hy];
        [ exfalso; apply Hyw; rewrite <- Hy; exact Hxw | apply Hb'; assumption ].
    + exists (Rmin d' (Cmod (Cminus x w))). split.
      * apply Rmin_pos; [ exact Hd' | apply Cmod_pos_ne; exact Hxw ].
      * intros y Hy Hyw. destruct Hy as [Hy | Hy].
        -- rewrite <- Hy. apply Rmin_r.
        -- apply Rle_trans with d'; [ apply Rmin_l | apply Hb'; assumption ].
Qed.

(* ----------------------------------------------------------------- *)
(*  B.  continuous functions agreeing off a finite list agree          *)
(* ----------------------------------------------------------------- *)
Lemma ptcont_eq_off_finite : forall (l : list C) (A B : C -> C),
  ptcont A -> ptcont B ->
  (forall z, ~ In z l -> A z = B z) ->
  forall w, A w = B w.
Proof.
  intros l A B HA HB Hoff w.
  (* the difference has modulus below every eps, hence is C0 *)
  assert (Hsmall : forall eps, 0 < eps -> Cmod (Cminus (A w) (B w)) < eps).
  { intros eps Heps.
    destruct (HA w (eps / 2) ltac:(lra)) as [dA [HdA HbA]].
    destruct (HB w (eps / 2) ltac:(lra)) as [dB [HdB HbB]].
    destruct (sep_exists l w) as [d [Hd Hbd]].
    set (t := Rmin (Rmin dA dB) d / 2).
    assert (Ht : 0 < t)
      by (unfold t; apply Rdiv_lt_0_compat; [ apply Rmin_pos; [ apply Rmin_pos | ] | ]; lra).
    assert (HtA : t < dA)
      by (unfold t; pose proof (Rmin_l (Rmin dA dB) d); pose proof (Rmin_l dA dB); lra).
    assert (HtB : t < dB)
      by (unfold t; pose proof (Rmin_l (Rmin dA dB) d); pose proof (Rmin_r dA dB); lra).
    assert (Htd : t < d)
      by (unfold t; pose proof (Rmin_r (Rmin dA dB) d); lra).
    set (z' := Cadd w (RtoC t)).
    assert (Hdist : Cmod (Cminus z' w) = t).
    { replace (Cminus z' w) with (RtoC t) by (unfold z'; ring).
      rewrite Cmod_RtoC. apply Rabs_right; lra. }
    (* z' misses the list *)
    assert (Hnotin : ~ In z' l).
    { intro Hin.
      destruct (classic (z' = w)) as [Hzw | Hzw].
      - assert (Hc : Cmod (Cminus z' w) = 0)
          by (apply (proj2 (Cmod0 _)); rewrite Hzw; ring).
        rewrite Hdist in Hc. lra.
      - pose proof (Hbd z' Hin Hzw) as Hge. rewrite Hdist in Hge. lra. }
    pose proof (Hoff z' Hnotin) as Heq.
    assert (Hz'w : Cmod (Cminus z' w) < dA) by (rewrite Hdist; exact HtA).
    assert (Hz'wB : Cmod (Cminus z' w) < dB) by (rewrite Hdist; exact HtB).
    pose proof (HbA z' Hz'w) as HAd.
    pose proof (HbB z' Hz'wB) as HBd.
    assert (Hsplit : Cminus (A w) (B w)
                     = Cadd (Copp (Cminus (A z') (A w)))
                            (Cadd (Cminus (A z') (B z')) (Cminus (B z') (B w))))
      by ring.
    rewrite Hsplit.
    eapply Rle_lt_trans; [ apply Cmod_triangle | ].
    rewrite Cmod_opp.
    assert (Hmid : Cmod (Cadd (Cminus (A z') (B z')) (Cminus (B z') (B w)))
                   <= Cmod (Cminus (A z') (B z')) + Cmod (Cminus (B z') (B w)))
      by apply Cmod_triangle.
    assert (Hzero : Cmod (Cminus (A z') (B z')) = 0)
      by (apply (proj2 (Cmod0 _)); rewrite Heq; ring).
    lra. }
  (* below every eps and nonnegative forces zero *)
  assert (Hz : Cminus (A w) (B w) = C0).
  { apply (proj1 (Cmod0 _)).
    destruct (Rle_lt_or_eq_dec 0 (Cmod (Cminus (A w) (B w))) (Cmod_nonneg _))
      as [Hlt | Heq]; [ | lra ].
    exfalso. pose proof (Hsmall _ Hlt). lra. }
  assert (HA' : A w = Cadd (Cminus (A w) (B w)) (B w)) by ring.
  rewrite Hz in HA'. rewrite HA'. ring.
Qed.

(* ----------------------------------------------------------------- *)
(*  C.  the cancellation                                               *)
(* ----------------------------------------------------------------- *)
Theorem prodfac_cancel : forall (l : list C) (A B : C -> C),
  ptcont A -> ptcont B ->
  (forall z, Cmul (prodfac l z) (A z) = Cmul (prodfac l z) (B z)) ->
  forall z, A z = B z.
Proof.
  intros l A B HA HB Hid.
  apply (ptcont_eq_off_finite l A B HA HB).
  intros z Hnotin.
  pose proof (prodfac_ne0_notin l z Hnotin) as Hne.
  apply (Cmul_cancel_l (prodfac l z)); [ exact Hne | exact (Hid z) ].
Qed.

Print Assumptions prodfac_cancel.
