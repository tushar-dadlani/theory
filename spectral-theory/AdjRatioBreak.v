(* ================================================================= *)
(*  AdjRatioBreak.v  —  Adj G breaks ratio 1: a group-like with no      *)
(*  inverse (bialgebra, not Hopf).                                      *)
(*                                                                    *)
(*  In Z[Adj G] the group-likes are all the deltas delta_x, x in Adj G  *)
(*  (grouplike_iff_delta), so they number |Adj G| = |G| + 1 (adj_card): *)
(*  the group G PLUS the adjoined absorbing point AZero.  But delta_AZero *)
(*  -- though group-like (azero_grouplike) -- has NO convolution inverse *)
(*  (azero_no_inverse): b * delta_AZero = e is impossible because       *)
(*  x * delta_AZero = eps(x) * delta_AZero  (gconv_zero_absorb) and       *)
(*  delta_AZero(e) = 0.  So the group-like MONOID is not a group: the     *)
(*  invertible ones are (at most) the |G| deltas over G, one short of    *)
(*  all |G|+1 group-likes.  That is why Z[Adj G] is a bialgebra but       *)
(*  never Hopf -- the antipode would have to invert delta_AZero.         *)
(*  This is the first structure with operand:operator ratio > 1.         *)
(* ================================================================= *)

From Stdlib Require Import List Arith ZArith Bool Lia.
Require Import HopfGroupAlgebraGen MonoidAlgebraZero GroupLike.
Import ListNotations.
Open Scope Z_scope.

Section AdjRatioBreak.

Variable G : Type.
Variable Geq : G -> G -> bool.
Hypothesis Geq_spec : forall x y, reflect (x = y) (Geq x y).
Variable gelts : list G.
Hypothesis gelts_nodup : NoDup gelts.
Hypothesis gelts_all : forall x, In x gelts.
Variable gop : G -> G -> G.
Variable geG : G.

(* delta_AZero is a genuine group-like element of Z[Adj G] *)
Theorem azero_grouplike :
  grouplike (Adj G) (aAeq G Geq) (aelts G gelts) (delta (Adj G) (aAeq G Geq) (AZero G)).
Proof.
  apply (delta_grouplike (Adj G) (aAeq G Geq) (aAeq_spec G Geq Geq_spec)
           (aelts G gelts) (aelts_nodup G gelts gelts_nodup) (AZero G)).
  apply (aelts_all G gelts gelts_all).
Qed.

(* ...but it has NO convolution inverse: b * delta_AZero = e is impossible. *)
Theorem azero_no_inverse : forall b : Adj G -> Z,
  ~ (forall g, gconv (Adj G) (aAeq G Geq) (aelts G gelts) (aop G gop)
                 b (delta (Adj G) (aAeq G Geq) (AZero G)) g
             = gunit (Adj G) (aAeq G Geq) (ae G geG) g).
Proof.
  intros b Hinv; specialize (Hinv (ae G geG)).
  rewrite (gconv_zero_absorb G Geq Geq_spec gelts gelts_nodup gelts_all gop
             b (ae G geG)) in Hinv.
  (* delta_AZero(e) = 0  (AZero <> AElt geG) *)
  assert (Hd : delta (Adj G) (aAeq G Geq) (AZero G) (ae G geG) = 0%Z) by reflexivity.
  (* gunit(e) = 1 *)
  assert (Hu : gunit (Adj G) (aAeq G Geq) (ae G geG) (ae G geG) = 1%Z).
  { unfold gunit, ae; simpl; destruct (Geq_spec geG geG); [ reflexivity | congruence ]. }
  rewrite Hd, Hu, Z.mul_0_r in Hinv; discriminate.
Qed.

(* the ratio break, in one statement *)
Theorem adj_ratio_break :
  (* group-likes number |Adj G| = |G| + 1 (adj_card + grouplike_iff_delta) *)
  length (aelts G gelts) = S (length gelts)
  (* the extra one, delta_AZero, is group-like ... *)
  /\ grouplike (Adj G) (aAeq G Geq) (aelts G gelts)
       (delta (Adj G) (aAeq G Geq) (AZero G))
  (* ... yet has no inverse: Z[Adj G] is a bialgebra, never Hopf *)
  /\ (forall b, ~ (forall g,
        gconv (Adj G) (aAeq G Geq) (aelts G gelts) (aop G gop)
          b (delta (Adj G) (aAeq G Geq) (AZero G)) g
        = gunit (Adj G) (aAeq G Geq) (ae G geG) g)).
Proof.
  split; [ exact (adj_card G gelts) | ].
  split; [ exact azero_grouplike | exact azero_no_inverse ].
Qed.

End AdjRatioBreak.

Print Assumptions adj_ratio_break.

(* ================================================================= *)
(*  END AdjRatioBreak.v  —  Adj G is the ratio-(>1) case: all |G|+1     *)
(*  group-likes, but delta_AZero has no inverse, so it is a bialgebra   *)
(*  and not a Hopf algebra.                                             *)
(* ================================================================= *)
