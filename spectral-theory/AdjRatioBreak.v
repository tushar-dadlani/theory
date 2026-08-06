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
(*  THE POSITIVE HALF (G a group):  the INVERTIBLE group-likes are     *)
(*  EXACTLY the deltas over G, so they are  ~= G, and the ratio is      *)
(*  pinned at exactly  (|G|+1) : |G|.                                   *)
(* ================================================================= *)
Section AdjInvertibleGrouplikes.

Variable G : Type.
Variable Geq : G -> G -> bool.
Hypothesis Geq_spec : forall x y, reflect (x = y) (Geq x y).
Variable gelts : list G.
Hypothesis gelts_nodup : NoDup gelts.
Hypothesis gelts_all : forall x, In x gelts.
Variable gop : G -> G -> G.
Variable geG : G.
Hypothesis gop_assoc : forall x y z, gop (gop x y) z = gop x (gop y z).
Hypothesis gop_comm : forall x y, gop x y = gop y x.
Hypothesis gop_id_l : forall x, gop geG x = x.
Variable ginv : G -> G.
Hypothesis gop_inv_l : forall x, gop (ginv x) x = geG.

(* every group element gives an INVERTIBLE group-like:                 *)
(*   delta_{AElt g} * delta_{AElt (ginv g)} = delta_e = gunit.          *)
Theorem aelt_grouplike_invertible : forall g k,
  gconv (Adj G) (aAeq G Geq) (aelts G gelts) (aop G gop)
    (delta (Adj G) (aAeq G Geq) (AElt G g))
    (delta (Adj G) (aAeq G Geq) (AElt G (ginv g))) k
  = gunit (Adj G) (aAeq G Geq) (ae G geG) k.
Proof.
  intros g k.
  rewrite (gconv_delta (Adj G) (aAeq G Geq) (aAeq_spec G Geq Geq_spec)
             (aelts G gelts) (aelts_nodup G gelts gelts_nodup)
             (aelts_all G gelts gelts_all) (aop G gop) (AElt G g) (AElt G (ginv g)) k).
  replace (aop G gop (AElt G g) (AElt G (ginv g))) with (ae G geG).
  - symmetry; apply (gunit_delta (Adj G) (aAeq G Geq) (ae G geG) k).
  - unfold aop, ae; rewrite gop_comm, gop_inv_l; reflexivity.
Qed.

(* convolution of deltas over G mirrors G's product (the group hom) *)
Theorem delta_aelt_hom : forall g h k,
  gconv (Adj G) (aAeq G Geq) (aelts G gelts) (aop G gop)
    (delta (Adj G) (aAeq G Geq) (AElt G g)) (delta (Adj G) (aAeq G Geq) (AElt G h)) k
  = delta (Adj G) (aAeq G Geq) (AElt G (gop g h)) k.
Proof.
  intros g h k.
  rewrite (gconv_delta (Adj G) (aAeq G Geq) (aAeq_spec G Geq Geq_spec)
             (aelts G gelts) (aelts_nodup G gelts gelts_nodup)
             (aelts_all G gelts gelts_all) (aop G gop) (AElt G g) (AElt G h) k).
  reflexivity.
Qed.

(* g |-> delta_{AElt g} is injective *)
Theorem delta_aelt_inj : forall g h,
  (forall k, delta (Adj G) (aAeq G Geq) (AElt G g) k
           = delta (Adj G) (aAeq G Geq) (AElt G h) k) -> g = h.
Proof.
  intros g h H; specialize (H (AElt G g)); unfold delta in H; simpl in H.
  destruct (Geq_spec h g) as [E|_]; [ symmetry; exact E | ].
  destruct (Geq_spec g g) as [_|Hne]; [ discriminate H | congruence ].
Qed.

(* the INVERTIBLE group-likes are EXACTLY the deltas over G (not AZero) *)
Theorem invertible_grouplike_iff : forall m : Adj G,
  (exists y, forall k, gconv (Adj G) (aAeq G Geq) (aelts G gelts) (aop G gop)
                         (delta (Adj G) (aAeq G Geq) m) y k
                     = gunit (Adj G) (aAeq G Geq) (ae G geG) k)
  <-> exists g, m = AElt G g.
Proof.
  intros m; split.
  - intros [y Hy]; destruct m as [|g].
    + exfalso.
      apply (azero_no_inverse G Geq Geq_spec gelts gelts_nodup gelts_all gop geG y).
      intros g.
      rewrite (gconv_comm (Adj G) (aAeq G Geq) (aelts G gelts) (aop G gop)
                 (aop_comm G gop gop_comm) y (delta (Adj G) (aAeq G Geq) (AZero G)) g).
      apply Hy.
    + exists g; reflexivity.
  - intros [g ->]; exists (delta (Adj G) (aAeq G Geq) (AElt G (ginv g)));
      intros k; apply aelt_grouplike_invertible.
Qed.

(* the pinned ratio: (|G|+1) group-likes, exactly |G| invertible ~= G *)
Theorem invertible_grouplikes_iso_G :
  (* hom: convolution mirrors G's product *)
  (forall g h k, gconv (Adj G) (aAeq G Geq) (aelts G gelts) (aop G gop)
      (delta (Adj G) (aAeq G Geq) (AElt G g)) (delta (Adj G) (aAeq G Geq) (AElt G h)) k
    = delta (Adj G) (aAeq G Geq) (AElt G (gop g h)) k)
  (* injective: g <-> delta_{AElt g} *)
  /\ (forall g h, (forall k, delta (Adj G) (aAeq G Geq) (AElt G g) k
                           = delta (Adj G) (aAeq G Geq) (AElt G h) k) -> g = h)
  (* surjective onto the invertibles: they are EXACTLY the deltas over G *)
  /\ (forall m, (exists y, forall k, gconv (Adj G) (aAeq G Geq) (aelts G gelts) (aop G gop)
                             (delta (Adj G) (aAeq G Geq) m) y k
                         = gunit (Adj G) (aAeq G Geq) (ae G geG) k)
                <-> exists g, m = AElt G g)
  (* the ratio, pinned: |Adj G| = |G| + 1 group-likes, |G| invertible *)
  /\ length (aelts G gelts) = S (length gelts).
Proof.
  split; [ exact delta_aelt_hom | ].
  split; [ exact delta_aelt_inj | ].
  split; [ exact invertible_grouplike_iff | exact (adj_card G gelts) ].
Qed.

End AdjInvertibleGrouplikes.

Print Assumptions invertible_grouplikes_iso_G.

(* ================================================================= *)
(*  END AdjRatioBreak.v  —  Adj G is the ratio-(>1) case: all |G|+1     *)
(*  group-likes, but delta_AZero has no inverse, so it is a bialgebra   *)
(*  and not a Hopf algebra.                                             *)
(* ================================================================= *)
