(* ================================================================= *)
(*  MonoidAlgebraZero.v  —  Brick 2: the zero-adjunction monoid Adj G.  *)
(*                                                                    *)
(*  Adj G = AZero | AElt g  adjoins an absorbing zero to a commutative  *)
(*  monoid G.  It IS a commutative monoid (aop_*, discharging exactly    *)
(*  Brick 1's MonoidAlgebra hypotheses), with |Adj G| = |G| + 1 -- so    *)
(*  prime length <-> |G| = p - 1.  This is the carrier over which the    *)
(*  monoid algebra Z[Adj G] (Brick 1's MonoidAlgebra, now inv-free) is    *)
(*  formed, and the p=3 case Adj bool = {I,N,F}.  Axiom-free.            *)
(* ================================================================= *)

From Stdlib Require Import List Arith FinFun ZArith.
Require Import HopfGroupAlgebraGen.
Import ListNotations.

Section ZeroAdjunction.

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

Inductive Adj : Type := AZero | AElt (g : G).

Definition aop (x y : Adj) : Adj :=
  match x, y with
  | AElt a, AElt b => AElt (gop a b)
  | _, _ => AZero
  end.

Definition ae : Adj := AElt geG.

Definition aAeq (x y : Adj) : bool :=
  match x, y with
  | AZero, AZero => true
  | AElt a, AElt b => Geq a b
  | _, _ => false
  end.

Definition aelts : list Adj := AZero :: map AElt gelts.

(* ---- the MonoidAlgebra hypotheses, discharged ---- *)

Lemma aAeq_spec : forall x y, reflect (x = y) (aAeq x y).
Proof.
  intros [|a] [|b]; simpl.
  - left; reflexivity.
  - right; discriminate.
  - right; discriminate.
  - destruct (Geq_spec a b) as [-> | Hne].
    + left; reflexivity.
    + right; intro H; apply Hne; injection H; auto.
Qed.

Lemma aelts_nodup : NoDup aelts.
Proof.
  unfold aelts; constructor.
  - rewrite in_map_iff; intros [g [H _]]; discriminate.
  - apply Injective_map_NoDup; [ intros x y H; injection H; auto | exact gelts_nodup ].
Qed.

Lemma aelts_all : forall x, In x aelts.
Proof.
  intros [|g]; unfold aelts.
  - left; reflexivity.
  - right; apply in_map, gelts_all.
Qed.

Lemma aop_assoc : forall x y z, aop (aop x y) z = aop x (aop y z).
Proof. intros [|a] [|b] [|c]; simpl; try reflexivity; rewrite gop_assoc; reflexivity. Qed.

Lemma aop_comm : forall x y, aop x y = aop y x.
Proof. intros [|a] [|b]; simpl; try reflexivity; rewrite gop_comm; reflexivity. Qed.

Lemma aop_id_l : forall x, aop ae x = x.
Proof. intros [|a]; unfold ae; simpl; try reflexivity; rewrite gop_id_l; reflexivity. Qed.

(* ---- prime-length count:  |Adj G| = |G| + 1 ---- *)
Lemma adj_card : length aelts = S (length gelts).
Proof. unfold aelts; simpl; rewrite length_map; reflexivity. Qed.

(* ---- the honest negative:  Adj G is NOT a group ----
   AZero has no inverse (aop _ AZero = AZero <> ae), so Brick 1's GroupPart --
   inv, ginv, the inversion antipode -- cannot be instantiated on Adj G.  This
   is the structural reason a monoid algebra with an absorbing zero is a
   bialgebra but never Hopf, i.e. why the {I,N,F} thread never produced one. *)
Lemma adj_no_inverse : ~ exists inv : Adj -> Adj, forall x, aop (inv x) x = ae.
Proof.
  intros [inv H]; specialize (H AZero); unfold ae in H.
  destruct (inv AZero); simpl in H; discriminate.
Qed.

End ZeroAdjunction.

Print Assumptions aop_assoc.
Print Assumptions adj_card.

(* ================================================================= *)
(*  ABSORPTION:  Z*delta_0 is a two-sided idempotent ideal.            *)
(*  gconv x (delta AZero) = (bigsum x) * delta AZero  -- every product   *)
(*  with delta_0 lands in Z*delta_0.  (The reason no_antipode holds at   *)
(*  the coalgebra level: nothing can invert delta_0.)                    *)
(* ================================================================= *)
Section AdjAbsorption.
Variable G : Type.
Variable Geq : G -> G -> bool.
Hypothesis Geq_spec : forall x y, reflect (x = y) (Geq x y).
Variable gelts : list G.
Hypothesis gelts_nodup : NoDup gelts.
Hypothesis gelts_all : forall x, In x gelts.
Variable gop : G -> G -> G.

Lemma aop_zero_r : forall i, aop G gop i (AZero G) = AZero G.
Proof. intros [|a]; reflexivity. Qed.

Theorem gconv_zero_absorb : forall (x : Adj G -> Z) (g : Adj G),
  gconv (Adj G) (aAeq G Geq) (aelts G gelts) (aop G gop) x
        (delta (Adj G) (aAeq G Geq) (AZero G)) g
  = (bigsum (Adj G) (aelts G gelts) x * delta (Adj G) (aAeq G Geq) (AZero G) g)%Z.
Proof.
  intros x g.
  unfold gconv, dsum.
  transitivity (bigsum (Adj G) (aelts G gelts)
                  (fun i => if aAeq G Geq (AZero G) g then x i else 0%Z)).
  { unfold bigsum; apply sumf_ext; intros i _.
    rewrite (sumf_ext (Adj G) (aelts G gelts)
      (fun j => if aAeq G Geq (aop G gop i j) g
                then (x i * delta (Adj G) (aAeq G Geq) (AZero G) j)%Z else 0%Z)
      (fun j => if aAeq G Geq (AZero G) j
                then (fun _ : Adj G => if aAeq G Geq (AZero G) g then x i else 0%Z) j
                else 0%Z)).
    - rewrite (sumf_sift (Adj G) (aAeq G Geq) (aAeq_spec G Geq Geq_spec)
        (aelts G gelts) (AZero G) (fun _ : Adj G => if aAeq G Geq (AZero G) g then x i else 0%Z)
        (aelts_nodup G gelts gelts_nodup) (aelts_all G gelts gelts_all (AZero G))).
      reflexivity.
    - intros j _; destruct j as [|a].
      + rewrite aop_zero_r; unfold delta;
          change (aAeq G Geq (AZero G) (AZero G)) with true; cbv beta iota;
          destruct (aAeq G Geq (AZero G) g); ring.
      + unfold delta;
          change (aAeq G Geq (AZero G) (AElt G a)) with false; cbv beta iota;
          destruct (aAeq G Geq (aop G gop i (AElt G a)) g); ring. }
  unfold delta; rewrite bigsum_mul_r; unfold bigsum; apply sumf_ext; intros i _;
    destruct (aAeq G Geq (AZero G) g); ring.
Qed.

(* ---- the SUBALGEBRA half:  AElt-supported functions = Z[G] ---- *)

(* lift a G-function to an AElt-supported Adj G-function *)
Definition alift (a : G -> Z) : Adj G -> Z :=
  fun x => match x with AZero _ => 0%Z | AElt _ g => a g end.

Lemma fold_map_AElt : forall (phi : Adj G -> Z) (l : list G),
  fold_right (fun k acc => (phi k + acc)%Z) 0%Z (map (AElt G) l)
  = fold_right (fun k acc => (phi (AElt G k) + acc)%Z) 0%Z l.
Proof. intros phi l; induction l as [|x l IH]; simpl; [ reflexivity | rewrite IH; reflexivity ]. Qed.

(* split a sum over Adj G into the AZero term and the AElt-reindexed rest *)
Lemma bigsum_adj_split : forall phi : Adj G -> Z,
  bigsum (Adj G) (aelts G gelts) phi
  = (phi (AZero G) + bigsum G gelts (fun g => phi (AElt G g)))%Z.
Proof.
  intros phi; unfold bigsum, aelts.
  change (sumf (Adj G) (AZero G :: map (AElt G) gelts) phi)
    with (phi (AZero G) + sumf (Adj G) (map (AElt G) gelts) phi)%Z.
  f_equal; unfold sumf; apply fold_map_AElt.
Qed.

(* closure: the product of two AElt-supported functions has 0 AZero-coefficient *)
Theorem gconv_adj_zero_coeff : forall a b,
  gconv (Adj G) (aAeq G Geq) (aelts G gelts) (aop G gop) (alift a) (alift b) (AZero G) = 0%Z.
Proof.
  intros a b; unfold gconv, dsum, bigsum.
  transitivity (sumf (Adj G) (aelts G gelts) (fun _ => 0%Z)); [ | apply sumf_zero ].
  apply sumf_ext; intros i _.
  transitivity (sumf (Adj G) (aelts G gelts) (fun _ => 0%Z)); [ | apply sumf_zero ].
  apply sumf_ext; intros j _.
  destruct i as [|p]; destruct j as [|q]; unfold alift; cbn [aAeq aop]; ring.
Qed.

(* the subalgebra iso: on AElt, Adj-convolution = G-convolution *)
Theorem gconv_adj_elt : forall a b h,
  gconv (Adj G) (aAeq G Geq) (aelts G gelts) (aop G gop) (alift a) (alift b) (AElt G h)
  = gconv G Geq gelts gop a b h.
Proof.
  intros a b h.
  unfold gconv, dsum.
  rewrite bigsum_adj_split.
  replace (bigsum (Adj G) (aelts G gelts)
             (fun j => if aAeq G Geq (aop G gop (AZero G) j) (AElt G h)
                       then (alift a (AZero G) * alift b j)%Z else 0%Z)) with 0%Z.
  2:{ symmetry; unfold bigsum;
      transitivity (sumf (Adj G) (aelts G gelts) (fun _ => 0%Z)); [ | apply sumf_zero ];
      apply sumf_ext; intros j _; cbn [alift aop aAeq]; ring. }
  rewrite Z.add_0_l.
  apply sumf_ext; intros p _.
  rewrite bigsum_adj_split.
  replace (if aAeq G Geq (aop G gop (AElt G p) (AZero G)) (AElt G h)
           then (alift a (AElt G p) * alift b (AZero G))%Z else 0%Z) with 0%Z.
  2:{ rewrite aop_zero_r; cbn [aAeq alift]; ring. }
  rewrite Z.add_0_l.
  apply sumf_ext; intros q _; cbn [aop aAeq alift]; reflexivity.
Qed.

End AdjAbsorption.

Print Assumptions gconv_zero_absorb.
Print Assumptions gconv_adj_zero_coeff.
Print Assumptions gconv_adj_elt.

(* ================================================================= *)
(*  END MonoidAlgebraZero.v (Brick 2: Adj monoid + no_inverse + absorb).*)
(* ================================================================= *)
