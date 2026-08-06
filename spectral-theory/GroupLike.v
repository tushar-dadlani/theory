(* ================================================================= *)
(*  GroupLike.v  —  group-like & primitive elements; the ratio-1        *)
(*  characterization of group algebras.                                *)
(*                                                                    *)
(*  The natural bialgebra on Z[M] has counit eps = bigsum and diagonal  *)
(*  coproduct Delta(delta_m) = delta_m (x) delta_m.  Then:              *)
(*    - GROUP-LIKE x  (Delta x = x(x)x, eps x = 1)  are EXACTLY the      *)
(*      deltas delta_m, m in M  (grouplike_is_delta / delta_grouplike): *)
(*      the "operators/group" subset IS the group M.                    *)
(*    - PRIMITIVE x  (Delta x = x(x)1 + 1(x)x, eps x = 0)  is ONLY 0     *)
(*      (primitive_is_zero): a group algebra has no infinitesimal       *)
(*      "operations" part.                                              *)
(*    - the deltas SPAN (delta_expansion) and are DISTINCT: they are a   *)
(*      basis indexed by M, so #group-likes = dim = |M|  --  RATIO 1.   *)
(*                                                                    *)
(*  This is the operand/operator picture made precise: a set = group    *)
(*  (group-likes) (+) operations (primitives), and a group algebra is    *)
(*  the rigid ratio-1 case (all group-like, no primitive).  Axiom-free. *)
(* ================================================================= *)

From Stdlib Require Import List Arith ZArith Bool Lia.
Require Import HopfGroupAlgebraGen.
Import ListNotations.
Open Scope Z_scope.

Section GroupLike.

Variable A : Type.
Variable Aeq : A -> A -> bool.
Hypothesis Aeq_spec : forall x y, reflect (x = y) (Aeq x y).
Variable elts : list A.
Hypothesis elts_nodup : NoDup elts.
Hypothesis elts_all : forall x, In x elts.
Variable e : A.

(* ---- Aeq basics ---- *)
Lemma Aeq_refl : forall m, Aeq m m = true.
Proof. intro m; destruct (Aeq_spec m m); [ reflexivity | congruence ]. Qed.
Lemma Aeq_sym : forall m k, Aeq m k = Aeq k m.
Proof. intros m k; destruct (Aeq_spec m k), (Aeq_spec k m); congruence. Qed.
Lemma Aeq_true : forall x y, Aeq x y = true -> x = y.
Proof. intros x y H; destruct (Aeq_spec x y); [ assumption | discriminate ]. Qed.
Lemma Aeq_false : forall x y, Aeq x y = false -> x <> y.
Proof. intros x y H; destruct (Aeq_spec x y); [ discriminate | assumption ]. Qed.
Lemma sumf_cons : forall a l (f : A -> Z), sumf A (a :: l) f = (f a + sumf A l f)%Z.
Proof. reflexivity. Qed.

(* ---- the bialgebra conditions (Delta diagonal, eps = bigsum) ---- *)
Definition grouplike (x : A -> Z) : Prop :=
  bigsum A elts x = 1%Z /\
  forall m n, (if Aeq m n then x m else 0)%Z = (x m * x n)%Z.

Definition primitive (x : A -> Z) : Prop :=
  bigsum A elts x = 0%Z /\
  forall m n, (if Aeq m n then x m else 0)%Z
    = (x m * (if Aeq e n then 1 else 0) + (if Aeq e m then 1 else 0) * x n)%Z.

(* ---- sum of a delta is 1; every element expands over the deltas ---- *)
Lemma bigsum_delta : forall m, In m elts -> bigsum A elts (delta A Aeq m) = 1%Z.
Proof.
  intros m Hm; unfold bigsum, delta.
  exact (sumf_sift A Aeq Aeq_spec elts m (fun _ => 1%Z) elts_nodup Hm).
Qed.

Lemma delta_expansion : forall (a : A -> Z) k,
  a k = bigsum A elts (fun m => (a m * delta A Aeq m k)%Z).
Proof.
  intros a k; unfold bigsum, delta.
  transitivity (sumf A elts (fun m => if Aeq k m then a m else 0)).
  - symmetry; exact (sumf_sift A Aeq Aeq_spec elts k a elts_nodup (elts_all k)).
  - apply sumf_ext; intros m _; rewrite (Aeq_sym m k); destruct (Aeq k m); ring.
Qed.

Lemma sumf_nonzero_witness : forall l (x : A -> Z),
  sumf A l x <> 0%Z -> exists m, In m l /\ x m <> 0%Z.
Proof.
  induction l as [|a l IH]; intros x H; [ simpl in H; congruence | ].
  rewrite sumf_cons in H; destruct (Z.eq_dec (x a) 0%Z) as [Ha | Ha].
  - rewrite Ha in H; destruct (IH x ltac:(lia)) as [m [Hm Hxm]];
      exists m; split; [ right; exact Hm | exact Hxm ].
  - exists a; split; [ left; reflexivity | exact Ha ].
Qed.

(* ================================================================= *)
(*  GROUP-LIKES ARE EXACTLY THE DELTAS  (= the group M)               *)
(* ================================================================= *)
Lemma delta_grouplike : forall m, In m elts -> grouplike (delta A Aeq m).
Proof.
  intros m Hm; split; [ apply bigsum_delta; exact Hm | ].
  intros p q; unfold delta.
  destruct (Aeq p q) eqn:Hpq; destruct (Aeq m p) eqn:Hmp; destruct (Aeq m q) eqn:Hmq;
    simpl; try ring; exfalso;
    repeat match goal with
    | [ H : Aeq ?x ?y = true |- _ ] => apply Aeq_true in H
    | [ H : Aeq ?x ?y = false |- _ ] => apply Aeq_false in H
    end; congruence.
Qed.

Lemma grouplike_is_delta : forall x, grouplike x ->
  exists m, In m elts /\ forall k, x k = delta A Aeq m k.
Proof.
  intros x [Hsum Hdiag].
  assert (Hex : exists m0, In m0 elts /\ x m0 <> 0%Z).
  { apply (sumf_nonzero_witness elts x); unfold bigsum in Hsum; rewrite Hsum; discriminate. }
  destruct Hex as [m0 [Hm0 Hx0]].
  assert (Hdiag0 : x m0 = (x m0 * x m0)%Z)
    by (specialize (Hdiag m0 m0); rewrite Aeq_refl in Hdiag; exact Hdiag).
  assert (Hx1 : x m0 = 1%Z) by nia.
  exists m0; split; [ exact Hm0 | ].
  intros k; unfold delta; destruct (Aeq m0 k) eqn:Hb.
  - assert (m0 = k) by (apply Aeq_true; exact Hb); subst k; exact Hx1.
  - specialize (Hdiag m0 k); rewrite Hb in Hdiag; simpl in Hdiag;
      rewrite Hx1 in Hdiag; simpl; nia.
Qed.

Theorem grouplike_iff_delta : forall x,
  grouplike x <-> exists m, In m elts /\ forall k, x k = delta A Aeq m k.
Proof.
  intros x; split; [ apply grouplike_is_delta | ].
  intros [m [Hm Hxk]].
  (* grouplike is invariant under pointwise-equal functions; delta m is grouplike *)
  destruct (delta_grouplike m Hm) as [Hs Hd]; split.
  - unfold bigsum; rewrite (sumf_ext A elts x (delta A Aeq m)); [ exact Hs | intros k _; apply Hxk ].
  - intros p q; rewrite !Hxk; exact (Hd p q).
Qed.

(* ================================================================= *)
(*  NO NONTRIVIAL PRIMITIVES  (no infinitesimal "operations")         *)
(* ================================================================= *)
Theorem primitive_is_zero : forall x, primitive x -> forall k, x k = 0%Z.
Proof.
  intros x [_ Hdiag] k; specialize (Hdiag k k); rewrite Aeq_refl in Hdiag.
  change (if true then x k else 0%Z) with (x k) in Hdiag.
  (* the identity is the witness: at k = e the condition self-references *)
  destruct (Aeq e k) eqn:Hek.
  - change (if true then 1%Z else 0%Z) with 1%Z in Hdiag; lia.
  - change (if false then 1%Z else 0%Z) with 0%Z in Hdiag; lia.
Qed.

(* ================================================================= *)
(*  RATIO 1:  group-likes = deltas = a basis indexed by M.            *)
(* ================================================================= *)
Lemma delta_distinct : forall m m', In m elts -> In m' elts -> m <> m' ->
  delta A Aeq m m <> delta A Aeq m' m.
Proof.
  intros m m' Hm Hm' Hne; unfold delta; rewrite Aeq_refl.
  assert (Hf : Aeq m' m = false) by (destruct (Aeq_spec m' m); [ subst m'; congruence | reflexivity ]).
  rewrite Hf; discriminate.
Qed.

Theorem group_algebra_ratio_one :
  (* group-likes are EXACTLY the deltas (bijective with M) *)
  (forall m, In m elts -> grouplike (delta A Aeq m))
  /\ (forall x, grouplike x -> exists m, In m elts /\ forall k, x k = delta A Aeq m k)
  (* no nontrivial primitives *)
  /\ (forall x, primitive x -> forall k, x k = 0%Z)
  (* the deltas span (basis) and are distinct: #group-likes = dim = |M| *)
  /\ (forall a k, a k = bigsum A elts (fun m => (a m * delta A Aeq m k)%Z))
  /\ (forall m m', In m elts -> In m' elts -> m <> m' ->
        delta A Aeq m m <> delta A Aeq m' m).
Proof.
  split; [ exact delta_grouplike | ].
  split; [ exact grouplike_is_delta | ].
  split; [ exact primitive_is_zero | ].
  split; [ exact delta_expansion | exact delta_distinct ].
Qed.

End GroupLike.

Print Assumptions grouplike_iff_delta.
Print Assumptions group_algebra_ratio_one.

(* ================================================================= *)
(*  END GroupLike.v  —  in Z[M] the group-likes ARE the group M        *)
(*  (a basis, ratio 1) and there are no primitives: the rigid          *)
(*  "operand = operator" case of the bialgebra decomposition.          *)
(* ================================================================= *)
