(* ================================================================= *)
(*  CListProdBound.v  —  LOWER bounds for a product over a list.       *)
(*                                                                    *)
(*    prodR f l  =  PROD_{x in l} f x,  and                            *)
(*                                                                    *)
(*    prodR_le_Wlist : bounding each Weierstrass factor below by f x   *)
(*      bounds the whole product below by prodR f l.                   *)
(*                                                                    *)
(*  CInfProd's RPdev machinery is the UPPER-bound analogue of this and *)
(*  has no mirror: everything about infinite products in the repo so   *)
(*  far has been about convergence, which needs factors close to 1     *)
(*  from above.  A minimum modulus needs the other direction, and      *)
(*  needs it factor by factor, since the two regimes of CEfacLower     *)
(*  give different-shaped bounds.                                     *)
(*                                                                    *)
(*  prodR_mult is what lets the near-zero bound -- a constant q times  *)
(*  an exponential -- be split into a pure power and a pure            *)
(*  exponential, so that the power meets the COUNTING bound and the    *)
(*  exponential meets the SUM bound.  Those are the only two facts     *)
(*  about the zeros available, and they answer to different queries.   *)
(*                                                                    *)
(*  pow_exp is the bridge the caller actually needs: the counting      *)
(*  bound Bxi is a REAL, not a nat, so q ^ n >= q ^ Bxi is not a pow   *)
(*  fact.  Written as exp (n ln q) it is just monotonicity of exp      *)
(*  against n ln q >= Bxi ln q, which holds because ln q <= 0.         *)
(*  Axiom-clean.                                                       *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia List.
Require Import ComplexField Cmodulus CDeriv CDyadicSum
        XiHadamardProd XiProdFactor.
Open Scope R_scope.

Fixpoint prodR (f : C -> R) (l : list C) : R :=
  match l with
  | nil => 1
  | x :: t => f x * prodR f t
  end.

Lemma prodR_mult : forall (f g : C -> R) (l : list C),
  prodR (fun x => f x * g x) l = prodR f l * prodR g l.
Proof.
  intros f g l. induction l as [| x t IH]; cbn [prodR];
    [ ring | rewrite IH; ring ].
Qed.

Lemma prodR_exp : forall (g : C -> R) (l : list C),
  prodR (fun x => exp (g x)) l = exp (sumlist g l).
Proof.
  intros g l. induction l as [| x t IH]; cbn [prodR sumlist];
    [ symmetry; apply exp_0 | rewrite IH, <- exp_plus; reflexivity ].
Qed.

Lemma prodR_nonneg : forall (f : C -> R) (l : list C),
  (forall x, In x l -> 0 <= f x) -> 0 <= prodR f l.
Proof.
  intros f l H. induction l as [| x t IH]; cbn [prodR]; [ lra | ].
  apply Rmult_le_pos;
    [ apply H; left; reflexivity | apply IH; intros y Hy; apply H; right; exact Hy ].
Qed.

(* the factorwise lower bound, transported to the whole product *)
Lemma prodR_le_Wlist : forall (f : C -> R) (l : list C) (z : C),
  (forall x, In x l -> 0 <= f x /\ f x <= Cmod (Efac z x)) ->
  prodR f l <= Cmod (Wlist l z).
Proof.
  intros f l z H. induction l as [| x t IH]; cbn [prodR Wlist].
  - rewrite Cmod_C1. lra.
  - rewrite Cmod_mul.
    destruct (H x (or_introl eq_refl)) as [Hf0 Hfle].
    assert (Ht : prodR f t <= Cmod (Wlist t z))
      by (apply IH; intros y Hy; apply H; right; exact Hy).
    assert (H0 : 0 <= prodR f t)
      by (apply prodR_nonneg; intros y Hy; apply (H y (or_intror Hy))).
    apply Rmult_le_compat; assumption.
Qed.

Lemma prodR_const_ge : forall (f : C -> R) (l : list C) (q : R), 0 < q ->
  (forall x, In x l -> q <= f x) ->
  q ^ (length l) <= prodR f l.
Proof.
  intros f l q Hq H. induction l as [| x t IH]; cbn [prodR length pow]; [ lra | ].
  assert (Ht : q ^ (length t) <= prodR f t)
    by (apply IH; intros y Hy; apply H; right; exact Hy).
  assert (Hq0 : 0 <= q ^ (length t)) by (apply pow_le; lra).
  pose proof (H x (or_introl eq_refl)).
  apply Rmult_le_compat; lra.
Qed.

Lemma sumlist_scal : forall (c : R) (f : C -> R) (l : list C),
  sumlist (fun x => c * f x) l = c * sumlist f l.
Proof.
  intros c f l. induction l as [| x t IH]; cbn [sumlist];
    [ ring | rewrite IH; ring ].
Qed.

(* a power, as an exponential -- so a REAL count bound can be used *)
Lemma pow_exp : forall (q : R) (n : nat), 0 < q ->
  q ^ n = exp (INR n * ln q).
Proof.
  intros q n Hq. rewrite <- (Rpower_pow n q Hq). unfold Rpower. reflexivity.
Qed.

(* the Weierstrass product splits along any boolean predicate *)
Lemma Wlist_filter_split : forall (p : C -> bool) (l : list C) (z : C),
  Wlist l z
  = Cmul (Wlist (filter p l) z) (Wlist (filter (fun x => negb (p x)) l) z).
Proof.
  intros p l z. induction l as [| x t IH]; cbn [filter].
  - cbn [Wlist]. ring.
  - destruct (p x); cbn [Wlist negb]; rewrite IH; ring.
Qed.

Print Assumptions prodR_le_Wlist.
