(* ================================================================= *)
(*  RealMobius.v  —  real-valued Mobius / divisor-sum groundwork for    *)
(*  the Selberg route (Step 2).                                        *)
(*                                                                    *)
(*  Bridges the nat->Z Mobius machinery (DirichletConv: mu, mu_one)     *)
(*  to real divisor sums over the SAME `divisors` (they share the        *)
(*  identical filter definition).  Delivers the real Mobius identity     *)
(*      Sum_{d|m} mu(d)  =  [m = 1]      (as reals)                      *)
(*  and the generic real list-sum toolkit (Rls) used downstream.        *)
(*  Axiom-clean.                                                        *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia Arith List ZArith Permutation.
Require Import DirichletConv VonMangoldtGlobal.
Import ListNotations.
Open Scope R_scope.

(* ================================================================= *)
(*  0.  a generic real list-sum                                       *)
(* ================================================================= *)

Definition Rls {A : Type} (l : list A) (f : A -> R) : R :=
  fold_right Rplus 0%R (map f l).

Lemma Rls_cons : forall A (f : A -> R) x l, Rls (x :: l) f = f x + Rls l f.
Proof. reflexivity. Qed.

Lemma Rls_ext : forall A (f g : A -> R) l,
  (forall x, In x l -> f x = g x) -> Rls l f = Rls l g.
Proof.
  intros A f g l; induction l as [|a l IH]; intro H; [ reflexivity | ].
  rewrite !Rls_cons, (H a (in_eq a l)), IH.
  - reflexivity.
  - intros x Hx; apply H; right; exact Hx.
Qed.

Lemma Rls_perm : forall A (f : A -> R) l l',
  Permutation l l' -> Rls l f = Rls l' f.
Proof.
  intros A f l l' Hp; induction Hp; try reflexivity.
  - rewrite !Rls_cons, IHHp; reflexivity.
  - rewrite !Rls_cons; ring.
  - rewrite IHHp1, IHHp2; reflexivity.
Qed.

Lemma Rls_scal : forall A (c : R) (f : A -> R) l,
  c * Rls l f = Rls l (fun x => c * f x).
Proof.
  intros A c f l; induction l as [|a l IH]; [ unfold Rls; simpl; ring | ].
  rewrite !Rls_cons, Rmult_plus_distr_l, IH; reflexivity.
Qed.

Lemma Rls_app : forall A (f : A -> R) l1 l2, Rls (l1 ++ l2) f = Rls l1 f + Rls l2 f.
Proof.
  intros A f l1 l2; induction l1 as [|a l1 IH]; [ unfold Rls; simpl; ring | ].
  cbn [app]; rewrite !Rls_cons, IH; ring.
Qed.

Lemma Rls_flat_map : forall A B (f : B -> R) (h : A -> list B) l,
  Rls (flat_map h l) f = Rls l (fun x => Rls (h x) f).
Proof.
  intros A B f h l; induction l as [|a l IH]; [ reflexivity | ].
  cbn [flat_map]; rewrite Rls_app, IH, Rls_cons; reflexivity.
Qed.

(* ================================================================= *)
(*  1.  IZR distributes over the Z list-sum `sumf`                     *)
(* ================================================================= *)

Lemma IZR_sumf : forall (l : list nat) (h : nat -> Z),
  IZR (HopfGroupTensor.sumf l h) = Rls l (fun d => IZR (h d)).
Proof.
  intros l h; induction l as [|a l IH]; [ reflexivity | ].
  rewrite Rls_cons, <- IH.
  change (HopfGroupTensor.sumf (a :: l) h) with (h a + HopfGroupTensor.sumf l h)%Z.
  apply plus_IZR.
Qed.

(* ================================================================= *)
(*  2.  the real Mobius identity  Sum_{d|m} mu(d) = [m=1]              *)
(* ================================================================= *)

Theorem mu_real_sum : forall m, (1 <= m)%nat ->
  Rls (divisors m) (fun d => IZR (mu d)) = (if Nat.eqb m 1 then 1 else 0).
Proof.
  intros m Hm.
  pose proof (mu_one m Hm) as H.
  rewrite (dconv_as_div mu done m Hm) in H.
  apply (f_equal IZR) in H.
  rewrite IZR_sumf in H.
  rewrite (Rls_ext _ (fun d => IZR (mu d * done (m / d))) (fun d => IZR (mu d))) in H
    by (intros d _; replace (done (m / d)) with 1%Z by reflexivity;
        rewrite Z.mul_1_r; reflexivity).
  change (Totient.divisors m) with (divisors m) in H.
  rewrite H; unfold deps; destruct (Nat.eqb m 1); reflexivity.
Qed.

Print Assumptions mu_real_sum.

(* ================================================================= *)
(*  END RealMobius.v (part 1: Rls toolkit + real Mobius identity)      *)
(* ================================================================= *)
