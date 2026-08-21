(* ================================================================= *)
(*  CEisensteinUFD.v  —  EXISTENCE of factorization in Z[omega].       *)
(*                                                                    *)
(*    emul_eq_zero  : Z[omega] is an integral domain                   *)
(*    emul_cancel   : cancellation                                     *)
(*    prodl         : the product over a list                          *)
(*    exists_factorization : every nonzero nonunit is a product of     *)
(*                    irreducibles                                     *)
(*    irred_dvd_prodl : an irreducible dividing a product divides a    *)
(*                    factor                                           *)
(*                                                                    *)
(*  BEING A DOMAIN IS A NORM FACT, like everything else here:          *)
(*  N(a)N(b) = N(ab) = 0 forces one norm to vanish, and enorm_zero     *)
(*  turns that back into the element.  Cancellation follows.           *)
(*                                                                    *)
(*  EXISTENCE IS STRONG INDUCTION ON THE NORM.  A nonzero nonunit is   *)
(*  either irreducible -- a one-element list -- or splits as d.q with  *)
(*  both nonunits, and then N(d), N(q) >= 2 forces both strictly below *)
(*  N(z), so the induction bites.  Concatenating the two lists is the  *)
(*  whole construction.                                               *)
(*                                                                    *)
(*  THIS IS THE FIRST FILE IN THE Z[omega] TOWER THAT IS NOT           *)
(*  AXIOM-FREE, and the reason is worth stating precisely: deciding    *)
(*  "is z irreducible" is a universally quantified statement over all  *)
(*  factorizations, and nothing here makes it decidable.  In principle *)
(*  it is -- divisors are bounded in norm, so it is a finite search -- *)
(*  but enumerating Z[omega] elements by norm is a lot of machinery to *)
(*  build for a case split.  classic is already one of the four        *)
(*  standing axioms, so it is used, and only here; the ring, units,    *)
(*  division, Bezout and splitting files all remain closed under the   *)
(*  global context.                                                    *)
(* ================================================================= *)

From Stdlib Require Import ZArith Znumtheory Lia Ring List
        Classical_Prop Classical_Pred_Type.
Require Import CEisenstein CEisensteinUnits CEisensteinDiv CEisensteinGcd.
Import ListNotations.
Open Scope Z_scope.

(* ----------------------------------------------------------------- *)
(*  A.  Z[omega] is an integral domain                                 *)
(* ----------------------------------------------------------------- *)
Lemma emul_eq_zero : forall a b, emul a b = ezero -> a = ezero \/ b = ezero.
Proof.
  intros a b H.
  assert (Hn : enorm a * enorm b = 0)
    by (rewrite <- enorm_mul, H; unfold enorm, ezero; cbn [ea eb]; ring).
  destruct (Z.eq_dec (enorm a) 0) as [Ha | Ha].
  - left. apply enorm_zero. exact Ha.
  - right. apply enorm_zero. nia.
Qed.

Lemma emul_cancel : forall z x y, z <> ezero -> emul z x = emul z y -> x = y.
Proof.
  intros z x y Hz H.
  assert (Hd : emul z (esub x y) = ezero).
  { assert (E : emul z (esub x y) = esub (emul z x) (emul z y))
      by (unfold esub; ring).
    rewrite E, H. unfold esub. ring. }
  destruct (emul_eq_zero _ _ Hd) as [Hc | Hc]; [ contradiction | ].
  assert (Hxy : esub x y = ezero) by exact Hc.
  assert (x = eadd (esub x y) y) by (unfold esub; ring).
  rewrite Hxy in H0. rewrite H0. ring.
Qed.

(* ----------------------------------------------------------------- *)
(*  B.  products over lists                                            *)
(* ----------------------------------------------------------------- *)
Fixpoint prodl (l : list Eis) : Eis :=
  match l with
  | [] => eone
  | x :: t => emul x (prodl t)
  end.

Lemma prodl_app : forall l1 l2, prodl (l1 ++ l2) = emul (prodl l1) (prodl l2).
Proof.
  induction l1 as [| x t IH]; intro l2; simpl.
  - ring.
  - rewrite IH. ring.
Qed.

(* ----------------------------------------------------------------- *)
(*  C.  existence of a factorization                                   *)
(* ----------------------------------------------------------------- *)
Lemma nonunit_nonzero_norm : forall z, z <> ezero -> ~ eunit z -> 2 <= enorm z.
Proof.
  intros z Hz Hu.
  pose proof (enorm_nonneg z) as H0.
  assert (Hne0 : enorm z <> 0) by (intro Hc; apply Hz; apply enorm_zero; exact Hc).
  assert (Hne1 : enorm z <> 1) by (intro Hc; apply Hu; apply norm_eunit; exact Hc).
  lia.
Qed.

Lemma factor_aux : forall (k : nat) (z : Eis),
  (Z.to_nat (enorm z) <= k)%nat -> z <> ezero -> ~ eunit z ->
  exists l, Forall eirred l /\ z = prodl l.
Proof.
  induction k as [| k IH]; intros z Hk Hz Hu.
  - exfalso. pose proof (nonunit_nonzero_norm z Hz Hu) as H2. lia.
  - destruct (classic (eirred z)) as [Hirr | Hnirr].
    + exists [z]. split; [ constructor; [ exact Hirr | constructor ] | simpl; ring ].
    + (* not irreducible: extract a genuine splitting *)
      assert (Hsplit : exists d q, z = emul d q /\ ~ eunit d /\ ~ eunit q).
      { apply NNPP. intro Hno.
        apply Hnirr. unfold eirred. split; [ exact Hu | ]. split; [ exact Hz | ].
        intros d q Hdq. apply NNPP. intro Hnu.
        apply Hno. exists d, q. split; [ exact Hdq | ].
        split; intro Hc; apply Hnu; [ left | right ]; exact Hc. }
      destruct Hsplit as [d [q [Hdq [Hnd Hnq]]]].
      assert (Hd0 : d <> ezero)
        by (intro Hc; apply Hz; rewrite Hdq, Hc; ring).
      assert (Hq0 : q <> ezero)
        by (intro Hc; apply Hz; rewrite Hdq, Hc; ring).
      pose proof (nonunit_nonzero_norm d Hd0 Hnd) as Hd2.
      pose proof (nonunit_nonzero_norm q Hq0 Hnq) as Hq2.
      assert (Hnz : enorm z = enorm d * enorm q)
        by (rewrite Hdq, enorm_mul; reflexivity).
      assert (Hdk : (Z.to_nat (enorm d) <= k)%nat).
      { assert (Hlt : enorm d < enorm z) by nia.
        pose proof (enorm_nonneg d) as Hdn. pose proof (enorm_nonneg z) as Hzn.
        apply (proj1 (Z2Nat.inj_lt (enorm d) (enorm z) Hdn Hzn)) in Hlt. lia. }
      assert (Hqk : (Z.to_nat (enorm q) <= k)%nat).
      { assert (Hlt : enorm q < enorm z) by nia.
        pose proof (enorm_nonneg q) as Hqn. pose proof (enorm_nonneg z) as Hzn.
        apply (proj1 (Z2Nat.inj_lt (enorm q) (enorm z) Hqn Hzn)) in Hlt. lia. }
      destruct (IH d Hdk Hd0 Hnd) as [l1 [Hl1 Hp1]].
      destruct (IH q Hqk Hq0 Hnq) as [l2 [Hl2 Hp2]].
      exists (l1 ++ l2). split.
      * apply Forall_app. split; assumption.
      * rewrite prodl_app, <- Hp1, <- Hp2. exact Hdq.
Qed.

Theorem exists_factorization : forall z, z <> ezero -> ~ eunit z ->
  exists l, Forall eirred l /\ z = prodl l.
Proof.
  intros z Hz Hu. apply (factor_aux (Z.to_nat (enorm z))); [ lia | assumption .. ].
Qed.

(* ----------------------------------------------------------------- *)
(*  D.  Euclid's lemma, over a list                                    *)
(* ----------------------------------------------------------------- *)
Theorem irred_dvd_prodl : forall pi l, eirred pi -> edvd pi (prodl l) ->
  exists x, In x l /\ edvd pi x.
Proof.
  intros pi l Hirr. induction l as [| x t IH]; intro Hd; simpl in Hd.
  - exfalso. apply (proj1 Hirr). apply edvd_eone. exact Hd.
  - destruct (irred_prime pi x (prodl t) Hirr Hd) as [Hx | Ht].
    + exists x. split; [ left; reflexivity | exact Hx ].
    + destruct (IH Ht) as [y [Hy Hdy]].
      exists y. split; [ right; exact Hy | exact Hdy ].
Qed.

Print Assumptions emul_cancel.
Print Assumptions exists_factorization.
Print Assumptions irred_dvd_prodl.
