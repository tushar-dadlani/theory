(* ================================================================= *)
(*  CCircleBound.v  (identity-theorem plan, FE chain brick 5 — base)    *)
(*                                                                    *)
(*  A path-continuous g : C -> C is bounded on the whole circle         *)
(*  { arc Rr u : u in R } by its sup on [0,2 pi] -- arc is 2 pi         *)
(*  periodic, so every arc Rr u equals arc Rr u' for some u' in         *)
(*  [0,2 pi].  This furnishes the tower's Hgb (bound for ALL u) from     *)
(*  Ccont_bounded (bound on the compact [0,2 pi]).                     *)
(*                                                                    *)
(*  Axioms: standard classical-Reals only.                            *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia ZArith.
Require Import ComplexField Cmodulus CIntegral2 CSegInt CPathIntegral CContBounded.
Open Scope R_scope.

Lemma arc_shift : forall Rr x k, arc Rr (x + 2 * INR k * PI) = arc Rr x.
Proof. intros Rr x k. unfold arc. rewrite cos_period, sin_period. reflexivity. Qed.

Lemma cos_sub_period : forall x k, cos (x - 2 * INR k * PI) = cos x.
Proof.
  intros x k. pose proof (cos_period (x - 2 * INR k * PI) k) as H.
  replace (x - 2 * INR k * PI + 2 * INR k * PI) with x in H by ring.
  symmetry; exact H.
Qed.

Lemma sin_sub_period : forall x k, sin (x - 2 * INR k * PI) = sin x.
Proof.
  intros x k. pose proof (sin_period (x - 2 * INR k * PI) k) as H.
  replace (x - 2 * INR k * PI + 2 * INR k * PI) with x in H by ring.
  symmetry; exact H.
Qed.

Lemma arc_shift_sub : forall Rr x k, arc Rr (x - 2 * INR k * PI) = arc Rr x.
Proof. intros Rr x k. unfold arc. rewrite cos_sub_period, sin_sub_period. reflexivity. Qed.

Lemma arc_reduce : forall Rr u, exists u', 0 <= u' <= 2 * PI /\ arc Rr u = arc Rr u'.
Proof.
  intros Rr u.
  assert (Hpi : 0 < 2 * PI) by (generalize PI_RGT_0; lra).
  set (n := Int_part (u / (2 * PI))).
  set (u' := u - 2 * PI * IZR n).
  pose proof (base_Int_part (u / (2 * PI))) as [Hle Hgt]. fold n in Hle, Hgt.
  assert (H1 : 2 * PI * IZR n <= u).
  { pose proof (Rmult_le_compat_l (2 * PI) (IZR n) (u / (2 * PI))
                  ltac:(lra) Hle) as HH.
    replace (2 * PI * (u / (2 * PI))) with u in HH by (field; lra). exact HH. }
  assert (H2 : u < 2 * PI * (IZR n + 1)).
  { assert (Hgt' : u / (2 * PI) < IZR n + 1) by lra.
    pose proof (Rmult_lt_compat_l (2 * PI) (u / (2 * PI)) (IZR n + 1)
                  Hpi Hgt') as HH.
    replace (2 * PI * (u / (2 * PI))) with u in HH by (field; lra). exact HH. }
  exists u'. split; [ split | ].
  - unfold u'; lra.
  - unfold u'; lra.
  - destruct (Rle_or_lt 0 (IZR n)) as [Hn | Hn].
    + assert (Hn' : (0 <= n)%Z) by (apply le_IZR; simpl; lra).
      replace u with (u' + 2 * INR (Z.to_nat n) * PI).
      * rewrite arc_shift; reflexivity.
      * unfold u'. rewrite INR_IZR_INZ, Z2Nat.id by lia. ring.
    + assert (Hn' : (n < 0)%Z) by (apply lt_IZR; simpl; lra).
      replace u with (u' - 2 * INR (Z.to_nat (- n)) * PI).
      * rewrite arc_shift_sub; reflexivity.
      * unfold u'. rewrite INR_IZR_INZ, Z2Nat.id by lia.
        rewrite opp_IZR. ring.
Qed.

Theorem Ccont_circle_bounded : forall (g : C -> C) (Rr : R), CcontC g ->
  exists M, 0 <= M /\ forall u, Cmod (g (arc Rr u)) <= M.
Proof.
  intros g Rr Hg.
  assert (Hcont : Ccont (fun u => g (arc Rr u)))
    by (apply Hg, Ccont_arc).
  assert (Hpi : 0 <= 2 * PI) by (generalize PI_RGT_0; lra).
  destruct (Ccont_bounded (fun u => g (arc Rr u)) Hcont 0 (2 * PI) Hpi)
    as [M HM].
  exists (Rabs M). split; [ apply Rabs_pos | ].
  intro u. destruct (arc_reduce Rr u) as [u' [Hu' Heq]].
  rewrite Heq.
  eapply Rle_trans; [ apply (HM u' Hu') | apply Rle_abs ].
Qed.

Print Assumptions Ccont_circle_bounded.
