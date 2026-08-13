(* ================================================================= *)
(*  CIdentityPropDom.v  (identity-theorem plan, DOMAIN-RESTRICTED B6)   *)
(*                                                                    *)
(*  Propagation of vanishing across a convex domain U that is closed    *)
(*  under (R+1)-disks (so the moving disks stay inside U).  If all       *)
(*  derivatives vanish at one p in U, then fseq 0 vanishes at every w    *)
(*  in U.  Chain differentiable on U (Hchain_U) + pointwise-continuous   *)
(*  everywhere (Fptc).  Axiom-clean.                                   *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import ComplexField Cmodulus CIntegral2 CSegInt CPathIntegral CPrimConv
        Holomorphic CDeriv CWindingOffCenter CIdentityProp CIdentityZeroDom.
Open Scope R_scope.

Section PropagateDom.
Variable Rr : R.
Variable fseq : nat -> C -> C.
Variable U : C -> Prop.
Hypothesis HR : 0 < Rr.
Hypothesis HUconv : Convex U.
Hypothesis HUmargin : forall z z', U z -> Cmod (Cminus z' z) < Rr + 1 -> U z'.
Hypothesis Hchain_U : forall k z, U z -> is_Cderiv (fseq k) z (fseq (S k) z).
Hypothesis Fptc : forall k z e, 0 < e -> exists del, 0 < del /\
  forall z', Cmod (Cminus z' z) < del -> Cmod (Cminus (fseq k z') (fseq k z)) < e.
Hypothesis Hbd : forall p k, exists Mf, 0 <= Mf /\
  forall u, Cmod (fseq k (Cadd (arc Rr u) p)) <= Mf.

Lemma identity_disk_at_D : forall p, U p -> forall w,
  (forall k, fseq k p = C0) -> Cmod w < Rr -> fseq 0 (Cadd w p) = C0.
Proof.
  intros p Hp w Hvan Hw.
  assert (Hres : (fun k z => fseq k (Cadd z p)) 0%nat w = C0).
  { apply (identity_at_zero_D Rr (fun k z => fseq k (Cadd z p)) HR).
    - intros k z Hzd. cbn beta.
      apply (is_Cderiv_ext (fun ww => fseq k (Cadd (Cmul C1 ww) p))
                           (fun ww => fseq k (Cadd ww p)) z (fseq (S k) (Cadd z p))).
      + intro ww; rewrite Cmul_1_l; reflexivity.
      + replace (fseq (S k) (Cadd z p))
          with (Cmul C1 (fseq (S k) (Cadd (Cmul C1 z) p)))
          by (rewrite !Cmul_1_l; reflexivity).
        apply Cderiv_comp_affine. rewrite Cmul_1_l.
        apply Hchain_U. apply (HUmargin p); [ exact Hp | ].
        replace (Cminus (Cadd z p) p) with z by ring. exact Hzd.
    - intros k z e He. cbn beta.
      destruct (Fptc k (Cadd z p) e He) as [del [Hdel Hb]].
      exists del; split; [ exact Hdel | ].
      intros z' Hz'. apply (Hb (Cadd z' p)).
      replace (Cminus (Cadd z' p) (Cadd z p)) with (Cminus z' z) by ring. exact Hz'.
    - intros k. cbn beta. destruct (Hbd p k) as [Mf [HMf HB]].
      exists Mf; split; [ exact HMf | intro u; apply HB ].
    - intros k. cbn beta. replace (Cadd C0 p) with p by ring. apply Hvan.
    - exact Hw. }
  cbn beta in Hres. exact Hres.
Qed.

Lemma chain_vanishes_disk_D : forall p, U p ->
  (forall k, fseq k p = C0) ->
  forall k z, Cmod (Cminus z p) < Rr -> fseq k z = C0.
Proof.
  intros p Hp Hvan k. induction k as [|k IH]; intros z Hz.
  - replace z with (Cadd (Cminus z p) p) by ring.
    apply identity_disk_at_D; [ exact Hp | exact Hvan | exact Hz ].
  - apply (deriv_zero_on_open (fseq k) (fseq (S k)) z (Rr - Cmod (Cminus z p))).
    + lra.
    + apply Hchain_U. apply (HUmargin p); [ exact Hp | lra ].
    + intros z' Hz'. apply IH.
      replace (Cminus z' p) with (Cadd (Cminus z' z) (Cminus z p)) by ring.
      eapply Rle_lt_trans; [ apply Cmod_triangle | ]. lra.
Qed.

Lemma propagate_step_D : forall p q, U p ->
  (forall k, fseq k p = C0) -> Cmod (Cminus q p) < Rr ->
  forall k, fseq k q = C0.
Proof.
  intros p q Hp Hvan Hq k. apply (chain_vanishes_disk_D p Hp Hvan k q Hq).
Qed.

Lemma seg_all_vanish_D : forall (p w : C) (N : nat), (0 < N)%nat ->
  U p -> U w ->
  (forall k, fseq k p = C0) ->
  Cmod (Cminus w p) / INR N < Rr ->
  forall i, (i <= N)%nat ->
  forall k, fseq k (Cadd p (Cmul (RtoC (INR i * / INR N)) (Cminus w p))) = C0.
Proof.
  intros p w N HN HUp HUw Hvan Hstep i.
  assert (HNr : 0 < INR N) by (apply lt_0_INR; lia).
  induction i as [|i IH]; intros Hi k.
  - replace (Cadd p (Cmul (RtoC (INR 0 * / INR N)) (Cminus w p))) with p.
    2:{ replace (INR 0 * / INR N) with 0 by (simpl; ring).
        change (RtoC 0) with C0. ring. }
    apply Hvan.
  - assert (HUpi : U (Cadd p (Cmul (RtoC (INR i * / INR N)) (Cminus w p)))).
    { change (U (seg p w (INR i * / INR N))). apply HUconv; [ exact HUp | exact HUw | ].
      split.
      - apply Rmult_le_pos; [ apply pos_INR | left; apply Rinv_0_lt_compat; exact HNr ].
      - apply (Rmult_le_reg_r (INR N)); [ exact HNr | ].
        unfold Rdiv. rewrite Rmult_assoc. rewrite Rinv_l by lra.
        rewrite Rmult_1_r. rewrite Rmult_1_l. apply le_INR; lia. }
    apply (propagate_step_D
             (Cadd p (Cmul (RtoC (INR i * / INR N)) (Cminus w p)))
             (Cadd p (Cmul (RtoC (INR (S i) * / INR N)) (Cminus w p)))
             HUpi).
    + apply IH; lia.
    + replace (Cminus (Cadd p (Cmul (RtoC (INR (S i) * / INR N)) (Cminus w p)))
                      (Cadd p (Cmul (RtoC (INR i * / INR N)) (Cminus w p))))
        with (Cmul (Cminus (RtoC (INR (S i) * / INR N)) (RtoC (INR i * / INR N)))
                   (Cminus w p)) by ring.
      replace (Cminus (RtoC (INR (S i) * / INR N)) (RtoC (INR i * / INR N)))
        with (RtoC (/ INR N)).
      2:{ apply Ceq; unfold RtoC, Cminus; cbn [Re Im].
          - rewrite S_INR; field; lra.
          - ring. }
      rewrite Cmod_mul, Cmod_RtoC, Rabs_right by (left; apply Rinv_0_lt_compat; exact HNr).
      unfold Rdiv in Hstep. rewrite Rmult_comm. exact Hstep.
Qed.

Theorem identity_propagate_D : forall p w, U p -> U w ->
  (forall k, fseq k p = C0) -> fseq 0 w = C0.
Proof.
  intros p w HUp HUw Hvan.
  destruct (exists_nat_gt (Cmod (Cminus w p) / Rr)
              ltac:(apply Rle_mult_inv_pos; [ apply Cmod_nonneg | exact HR ])) as [N HNgt].
  set (N' := S N).
  assert (HN' : (0 < N')%nat) by lia.
  assert (HNr' : 0 < INR N') by (apply lt_0_INR; lia).
  assert (HNge : Cmod (Cminus w p) / Rr < INR N') by (unfold N'; rewrite S_INR; lra).
  assert (Hstep : Cmod (Cminus w p) / INR N' < Rr).
  { apply (Rmult_lt_reg_r (INR N')); [ exact HNr' | ].
    unfold Rdiv. rewrite Rmult_assoc. rewrite Rinv_l by lra. rewrite Rmult_1_r.
    apply (Rmult_lt_reg_r (/ Rr)); [ apply Rinv_0_lt_compat; exact HR | ].
    replace (Rr * INR N' * / Rr) with (INR N') by (field; lra).
    unfold Rdiv in HNge. exact HNge. }
  pose proof (seg_all_vanish_D p w N' HN' HUp HUw Hvan Hstep N' (le_n N') 0%nat) as Hend.
  replace (Cadd p (Cmul (RtoC (INR N' * / INR N')) (Cminus w p))) with w in Hend.
  2:{ replace (INR N' * / INR N') with 1 by (field; lra).
      change (RtoC 1) with C1. ring. }
  exact Hend.
Qed.

End PropagateDom.

Print Assumptions identity_propagate_D.
