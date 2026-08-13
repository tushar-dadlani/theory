(* ================================================================= *)
(*  CRemovableExt.v  (identity-theorem plan, brick B1)                 *)
(*                                                                    *)
(*  The REMOVABLE EXTENSION of the quotient  (F(z)-F(w))/(z-w)  at w,   *)
(*  for a holomorphic F.  This discharges the phi-hypotheses of        *)
(*  CCauchyInterior.cauchy_interior_cond from F's differentiability at  *)
(*  w, making the interior Cauchy formula UNCONDITIONAL.               *)
(*                                                                    *)
(*  Structure mirrors PerronRemovable (which does the specific y^s      *)
(*  case): rphi(z) = dw at z=w, (F(z)-F(w))/(z-w) off w; then           *)
(*   - rphi_bd: bounded near w (from is_Cderiv F w dw);                 *)
(*   - rphi_ptcont: pointwise continuous, incl. through w (removable);  *)
(*   - rphi_cc: CcontC rphi (via ptcont_CcontC);                        *)
(*   - rphi_holo_off: holomorphic off w (Cderiv_div + is_Cderiv_congr). *)
(*  For a general holomorphic F the removable bound is DIRECT (the      *)
(*  derivative bound), cleaner than the y^s remainder.                 *)
(*                                                                    *)
(*  Axioms: standard classical-Reals only.                            *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra.
Require Import ComplexField Cmodulus CSegInt Holomorphic CDeriv CHoloCalculus
        PerronRemovable CWindingOffCenter.
Open Scope R_scope.

Definition Ceq_dec (a b : C) : {a = b} + {a <> b}.
Proof.
  destruct (Req_dec_T (Re a) (Re b)) as [HR | HR];
    [ | right; intro H; apply HR; rewrite H; reflexivity ].
  destruct (Req_dec_T (Im a) (Im b)) as [HI | HI];
    [ left; apply Ceq; assumption | right; intro H; apply HI; rewrite H; reflexivity ].
Defined.

Section Removable.
Variable F : C -> C.
Hypothesis HFhol : forall z, exists d, is_Cderiv F z d.
Variable w dw : C.
Hypothesis Hdw : is_Cderiv F w dw.

Definition rphi (z : C) : C :=
  if Ceq_dec z w then dw else Cmul (Cminus (F z) (F w)) (Cinv (Cminus z w)).

Lemma rphi_w : rphi w = dw.
Proof. unfold rphi; destruct (Ceq_dec w w) as [_ | N]; [ reflexivity | exfalso; apply N; reflexivity ]. Qed.

Lemma rphi_off : forall z, z <> w -> rphi z = Cmul (Cminus (F z) (F w)) (Cinv (Cminus z w)).
Proof. intros z Hz; unfold rphi; destruct (Ceq_dec z w) as [E | _]; [ contradiction | reflexivity ]. Qed.

(* h = z - w is nonzero iff z <> w *)
Lemma minus_w_ne : forall z, z <> w -> Cminus z w <> C0.
Proof.
  intros z Hz Hc. apply Hz. apply Ceq.
  - apply (f_equal Re) in Hc; unfold Cminus, C0 in Hc; cbn in Hc; lra.
  - apply (f_equal Im) in Hc; unfold Cminus, C0 in Hc; cbn in Hc; lra.
Qed.

(* the key quotient/remainder algebra:  (F z - F w)/h - dw = (num)/h.    *)
Lemma rphi_minus_dw : forall z (Hz : z <> w),
  Cminus (rphi z) dw
  = Cmul (Cminus (Cminus (F z) (F w)) (Cmul dw (Cminus z w))) (Cinv (Cminus z w)).
Proof.
  intros z Hz. rewrite (rphi_off z Hz).
  assert (Hne := minus_w_ne z Hz).
  symmetry.
  rewrite Cmul_minus_r, Cmul_assoc, (Cinv_r (Cminus z w) Hne), Cmul_1_r. reflexivity.
Qed.

(* bounded near w *)
Lemma rphi_bd : exists M eta, 0 < eta /\
  forall z, Cmod (Cminus z w) < eta -> Cmod (rphi z) <= M.
Proof.
  destruct (Hdw 1 Rlt_0_1) as [del [Hdel Hb]].
  exists (Cmod dw + 1), del. split; [ exact Hdel | ].
  intros z Hz. destruct (Ceq_dec z w) as [Hzw | Hzw].
  - subst z; rewrite rphi_w; pose proof (Cmod_nonneg dw); lra.
  - assert (Hne := minus_w_ne z Hzw).
    assert (Hpos : 0 < Cmod (Cminus z w)) by (pose proof (Cmod_nonneg (Cminus z w));
      destruct (Cmod0 (Cminus z w)) as [Hc _]; assert (Cmod (Cminus z w) <> 0) by
      (intro H0; apply Hne, Hc; exact H0); lra).
    pose proof (Hb (Cminus z w) Hz) as Hrem.
    replace (Cadd w (Cminus z w)) with z in Hrem by (apply Ceq; simpl; ring).
    rewrite Rmult_1_l in Hrem.
    (* Cmod (F z - F w) <= (Cmod dw + 1) * Cmod (z-w) via reverse triangle *)
    pose proof (Cmod_rev_triangle (Cminus (F z) (F w)) (Cmul dw (Cminus z w))) as Hrt.
    rewrite Cmod_mul in Hrt.
    (* Cmod (rphi z) = Cmod(F z-F w) * / Cmod(z-w) *)
    rewrite (rphi_off z Hzw), Cmod_mul, (Cmod_inv (Cminus z w) Hne).
    apply (Rmult_le_reg_r (Cmod (Cminus z w))); [ exact Hpos | ].
    rewrite Rmult_assoc. rewrite Rinv_l by lra. rewrite Rmult_1_r.
    nra.
Qed.

(* pointwise continuous, including through w *)
Lemma rphi_ptcont : forall z eps, 0 < eps -> exists del, 0 < del /\
  forall z', Cmod (Cminus z' z) < del -> Cmod (Cminus (rphi z') (rphi z)) < eps.
Proof.
  intros z eps Heps. destruct (Ceq_dec z w) as [Hzw | Hzw].
  - (* z = w: removability *)
    subst z; rewrite rphi_w.
    destruct (Hdw (eps / 2) ltac:(lra)) as [del [Hdel Hb]].
    exists del; split; [ exact Hdel | ].
    intros z' Hz'. destruct (Ceq_dec z' w) as [Hz'w | Hz'w].
    + subst z'; rewrite rphi_w.
      replace (Cminus dw dw) with C0 by (apply Ceq; simpl; ring).
      rewrite (proj2 (Cmod0 C0) eq_refl); exact Heps.
    + assert (Hne := minus_w_ne z' Hz'w).
      assert (Hpos : 0 < Cmod (Cminus z' w)) by (pose proof (Cmod_nonneg (Cminus z' w));
        destruct (Cmod0 (Cminus z' w)) as [Hc _]; assert (Cmod (Cminus z' w) <> 0) by
        (intro H0; apply Hne, Hc; exact H0); lra).
      pose proof (Hb (Cminus z' w) Hz') as Hrem.
      replace (Cadd w (Cminus z' w)) with z' in Hrem by (apply Ceq; simpl; ring).
      rewrite (rphi_minus_dw z' Hz'w), Cmod_mul, (Cmod_inv (Cminus z' w) Hne).
      apply (Rmult_lt_reg_r (Cmod (Cminus z' w))); [ exact Hpos | ].
      rewrite Rmult_assoc. rewrite Rinv_l by lra. rewrite Rmult_1_r.
      eapply Rle_lt_trans; [ exact Hrem | nra ].
  - (* z <> w: rphi = quotient near z, use is_Cderiv_cont on the quotient *)
    destruct (HFhol z) as [dF HdF].
    assert (Hne := minus_w_ne z Hzw).
    assert (HG : is_Cderiv (fun z' => Cmul (Cminus (F z') (F w)) (Cinv (Cminus z' w))) z
                   (Cadd (Cmul (Cminus dF C0) (Cinv (Cminus z w)))
                         (Cmul (Cminus (F z) (F w))
                               (Cmul (Copp (Cinv (Cmul (Cminus z w) (Cminus z w))))
                                     (Cminus C1 C0))))).
    { apply (Cderiv_div (fun z' => Cminus (F z') (F w)) (fun z' => Cminus z' w) z
               (Cminus dF C0) (Cminus C1 C0)).
      - apply (Cderiv_minus F (fun _ => F w) z dF C0); [ exact HdF | apply Cderiv_const ].
      - apply (Cderiv_minus (fun z' => z') (fun _ => w) z C1 C0);
          [ apply Cderiv_id | apply Cderiv_const ].
      - exact Hne. }
    destruct (is_Cderiv_cont _ z _ HG eps Heps) as [del0 [Hdel0 Hc]].
    exists (Rmin del0 (Cmod (Cminus z w))); split;
      [ apply Rmin_pos; [ exact Hdel0 | pose proof (Cmod_nonneg (Cminus z w));
        destruct (Cmod0 (Cminus z w)) as [Hcm _];
        assert (Cmod (Cminus z w) <> 0) by (intro H0; apply Hne, Hcm; exact H0); lra ] | ].
    intros z' Hz'.
    assert (Hz'w : z' <> w).
    { intro E; subst z'.
      assert (Cmod (Cminus w z) = Cmod (Cminus z w))
        by (replace (Cminus w z) with (Copp (Cminus z w)) by (apply Ceq; simpl; ring);
            apply Cmod_opp).
      assert (Cmod (Cminus w z) < Cmod (Cminus z w))
        by (eapply Rlt_le_trans; [ exact Hz' | apply Rmin_r ]). lra. }
    rewrite (rphi_off z' Hz'w), (rphi_off z Hzw).
    replace z' with (Cadd z (Cminus z' z)) by (apply Ceq; simpl; ring).
    apply Hc. eapply Rlt_le_trans; [ | apply Rmin_l ]. exact Hz'.
Qed.

Lemma rphi_cc : CcontC rphi.
Proof. apply ptcont_CcontC, rphi_ptcont. Qed.

(* holomorphic off w *)
Lemma rphi_holo_off : forall z, z <> w -> exists d, is_Cderiv rphi z d.
Proof.
  intros z Hz. destruct (HFhol z) as [dF HdF].
  assert (Hne := minus_w_ne z Hz).
  eexists.
  apply (is_Cderiv_congr rphi
           (fun z' => Cmul (Cminus (F z') (F w)) (Cinv (Cminus z' w)))
           z _ (Cmod (Cminus z w))).
  - pose proof (Cmod_nonneg (Cminus z w)); destruct (Cmod0 (Cminus z w)) as [Hcm _];
      assert (Cmod (Cminus z w) <> 0) by (intro H0; apply Hne, Hcm; exact H0); lra.
  - intros z' Hz'. apply rphi_off. intro E; subst z'.
    assert (Cmod (Cminus w z) = Cmod (Cminus z w))
      by (replace (Cminus w z) with (Copp (Cminus z w)) by (apply Ceq; simpl; ring);
          apply Cmod_opp). lra.
  - apply (Cderiv_div (fun z' => Cminus (F z') (F w)) (fun z' => Cminus z' w) z
             (Cminus dF C0) (Cminus C1 C0)).
    + apply (Cderiv_minus F (fun _ => F w) z dF C0); [ exact HdF | apply Cderiv_const ].
    + apply (Cderiv_minus (fun z' => z') (fun _ => w) z C1 C0);
        [ apply Cderiv_id | apply Cderiv_const ].
    + exact Hne.
Qed.

End Removable.

Print Assumptions rphi_cc.
Print Assumptions rphi_holo_off.
