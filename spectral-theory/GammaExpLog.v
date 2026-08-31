(* ================================================================= *)
(*  GammaExpLog.v  --  the exp/log bridge for the Gamma product.      *)
(*                                                                    *)
(*  The repo builds 1/Gamma twice:                                    *)
(*    GammaCNe0.Pc      = z e^{gamma z} * Cexpf (Lf z)   (log-sum)    *)
(*    GammaCWeierstrass.Pc = z e^{gamma z} * Wc z        (product)    *)
(*  and proves GammaC * Pc = 1 only for the first (Lf is holomorphic; *)
(*  the infinite product Wc is not known to be).  But the explicit    *)
(*  ANGLE (GammaDir.Wangl) is available only for the second.          *)
(*                                                                    *)
(*  This file links them, per factor:                                 *)
(*                                                                    *)
(*     Cexpf (tterm n z) = wcf z (S n)      on  Re z > -1/2           *)
(*                                                                    *)
(*  Both sides solve F' = F * gterm n with value 1 at z = 0 -- tterm  *)
(*  is by construction the primitive of gterm, and the product factor  *)
(*  (1+z/k)e^{-z/k} has logarithmic derivative 1/(k+z) - 1/k = gterm.  *)
(*  So their quotient has zero derivative on the convex half-plane     *)
(*  Re z > -1/2 and CDerivConst.Cderiv0_const pins it to its value at  *)
(*  0.  No complex logarithm and no branch choice is involved.        *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import ComplexField Cmodulus Holomorphic CDeriv CHoloCalculus
        CexpFull CexpfDeriv CSeries CInfProd CPrimConv CDerivConst
        CPathIntegral GammaCLogTerm GammaCLogSum GammaCWeierstrass CPolarDir.
Open Scope R_scope.

(* ---- the domain ---- *)

Lemma RG_convex : Convex RG.
Proof.
  intros a b Ha Hb s [Hs0 Hs1]. unfold RG, seg in *.
  unfold Cadd, Cmul, Cminus, Copp, RtoC; cbn [Re Im].
  destruct (Rle_lt_dec (Re a) (Re b)) as [Hc|Hc].
  - assert (H : 0 <= s * (Re b - Re a)) by (apply Rmult_le_pos; lra). lra.
  - assert (H : 0 <= (1 - s) * (Re a - Re b)) by (apply Rmult_le_pos; lra). lra.
Qed.

Lemma RG_C0 : RG C0.
Proof. unfold RG, C0; cbn [Re]; lra. Qed.

Lemma Cexpf_zero : Cexpf C0 = C1.
Proof.
  replace C0 with (RtoC 0) by reflexivity.
  rewrite Cexpf_RtoC, exp_0. reflexivity.
Qed.

Lemma tterm_C0 : forall n, tterm n C0 = C0.
Proof. intro n. unfold tterm, PrimC. apply seg_int_self. Qed.

(* ---- the k-th product factor ---- *)

Lemma wcf_val : forall w n, wcf w (S n) =
  Cmul (Cadd C1 (Cdiv w (RtoC (INR (S n)))))
       (Cexpf (Copp (Cdiv w (RtoC (INR (S n)))))).
Proof. reflexivity. Qed.

Lemma wcf_C0 : forall n, wcf C0 (S n) = C1.
Proof.
  intro n. rewrite wcf_val.
  assert (Hk : RtoC (INR (S n)) <> C0) by apply kk_ne0.
  assert (E : Cdiv C0 (RtoC (INR (S n))) = C0) by (unfold Cdiv; ring).
  rewrite E. replace (Copp C0) with C0 by ring. rewrite Cexpf_zero. ring.
Qed.

Lemma wcf_ne0 : forall z n, RG z -> wcf z (S n) <> C0.
Proof.
  intros z n Hz. rewrite wcf_val.
  assert (Hk : RtoC (INR (S n)) <> C0) by apply kk_ne0.
  assert (Hkz : Cadd (RtoC (INR (S n))) z <> C0) by (apply kz_ne0; exact Hz).
  assert (Hfac : Cadd C1 (Cdiv z (RtoC (INR (S n))))
                 = Cmul (Cadd (RtoC (INR (S n))) z) (Cinv (RtoC (INR (S n)))))
    by (field; exact Hk).
  rewrite Hfac.
  intro E.
  assert (Hne : Cmul (Cadd (RtoC (INR (S n))) z) (Cinv (RtoC (INR (S n)))) <> C0).
  { intro E2.
    assert (Hz0 : Cadd (RtoC (INR (S n))) z = C0).
    { transitivity (Cmul (Cmul (Cadd (RtoC (INR (S n))) z) (Cinv (RtoC (INR (S n)))))
                      (RtoC (INR (S n)))); [ field; exact Hk | ].
      rewrite E2. ring. }
    exact (Hkz Hz0). }
  (* a product of two nonzero factors is nonzero *)
  assert (Hex : Cexpf (Copp (Cdiv z (RtoC (INR (S n))))) <> C0) by apply Cexpf_ne0.
  apply Hex.
  transitivity (Cmul (Cinv (Cmul (Cadd (RtoC (INR (S n))) z) (Cinv (RtoC (INR (S n))))))
                  (Cmul (Cmul (Cadd (RtoC (INR (S n))) z) (Cinv (RtoC (INR (S n)))))
                        (Cexpf (Copp (Cdiv z (RtoC (INR (S n)))))))).
  - field. split; assumption.
  - rewrite E. ring.
Qed.

Lemma Cderiv_mul_cst_r : forall F z dF c,
  is_Cderiv F z dF -> is_Cderiv (fun w => Cmul (F w) c) z (Cmul dF c).
Proof.
  intros F z dF c HF.
  replace (Cmul dF c) with (Cadd (Cmul dF c) (Cmul (F z) C0)) by ring.
  apply (Cderiv_mul F (fun _ => c) z dF C0); [ exact HF | apply Cderiv_const ].
Qed.

(* ---- both sides solve F' = F * gterm ---- *)

Lemma wcf_deriv : forall z n, RG z ->
  is_Cderiv (fun w => wcf w (S n)) z (Cmul (wcf z (S n)) (gterm n z)).
Proof.
  intros z n Hz.
  assert (Hk : RtoC (INR (S n)) <> C0) by apply kk_ne0.
  assert (Hkz : Cadd (RtoC (INR (S n))) z <> C0) by (apply kz_ne0; exact Hz).
  set (kk := RtoC (INR (S n))) in *.
  assert (Hgt : gterm n z = Cmul (Copp z) (Cinv (Cmul kk (Cadd kk z))))
    by (unfold kk; apply gterm_closed; exact Hz).
  assert (Hfun : (fun w => wcf w (S n))
                 = (fun w => Cmul (Cadd C1 (Cdiv w kk)) (Cexpf (Copp (Cdiv w kk)))))
    by reflexivity.
  rewrite Hfun.
  assert (Hval : wcf z (S n) = Cmul (Cadd C1 (Cdiv z kk)) (Cexpf (Copp (Cdiv z kk))))
    by reflexivity.
  rewrite Hval.
  assert (Hf : is_Cderiv (fun w => Cadd C1 (Cdiv w kk)) z (Cmul C1 (Cinv kk))).
  { replace (Cmul C1 (Cinv kk)) with (Cadd C0 (Cmul C1 (Cinv kk))) by ring.
    apply Cderiv_add; [ apply Cderiv_const | ].
    unfold Cdiv. apply Cderiv_mul_cst_r. apply Cderiv_id. }
  assert (Hg : is_Cderiv (fun w => Cexpf (Copp (Cdiv w kk))) z
                 (Cmul (Cexpf (Copp (Cdiv z kk))) (Copp (Cmul C1 (Cinv kk))))).
  { apply (Cexpf_comp_deriv (fun w => Copp (Cdiv w kk)) z
             (Copp (Cmul C1 (Cinv kk)))).
    apply Cderiv_opp.
    unfold Cdiv. apply Cderiv_mul_cst_r. apply Cderiv_id. }
  pose proof (Cderiv_mul (fun w => Cadd C1 (Cdiv w kk))
                (fun w => Cexpf (Copp (Cdiv w kk))) z _ _ Hf Hg) as Hm.
  cbv beta in Hm.
  replace (Cmul (Cmul (Cadd C1 (Cdiv z kk)) (Cexpf (Copp (Cdiv z kk)))) (gterm n z))
    with (Cadd (Cmul (Cmul C1 (Cinv kk)) (Cexpf (Copp (Cdiv z kk))))
               (Cmul (Cadd C1 (Cdiv z kk))
                     (Cmul (Cexpf (Copp (Cdiv z kk))) (Copp (Cmul C1 (Cinv kk))))))
    by (rewrite Hgt; field; repeat split; assumption).
  exact Hm.
Qed.

(* ---- the quotient is constant ---- *)

Definition Qf (n : nat) (w : C) : C :=
  Cmul (Cexpf (tterm n w)) (Cinv (wcf w (S n))).

Lemma Qf_deriv0 : forall n z, RG z -> is_Cderiv (Qf n) z C0.
Proof.
  intros n z Hz.
  assert (Hne : wcf z (S n) <> C0) by (apply wcf_ne0; exact Hz).
  assert (HF : is_Cderiv (fun w => Cexpf (tterm n w)) z
                 (Cmul (Cexpf (tterm n z)) (gterm n z)))
    by (apply (Cexpf_comp_deriv (tterm n) z (gterm n z));
        apply tterm_deriv; exact Hz).
  assert (HG : is_Cderiv (fun w => wcf w (S n)) z (Cmul (wcf z (S n)) (gterm n z)))
    by (apply wcf_deriv; exact Hz).
  pose proof (Cderiv_div (fun w => Cexpf (tterm n w)) (fun w => wcf w (S n)) z
                _ _ HF HG Hne) as Hd.
  cbv beta in Hd. unfold Qf.
  replace C0 with
    (Cadd (Cmul (Cmul (Cexpf (tterm n z)) (gterm n z)) (Cinv (wcf z (S n))))
          (Cmul (Cexpf (tterm n z))
                (Cmul (Copp (Cinv (Cmul (wcf z (S n)) (wcf z (S n)))))
                      (Cmul (wcf z (S n)) (gterm n z)))))
    by (field; exact Hne).
  exact Hd.
Qed.

Theorem exp_tterm : forall n z, RG z -> Cexpf (tterm n z) = wcf z (S n).
Proof.
  intros n z Hz.
  assert (HQ : Qf n z = Qf n C0)
    by (apply (Cderiv0_const RG RG_convex (Qf n)
                 (fun w Hw => Qf_deriv0 n w Hw) z C0 Hz RG_C0)).
  assert (HQ0 : Qf n C0 = C1).
  { unfold Qf. rewrite tterm_C0, wcf_C0, Cexpf_zero.
    replace (Cinv C1) with C1 by (field; exact C1_neq_C0). ring. }
  rewrite HQ0 in HQ. unfold Qf in HQ.
  assert (Hne : wcf z (S n) <> C0) by (apply wcf_ne0; exact Hz).
  transitivity (Cmul (Cmul (Cexpf (tterm n z)) (Cinv (wcf z (S n)))) (wcf z (S n))).
  - field. exact Hne.
  - rewrite HQ. ring.
Qed.

(* ================================================================= *)
(*  From the per-factor bridge to the whole product.                  *)
(* ================================================================= *)

Lemma RG_of_Re : forall z, 0 < Re z -> RG z.
Proof. intros z Hz. unfold RG. lra. Qed.

Lemma wcf_zero : forall z, wcf z 0 = C1.
Proof. reflexivity. Qed.

Lemma Cexpf_Cpsum : forall z N, RG z ->
  Cexpf (Cpsum (fun k => tterm k z) N) = Pprod (wcf z) (S N).
Proof.
  intros z N Hz. induction N as [| N IH].
  - cbn [Cpsum]. rewrite Pprod_S. cbn [Pprod].
    rewrite wcf_zero, (exp_tterm 0 z Hz). ring.
  - cbn [Cpsum]. rewrite Cexpf_add, IH, Pprod_S, (exp_tterm (S N) z Hz).
    reflexivity.
Qed.

Lemma CUn_cv_Cexpf : forall u l,
  CUn_cv u l -> CUn_cv (fun n => Cexpf (u n)) (Cexpf l).
Proof.
  intros u l H eps Heps.
  destruct (is_Cderiv_cont Cexpf l (Cexpf l) (Cexpf_deriv l) eps Heps)
    as [del [Hdel Hc]].
  destruct (H del Hdel) as [N HN].
  exists N. intros n Hn.
  assert (Hh : Cmod (Cminus (u n) l) < del) by (apply HN; exact Hn).
  pose proof (Hc (Cminus (u n) l) Hh) as Hlt.
  replace (Cadd l (Cminus (u n) l)) with (u n) in Hlt by ring.
  exact Hlt.
Qed.

Lemma CUn_cv_shift : forall u l, CUn_cv u l -> CUn_cv (fun n => u (S n)) l.
Proof.
  intros u l H eps Heps. destruct (H eps Heps) as [N HN].
  exists N. intros n Hn. apply HN. lia.
Qed.

Lemma CUn_cv_unique : forall u l1 l2, CUn_cv u l1 -> CUn_cv u l2 -> l1 = l2.
Proof.
  intros u l1 l2 H1 H2.
  destruct (proj1 (CUn_cv_comp u l1) H1) as [R1 I1].
  destruct (proj1 (CUn_cv_comp u l2) H2) as [R2 I2].
  apply Ceq.
  - apply (UL_sequence (fun n => Re (u n))); assumption.
  - apply (UL_sequence (fun n => Im (u n))); assumption.
Qed.

Theorem Cexpf_Lf : forall z, 0 < Re z -> Cexpf (Lf z) = Wc z.
Proof.
  intros z Hz.
  assert (HL : CUn_cv (Cpsum (fun k => tterm k z)) (Lf z)) by (apply Lf_series; exact Hz).
  assert (H1 : CUn_cv (fun N => Cexpf (Cpsum (fun k => tterm k z) N)) (Cexpf (Lf z)))
    by (apply CUn_cv_Cexpf; exact HL).
  assert (H2 : CUn_cv (fun N => Pprod (wcf z) (S N)) (Cexpf (Lf z))).
  { intros eps Heps. destruct (H1 eps Heps) as [N HN].
    exists N. intros n Hn.
    rewrite <- (Cexpf_Cpsum z n (RG_of_Re z Hz)). apply HN; exact Hn. }
  assert (H3 : CUn_cv (fun N => Pprod (wcf z) (S N)) (Wc z))
    by (apply CUn_cv_shift; apply Wc_spec).
  exact (CUn_cv_unique _ _ _ H2 H3).
Qed.

(* ---- the two Pc's coincide, so the product is nonvanishing ---- *)

Theorem Wc_ne0 : forall z, 0 < Re z -> Wc z <> C0.
Proof.
  intros z Hz. rewrite <- (Cexpf_Lf z Hz). apply Cexpf_ne0.
Qed.
