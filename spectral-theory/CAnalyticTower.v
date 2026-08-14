(* ================================================================= *)
(*  CAnalyticTower.v  (identity-theorem plan, FE chain brick 3)         *)
(*                                                                    *)
(*  Holomorphic => analytic, the inductive engine.  For a fixed         *)
(*  continuous g on the circle |z| = Rr, the Cauchy power integrals      *)
(*     Psi m (w) = oint_{|z|=Rr} g(z) / (z - w)^m dz                    *)
(*  form a derivative tower:                                            *)
(*     d/dw Psi m (w) = m . Psi (S m) (w)      (|w| < Rr/2)             *)
(*  proved from cauchy_integral_holo (the Cauchy-power integral is       *)
(*  holomorphic) after transferring the fixed-centre clamp to the        *)
(*  origin clamp via is_Cderiv_congr.  Iterated, this gives all higher   *)
(*  derivatives of a holomorphic F as Cauchy integrals -- the tower      *)
(*  the domain-restricted identity theorem consumes.                    *)
(*                                                                    *)
(*  Axioms: standard classical-Reals only.                            *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Factorial.
Require Import ComplexField Cmodulus Holomorphic CDeriv CIntegral2 CSegInt CPathIntegral
        CLeibniz RootsOfUnity CWindingOffCenter CCauchyAnalytic PerronRemovable.
Open Scope R_scope.

(* scalar reassociation of the kernel (fresh vars: ring treats Cpow/Cinv
   subterms as atoms) *)
Lemma scal3 : forall A c B D : C,
  Cmul (Cmul A (Cmul c B)) D = Cmul c (Cmul (Cmul A B) D).
Proof. intros; ring. Qed.

(* derivative of a scalar multiple *)
Lemma Cderiv_scal : forall (k : C) (F : C -> C) (z d : C),
  is_Cderiv F z d -> is_Cderiv (fun w => Cmul k (F w)) z (Cmul k d).
Proof.
  intros k F z d HF.
  pose proof (Cderiv_mul (fun _ => k) F z C0 d (Cderiv_const k z) HF) as H.
  replace (Cmul k d) with (Cadd (Cmul C0 (F z)) (Cmul k d)) by ring.
  exact H.
Qed.

(* the arc stays off any interior point *)
Lemma arc_ne_pt : forall Rr w, 0 < Rr -> Cmod w < Rr ->
  forall u, Cminus (arc Rr u) w <> C0.
Proof.
  intros Rr w HR Hw u Hc.
  assert (H : Rr - Cmod w <= Cmod (Cminus (arc Rr u) w)).
  { eapply Rle_trans; [ | apply Cmod_rev_triangle ].
    rewrite (Cmod_arc Rr u) by lra. lra. }
  rewrite Hc, (proj2 (Cmod0 C0) eq_refl) in H. lra.
Qed.

Section Tower.
Variable g : C -> C.
Variable Rr : R.
Hypothesis HR : 0 < Rr.
Hypothesis Hg : CcontC g.
Hypothesis Hgb : exists Mg, 0 <= Mg /\ forall u, Cmod (g (arc Rr u)) <= Mg.

Lemma H0R : Cmod C0 < Rr.
Proof. rewrite (proj2 (Cmod0 C0) eq_refl); exact HR. Qed.

(* the origin-clamped Cauchy power integral: a TOTAL C -> C function
   equal to the true integral on |w| < Rr/2 *)
Definition Psi (m : nat) : C -> C := PhiN g Rr C0 m HR H0R Hg.

(* Dn (the derivative kernel from cauchy_integral_holo) is m times the
   (m+1)-power kernel *)
Lemma Dn_eq_scal : forall z m u,
  Dn g Rr z m u = Cmul (RtoC (INR m)) (Kwn g Rr (S m) z u).
Proof. intros z m u. unfold Dn, Kwn. apply scal3. Qed.

Lemma Psi_step : forall m z, Cmod z < Rr / 2 ->
  is_Cderiv (Psi m) z (Cmul (RtoC (INR m)) (Psi (S m) z)).
Proof.
  intros m z Hz.
  pose proof (Cmod_nonneg z) as Hcz.
  assert (HzR : Cmod z < Rr) by lra.
  assert (Hpi : 0 <= 2 * PI) by (generalize PI_RGT_0; lra).
  assert (Hcl0z : clampw Rr C0 z = z).
  { apply clampw_id. rewrite (proj2 (Cmod0 C0) eq_refl).
    replace (Cminus z C0) with z by ring. lra. }
  (* the derivative from cauchy_integral_holo, clamp centred at z *)
  pose proof (cauchy_integral_holo g Rr z m HR HzR Hg Hgb) as Hd.
  assert (Hval : Cintf (Dn g Rr z m) (Dn_cont g Rr z m HR HzR Hg) 0 (2 * PI)
                 = Cmul (RtoC (INR m)) (Psi (S m) z)).
  { assert (Harc : forall u, Cminus (arc Rr u) z <> C0)
      by (apply arc_ne_pt; [ exact HR | exact HzR ]).
    assert (Hkc : Ccont (Kwn g Rr (S m) z))
      by (apply (Kwn_cont g Rr (S m) Hg z); exact Harc).
    assert (Hsc : Ccont (fun u => Cmul (RtoC (INR m)) (Kwn g Rr (S m) z u)))
      by (apply Ccont_scal; exact Hkc).
    rewrite (Cintf_ext (Dn g Rr z m)
               (fun u => Cmul (RtoC (INR m)) (Kwn g Rr (S m) z u))
               (Dn_cont g Rr z m HR HzR Hg) Hsc 0 (2 * PI)
               (fun u => Dn_eq_scal z m u)).
    rewrite (Cintf_cmul_l (RtoC (INR m)) (Kwn g Rr (S m) z) Hkc Hsc 0 (2 * PI) Hpi).
    f_equal.
    unfold Psi, PhiN.
    apply Cintf_ext. intro u. rewrite Hcl0z. reflexivity. }
  rewrite Hval in Hd.
  (* transfer origin clamp <- z clamp on a small disk about z *)
  set (r := Rr / 2 - Cmod z).
  apply (is_Cderiv_congr (Psi m) (PhiN g Rr z m HR HzR Hg) z
           (Cmul (RtoC (INR m)) (Psi (S m) z)) r).
  - unfold r; lra.
  - intros w Hw. unfold r in Hw.
    assert (Hwmod : Cmod w < Rr / 2).
    { assert (Cmod w <= Cmod z + Cmod (Cminus w z)).
      { replace w with (Cadd z (Cminus w z)) at 1 by ring. apply Cmod_triangle. }
      lra. }
    assert (Hcl0w : clampw Rr C0 w = w).
    { apply clampw_id. rewrite (proj2 (Cmod0 C0) eq_refl).
      replace (Cminus w C0) with w by ring. lra. }
    assert (Hclzw : clampw Rr z w = w).
    { apply clampw_id. lra. }
    unfold Psi, PhiN.
    apply Cintf_ext. intro u. rewrite Hcl0w, Hclzw. reflexivity.
  - exact Hd.
Qed.

(* the derivative tower: fseq k = (k! / 2 pi i) . Psi (k+1) *)
Definition cc : C := Cinv (mkC 0 (2 * PI)).
Definition fseq (k : nat) : C -> C :=
  fun w => Cmul (RtoC (INR (fact k))) (Cmul cc (Psi (S k) w)).

Lemma fact_S_RtoC : forall k,
  RtoC (INR (fact (S k))) = Cmul (RtoC (INR (S k))) (RtoC (INR (fact k))).
Proof. intro k. rewrite <- RtoC_mul, <- mult_INR. reflexivity. Qed.

Theorem fseq_chain : forall k z, Cmod z < Rr / 2 ->
  is_Cderiv (fseq k) z (fseq (S k) z).
Proof.
  intros k z Hz.
  pose proof (Psi_step (S k) z Hz) as Hp.
  pose proof (Cderiv_scal cc (Psi (S k)) z
                (Cmul (RtoC (INR (S k))) (Psi (S (S k)) z)) Hp) as H1.
  pose proof (Cderiv_scal (RtoC (INR (fact k)))
                (fun w => Cmul cc (Psi (S k) w)) z
                (Cmul cc (Cmul (RtoC (INR (S k))) (Psi (S (S k)) z))) H1) as H2.
  assert (Hgoal : fseq (S k) z
    = Cmul (RtoC (INR (fact k)))
        (Cmul cc (Cmul (RtoC (INR (S k))) (Psi (S (S k)) z)))).
  { unfold fseq. rewrite fact_S_RtoC. ring. }
  rewrite Hgoal. exact H2.
Qed.

End Tower.

Print Assumptions Psi_step.
Print Assumptions fseq_chain.
