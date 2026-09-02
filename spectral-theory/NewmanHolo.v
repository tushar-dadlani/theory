(* ================================================================= *)
(*  NewmanHolo.v  --  the truncated Newman transform is holomorphic    *)
(*  IN z.  Needed by E5's contour identity.                            *)
(*                                                                    *)
(*  CLaplace.gT_holo proves this for continuous f via Cintf.  Its two  *)
(*  analytic ingredients, lint_increment and lint_increment_mod, turn  *)
(*  out to be generalised over f (they use no continuity), so they are *)
(*  REUSED verbatim at f := nfC.  Only the integral layer changes:     *)
(*  Cintf_sub / Cintf_cmul_l / Cintf_ML become their CintfD versions.  *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia Arith.
Require Import ComplexField Cmodulus Holomorphic CDeriv CSeries CIntegral2 CSegInt CLeibniz CExpKernel CexpFull
        Chebyshev ChebyshevBound ChebyshevPsiR PsiRIntegrable TintCoV
        CIntegralD CIntegralDLin NewmanTransform CLaplace.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  nfC times ANY continuous kernel is integrable, by the cell         *)
(*  argument -- generalising lintN_Re_int / lintN_Im_int.              *)
(* ----------------------------------------------------------------- *)

Lemma nfK_Re_int : forall (K : R -> C), Ccont K ->
  forall a b, 0 <= a -> a <= b ->
  Riemann_integrable (fun t => Re (Cmul (nfC t) (K t))) a b.
Proof.
  intros K HK a b Ha Hab.
  apply (cellwise_integrable (fun t => Re (Cmul (nfC t) (K t))));
    [ | exact Ha | exact Hab ].
  intros N c d HN Hc Hcd Hd.
  apply (Riemann_integrable_ext_open _
           (fun t => hu N (exp t) * exp t * Re (K t)) c d Hcd).
  - intros t Ht.
    replace (Re (Cmul (nfC t) (K t))) with (nf t * Re (K t))
      by (unfold nfC, Cmul, RtoC; cbn [Re Im]; ring).
    rewrite (nf_cell_eq N c d t HN Hc Hd Ht). reflexivity.
  - destruct (Rle_lt_or_eq_dec c d Hcd) as [Hlt | He];
      [ | rewrite <- He; apply RiemannInt_P7 ].
    apply RiemannInt_P6; [ exact Hlt | ].
    intros x Hx. apply continuity_pt_mult.
    + apply continuity_pt_mult; [ | apply cont_exp2 ].
      apply (continuity_pt_comp exp (hu N));
        [ apply cont_exp2 | apply hu_cont; apply exp_pos ].
    + apply (proj1 HK).
Qed.

Lemma nfK_Im_int : forall (K : R -> C), Ccont K ->
  forall a b, 0 <= a -> a <= b ->
  Riemann_integrable (fun t => Im (Cmul (nfC t) (K t))) a b.
Proof.
  intros K HK a b Ha Hab.
  apply (cellwise_integrable (fun t => Im (Cmul (nfC t) (K t))));
    [ | exact Ha | exact Hab ].
  intros N c d HN Hc Hcd Hd.
  apply (Riemann_integrable_ext_open _
           (fun t => hu N (exp t) * exp t * Im (K t)) c d Hcd).
  - intros t Ht.
    replace (Im (Cmul (nfC t) (K t))) with (nf t * Im (K t))
      by (unfold nfC, Cmul, RtoC; cbn [Re Im]; ring).
    rewrite (nf_cell_eq N c d t HN Hc Hd Ht). reflexivity.
  - destruct (Rle_lt_or_eq_dec c d Hcd) as [Hlt | He];
      [ | rewrite <- He; apply RiemannInt_P7 ].
    apply RiemannInt_P6; [ exact Hlt | ].
    intros x Hx. apply continuity_pt_mult.
    + apply continuity_pt_mult; [ | apply cont_exp2 ].
      apply (continuity_pt_comp exp (hu N));
        [ apply cont_exp2 | apply hu_cont; apply exp_pos ].
    + apply (proj2 HK).
Qed.

(* ----------------------------------------------------------------- *)
(*  The "nfC times a continuous kernel" algebra.  Every integrand in   *)
(*  the increment argument has this shape, so linearity is proved once *)
(*  at the kernel level instead of per-integrand.                      *)
(* ----------------------------------------------------------------- *)

Definition NK (K : R -> C) (HK : Ccont K) (a b : R) (Ha : 0 <= a) (Hab : a <= b) : C :=
  CintfD (fun t => Cmul (nfC t) (K t)) a b
    (nfK_Re_int K HK a b Ha Hab) (nfK_Im_int K HK a b Ha Hab).

Lemma NK_irrel : forall K HK HK' a b Ha Hab Ha' Hab',
  NK K HK a b Ha Hab = NK K HK' a b Ha' Hab'.
Proof. intros; unfold NK; apply CintfD_irrel. Qed.

Lemma NK_sub : forall K1 HK1 K2 HK2 K3 HK3 a b Ha Hab,
  (forall t, K3 t = Cminus (K1 t) (K2 t)) ->
  NK K3 HK3 a b Ha Hab = Cminus (NK K1 HK1 a b Ha Hab) (NK K2 HK2 a b Ha Hab).
Proof.
  intros K1 HK1 K2 HK2 K3 HK3 a b Ha Hab Heq.
  assert (Hptw : forall t, Cmul (nfC t) (K3 t)
                 = Cminus (Cmul (nfC t) (K1 t)) (Cmul (nfC t) (K2 t)))
    by (intro t; rewrite Heq; ring).
  assert (prRe : Riemann_integrable
            (fun t => Re (Cminus (Cmul (nfC t) (K1 t)) (Cmul (nfC t) (K2 t)))) a b).
  { apply (Riemann_integrable_ext_open _ (fun t => Re (Cmul (nfC t) (K3 t))) a b Hab).
    - intros t Ht. rewrite Hptw. reflexivity.
    - apply nfK_Re_int; assumption. }
  assert (prIm : Riemann_integrable
            (fun t => Im (Cminus (Cmul (nfC t) (K1 t)) (Cmul (nfC t) (K2 t)))) a b).
  { apply (Riemann_integrable_ext_open _ (fun t => Im (Cmul (nfC t) (K3 t))) a b Hab).
    - intros t Ht. rewrite Hptw. reflexivity.
    - apply nfK_Im_int; assumption. }
  unfold NK.
  rewrite (CintfD_ext_open (fun t => Cmul (nfC t) (K3 t))
             (fun t => Cminus (Cmul (nfC t) (K1 t)) (Cmul (nfC t) (K2 t)))
             a b _ _ prRe prIm Hab (fun t _ => Hptw t)).
  apply CintfD_sub; exact Hab.
Qed.

Lemma NK_cmul : forall c K1 HK1 K2 HK2 a b Ha Hab,
  (forall t, K2 t = Cmul c (K1 t)) ->
  NK K2 HK2 a b Ha Hab = Cmul c (NK K1 HK1 a b Ha Hab).
Proof.
  intros c K1 HK1 K2 HK2 a b Ha Hab Heq.
  assert (Hptw : forall t, Cmul (nfC t) (K2 t) = Cmul c (Cmul (nfC t) (K1 t)))
    by (intro t; rewrite Heq; ring).
  assert (prRe : Riemann_integrable
            (fun t => Re (Cmul c (Cmul (nfC t) (K1 t)))) a b).
  { apply (Riemann_integrable_ext_open _ (fun t => Re (Cmul (nfC t) (K2 t))) a b Hab).
    - intros t Ht. rewrite Hptw. reflexivity.
    - apply nfK_Re_int; assumption. }
  assert (prIm : Riemann_integrable
            (fun t => Im (Cmul c (Cmul (nfC t) (K1 t)))) a b).
  { apply (Riemann_integrable_ext_open _ (fun t => Im (Cmul (nfC t) (K2 t))) a b Hab).
    - intros t Ht. rewrite Hptw. reflexivity.
    - apply nfK_Im_int; assumption. }
  unfold NK.
  rewrite (CintfD_ext_open (fun t => Cmul (nfC t) (K2 t))
             (fun t => Cmul c (Cmul (nfC t) (K1 t)))
             a b _ _ prRe prIm Hab (fun t _ => Hptw t)).
  apply CintfD_cmul_l; exact Hab.
Qed.

Lemma NK_ML : forall K HK a b Ha Hab M,
  (forall u, a <= u <= b -> Cmod (Cmul (nfC u) (K u)) <= M) ->
  Cmod (NK K HK a b Ha Hab) <= 2 * M * (b - a).
Proof. intros; unfold NK; apply CintfD_ML; assumption. Qed.


(* ----------------------------------------------------------------- *)
(*  The two kernels, and LTN / LTN' in NK form.                        *)
(* ----------------------------------------------------------------- *)

Definition Kz (z : C) (t : R) : C := cexpzt (Copp z) t.
Definition Kd (z : C) (t : R) : C := Cmul (Copp (RtoC t)) (cexpzt (Copp z) t).

Lemma Kz_cont : forall z, Ccont (Kz z).
Proof. intro z; apply Ccont_cexpzt. Qed.

Lemma Kd_cont : forall z, Ccont (Kd z).
Proof.
  intro z; apply Ccont_mul; [ apply negRtoC_cont | apply Ccont_cexpzt ].
Qed.

Lemma LTN_as_NK : forall z a b Ha Hab,
  LTN z a b Ha Hab = NK (Kz z) (Kz_cont z) a b Ha Hab.
Proof. intros; unfold LTN, NK; apply CintfD_irrel. Qed.

Definition LTN' (z : C) (a b : R) (Ha : 0 <= a) (Hab : a <= b) : C :=
  NK (Kd z) (Kd_cont z) a b Ha Hab.

(* the increment kernel, in the exact shape of lint_increment's RHS *)
Definition brk (z h : C) (t : R) : C :=
  Cmul (cexpzt (Copp z) t)
       (Cminus (Cminus (Cexpf (Cmul (Copp h) (RtoC t))) C1)
               (Cmul (Copp h) (RtoC t))).

Lemma brk_cont : forall z h, Ccont (brk z h).
Proof.
  intros z h. apply Ccont_mul; [ apply Ccont_cexpzt | ].
  apply Ccont_sub;
    [ apply Ccont_sub; [ apply (Ccont_cexpzt (Copp h)) | apply Ccont_const ] | ].
  apply Ccont_mul; [ apply Ccont_const | ].
  apply (Ccont_RtoC (fun t => t)); intro x;
    apply derivable_continuous_pt, derivable_pt_id.
Qed.

Lemma brk_id : forall z h t,
  brk z h t = Cminus (Cminus (Kz (Cadd z h) t) (Kz z t)) (Cmul h (Kd z t)).
Proof.
  intros z h t. unfold brk, Kz, Kd. rewrite (cexpzt_add z h t). ring.
Qed.

(* ----------------------------------------------------------------- *)
(*  LTN is holomorphic in z, with derivative LTN'.                     *)
(* ----------------------------------------------------------------- *)

Theorem LTN_holo : forall T (HT : 0 <= T) z,
  is_Cderiv (fun w => LTN w 0 T (Rle_refl 0) HT) z (LTN' z 0 T (Rle_refl 0) HT).
Proof.
  intros T HT z eps Heps.
  set (B := Kup + 1).
  assert (HB0 : 0 <= B) by (pose proof Kup_pos; unfold B; lra).
  set (EB := exp (Rabs (Re z) * T)). set (ET := exp T).
  assert (HEB : 0 < EB) by apply exp_pos. assert (HET : 0 < ET) by apply exp_pos.
  set (K0 := 3 * B * (T * T) * EB * ET).
  assert (HK0 : 0 <= K0) by (unfold K0; repeat apply Rmult_le_pos; lra).
  set (K := 2 * K0 * T + 1).
  assert (HK : 0 < K)
    by (unfold K; assert (0 <= 2 * K0 * T) by (repeat apply Rmult_le_pos; lra); lra).
  exists (Rmin 1 (eps / K)); split;
    [ apply Rmin_pos; [ lra | apply Rdiv_lt_0_compat; lra ] | ].
  intros h Hh.
  assert (Hh1 : Cmod h < 1) by (eapply Rlt_le_trans; [ exact Hh | apply Rmin_l ]).
  assert (HhK : Cmod h < eps / K) by (eapply Rlt_le_trans; [ exact Hh | apply Rmin_r ]).
  assert (Hh0 : 0 <= Cmod h) by apply Cmod_nonneg.
  assert (HT0 : 0 <= T) by exact HT.
  (* the increment collapses to a single NK *)
  assert (HD : Ccont (fun t => Cminus (Kz (Cadd z h) t) (Kz z t)))
    by (apply Ccont_sub; apply Kz_cont).
  assert (HE : Ccont (fun t => Cmul h (Kd z t)))
    by (apply Ccont_scal, Kd_cont).
  assert (Hrw : Cminus (Cminus (LTN (Cadd z h) 0 T (Rle_refl 0) HT)
                               (LTN z 0 T (Rle_refl 0) HT))
                       (Cmul (LTN' z 0 T (Rle_refl 0) HT) h)
              = NK (brk z h) (brk_cont z h) 0 T (Rle_refl 0) HT).
  { rewrite (NK_sub (fun t => Cminus (Kz (Cadd z h) t) (Kz z t)) HD
               (fun t => Cmul h (Kd z t)) HE (brk z h) (brk_cont z h)
               0 T (Rle_refl 0) HT (fun t => brk_id z h t)).
    rewrite (NK_sub (Kz (Cadd z h)) (Kz_cont (Cadd z h)) (Kz z) (Kz_cont z)
               (fun t => Cminus (Kz (Cadd z h) t) (Kz z t)) HD
               0 T (Rle_refl 0) HT (fun t => eq_refl)).
    rewrite (NK_cmul h (Kd z) (Kd_cont z) (fun t => Cmul h (Kd z t)) HE
               0 T (Rle_refl 0) HT (fun t => eq_refl)).
    rewrite !LTN_as_NK. unfold LTN'. ring. }
  rewrite Hrw.
  (* ML estimate with the uniform per-t bound K0 * Cmod h^2 *)
  eapply Rle_trans.
  { apply (NK_ML (brk z h) (brk_cont z h) 0 T (Rle_refl 0) HT (K0 * Cmod h ^ 2)).
    intros t Ht.
    replace (Cmul (nfC t) (brk z h t))
      with (Cminus (Cminus (lint nfC (Cadd z h) t) (lint nfC z t))
                   (Cmul h (ldint nfC z t)))
      by (rewrite (lint_increment nfC z h t); reflexivity).
    eapply Rle_trans; [ apply lint_increment_mod; lra | ].
    assert (E1 : exp (- Re z * t) <= EB).
    { apply exp_le_compat. apply Rle_trans with (Rabs (Re z) * t).
      - apply Rmult_le_compat_r; [ lra | ].
        eapply Rle_trans; [ apply Rle_abs | rewrite Rabs_Ropp; apply Rle_refl ].
      - apply Rmult_le_compat_l; [ apply Rabs_pos | lra ]. }
    assert (E2 : exp (Cmod h * t) <= ET).
    { apply exp_le_compat. apply Rle_trans with (1 * T); [ | lra ].
      apply Rmult_le_compat; lra. }
    assert (Hf0 : 0 <= Cmod (nfC t)) by apply Cmod_nonneg.
    assert (Hft : Cmod (nfC t) <= B)
      by (unfold nfC, B; rewrite Cmod_RtoC; apply nf_bound; lra).
    assert (Ht2 : (Cmod h * t) ^ 2 <= Cmod h ^ 2 * (T * T)).
    { rewrite Rpow_mult_distr. apply Rmult_le_compat_l; [ apply pow2_ge_0 | ].
      replace (t ^ 2) with (t * t) by ring. apply Rmult_le_compat; lra. }
    apply Rle_trans with (B * EB * (3 * (Cmod h ^ 2 * (T * T)) * ET)).
    - apply Rmult_le_compat.
      + apply Rmult_le_pos; [ exact Hf0 | left; apply exp_pos ].
      + apply Rmult_le_pos;
          [ apply Rmult_le_pos; [ lra | apply pow2_ge_0 ] | left; apply exp_pos ].
      + apply Rmult_le_compat; [ exact Hf0 | left; apply exp_pos | exact Hft | exact E1 ].
      + apply Rmult_le_compat.
        * apply Rmult_le_pos; [ lra | apply pow2_ge_0 ].
        * left; apply exp_pos.
        * apply Rmult_le_compat_l; [ lra | exact Ht2 ].
        * exact E2.
    - unfold K0; apply Req_le; ring. }
  replace (T - 0) with T by ring.
  apply Rle_trans with ((2 * K0 * T) * Cmod h * Cmod h); [ apply Req_le; ring | ].
  apply Rmult_le_compat_r; [ exact Hh0 | ].
  apply Rle_trans with (2 * K0 * T * (eps / K)).
  - apply Rmult_le_compat_l; [ repeat apply Rmult_le_pos; lra | left; exact HhK ].
  - apply Rle_trans with (K * (eps / K)); [ | apply Req_le; field; lra ].
    apply Rmult_le_compat_r; [ apply Rlt_le, Rdiv_lt_0_compat; lra | unfold K; lra ].
Qed.

Print Assumptions LTN_holo.
