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
Require Import ComplexField Cmodulus CSeries CIntegral2 CExpKernel CexpFull
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

Print Assumptions NK_sub.
Print Assumptions NK_cmul.
