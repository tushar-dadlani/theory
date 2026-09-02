(* ================================================================= *)
(*  NewmanTransform.v  --  Newman's Laplace transform as an HONEST     *)
(*  integral.  Brick E2 of docs/pnt_endgame_plan.md.                   *)
(*                                                                    *)
(*  LaplaceFull.LT is Cintf-based, hence needs Ccont f, which Newman's *)
(*  step-function f does not satisfy.  LTN is the same object built on *)
(*  CIntegralD.CintfD instead.                                         *)
(*                                                                    *)
(*  Integrability comes from the SAME cell argument as TintCoV: on each *)
(*  open cell (ln N, ln (N+1)) the integrand agrees with a continuous  *)
(*  function.  That gluing is abstracted here as cellwise_integrable,  *)
(*  which TintCoV.nf_int_k had inlined for one integrand.              *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia Arith.
Require Import ComplexField Cmodulus CIntegral2 CExpKernel
        Chebyshev ChebyshevBound ChebyshevPsiR PsiRIntegrable TintCoV CIntegralD.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  The cell gluing, abstracted.                                      *)
(* ----------------------------------------------------------------- *)

Lemma cellwise_int_k : forall (F : R -> R),
  (forall (N : nat) (a b : R), (1 <= N)%nat ->
     ln (INR N) <= a -> a <= b -> b <= ln (INR (S N)) ->
     Riemann_integrable F a b) ->
  forall (k : nat) (a b : R), 0 <= a -> a <= b ->
  (floorN (exp b) <= floorN (exp a) + k)%nat -> Riemann_integrable F a b.
Proof.
  intros F Hcell.
  induction k as [| k IH]; intros a b Ha Hab Hk.
  - apply (Hcell (floorN (exp a)) a b (floor_exp_ge1 a Ha) (cell_lo a Ha) Hab).
    apply cell_hi; [ exact Ha | exact Hab | lia ].
  - destruct (le_gt_dec (floorN (exp b)) (floorN (exp a) + k)) as [Hle | Hgt].
    + exact (IH a b Ha Hab Hle).
    + destruct (split_point a b Ha Hab ltac:(lia)) as [Hc0 [Hac [Hcb Hexpc]]].
      apply RiemannInt_P24 with (b := ln (INR (S (floorN (exp a))))).
      * apply (Hcell (floorN (exp a)) a (ln (INR (S (floorN (exp a)))))
                 (floor_exp_ge1 a Ha) (cell_lo a Ha) Hac (Rle_refl _)).
      * apply (IH (ln (INR (S (floorN (exp a))))) b Hc0 Hcb).
        rewrite Hexpc, floorN_INR. lia.
Qed.

Theorem cellwise_integrable : forall (F : R -> R),
  (forall (N : nat) (a b : R), (1 <= N)%nat ->
     ln (INR N) <= a -> a <= b -> b <= ln (INR (S N)) ->
     Riemann_integrable F a b) ->
  forall a b, 0 <= a -> a <= b -> Riemann_integrable F a b.
Proof.
  intros F Hcell a b Ha Hab.
  apply (cellwise_int_k F Hcell (floorN (exp b)) a b Ha Hab). lia.
Qed.

(* ----------------------------------------------------------------- *)
(*  Newman's f and the Laplace integrand.                             *)
(* ----------------------------------------------------------------- *)

Definition nfC (t : R) : C := RtoC (nf t).
Definition lintN (z : C) (t : R) : C := Cmul (nfC t) (cexpzt (Copp z) t).

Lemma Re_lintN : forall z t, Re (lintN z t) = nf t * Re (cexpzt (Copp z) t).
Proof. intros z t; unfold lintN, nfC, Cmul, RtoC; cbn [Re Im]; ring. Qed.

Lemma Im_lintN : forall z t, Im (lintN z t) = nf t * Im (cexpzt (Copp z) t).
Proof. intros z t; unfold lintN, nfC, Cmul, RtoC; cbn [Re Im]; ring. Qed.

Lemma Cmod_lintN : forall z t,
  Cmod (lintN z t) = Rabs (nf t) * exp (- Re z * t).
Proof.
  intros z t. unfold lintN, nfC.
  rewrite Cmod_mul, Cmod_RtoC, (Cmod_cexpzt (Copp z) t).
  cbn [Re Copp]. reflexivity.
Qed.

(* ----------------------------------------------------------------- *)
(*  Integrability of both components, by the cell argument.           *)
(* ----------------------------------------------------------------- *)

Lemma lintN_Re_int : forall z a b, 0 <= a -> a <= b ->
  Riemann_integrable (fun t => Re (lintN z t)) a b.
Proof.
  intros z a b Ha Hab.
  apply (cellwise_integrable (fun t => Re (lintN z t))); [ | exact Ha | exact Hab ].
  intros N c d HN Hc Hcd Hd.
  apply (Riemann_integrable_ext_open (fun t => Re (lintN z t))
           (fun t => hu N (exp t) * exp t * Re (cexpzt (Copp z) t)) c d Hcd).
  - intros t Ht. rewrite Re_lintN, (nf_cell_eq N c d t HN Hc Hd Ht). reflexivity.
  - destruct (Rle_lt_or_eq_dec c d Hcd) as [Hlt | He];
      [ | rewrite <- He; apply RiemannInt_P7 ].
    apply RiemannInt_P6; [ exact Hlt | ].
    intros x Hx. apply continuity_pt_mult.
    + apply continuity_pt_mult; [ | apply cont_exp2 ].
      apply (continuity_pt_comp exp (hu N));
        [ apply cont_exp2 | apply hu_cont; apply exp_pos ].
    + apply (proj1 (Ccont_cexpzt (Copp z))).
Qed.

Lemma lintN_Im_int : forall z a b, 0 <= a -> a <= b ->
  Riemann_integrable (fun t => Im (lintN z t)) a b.
Proof.
  intros z a b Ha Hab.
  apply (cellwise_integrable (fun t => Im (lintN z t))); [ | exact Ha | exact Hab ].
  intros N c d HN Hc Hcd Hd.
  apply (Riemann_integrable_ext_open (fun t => Im (lintN z t))
           (fun t => hu N (exp t) * exp t * Im (cexpzt (Copp z) t)) c d Hcd).
  - intros t Ht. rewrite Im_lintN, (nf_cell_eq N c d t HN Hc Hd Ht). reflexivity.
  - destruct (Rle_lt_or_eq_dec c d Hcd) as [Hlt | He];
      [ | rewrite <- He; apply RiemannInt_P7 ].
    apply RiemannInt_P6; [ exact Hlt | ].
    intros x Hx. apply continuity_pt_mult.
    + apply continuity_pt_mult; [ | apply cont_exp2 ].
      apply (continuity_pt_comp exp (hu N));
        [ apply cont_exp2 | apply hu_cont; apply exp_pos ].
    + apply (proj2 (Ccont_cexpzt (Copp z))).
Qed.

(* ----------------------------------------------------------------- *)
(*  The truncated Newman transform.                                   *)
(* ----------------------------------------------------------------- *)

Definition LTN (z : C) (a b : R) (Ha : 0 <= a) (Hab : a <= b) : C :=
  CintfD (lintN z) a b (lintN_Re_int z a b Ha Hab) (lintN_Im_int z a b Ha Hab).

Lemma LTN_irrel : forall z a b Ha Hab Ha' Hab',
  LTN z a b Ha Hab = LTN z a b Ha' Hab'.
Proof. intros; unfold LTN; apply CintfD_irrel. Qed.

Lemma LTN_split : forall z a b c Ha Hab Hb Hbc Hac,
  Cadd (LTN z a b Ha Hab) (LTN z b c Hb Hbc) = LTN z a c Ha Hac.
Proof. intros; unfold LTN; apply CintfD_split. Qed.

(* ----------------------------------------------------------------- *)
(*  |f| is bounded, hence so is the integrand for Re z >= 0.          *)
(* ----------------------------------------------------------------- *)

Lemma nf_closed_form : forall t, nf t = psiR (exp t) / exp t - 1.
Proof.
  intro t. unfold nf, tint.
  pose proof (exp_pos t) as H. field. lra.
Qed.

Lemma nf_bound : forall t, 0 <= t -> Rabs (nf t) <= Kup + 1.
Proof.
  intros t Ht. pose proof (exp_pos t) as He.
  pose proof Kup_pos as HK.
  assert (Hlo : 0 <= psiR (exp t)) by apply psiR_nonneg.
  assert (Hhi : psiR (exp t) <= exp t * Kup) by (apply psiR_upper; lra).
  rewrite nf_closed_form.
  assert (H1 : 0 <= psiR (exp t) / exp t)
    by (apply Rmult_le_pos; [ exact Hlo | left; apply Rinv_0_lt_compat; exact He ]).
  assert (H2 : psiR (exp t) / exp t <= Kup).
  { apply (Rmult_le_reg_r (exp t)); [ exact He | ].
    replace (psiR (exp t) / exp t * exp t) with (psiR (exp t)) by (field; lra).
    lra. }
  unfold Rabs; destruct (Rcase_abs (psiR (exp t) / exp t - 1)); lra.
Qed.

Theorem Cmod_lintN_bound : forall z t, 0 <= Re z -> 0 <= t ->
  Cmod (lintN z t) <= Kup + 1.
Proof.
  intros z t Hz Ht.
  rewrite Cmod_lintN.
  assert (Hex : exp (- Re z * t) <= 1).
  { rewrite <- exp_0. destruct (Rle_lt_or_eq_dec (- Re z * t) 0 ltac:(nra)) as [H | H];
      [ left; apply exp_increasing; exact H | rewrite H; apply Rle_refl ]. }
  pose proof (nf_bound t Ht) as Hnf.
  pose proof (Rabs_pos (nf t)) as Hp.
  pose proof (exp_pos (- Re z * t)).
  nra.
Qed.

Theorem LTN_ML : forall z a b Ha Hab, 0 <= Re z ->
  Cmod (LTN z a b Ha Hab) <= 2 * (Kup + 1) * (b - a).
Proof.
  intros z a b Ha Hab Hz. unfold LTN.
  apply (CintfD_ML (lintN z) a b _ _ (Kup + 1) Hab).
  intros u Hu. apply Cmod_lintN_bound; [ exact Hz | lra ].
Qed.

Print Assumptions LTN_ML.
Print Assumptions LTN_split.
