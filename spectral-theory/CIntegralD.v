(* ================================================================= *)
(*  CIntegralD.v  --  the complex integral for MERELY INTEGRABLE       *)
(*  integrands.  Brick E1 of docs/pnt_endgame_plan.md.                 *)
(*                                                                    *)
(*  CIntegral2.Cintf is built from cont_RI, so `Ccont f` is a          *)
(*  PARAMETER OF THE DEFINITION, not a convenience hypothesis.  That   *)
(*  is why LaplaceFull.LT / gfull and the Newman arc bounds cannot be  *)
(*  instantiated at Newman's f, which is a step function.              *)
(*                                                                    *)
(*  CintfD takes Riemann_integrable witnesses for the real and         *)
(*  imaginary parts instead, and agrees with Cintf wherever both are   *)
(*  defined.  The ML constant 2 matches CIntegral2.Cintf_ML.           *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import ComplexField Cmodulus CIntegral2 PsiRIntegrable.
Open Scope R_scope.

Definition CintfD (f : R -> C) (a b : R)
  (prRe : Riemann_integrable (fun t => Re (f t)) a b)
  (prIm : Riemann_integrable (fun t => Im (f t)) a b) : C :=
  mkC (RiemannInt prRe) (RiemannInt prIm).

Lemma Re_CintfD : forall f a b prRe prIm,
  Re (CintfD f a b prRe prIm) = RiemannInt prRe.
Proof. reflexivity. Qed.

Lemma Im_CintfD : forall f a b prRe prIm,
  Im (CintfD f a b prRe prIm) = RiemannInt prIm.
Proof. reflexivity. Qed.

(* proof irrelevance, componentwise *)
Lemma CintfD_irrel : forall f a b prRe prIm prRe' prIm',
  CintfD f a b prRe prIm = CintfD f a b prRe' prIm'.
Proof.
  intros f a b prRe prIm prRe' prIm'.
  unfold CintfD. f_equal; apply RiemannInt_P5.
Qed.

(* agreement with the continuous integral *)
Lemma CintfD_Cintf : forall f (Hf : Ccont f) a b prRe prIm,
  CintfD f a b prRe prIm = Cintf f Hf a b.
Proof.
  intros f Hf a b prRe prIm.
  unfold CintfD, Cintf. f_equal; apply RiemannInt_P5.
Qed.

(* the transfer lemma, componentwise *)
Lemma CintfD_ext_open : forall f g a b prFRe prFIm prGRe prGIm, a <= b ->
  (forall t, a < t < b -> f t = g t) ->
  CintfD f a b prFRe prFIm = CintfD g a b prGRe prGIm.
Proof.
  intros f g a b prFRe prFIm prGRe prGIm Hab Heq.
  unfold CintfD. f_equal.
  - apply (RiemannInt_P18 prFRe prGRe Hab).
    intros x Hx. rewrite (Heq x Hx). reflexivity.
  - apply (RiemannInt_P18 prFIm prGIm Hab).
    intros x Hx. rewrite (Heq x Hx). reflexivity.
Qed.

(* Chasles *)
Lemma CintfD_split : forall f a b c pr1Re pr1Im pr2Re pr2Im pr3Re pr3Im,
  Cadd (CintfD f a b pr1Re pr1Im) (CintfD f b c pr2Re pr2Im)
  = CintfD f a c pr3Re pr3Im.
Proof.
  intros f a b c pr1Re pr1Im pr2Re pr2Im pr3Re pr3Im.
  unfold CintfD, Cadd. apply Ceq; cbn [Re Im];
    apply RiemannInt_P26.
Qed.

(* ----------------------------------------------------------------- *)
(*  The ML bound.                                                     *)
(* ----------------------------------------------------------------- *)

Lemma Rabs_Re_le4 : forall c : C, Rabs (Re c) <= Cmod c.
Proof.
  intro c. unfold Cmod, Cnorm2.
  rewrite <- (sqrt_Rsqr_abs (Re c)). apply sqrt_le_1_alt.
  unfold Rsqr. pose proof (Rle_0_sqr (Im c)). unfold Rsqr in *. lra.
Qed.

Lemma Rabs_Im_le4 : forall c : C, Rabs (Im c) <= Cmod c.
Proof.
  intro c. unfold Cmod, Cnorm2.
  rewrite <- (sqrt_Rsqr_abs (Im c)). apply sqrt_le_1_alt.
  unfold Rsqr. pose proof (Rle_0_sqr (Re c)). unfold Rsqr in *. lra.
Qed.

Lemma Cmod_le_ReIm4 : forall c : C, Cmod c <= Rabs (Re c) + Rabs (Im c).
Proof.
  intro c. unfold Cmod, Cnorm2.
  apply Rsqr_incr_0_var.
  - unfold Rsqr. rewrite sqrt_sqrt by nra.
    pose proof (Rabs_no_R0 (Re c)). pose proof (Rabs_pos (Re c)).
    pose proof (Rabs_pos (Im c)).
    pose proof (Rsqr_abs (Re c)) as HR. pose proof (Rsqr_abs (Im c)) as HI.
    unfold Rsqr in HR, HI. nra.
  - pose proof (Rabs_pos (Re c)); pose proof (Rabs_pos (Im c)); lra.
Qed.

(* one component: |int g| <= M (b - a) when |g| <= M on [a,b] *)
Lemma RiemannInt_abs_bound : forall (g : R -> R) a b (pr : Riemann_integrable g a b) M,
  a <= b -> (forall u, a <= u <= b -> Rabs (g u) <= M) ->
  Rabs (RiemannInt pr) <= M * (b - a).
Proof.
  intros g a b pr M Hab Hb.
  assert (Hup : RiemannInt pr <= M * (b - a)).
  { rewrite <- (RiemannInt_P15 (RiemannInt_P14 a b M)).
    apply (RiemannInt_P19 pr (RiemannInt_P14 a b M) Hab).
    intros x Hx. unfold fct_cte.
    pose proof (Hb x ltac:(lra)) as H.
    unfold Rabs in H; destruct (Rcase_abs (g x)); lra. }
  assert (Hlo : - (M * (b - a)) <= RiemannInt pr).
  { assert (Heq : - (M * (b - a)) = (- M) * (b - a)) by ring.
    rewrite Heq, <- (RiemannInt_P15 (RiemannInt_P14 a b (- M))).
    apply (RiemannInt_P19 (RiemannInt_P14 a b (- M)) pr Hab).
    intros x Hx. unfold fct_cte.
    pose proof (Hb x ltac:(lra)) as H.
    unfold Rabs in H; destruct (Rcase_abs (g x)); lra. }
  unfold Rabs; destruct (Rcase_abs (RiemannInt pr)); lra.
Qed.

Theorem CintfD_ML : forall f a b prRe prIm M, a <= b ->
  (forall u, a <= u <= b -> Cmod (f u) <= M) ->
  Cmod (CintfD f a b prRe prIm) <= 2 * M * (b - a).
Proof.
  intros f a b prRe prIm M Hab HM.
  assert (HR : Rabs (RiemannInt prRe) <= M * (b - a)).
  { apply (RiemannInt_abs_bound _ a b prRe M Hab).
    intros u Hu. eapply Rle_trans; [ apply Rabs_Re_le4 | apply HM; exact Hu ]. }
  assert (HI : Rabs (RiemannInt prIm) <= M * (b - a)).
  { apply (RiemannInt_abs_bound _ a b prIm M Hab).
    intros u Hu. eapply Rle_trans; [ apply Rabs_Im_le4 | apply HM; exact Hu ]. }
  eapply Rle_trans; [ apply Cmod_le_ReIm4 | ].
  rewrite Re_CintfD, Im_CintfD. lra.
Qed.

Print Assumptions CintfD_ML.
Print Assumptions CintfD_split.
