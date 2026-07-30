(* ================================================================= *)
(*  GaussFull.v  —  Gaussian part-A stack, step 1 of the finale:       *)
(*  the full-line Gaussian ∫_ℝ e^{−x²} = √π.                           *)
(*                                                                    *)
(*  From the half-line value ∫₀^∞ e^{−x²} = √π/2 (GaussValue) and       *)
(*  evenness.  The reflection x ↦ −x (refl_neg, same local-antideriv   *)
(*  technique as GaussWallis.reflect_integral) gives ∫_{−A}^0 = ∫_0^A,  *)
(*  so ∫_{−A}^A e^{−x²} = 2·∫_0^A e^{−x²}.  A two-sided monotone         *)
(*  improper scaffold (ImproperCvR, built on monotone_seq_transfer)     *)
(*  then makes the A→∞ limit well defined along every sequence, and     *)
(*                                                                    *)
(*      ∫_ℝ e^{−x²} = √π   (gauss_R).                                  *)
(*                                                                    *)
(*  No new axioms (classical Reals only).                             *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import ContinuousCoV GaussSubst GaussSqrtStep GaussImproper GaussValue.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  The reflection x ↦ −x:  ∫_{−A}^0 f = ∫_0^A f(−·).                 *)
(* ----------------------------------------------------------------- *)

Lemma refl_neg : forall (f : R -> R) (A : R), 0 <= A ->
  (forall x, - A <= x <= 0 -> continuity_pt f x) ->
  forall (pr1 : Riemann_integrable f (- A) 0)
         (pr2 : Riemann_integrable (fun x => f (- x)) 0 A),
  RiemannInt pr1 = RiemannInt pr2.
Proof.
  intros f A HA Hcont pr1 pr2.
  assert (HmA : - A <= 0) by lra.
  destruct (RiemannInt_P30 HmA Hcont) as [H HH].
  assert (Hcont' : forall x, 0 <= x <= A -> continuity_pt (fun x => f (- x)) x).
  { intros x Hx; apply (continuity_pt_comp (fun y => - y) f x).
    - apply (continuity_pt_opp (fun y => y) x); apply cont_id.
    - apply Hcont; lra. }
  assert (HK : antiderivative (fun x => f (- x)) (fun t => - H (- t)) 0 A).
  { split; [ | exact HA ]. intros t Ht.
    assert (Hnt : - A <= - t <= 0) by lra.
    destruct (proj1 HH (- t) Hnt) as [prH HprH].
    set (v := f (- t)).
    assert (Hlim : derivable_pt_lim (fun s => - H (- s)) t v).
    { unfold v.
      assert (Hin : derivable_pt_lim (fun s => - s) t (-1))
        by (exact (derivable_pt_lim_opp (fun s => s) t 1 (derivable_pt_lim_id t))).
      pose proof (derivable_pt_lim_comp (fun s => - s) H t (-1)
                    (derive_pt H (- t) prH) Hin
                    ltac:(unfold derive_pt; exact (proj2_sig prH))) as Hco.
      pose proof (derivable_pt_lim_opp (fun s => H (- s)) t
                    (derive_pt H (- t) prH * -1) Hco) as Hop.
      replace (- (derive_pt H (- t) prH * -1)) with (f (- t)) in Hop
        by (rewrite <- HprH; ring).
      exact Hop. }
    exists (exist _ v Hlim); reflexivity. }
  rewrite (FTC_antideriv f H (- A) 0 HmA Hcont pr1 HH).
  rewrite (FTC_antideriv (fun x => f (- x)) (fun t => - H (- t)) 0 A HA Hcont' pr2 HK).
  replace (- (0:R)) with (0:R) by ring; ring.
Qed.

(* ----------------------------------------------------------------- *)
(*  Evenness:  ∫_{−A}^A e^{−x²} = 2·∫_0^A e^{−x²}.                    *)
(* ----------------------------------------------------------------- *)

Lemma gauss_symmetric : forall A, 0 <= A ->
  forall (prF : Riemann_integrable exp_sq (- A) A)
         (prH : Riemann_integrable exp_sq 0 A),
  RiemannInt prF = 2 * RiemannInt prH.
Proof.
  intros A HA prF prH.
  assert (HNH : RiemannInt (exp_sq_int (- A) 0) = RiemannInt prH).
  { assert (prNeg : Riemann_integrable (fun x => exp_sq (- x)) 0 A).
    { apply continuity_implies_RiemannInt; [ exact HA | intros x _ ].
      apply (continuity_pt_comp (fun y => - y) exp_sq x);
        [ apply (continuity_pt_opp (fun y => y) x); apply cont_id | apply cont_exp_sq ]. }
    transitivity (RiemannInt prNeg).
    - exact (refl_neg exp_sq A HA (fun x _ => cont_exp_sq x) (exp_sq_int (- A) 0) prNeg).
    - apply RiemannInt_P18; [ exact HA | intros x _; unfold exp_sq; f_equal; ring ]. }
  pose proof (RiemannInt_P26 (exp_sq_int (- A) 0) prH prF) as Hadd; lra.
Qed.

(* ----------------------------------------------------------------- *)
(*  Two-sided monotone improper scaffold.                            *)
(* ----------------------------------------------------------------- *)

Lemma nonneg_int : forall (f : R -> R) a b (pr : Riemann_integrable f a b),
  a <= b -> (forall x, a <= x <= b -> 0 <= f x) -> 0 <= RiemannInt pr.
Proof.
  intros f a b pr Hab Hpos.
  apply Rle_trans with (RiemannInt (RiemannInt_P14 a b 0)).
  - rewrite (RiemannInt_P15 (RiemannInt_P14 a b 0)); ring_simplify; apply Rle_refl.
  - apply RiemannInt_P19; [ exact Hab | intros x Hx; unfold fct_cte; apply Hpos; lra ].
Qed.

Definition pintR (f : R -> R) (Hint : forall a b, Riemann_integrable f a b) (A : R) : R :=
  RiemannInt (Hint (- A) A).

Lemma pintR_mono : forall (f : R -> R) (Hint : forall a b, Riemann_integrable f a b),
  (forall x, 0 <= f x) -> forall A B, 0 <= A -> A <= B -> pintR f Hint A <= pintR f Hint B.
Proof.
  intros f Hint Hpos A B HA HAB; unfold pintR.
  assert (H1 : 0 <= RiemannInt (Hint (- B) (- A))) by (apply nonneg_int; [ lra | intros x _; apply Hpos ]).
  assert (H2 : 0 <= RiemannInt (Hint A B)) by (apply nonneg_int; [ lra | intros x _; apply Hpos ]).
  pose proof (RiemannInt_P26 (Hint (- B) (- A)) (Hint (- A) B) (Hint (- B) B)) as Ha1.
  pose proof (RiemannInt_P26 (Hint (- A) A) (Hint A B) (Hint (- A) B)) as Ha2.
  lra.
Qed.

Definition ImproperCvR (f : R -> R) (Hint : forall a b, Riemann_integrable f a b) (I : R) : Prop :=
  forall (b : nat -> R), (forall k, 0 <= b k) -> cv_infty b ->
    Un_cv (fun k => pintR f Hint (b k)) I.

Theorem improperR_welldef : forall (f : R -> R) (Hint : forall a b, Riemann_integrable f a b),
  (forall x, 0 <= f x) ->
  forall (a : nat -> R) (I : R),
    (forall k, 0 <= a k) -> cv_infty a -> Un_cv (fun k => pintR f Hint (a k)) I ->
    ImproperCvR f Hint I.
Proof.
  intros f Hint Hpos a I Ha0 Hainf HaI b Hb0 Hbinf.
  apply (monotone_seq_transfer (pintR f Hint) I (pintR_mono f Hint Hpos) a Ha0 Hainf HaI b Hb0 Hbinf).
Qed.

(* ----------------------------------------------------------------- *)
(*  ∫_{−√k}^{√k} e^{−x²} → √π, hence ∫_ℝ e^{−x²} = √π.                *)
(* ----------------------------------------------------------------- *)

Lemma gauss_R_seq :
  forall (pr : forall k, Riemann_integrable exp_sq (- sqrt (INR k)) (sqrt (INR k))),
  Un_cv (fun k => RiemannInt (pr k)) (sqrt PI).
Proof.
  intro pr.
  pose proof (gauss_improper (fun k => sqrt (INR k)) (fun k => sqrt_pos (INR k)) cv_infty_sqrt) as Hos.
  assert (H2 : Un_cv (fun k => 2 * pint exp_sq exp_sq_int (sqrt (INR k))) (sqrt PI)).
  { replace (sqrt PI) with (2 * (sqrt PI / 2)) by lra.
    apply (CV_mult (fun _ => 2) (fun k => pint exp_sq exp_sq_int (sqrt (INR k))) 2 (sqrt PI / 2)).
    - intros eps He; exists 0%nat; intros n _; unfold R_dist; replace (2 - 2) with 0 by ring;
        rewrite Rabs_R0; exact He.
    - exact Hos. }
  apply (Un_cv_ext (fun k => 2 * pint exp_sq exp_sq_int (sqrt (INR k)))
                   (fun k => RiemannInt (pr k)) (sqrt PI)).
  - intro k; unfold pint;
      rewrite (gauss_symmetric (sqrt (INR k)) (sqrt_pos (INR k)) (pr k)
                 (exp_sq_int 0 (sqrt (INR k)))); reflexivity.
  - exact H2.
Qed.

Theorem gauss_R : ImproperCvR exp_sq exp_sq_int (sqrt PI).
Proof.
  apply (improperR_welldef exp_sq exp_sq_int
           (fun x => Rlt_le _ _ (exp_pos (- x ^ 2)))
           (fun k => sqrt (INR k)) (sqrt PI)).
  - intro k; apply sqrt_pos.
  - exact cv_infty_sqrt.
  - exact (gauss_R_seq (fun k => exp_sq_int (- sqrt (INR k)) (sqrt (INR k)))).
Qed.

Print Assumptions gauss_R.

(* ================================================================= *)
(*  END GaussFull.v                                                  *)
(*  ∫_ℝ e^{−x²} = √π, as the A→∞ limit of ∫_{−A}^A (well defined along  *)
(*  every sequence, monotone).  Axiom-free.  Next: the π-scaling       *)
(*  ∫_ℝ e^{−πx²} = 1, then the Gaussian Fourier self-duality.         *)
(* ================================================================= *)
