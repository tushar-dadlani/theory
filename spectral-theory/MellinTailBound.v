(* ================================================================= *)
(*  MellinTailBound.v  —  Stage 2, brick 3: a general tail-split bound.  *)
(*                                                                    *)
(*  For improper integrals on [1,infinity) (the repo's ImproperCv1),    *)
(*  a pointwise domination |f| <= g bounds the truncation error of f    *)
(*  by that of g:                                                       *)
(*                                                                    *)
(*    improper_tail_le :                                                *)
(*      ImproperCv1 f Hf I -> ImproperCv1 g Hg J ->                     *)
(*      (forall u, 1<=u -> Rabs (f u) <= g u) -> 1 <= X ->              *)
(*      Rabs (I - pint1 f Hf X) <= J - pint1 g Hg X.                    *)
(*                                                                    *)
(*  i.e. |I - int_1^X f| <= (tail of the dominating g).  Applied with   *)
(*  f = Re(wkerC(1/2+it) .) (I = Re TC(1/2+it)) and an EXPONENTIAL      *)
(*  dominator g, this reduces the oscillatory-integral truncation error *)
(*  to a closed-form exponential tail.  Proof mirrors MellinTailSeries. *)
(*  bound_M (RiemannInt_P26 additivity + P17 |int|<=int|.| + P19        *)
(*  monotonicity, then a limit b n = X + n).                           *)
(*                                                                    *)
(*  Axioms: standard classical-Reals only.                            *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra.
Require Import ImproperCv1 MellinElem CImproperIntegral JacobiTheta.
Open Scope R_scope.

Theorem improper_tail_le :
  forall f Hf (g : R -> R) Hg I J X,
    ImproperCv1 f Hf I -> ImproperCv1 g Hg J ->
    (forall u, 1 <= u -> Rabs (f u) <= g u) -> 1 <= X ->
    Rabs (I - pint1 f Hf X) <= J - pint1 g Hg X.
Proof.
  intros f Hf g Hg I J X HF HG Hdom HX.
  set (b := fun n => X + INR n).
  assert (Hb1 : forall n, 1 <= b n) by (intro n; unfold b; pose proof (pos_INR n); lra).
  assert (HbX : forall n, X <= b n) by (intro n; unfold b; pose proof (pos_INR n); lra).
  assert (Hbinf : cv_infty b).
  { intro M. destruct (INR_unbounded (M - X)) as [N HN]. exists N. intros n Hn.
    unfold b. assert (INR N <= INR n) by (apply le_INR; exact Hn). lra. }
  assert (HFcv : Un_cv (fun n => pint1 f Hf (b n)) I) by (apply HF; assumption).
  assert (HGcv : Un_cv (fun n => pint1 g Hg (b n)) J) by (apply HG; assumption).
  (* per-n: |int_1^{bn} f - int_1^X f| <= int_1^{bn} g - int_1^X g *)
  assert (Hstep : forall n,
    Rabs (pint1 f Hf (b n) - pint1 f Hf X) <= pint1 g Hg (b n) - pint1 g Hg X).
  { intro n. pose proof (HbX n) as HXbn.
    assert (Ediff : pint1 f Hf (b n) - pint1 f Hf X = RiemannInt (Hf X (b n))).
    { unfold pint1. pose proof (RiemannInt_P26 (Hf 1 X) (Hf X (b n)) (Hf 1 (b n))). lra. }
    assert (Eg : pint1 g Hg (b n) - pint1 g Hg X = RiemannInt (Hg X (b n))).
    { unfold pint1. pose proof (RiemannInt_P26 (Hg 1 X) (Hg X (b n)) (Hg 1 (b n))). lra. }
    rewrite Ediff, Eg.
    eapply Rle_trans.
    - apply (RiemannInt_P17 (Hf X (b n)) (RiemannInt_P16 (Hf X (b n)))); exact HXbn.
    - apply RiemannInt_P19; [ exact HXbn | intros x Hx; apply Hdom; lra ]. }
  (* pass to the limit *)
  apply (Un_cv_le
           (fun n => Rabs (pint1 f Hf (b n) - pint1 f Hf X))
           (fun n => pint1 g Hg (b n) - pint1 g Hg X)
           (Rabs (I - pint1 f Hf X)) (J - pint1 g Hg X)).
  - exact Hstep.
  - (* Rabs of a convergent sequence converges to Rabs of the limit *)
    assert (Hd : Un_cv (fun n => pint1 f Hf (b n) - pint1 f Hf X) (I - pint1 f Hf X))
      by (apply CV_minus; [ exact HFcv | apply Un_cv_const ]).
    intros eps Heps. destruct (Hd eps Heps) as [N HN]. exists N. intros n Hn.
    specialize (HN n Hn). unfold R_dist in HN |- *.
    eapply Rle_lt_trans; [ apply Rabs_triang_inv2 | exact HN ].
  - apply CV_minus; [ exact HGcv | apply Un_cv_const ].
Qed.

Print Assumptions improper_tail_le.
