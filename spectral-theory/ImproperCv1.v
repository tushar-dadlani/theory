(* ================================================================= *)
(*  ImproperCv1.v  —  Riemann FE milestone R1, file 3:               *)
(*  a base-1 improper-integral toolkit  ∫₁^∞ f = lim_{A→∞} ∫₁^A f.     *)
(*                                                                    *)
(*  GaussImproper.v gives the base-0 version inside a Section that     *)
(*  fixes one integrand and needs f ≥ 0.  Here we (i) rebase to 1,     *)
(*  reusing the base-agnostic core `monotone_seq_transfer` via an      *)
(*  Rmax-clamp, and (ii) expose the predicate parameterised by the     *)
(*  integrand so it composes:                                          *)
(*    improper_bounded_cv : f ≥ 0 & ∫₁^A f bounded ⇒ the value exists; *)
(*    improper_linear     : ∫₁^∞ (f + l·g) = ∫₁^∞ f + l·∫₁^∞ g;        *)
(*    improper_ext        : f = g on [1,∞) ⇒ same improper value.      *)
(*  No new axioms (classical Reals only).                            *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import GaussImproper.
Open Scope R_scope.

Lemma Un_cv_ext : forall u v L, (forall n, u n = v n) -> Un_cv u L -> Un_cv v L.
Proof.
  intros u v L He Hu eps Heps; destruct (Hu eps Heps) as [N HN]; exists N; intros n Hn.
  rewrite <- (He n); apply HN; exact Hn.
Qed.

Lemma Un_cv_const : forall c : R, Un_cv (fun _ => c) c.
Proof.
  intros c eps Heps; exists 0%nat; intros n _; unfold R_dist;
    replace (c - c) with 0 by ring; rewrite Rabs_R0; exact Heps.
Qed.

Lemma cv_infty_1_INR : cv_infty (fun n => 1 + INR n).
Proof.
  intro M; destruct (INR_unbounded M) as [N HN]; exists N; intros n Hn.
  pose proof (le_INR N n Hn); lra.
Qed.

(* --- the partial integral and the improper predicate, base 1 --- *)

Definition pint1 (f : R -> R) (Hf : forall a b, Riemann_integrable f a b) (A : R) : R :=
  RiemannInt (Hf 1 A).

Definition ImproperCv1 (f : R -> R) (Hf : forall a b, Riemann_integrable f a b) (I : R) : Prop :=
  forall (b : nat -> R), (forall k, 1 <= b k) -> cv_infty b ->
    Un_cv (fun k => pint1 f Hf (b k)) I.

(* f ≥ 0 on [1,∞) ⇒ ∫₁^A f nondecreasing for A ≥ 1. *)
Lemma pint1_mono : forall f Hf, (forall x, 1 <= x -> 0 <= f x) ->
  forall x y, 1 <= x -> x <= y -> pint1 f Hf x <= pint1 f Hf y.
Proof.
  intros f Hf Hpos x y Hx Hxy; unfold pint1.
  assert (Hxy0 : 0 <= RiemannInt (Hf x y)).
  { pose proof (RiemannInt_P15 (RiemannInt_P14 x y 0)) as Hz.
    apply Rle_trans with (RiemannInt (RiemannInt_P14 x y 0)).
    - rewrite Hz; ring_simplify; apply Rle_refl.
    - apply RiemannInt_P19; [ exact Hxy | intros t Ht; unfold fct_cte; apply Hpos; lra ]. }
  pose proof (RiemannInt_P26 (Hf 1 x) (Hf x y) (Hf 1 y)) as Hadd; lra.
Qed.

(* well-definedness: one exhausting sequence pins ∫₁^∞ for every sequence. *)
Theorem improper_welldef1 : forall f Hf, (forall x, 1 <= x -> 0 <= f x) ->
  forall (a : nat -> R) (I : R),
    (forall k, 1 <= a k) -> cv_infty a -> Un_cv (fun k => pint1 f Hf (a k)) I ->
    ImproperCv1 f Hf I.
Proof.
  intros f Hf Hpos a I Ha1 Hainf HaI b Hb1 Hbinf.
  set (G := fun x => pint1 f Hf (Rmax 1 x)).
  assert (Gmono : forall x y, 0 <= x -> x <= y -> G x <= G y).
  { intros x y Hx Hxy; unfold G; apply (pint1_mono f Hf Hpos).
    - apply Rmax_l.
    - apply Rmax_lub; [ apply Rmax_l | apply Rle_trans with y; [ exact Hxy | apply Rmax_r ] ]. }
  assert (Hga : Un_cv (fun k => G (a k)) I).
  { apply (Un_cv_ext (fun k => pint1 f Hf (a k))); [ | exact HaI ].
    intro k; unfold G; rewrite Rmax_right; [ reflexivity | apply Ha1 ]. }
  assert (Hgb : Un_cv (fun k => G (b k)) I).
  { apply (monotone_seq_transfer G I Gmono a
             (fun k => Rle_trans _ _ _ Rle_0_1 (Ha1 k)) Hainf Hga
             b (fun k => Rle_trans _ _ _ Rle_0_1 (Hb1 k)) Hbinf). }
  apply (Un_cv_ext (fun k => G (b k))); [ | exact Hgb ].
  intro k; unfold G; rewrite Rmax_right; [ reflexivity | apply Hb1 ].
Qed.

(* existence from boundedness: f ≥ 0 and ∫₁^A f ≤ M ⇒ the improper value exists. *)
Theorem improper_bounded_cv : forall f Hf, (forall x, 1 <= x -> 0 <= f x) ->
  (exists M, forall A, 1 <= A -> pint1 f Hf A <= M) ->
  { I : R | ImproperCv1 f Hf I }.
Proof.
  intros f Hf Hpos Hbnd.
  set (a := fun n => 1 + INR n).
  assert (Ha1 : forall n, 1 <= a n) by (intro n; unfold a; pose proof (pos_INR n); lra).
  assert (Hgrow : Un_growing (fun n => pint1 f Hf (a n))).
  { intro n; apply (pint1_mono f Hf Hpos); [ apply Ha1 | unfold a; rewrite S_INR; lra ]. }
  assert (Hub : has_ub (fun n => pint1 f Hf (a n))).
  { destruct Hbnd as [M HM]; unfold has_ub, EUn, bound, is_upper_bound;
      exists M; intros r [n ->]; apply HM; apply Ha1. }
  destruct (growing_cv (fun n => pint1 f Hf (a n)) Hgrow Hub) as [I HI].
  exists I; apply (improper_welldef1 f Hf Hpos a I Ha1); [ apply cv_infty_1_INR | exact HI ].
Qed.

(* linearity: covers both addition (l=1) and scaling (via the l factor). *)
Theorem improper_linear : forall f g l Hf Hg Hfg If Ig,
  ImproperCv1 f Hf If -> ImproperCv1 g Hg Ig ->
  ImproperCv1 (fun x => f x + l * g x) Hfg (If + l * Ig).
Proof.
  intros f g l Hf Hg Hfg If Ig HF HG b Hb1 Hbinf.
  apply (Un_cv_ext (fun k => pint1 f Hf (b k) + l * pint1 g Hg (b k))).
  - intro k; unfold pint1; symmetry; apply (RiemannInt_P13 (Hf 1 (b k)) (Hg 1 (b k))).
  - apply CV_plus; [ apply HF; assumption | ].
    apply (CV_mult (fun _ => l) (fun k => pint1 g Hg (b k)) l Ig);
      [ apply Un_cv_const | apply HG; assumption ].
Qed.

(* extensionality on [1,∞): equal integrands ⇒ equal improper value. *)
Theorem improper_ext : forall f g Hf Hg I,
  (forall x, 1 <= x -> f x = g x) -> ImproperCv1 f Hf I -> ImproperCv1 g Hg I.
Proof.
  intros f g Hf Hg I Heq HF b Hb1 Hbinf.
  apply (Un_cv_ext (fun k => pint1 f Hf (b k))); [ | apply HF; assumption ].
  intro k; unfold pint1; apply RiemannInt_P18; [ apply Hb1 | ].
  intros x Hx; apply Heq; lra.
Qed.

Print Assumptions improper_bounded_cv.
Print Assumptions improper_linear.

(* ================================================================= *)
(*  END ImproperCv1.v                                                *)
(*  ∫₁^∞ toolkit: existence (bounded-monotone), linearity, extensionality. *)
(* ================================================================= *)
