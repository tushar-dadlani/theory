(* ================================================================= *)
(*  CImproperIntegral.v  —  toward the complex improper integral.     *)
(*  Generic real ImproperCv1 helper: value monotonicity.  Axiom-clean.*)
(* ================================================================= *)

From Stdlib Require Import Reals Lra.
Require Import ComplexField Cmodulus ImproperCv1.
Open Scope R_scope.

(* value monotonicity: f <= g on [1,∞) ⇒ ∫₁^∞ f <= ∫₁^∞ g *)
Lemma improper_mono : forall f g Hf Hg If Ig,
  (forall x, 1 <= x -> f x <= g x) ->
  ImproperCv1 f Hf If -> ImproperCv1 g Hg Ig -> If <= Ig.
Proof.
  intros f g Hf Hg If Ig Hle HF HG.
  set (b := fun n => 1 + INR n).
  assert (Hb1 : forall k, 1 <= b k) by (intro k; unfold b; pose proof (pos_INR k); lra).
  assert (Hbinf : cv_infty b) by apply cv_infty_1_INR.
  apply Rle_cv_lim with (Un := fun k => pint1 f Hf (b k)) (Vn := fun k => pint1 g Hg (b k)).
  - intro k; unfold pint1; apply RiemannInt_P19; [ apply Hb1 | intros x Hx; apply Hle; lra ].
  - apply HF; assumption.
  - apply HG; assumption.
Qed.

Print Assumptions improper_mono.
