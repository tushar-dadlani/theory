(* ================================================================= *)
(*  XSpaceIntegral.v  --  the integral of Re TC, moved to x-space.     *)
(*                                                                    *)
(*    xspace_substitution : int_0^L f(e^x) e^x dx = int_1^{e^L} f(u) du *)
(*                                                                    *)
(*  Stage 4b, first brick.  The u-space integrand of Re TC is          *)
(*  Psi(u) u^{-3/4} cos((t/2) ln u), and the ln in it is what makes a  *)
(*  u-space quadrature impractical: IntervalLn.Iln_bisect costs ~8s    *)
(*  per node at m = 20, and its width is capped by Iexp_pt's own       *)
(*  width, so reaching 1e-13 needs m ~ 45 and ~2000 squarings a node.  *)
(*  At a few thousand nodes that is hours.                             *)
(*                                                                    *)
(*  Substituting u = e^x removes ln outright:                          *)
(*                                                                    *)
(*    Psi(u) u^{-3/4} cos((t/2) ln u) du                               *)
(*      = Psi(e^x) e^{-3x/4} cos(t x/2) . e^x dx                       *)
(*      = Psi(e^x) e^{x/4} cos(t x/2) dx,                              *)
(*                                                                    *)
(*  which needs only IntervalArithFun.Iexp_pt and IntervalCos.Icos_pt, *)
(*  both of which run in under a second.                               *)
(*                                                                    *)
(*  The substitution itself is NOT proved here from scratch: the repo  *)
(*  already has ContinuousCoV.cov_continuous, the change of variables  *)
(*  for a continuous integrand with no elementary antiderivative --    *)
(*  exactly this case.  All that is needed is to bundle exp as a       *)
(*  C1_fun and check its hypotheses, which are that exp is increasing  *)
(*  (so it maps [0,L] into [exp 0, exp L]) and that the integrand is   *)
(*  continuous on the image.  Axiom-clean.                             *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra FunctionalExtensionality.
Require Import ContinuousCoV.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  A.  exp as a C1_fun                                                *)
(* ----------------------------------------------------------------- *)
Lemma derive_exp_val : forall x, derive exp derivable_exp x = exp x.
Proof.
  intro x. unfold derive.
  apply derive_pt_eq_0. apply derivable_pt_lim_exp.
Qed.

Lemma derive_exp_eq : derive exp derivable_exp = exp.
Proof. apply functional_extensionality. exact derive_exp_val. Qed.

Lemma cont_derive_exp : continuity (derive exp derivable_exp).
Proof. rewrite derive_exp_eq. apply derivable_continuous. exact derivable_exp. Qed.

Definition exp_C1 : C1_fun := mkC1 cont_derive_exp.

Lemma exp_C1_val : forall x, exp_C1 x = exp x.
Proof. reflexivity. Qed.

Lemma exp_C1_deriv : forall x, derive exp_C1 (diff0 exp_C1) x = exp x.
Proof. intro x. apply derive_exp_val. Qed.

(* ----------------------------------------------------------------- *)
(*  B.  THE SUBSTITUTION                                               *)
(* ----------------------------------------------------------------- *)
Theorem xspace_substitution : forall (f : R -> R) (L : R),
  0 <= L ->
  (forall u, 1 <= u <= exp L -> continuity_pt f u) ->
  forall (prL : Riemann_integrable
                  (fun t => f (exp_C1 t) * derive exp_C1 (diff0 exp_C1) t) 0 L)
         (prR : Riemann_integrable f (exp_C1 0) (exp_C1 L)),
  RiemannInt prL = RiemannInt prR.
Proof.
  intros f L HL Hcont prL prR.
  apply cov_continuous.
  - exact HL.
  - intros t Ht. rewrite !exp_C1_val, exp_0. split.
    + rewrite <- exp_0. destruct (Rle_lt_or_eq_dec 0 t (proj1 Ht)) as [H | H].
      * left; apply exp_increasing; exact H.
      * subst t; right; reflexivity.
    + destruct (Rle_lt_or_eq_dec t L (proj2 Ht)) as [H | H].
      * left; apply exp_increasing; exact H.
      * subst t; right; reflexivity.
  - intros u Hu. apply Hcont. rewrite !exp_C1_val, exp_0 in Hu. exact Hu.
Qed.

(*  NOTE.  The statement is left in the C1_fun shape that cov_continuous
    produces -- f (exp_C1 t) * derive exp_C1 (diff0 exp_C1) t -- rather than
    the prettier f (exp t) * exp t.  The two integrands are pointwise equal
    (exp_C1_val, exp_C1_deriv), but transporting a Riemann_integrable proof
    term along that equality is separate plumbing, and the caller building
    the quadrature has to supply an integrability witness anyway.  Better to
    hand it the shape cov_continuous actually needs than to convert twice. *)

Print Assumptions xspace_substitution.
