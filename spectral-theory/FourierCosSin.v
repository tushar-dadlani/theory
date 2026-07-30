(* ================================================================= *)
(*  FourierCosSin.v  —  Fourier F3, first UNCONDITIONAL instances:    *)
(*  the Fourier series of cos and of sin converge pointwise.          *)
(*                                                                    *)
(*     S_N cos(x) → cos x,     S_N sin(x) → sin x     (every x).       *)
(*                                                                    *)
(*  These discharge FourierConverge.fourier_pointwise with NO         *)
(*  hypotheses: for a single mode the localised quotient collapses,   *)
(*  by product-to-sum, to a plain sin/cos of an affine argument — an  *)
(*  honest GLOBAL C¹ function with NO removable singularity at all.    *)
(*                                                                    *)
(*    f = cos:  g(y) = 2 sin((y+x)/2),                                *)
(*      2 sin((y+x)/2)·sin((x−y)/2) = cos y − cos x   (2 sinA sinB     *)
(*                                    = cos(A−B) − cos(A+B)).          *)
(*    f = sin:  g(y) = −2 cos((y+x)/2),                               *)
(*      −2 cos((y+x)/2)·sin((x−y)/2) = sin y − sin x  (2 cosA sinB     *)
(*                                    = sin(A+B) − sin(A−B)).          *)
(*                                                                    *)
(*  Here g satisfies the localiser identity for ALL y (globally), so  *)
(*  no interval restriction or 2π-periodicity is needed — the general *)
(*  removable-singularity construction (non-modal f) is a separate,   *)
(*  harder step this file deliberately sidesteps by using modes.      *)
(*                                                                    *)
(*  No new axioms (classical Reals only).                            *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra.
Require Import FourierKernelRep FourierConverge.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  Shared affine scaffolding: d/dt (½(t+x)) = ½, continuity.        *)
(* ----------------------------------------------------------------- *)

Lemma half_shift_deriv : forall x y, derivable_pt_lim (fun t => / 2 * (t + x)) y (/ 2).
Proof.
  intros x y.
  assert (H1 : derivable_pt_lim (fun t => t + x) y (1 + 0))
    by (apply (derivable_pt_lim_plus id (fct_cte x) y 1 0);
        [ apply derivable_pt_lim_id | apply derivable_pt_lim_const ]).
  rewrite Rplus_0_r in H1.
  pose proof (derivable_pt_lim_scal (fun t => t + x) (/ 2) y 1 H1) as H.
  rewrite Rmult_1_r in H; exact H.
Qed.

Lemma cont_half_shift : forall x, continuity (fun t => / 2 * (t + x)).
Proof.
  intros x y; apply (continuity_pt_scal (fun t => t + x) (/ 2) y).
  apply continuity_pt_plus;
    [ apply derivable_continuous_pt; exists 1; apply derivable_pt_lim_id
    | apply continuity_pt_const; intros a b; reflexivity ].
Qed.

Lemma cont_cos_half : forall x, continuity (fun t => cos (/ 2 * (t + x))).
Proof.
  intros x y; apply (continuity_pt_comp (fun t => / 2 * (t + x)) cos y);
    [ apply cont_half_shift | apply continuity_cos ].
Qed.

Lemma cont_sin_half : forall x, continuity (fun t => sin (/ 2 * (t + x))).
Proof.
  intros x y; apply (continuity_pt_comp (fun t => / 2 * (t + x)) sin y);
    [ apply cont_half_shift | apply continuity_sin ].
Qed.

(* product-to-sum atoms *)
Lemma two_sin_sin : forall A B, 2 * sin A * sin B = cos (A - B) - cos (A + B).
Proof. intros A B; rewrite cos_minus, cos_plus; ring. Qed.
Lemma two_cos_sin : forall A B, 2 * cos A * sin B = sin (A + B) - sin (A - B).
Proof. intros A B; rewrite sin_plus, sin_minus; ring. Qed.

(* ================================================================= *)
(*  1.  f = cos :  g(y) = 2 sin((y+x)/2)                              *)
(* ================================================================= *)

Lemma g_cos_deriv : forall x y,
  derivable_pt_lim (fun t => 2 * sin (/ 2 * (t + x))) y (cos (/ 2 * (y + x))).
Proof.
  intros x y.
  assert (Hsin : derivable_pt_lim (fun t => sin (/ 2 * (t + x))) y (cos (/ 2 * (y + x)) * / 2)).
  { apply (derivable_pt_lim_comp (fun t => / 2 * (t + x)) sin y (/ 2) (cos (/ 2 * (y + x))));
      [ apply half_shift_deriv | apply derivable_pt_lim_sin ]. }
  replace (cos (/ 2 * (y + x))) with (2 * (cos (/ 2 * (y + x)) * / 2)) by field.
  apply (derivable_pt_lim_scal (fun t => sin (/ 2 * (t + x))) 2 y (cos (/ 2 * (y + x)) * / 2)); exact Hsin.
Qed.

Definition gcos (x : R) : C1_fun :=
  mkC1 (c1 := fun t => 2 * sin (/ 2 * (t + x)))
       (diff0 := fun t => exist _ _ (g_cos_deriv x t))
       (cont_cos_half x).

Lemma gcos_val : forall x y, gcos x y = 2 * sin (/ 2 * (y + x)).
Proof. reflexivity. Qed.

(* the localiser identity for cos, holding globally *)
Lemma Hg_cos : forall x y, gcos x y * sin ((x - y) / 2) = cos y - cos x.
Proof.
  intros x y; rewrite gcos_val.
  replace (/ 2 * (y + x)) with ((y + x) / 2) by field.
  rewrite (two_sin_sin ((y + x) / 2) ((x - y) / 2)).
  replace ((y + x) / 2 - (x - y) / 2) with y by field.
  replace ((y + x) / 2 + (x - y) / 2) with x by field.
  reflexivity.
Qed.

Theorem fourier_cos : forall x, Un_cv (fun N => SN cos continuity_cos N x) (cos x).
Proof. intro x; exact (fourier_pointwise cos continuity_cos x (gcos x) (Hg_cos x)). Qed.

(* ================================================================= *)
(*  2.  f = sin :  g(y) = −2 cos((y+x)/2)                             *)
(* ================================================================= *)

Lemma g_sin_deriv : forall x y,
  derivable_pt_lim (fun t => -2 * cos (/ 2 * (t + x))) y (sin (/ 2 * (y + x))).
Proof.
  intros x y.
  assert (Hcos : derivable_pt_lim (fun t => cos (/ 2 * (t + x))) y (- sin (/ 2 * (y + x)) * / 2)).
  { apply (derivable_pt_lim_comp (fun t => / 2 * (t + x)) cos y (/ 2) (- sin (/ 2 * (y + x))));
      [ apply half_shift_deriv | apply derivable_pt_lim_cos ]. }
  replace (sin (/ 2 * (y + x))) with (-2 * (- sin (/ 2 * (y + x)) * / 2)) by field.
  apply (derivable_pt_lim_scal (fun t => cos (/ 2 * (t + x))) (-2) y (- sin (/ 2 * (y + x)) * / 2)); exact Hcos.
Qed.

Definition gsin (x : R) : C1_fun :=
  mkC1 (c1 := fun t => -2 * cos (/ 2 * (t + x)))
       (diff0 := fun t => exist _ _ (g_sin_deriv x t))
       (cont_sin_half x).

Lemma gsin_val : forall x y, gsin x y = -2 * cos (/ 2 * (y + x)).
Proof. reflexivity. Qed.

Lemma Hg_sin : forall x y, gsin x y * sin ((x - y) / 2) = sin y - sin x.
Proof.
  intros x y; rewrite gsin_val.
  replace (/ 2 * (y + x)) with ((y + x) / 2) by field.
  replace (-2 * cos ((y + x) / 2) * sin ((x - y) / 2))
    with (- (2 * cos ((y + x) / 2) * sin ((x - y) / 2))) by ring.
  rewrite (two_cos_sin ((y + x) / 2) ((x - y) / 2)).
  replace ((y + x) / 2 + (x - y) / 2) with x by field.
  replace ((y + x) / 2 - (x - y) / 2) with y by field.
  ring.
Qed.

Theorem fourier_sin : forall x, Un_cv (fun N => SN sin continuity_sin N x) (sin x).
Proof. intro x; exact (fourier_pointwise sin continuity_sin x (gsin x) (Hg_sin x)). Qed.

Print Assumptions fourier_cos.
Print Assumptions fourier_sin.

(* ================================================================= *)
(*  END FourierCosSin.v                                              *)
(*  S_N cos → cos and S_N sin → sin pointwise, unconditionally: the   *)
(*  first end-to-end instances of the F1→F2→F3 Fourier convergence    *)
(*  machinery, with explicit global C¹ localisers and no gaps.        *)
(* ================================================================= *)
