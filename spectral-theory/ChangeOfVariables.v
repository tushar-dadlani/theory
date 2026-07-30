(* ================================================================= *)
(*  ChangeOfVariables.v  —  change of variables for RiemannInt        *)
(*  (u-substitution), FTC form.                                       *)
(*                                                                    *)
(*  For C¹ functions F and g,                                        *)
(*                                                                    *)
(*     ∫_a^b F'(g(t))·g'(t) dt  =  F(g b) − F(g a)                    *)
(*                             =  ∫_{g a}^{g b} F'(u) du,             *)
(*                                                                    *)
(*  the substitution rule.  Proof: F∘g is C¹ with derivative          *)
(*  (F'∘g)·g' (chain rule, derivable_pt_lim_comp), so FTC_Riemann on   *)
(*  the bundled composite gives the boundary values; a second FTC on   *)
(*  F rewrites the right side as ∫_{g a}^{g b} F'.                     *)
(*                                                                    *)
(*  This is the u-substitution theorem in the "known antiderivative F" *)
(*  form.  stdlib RiemannInt has no change-of-variables lemma, so this *)
(*  is a reusable primitive.  (The continuous-integrand form — where   *)
(*  F is the primitive ∫_{g a}^x f, needed when the antiderivative is  *)
(*  not elementary, e.g. the Gaussian squeeze — additionally needs     *)
(*  stdlib's `primitive`/RiemannInt_P28 packaged as a global C1_fun.)  *)
(*                                                                    *)
(*  No new axioms (classical Reals only).                            *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra.
Open Scope R_scope.

(* the substituted integrand  (F'∘g)·g'  *)
Definition dcomp (F g : C1_fun) (t : R) : R :=
  derive F (diff0 F) (g t) * derive g (diff0 g) t.

(* chain rule: F∘g is differentiable with derivative dcomp *)
Lemma comp_deriv : forall (F g : C1_fun) t,
  derivable_pt_lim (fun s => F (g s)) t (dcomp F g t).
Proof.
  intros F g t; unfold dcomp.
  apply (derivable_pt_lim_comp g F t (derive g (diff0 g) t) (derive F (diff0 F) (g t))).
  - unfold derive, derive_pt; exact (proj2_sig (diff0 g t)).
  - unfold derive, derive_pt; exact (proj2_sig (diff0 F (g t))).
Qed.

(* the composite derivative is continuous *)
Lemma dcomp_cont : forall (F g : C1_fun), continuity (dcomp F g).
Proof.
  intros F g t; unfold dcomp; apply continuity_pt_mult.
  - apply (continuity_pt_comp g (derive F (diff0 F)) t).
    + apply derivable_continuous_pt; exists (derive g (diff0 g) t).
      unfold derive, derive_pt; exact (proj2_sig (diff0 g t)).
    + apply (cont1 F).
  - apply (cont1 g).
Qed.

(* F∘g bundled as a C¹ function *)
Definition comp_C1 (F g : C1_fun) : C1_fun :=
  mkC1 (c1 := fun t => F (g t))
       (diff0 := fun t => exist _ (dcomp F g t) (comp_deriv F g t))
       (dcomp_cont F g).

Lemma comp_C1_val : forall F g t, comp_C1 F g t = F (g t).
Proof. reflexivity. Qed.

(* ----------------------------------------------------------------- *)
(*  THE CHANGE OF VARIABLES.                                          *)
(* ----------------------------------------------------------------- *)

Theorem change_of_variables : forall (F g : C1_fun) (a b : R)
  (pr : Riemann_integrable (dcomp F g) a b),
  RiemannInt pr = F (g b) - F (g a).
Proof.
  intros F g a b pr.
  pose proof (FTC_Riemann (comp_C1 F g) pr : RiemannInt pr = comp_C1 F g b - comp_C1 F g a) as H.
  rewrite H, !comp_C1_val; reflexivity.
Qed.

(* u-substitution: ∫_a^b (F'∘g)·g' = ∫_{g a}^{g b} F' *)
Corollary cov_integral : forall (F g : C1_fun) (a b : R)
  (pr  : Riemann_integrable (dcomp F g) a b)
  (pr' : Riemann_integrable (derive F (diff0 F)) (g a) (g b)),
  RiemannInt pr = RiemannInt pr'.
Proof.
  intros F g a b pr pr'.
  rewrite (change_of_variables F g a b pr), (FTC_Riemann F pr'); reflexivity.
Qed.

Print Assumptions change_of_variables.
Print Assumptions cov_integral.

(* ================================================================= *)
(*  END ChangeOfVariables.v                                          *)
(*  ∫_a^b F'(g)·g' = F(g b) − F(g a) = ∫_{g a}^{g b} F'.  The u-        *)
(*  substitution primitive; the continuous-integrand form (primitive  *)
(*  as C1_fun) is the next step toward the Gaussian squeeze.          *)
(* ================================================================= *)
