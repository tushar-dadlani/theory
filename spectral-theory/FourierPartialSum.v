(* ================================================================= *)
(*  FourierPartialSum.v  —  Fourier milestone F2, foundations:        *)
(*  integral linearity on [-π,π].                                    *)
(*                                                                    *)
(*  The reusable engine for the F2 kernel representation (S_N f =      *)
(*  (1/2π)∫ f(y)·D_N(x−y) dy) and for F3 (pointwise convergence):      *)
(*                                                                    *)
(*    • RI_scal : ∫ (c·g) = c·∫ g                (continuous g);      *)
(*    • RI_add  : ∫ (u + v) = ∫ u + ∫ v          (continuous u, v).   *)
(*                                                                    *)
(*  Both via stdlib RiemannInt linearity (P13), extensionality (P18)  *)
(*  and the constant integral (P15).  The single-mode identity        *)
(*  ∫ f(y)cos(k(x−y)) dy = π(a_k cos kx + b_k sin kx) and the          *)
(*  convolution assembly (induction on N via Dsum_S) are the next      *)
(*  step, built directly on these two atoms.                         *)
(*                                                                    *)
(*  Built on stdlib RiemannInt and DirichletKernel / DirichletIntegral*)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import FourierRL DirichletKernel DirichletIntegral.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  Integral linearity on [-π,π] (for continuous integrands).        *)
(* ----------------------------------------------------------------- *)

Lemma RI_scal : forall (g : R -> R) (c : R), continuity g ->
  forall (pr1 : Riemann_integrable g (- PI) PI)
         (pr2 : Riemann_integrable (fun x => c * g x) (- PI) PI),
  RiemannInt pr2 = c * RiemannInt pr1.
Proof.
  intros g c Hg pr1 pr2; pose proof PI_RGT_0 as Hpi.
  assert (pr0 : Riemann_integrable (fun _ : R => 0) (- PI) PI)
    by (apply continuity_implies_RiemannInt;
        [ lra | intros x _; apply continuity_pt_const; intros u v; reflexivity ]).
  assert (pr3 : Riemann_integrable (fun x => 0 + c * g x) (- PI) PI)
    by (apply continuity_implies_RiemannInt; [ lra | intros x _; apply continuity_pt_plus;
        [ apply continuity_pt_const; intros u v; reflexivity
        | apply (continuity_pt_scal g c x); apply Hg ] ]).
  assert (H0 : RiemannInt pr0 = 0)
    by (transitivity (0 * (PI - - PI)); [ exact (RiemannInt_P15 pr0) | ring ]).
  assert (E : RiemannInt pr2 = RiemannInt pr3)
    by (apply RiemannInt_P18; [ lra | intros x _; ring ]).
  rewrite E, (RiemannInt_P13 pr0 pr1 pr3), H0; ring.
Qed.

Lemma RI_add : forall (u v : R -> R), continuity u -> continuity v ->
  forall (pr1 : Riemann_integrable u (- PI) PI)
         (pr2 : Riemann_integrable v (- PI) PI)
         (pr3 : Riemann_integrable (fun x => u x + v x) (- PI) PI),
  RiemannInt pr3 = RiemannInt pr1 + RiemannInt pr2.
Proof.
  intros u v Hu Hv pr1 pr2 pr3; pose proof PI_RGT_0 as Hpi.
  assert (pr3' : Riemann_integrable (fun x => u x + 1 * v x) (- PI) PI)
    by (apply continuity_implies_RiemannInt; [ lra | intros x _; apply continuity_pt_plus;
        [ apply Hu | apply (continuity_pt_scal v 1 x); apply Hv ] ]).
  assert (E : RiemannInt pr3 = RiemannInt pr3')
    by (apply RiemannInt_P18; [ lra | intros x _; ring ]).
  rewrite E, (RiemannInt_P13 pr1 pr2 pr3'); ring.
Qed.

Print Assumptions RI_scal.
Print Assumptions RI_add.
