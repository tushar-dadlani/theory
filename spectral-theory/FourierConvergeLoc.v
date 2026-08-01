(* ================================================================= *)
(*  FourierConvergeLoc.v  —  the INTERVAL-restricted pointwise Fourier *)
(*  convergence (additive variant of FourierConverge.fourier_pointwise).*)
(*                                                                    *)
(*  The only place fourier_pointwise uses the C¹ localiser identity Hg *)
(*  is the RiemannInt_P18 inside integral_expand, over [−π,π].  So the  *)
(*  hypothesis need only hold ON [−π,π]:                              *)
(*     Hg_loc : ∀ y, −π ≤ y ≤ π → g y·sin((x−y)/2) = f y − f x.        *)
(*  This is exactly what a 2π-periodic f needs — the removable         *)
(*  singularity of the localiser has to be resolved on ONE period      *)
(*  only, not glued across the whole antiperiodic lattice.            *)
(*                                                                    *)
(*  Pure addition: the completed FourierConverge is left untouched;    *)
(*  we duplicate ~40 lines (integral_expand + the finale) with the     *)
(*  weakened hypothesis.  No new axioms (classical Reals only).        *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import FourierRL FourierRLcos DirichletKernel FourierPartialSum
        FourierKernelRep FourierLocalize FourierConverge.
Open Scope R_scope.

Section ConvergeLoc.

Variable f : R -> R.
Hypothesis Cf : continuity f.
Variable x : R.
Variable g : C1_fun.
Hypothesis Hg_loc : forall y, - PI <= y <= PI -> g y * sin ((x - y) / 2) = f y - f x.

Lemma prdg_loc : Riemann_integrable (fun t => Rabs (derive g (diff0 g) t)) (- PI) PI.
Proof.
  apply continuity_implies_RiemannInt; [ exact HabPI | intros t _ ];
    apply (continuity_pt_comp (derive g (diff0 g)) Rabs t);
    [ apply (cont1 g) | apply Rcontinuity_abs ].
Qed.

Lemma integral_expand_loc : forall N,
  RiemannInt (ri_diffD f Cf N x)
  = sin ((INR N + / 2) * x) * RiemannInt (ri_gcos g (INR N + / 2) (- PI) PI HabPI)
  + (- cos ((INR N + / 2) * x)) * RiemannInt (ri_gsin g (INR N + / 2) (- PI) PI HabPI).
Proof.
  intro N; pose proof PI_RGT_0 as HPI.
  assert (Cu : continuity (fun y => g y * cos ((INR N + / 2) * y)))
    by (intro y; apply continuity_pt_mult;
        [ apply derivable_continuous_pt, (diff0 g) | apply cos_lam_cont ]).
  assert (Cv : continuity (fun y => g y * sin ((INR N + / 2) * y)))
    by (intro y; apply continuity_pt_mult;
        [ apply derivable_continuous_pt, (diff0 g) | apply sin_lam_cont ]).
  assert (CU : continuity (fun y => sin ((INR N + / 2) * x) * (g y * cos ((INR N + / 2) * y))))
    by (intro y; apply (continuity_pt_scal (fun y => g y * cos ((INR N + / 2) * y))
                          (sin ((INR N + / 2) * x)) y); apply Cu).
  assert (CV : continuity (fun y => (- cos ((INR N + / 2) * x)) * (g y * sin ((INR N + / 2) * y))))
    by (intro y; apply (continuity_pt_scal (fun y => g y * sin ((INR N + / 2) * y))
                          (- cos ((INR N + / 2) * x)) y); apply Cv).
  assert (pr_su : Riemann_integrable
                    (fun y => sin ((INR N + / 2) * x) * (g y * cos ((INR N + / 2) * y))) (- PI) PI)
    by (apply RIc, CU).
  assert (pr_nv : Riemann_integrable
                    (fun y => (- cos ((INR N + / 2) * x)) * (g y * sin ((INR N + / 2) * y))) (- PI) PI)
    by (apply RIc, CV).
  assert (pr_sum : Riemann_integrable
                     (fun y => sin ((INR N + / 2) * x) * (g y * cos ((INR N + / 2) * y))
                             + (- cos ((INR N + / 2) * x)) * (g y * sin ((INR N + / 2) * y))) (- PI) PI)
    by (apply RIc; intro y; apply continuity_pt_plus; [ apply (CU y) | apply (CV y) ]).
  assert (E : RiemannInt (ri_diffD f Cf N x) = RiemannInt pr_sum).
  { apply RiemannInt_P18; [ lra | intros y Hy ].
    rewrite <- (Hg_loc y ltac:(lra)), Rmult_assoc,
      (Rmult_comm (sin ((x - y) / 2)) (Dsum N (x - y))), (dirichlet_kernel N (x - y)).
    replace ((INR N + / 2) * (x - y)) with ((INR N + / 2) * x - (INR N + / 2) * y) by ring.
    rewrite sin_minus; ring. }
  rewrite E.
  rewrite (RI_add (fun y => sin ((INR N + / 2) * x) * (g y * cos ((INR N + / 2) * y)))
                  (fun y => (- cos ((INR N + / 2) * x)) * (g y * sin ((INR N + / 2) * y)))
                  CU CV pr_su pr_nv pr_sum).
  rewrite (RI_scal (fun y => g y * cos ((INR N + / 2) * y)) (sin ((INR N + / 2) * x))
                   Cu (ri_gcos g (INR N + / 2) (- PI) PI HabPI) pr_su).
  rewrite (RI_scal (fun y => g y * sin ((INR N + / 2) * y)) (- cos ((INR N + / 2) * x))
                   Cv (ri_gsin g (INR N + / 2) (- PI) PI HabPI) pr_nv).
  reflexivity.
Qed.

Theorem fourier_pointwise_loc : Un_cv (fun N => SN f Cf N x) (f x).
Proof.
  assert (Igcos_cv : Un_cv (fun n => RiemannInt (ri_gcos g (INR n + / 2) (- PI) PI HabPI)) 0)
    by (apply (RL_cos_cv g (- PI) PI HabPI prdg_loc)).
  assert (Igsin_cv : Un_cv (fun n => RiemannInt (ri_gsin g (INR n + / 2) (- PI) PI HabPI)) 0)
    by (apply (RL_cv g (- PI) PI HabPI prdg_loc)).
  assert (P_cv : Un_cv (fun n => sin ((INR n + / 2) * x)
                              * RiemannInt (ri_gcos g (INR n + / 2) (- PI) PI HabPI)) 0).
  { apply (Un_cv_bnd_null (fun n => sin ((INR n + / 2) * x))
             (fun n => RiemannInt (ri_gcos g (INR n + / 2) (- PI) PI HabPI))).
    - intro n; apply Rabs_le; pose proof (SIN_bound ((INR n + / 2) * x)); lra.
    - exact Igcos_cv. }
  assert (Q_cv : Un_cv (fun n => (- cos ((INR n + / 2) * x))
                              * RiemannInt (ri_gsin g (INR n + / 2) (- PI) PI HabPI)) 0).
  { apply (Un_cv_bnd_null (fun n => - cos ((INR n + / 2) * x))
             (fun n => RiemannInt (ri_gsin g (INR n + / 2) (- PI) PI HabPI))).
    - intro n; rewrite Rabs_Ropp; apply Rabs_le; pose proof (COS_bound ((INR n + / 2) * x)); lra.
    - exact Igsin_cv. }
  assert (R_cv : Un_cv (fun n => sin ((INR n + / 2) * x)
                                 * RiemannInt (ri_gcos g (INR n + / 2) (- PI) PI HabPI)
                             + (- cos ((INR n + / 2) * x))
                                 * RiemannInt (ri_gsin g (INR n + / 2) (- PI) PI HabPI)) 0)
    by (replace 0 with (0 + 0) by ring; apply CV_plus; [ exact P_cv | exact Q_cv ]).
  assert (d_cv : Un_cv (fun n => / (2 * PI)
                     * (sin ((INR n + / 2) * x) * RiemannInt (ri_gcos g (INR n + / 2) (- PI) PI HabPI)
                        + (- cos ((INR n + / 2) * x)) * RiemannInt (ri_gsin g (INR n + / 2) (- PI) PI HabPI))) 0)
    by (apply Un_cv_scal0; exact R_cv).
  intros eps Heps; destruct (d_cv eps Heps) as [N0 HN0]; exists N0; intros n Hn.
  specialize (HN0 n Hn). unfold R_dist in *; rewrite Rminus_0_r in HN0.
  replace (SN f Cf n x - f x)
    with (/ (2 * PI)
          * (sin ((INR n + / 2) * x) * RiemannInt (ri_gcos g (INR n + / 2) (- PI) PI HabPI)
             + (- cos ((INR n + / 2) * x)) * RiemannInt (ri_gsin g (INR n + / 2) (- PI) PI HabPI)))
    by (rewrite <- (localization_identity f Cf n x), integral_expand_loc; reflexivity).
  exact HN0.
Qed.

End ConvergeLoc.

Print Assumptions fourier_pointwise_loc.

(* ================================================================= *)
(*  END FourierConvergeLoc.v                                         *)
(*  S_N f(x) → f(x) needing the localiser identity only on [−π,π].    *)
(* ================================================================= *)
