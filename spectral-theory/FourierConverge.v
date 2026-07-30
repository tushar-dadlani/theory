(* ================================================================= *)
(*  FourierConverge.v  —  Fourier F3, step 3 (capstone): POINTWISE    *)
(*  CONVERGENCE of the Fourier series.                               *)
(*                                                                    *)
(*     S_N f(x) → f(x)   as N → ∞.                                    *)
(*                                                                    *)
(*  Hypotheses: f continuous, and — the Dini / C¹ localisation        *)
(*  condition at x — a `C1_fun` g representing the localised quotient  *)
(*  in MULTIPLICATIVE form,                                           *)
(*                                                                    *)
(*     Hg :  g(y) · sin((x−y)/2) = f(y) − f(x)   for all y.           *)
(*                                                                    *)
(*  Writing it multiplicatively is the whole trick: it holds at y = x *)
(*  too (both sides 0), so the removable singularity of the quotient   *)
(*  (f(y)−f(x))/sin((x−y)/2) never enters the proof — g is an honest   *)
(*  total C¹ function, not a hypothesis about a 0/0 limit.  The        *)
(*  existence of such a g is exactly a strong (C¹) Dini condition on f *)
(*  at x; it is an explicit interface here, NOT an axiom or admit.     *)
(*                                                                    *)
(*  Proof.  Localisation (FourierLocalize) gives                      *)
(*     S_N f(x) − f(x) = (1/2π) ∫ (f(y)−f(x)) D_N(x−y) dy.             *)
(*  Hg and the Dirichlet closed form D_N(t)·sin(t/2) = sin((N+½)t)     *)
(*  (DirichletKernel.dirichlet_kernel) turn the integrand into        *)
(*     g(y) · sin((N+½)(x−y))                                         *)
(*     = sin((N+½)x)·(g(y)cos((N+½)y)) − cos((N+½)x)·(g(y)sin((N+½)y)),*)
(*  a bounded (|sin|,|cos| ≤ 1) combination of the two Riemann–        *)
(*  Lebesgue integrals RL_cos_cv (∫ g cos) and RL_cv (∫ g sin), each   *)
(*  → 0.  Bounded × null → null, so S_N f(x) − f(x) → 0.               *)
(*                                                                    *)
(*  No new axioms (classical Reals only).                            *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import FourierRL FourierRLcos DirichletKernel FourierPartialSum
        FourierKernelRep FourierLocalize.
Open Scope R_scope.

(* integrability of continuous integrands on [-π,π] *)
Lemma RIc : forall g, continuity g -> Riemann_integrable g (- PI) PI.
Proof.
  intros g Cg; apply continuity_implies_RiemannInt;
    [ pose proof PI_RGT_0; lra | intros x _; apply Cg ].
Qed.

Lemma HabPI : - PI <= PI.
Proof. pose proof PI_RGT_0; lra. Qed.

(* ----------------------------------------------------------------- *)
(*  Two convergence atoms.                                            *)
(* ----------------------------------------------------------------- *)

(* bounded sequence times a null sequence is null *)
Lemma Un_cv_bnd_null : forall (c A : nat -> R),
  (forall n, Rabs (c n) <= 1) -> Un_cv A 0 -> Un_cv (fun n => c n * A n) 0.
Proof.
  intros c A Hc HA eps Heps.
  destruct (HA eps Heps) as [N HN]. exists N; intros n Hn.
  specialize (HN n Hn). unfold R_dist in *. rewrite Rminus_0_r in *.
  rewrite Rabs_mult.
  apply Rle_lt_trans with (1 * Rabs (A n)).
  - apply Rmult_le_compat_r; [ apply Rabs_pos | apply Hc ].
  - rewrite Rmult_1_l; exact HN.
Qed.

(* a constant times a null sequence is null *)
Lemma Un_cv_scal0 : forall (A : nat -> R) (k : R), Un_cv A 0 -> Un_cv (fun n => k * A n) 0.
Proof.
  intros A k HA.
  destruct (Req_dec k 0) as [Hk | Hk].
  - intros eps Heps; exists 0%nat; intros n _; unfold R_dist;
      rewrite Rminus_0_r, Hk, Rmult_0_l, Rabs_R0; exact Heps.
  - assert (Hk' : 0 < Rabs k) by (apply Rabs_pos_lt; exact Hk).
    intros eps Heps.
    destruct (HA (eps / Rabs k) (Rdiv_lt_0_compat eps (Rabs k) Heps Hk')) as [N HN].
    exists N; intros n Hn; specialize (HN n Hn).
    unfold R_dist in *; rewrite Rminus_0_r in *.
    rewrite Rabs_mult.
    apply Rlt_le_trans with (Rabs k * (eps / Rabs k)).
    + apply Rmult_lt_compat_l; [ exact Hk' | exact HN ].
    + apply Req_le; field; apply Rgt_not_eq; exact Hk'.
Qed.

(* ----------------------------------------------------------------- *)
(*  The pointwise convergence theorem.                                *)
(* ----------------------------------------------------------------- *)

Section Converge.

Variable f : R -> R.
Hypothesis Cf : continuity f.
Variable x : R.

(* the Dini / C¹ localiser at x, in multiplicative (singularity-free) form *)
Variable g : C1_fun.
Hypothesis Hg : forall y, g y * sin ((x - y) / 2) = f y - f x.

(* |g'| is integrable on [-π,π] (from continuity of g') — RL input *)
Lemma prdg : Riemann_integrable (fun t => Rabs (derive g (diff0 g) t)) (- PI) PI.
Proof.
  apply continuity_implies_RiemannInt; [ exact HabPI | intros t _ ];
    apply (continuity_pt_comp (derive g (diff0 g)) Rabs t);
    [ apply (cont1 g) | apply Rcontinuity_abs ].
Qed.

(* THE key rewrite: the localisation integral is the RL combination *)
Lemma integral_expand : forall N,
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
  { apply RiemannInt_P18; [ lra | intros y _ ].
    rewrite <- (Hg y), Rmult_assoc,
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

Theorem fourier_pointwise : Un_cv (fun N => SN f Cf N x) (f x).
Proof.
  (* the two Riemann–Lebesgue limits *)
  assert (Igcos_cv : Un_cv (fun n => RiemannInt (ri_gcos g (INR n + / 2) (- PI) PI HabPI)) 0)
    by (apply (RL_cos_cv g (- PI) PI HabPI prdg)).
  assert (Igsin_cv : Un_cv (fun n => RiemannInt (ri_gsin g (INR n + / 2) (- PI) PI HabPI)) 0)
    by (apply (RL_cv g (- PI) PI HabPI prdg)).
  (* bounded (|sin|,|cos| ≤ 1) × null → null *)
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
  (* transfer to S_N f(x) via localisation + integral_expand *)
  intros eps Heps; destruct (d_cv eps Heps) as [N0 HN0]; exists N0; intros n Hn.
  specialize (HN0 n Hn). unfold R_dist in *; rewrite Rminus_0_r in HN0.
  replace (SN f Cf n x - f x)
    with (/ (2 * PI)
          * (sin ((INR n + / 2) * x) * RiemannInt (ri_gcos g (INR n + / 2) (- PI) PI HabPI)
             + (- cos ((INR n + / 2) * x)) * RiemannInt (ri_gsin g (INR n + / 2) (- PI) PI HabPI)))
    by (rewrite <- (localization_identity f Cf n x), integral_expand; reflexivity).
  exact HN0.
Qed.

End Converge.

Print Assumptions fourier_pointwise.

(* ================================================================= *)
(*  END FourierConverge.v                                            *)
(*  Fourier F3 complete (modulo the C¹ Dini localiser g as an         *)
(*  explicit hypothesis): S_N f(x) → f(x).  The full analytic route    *)
(*  F1 (Riemann–Lebesgue) → F2 (kernel representation) →              *)
(*  F3 (localisation + convergence) is now in place, axiom-free.       *)
(*  The one remaining analytic lemma is the CONSTRUCTION of g from a   *)
(*  concretely smooth f (e.g. f ∈ C¹): the removable singularity of    *)
(*  (f(y)−f(x))/(2 sin((x−y)/2)) at y = x.                             *)
(* ================================================================= *)
