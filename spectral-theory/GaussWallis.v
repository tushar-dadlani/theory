(* ================================================================= *)
(*  GaussWallis.v  —  Gaussian part-A stack, step 4c: the reflection   *)
(*  ∫cos = ∫sin, landing the lower substitution at √n·W_{2n+1}.        *)
(*                                                                    *)
(*    reflect_integral : ∫₀^c h(x) dx = ∫₀^c h(c−x) dx  (h continuous);*)
(*    cos_pow_int      : ∫₀^{π/2} cosᵐ = W_m  (reflection θ↦π/2−θ,     *)
(*                       then cos(π/2−x) = sin x);                     *)
(*    gauss_lower_wallis : ∫₀^√n (1−x²/n)ⁿ dx = √n · W_{2n+1}.         *)
(*                                                                    *)
(*  reflect_integral is the DECREASING substitution x ↦ c−x, done via  *)
(*  the local antiderivative K(t) = −H(c−t) of h(c−·) (FTC_antideriv,  *)
(*  ContinuousCoV) — cov_continuous only covers increasing g.          *)
(*                                                                    *)
(*  This turns the bounded lower Gaussian integral into √n·W_{2n+1},    *)
(*  for which we already have the asymptotics.  No new axioms          *)
(*  (classical Reals only).                                          *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import WallisIntegral ContinuousCoV GaussSubst.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  Reflection x ↦ c − x.                                            *)
(* ----------------------------------------------------------------- *)

Lemma reflect_integral : forall (h : R -> R) (c : R), 0 <= c ->
  (forall u, 0 <= u <= c -> continuity_pt h u) ->
  forall (pr1 : Riemann_integrable h 0 c)
         (pr2 : Riemann_integrable (fun x => h (c - x)) 0 c),
  RiemannInt pr1 = RiemannInt pr2.
Proof.
  intros h c Hc Hcont pr1 pr2.
  destruct (RiemannInt_P30 Hc Hcont) as [H HH].
  assert (Hcont' : forall x, 0 <= x <= c -> continuity_pt (fun x => h (c - x)) x).
  { intros x Hx; apply (continuity_pt_comp (fun y => c - y) h x).
    - apply continuity_pt_minus;
        [ apply continuity_pt_const; intros a b; reflexivity
        | apply derivable_continuous_pt; exists 1; apply derivable_pt_lim_id ].
    - apply Hcont; lra. }
  assert (HK : antiderivative (fun x => h (c - x)) (fun t => - H (c - t)) 0 c).
  { split; [ | exact Hc ].
    intros t Ht.
    assert (Hct : 0 <= c - t <= c) by lra.
    destruct (proj1 HH (c - t) Hct) as [prH HprH].
    set (v := h (c - t)).
    assert (Hlim : derivable_pt_lim (fun s => - H (c - s)) t v).
    { unfold v.
      pose proof (derivable_pt_lim_minus (fun _ => c) (fun s => s) t 0 1
                    (derivable_pt_lim_const c t) (derivable_pt_lim_id t)) as Hin.
      replace (0 - 1) with (-1) in Hin by ring.
      pose proof (derivable_pt_lim_comp (fun s => c - s) H t (-1)
                    (derive_pt H (c - t) prH) Hin
                    ltac:(unfold derive_pt; exact (proj2_sig prH))) as Hco.
      pose proof (derivable_pt_lim_opp (fun s => H (c - s)) t
                    (derive_pt H (c - t) prH * -1) Hco) as Hop.
      replace (- (derive_pt H (c - t) prH * -1)) with (h (c - t)) in Hop
        by (rewrite <- HprH; ring).
      exact Hop. }
    exists (exist _ v Hlim); reflexivity. }
  rewrite (FTC_antideriv h H 0 c Hc Hcont pr1 HH).
  rewrite (FTC_antideriv (fun x => h (c - x)) (fun t => - H (c - t)) 0 c Hc Hcont' pr2 HK).
  replace (c - c) with 0 by ring; replace (c - 0) with c by ring; ring.
Qed.

(* ----------------------------------------------------------------- *)
(*  ∫₀^{π/2} cosᵐ = W_m.                                             *)
(* ----------------------------------------------------------------- *)

Lemma cont_cos_pow : forall m, continuity (fun x => (cos x) ^ m).
Proof. intro m; exact (cont_pow cos m continuity_cos). Qed.

Lemma cos_pow_int : forall m
  (prCos : Riemann_integrable (fun x => (cos x) ^ m) 0 (PI / 2)),
  RiemannInt prCos = Wallis m.
Proof.
  intros m prCos; assert (Hpi : (0 : R) <= PI / 2) by (pose proof PI2_RGT_0; lra).
  assert (prRefl : Riemann_integrable (fun x => (cos (PI / 2 - x)) ^ m) 0 (PI / 2)).
  { apply continuity_implies_RiemannInt; [ exact Hpi | intros x _ ].
    apply (cont_pow (fun y => cos (PI / 2 - y)) m).
    intro z; apply (continuity_pt_comp (fun y => PI / 2 - y) cos z).
    - apply continuity_pt_minus;
        [ apply continuity_pt_const; intros a b; reflexivity
        | apply derivable_continuous_pt; exists 1; apply derivable_pt_lim_id ].
    - apply continuity_cos. }
  rewrite (reflect_integral (fun x => (cos x) ^ m) (PI / 2) Hpi
             (fun u _ => cont_cos_pow m u) prCos prRefl).
  unfold Wallis; apply RiemannInt_P18; [ exact Hpi | intros x _ ].
  unfold sin_pow.
  replace (cos (PI / 2 - x)) with (sin x) by (rewrite cos_minus, cos_PI2, sin_PI2; ring).
  reflexivity.
Qed.

(* ----------------------------------------------------------------- *)
(*  The lower Gaussian integral as √n · W_{2n+1}.                    *)
(* ----------------------------------------------------------------- *)

Corollary gauss_lower_wallis : forall n, 0 < INR n ->
  forall (prX : Riemann_integrable (fun x => (1 - x ^ 2 / INR n) ^ n) 0 (sqrt (INR n))),
  RiemannInt prX = sqrt (INR n) * Wallis (2 * n + 1).
Proof.
  intros n Hn prX; assert (Hpi : (0 : R) <= PI / 2) by (pose proof PI2_RGT_0; lra).
  assert (prCos : Riemann_integrable (fun t => (cos t) ^ (2 * n + 1)) 0 (PI / 2))
    by (apply continuity_implies_RiemannInt; [ exact Hpi | intros t _; apply cont_cos_pow ]).
  assert (prC : Riemann_integrable (fun t => sqrt (INR n) * (cos t) ^ (2 * n + 1)) 0 (PI / 2)).
  { apply continuity_implies_RiemannInt; [ exact Hpi | intros t _ ].
    apply (continuity_pt_scal (fun s => (cos s) ^ (2 * n + 1)) (sqrt (INR n)) t); apply cont_cos_pow. }
  rewrite (gauss_lower_subst n Hn prX prC).
  rewrite (int_scal (fun t => (cos t) ^ (2 * n + 1)) (sqrt (INR n)) (cont_cos_pow (2 * n + 1)) prCos prC).
  rewrite (cos_pow_int (2 * n + 1) prCos); reflexivity.
Qed.

Print Assumptions cos_pow_int.
Print Assumptions gauss_lower_wallis.

(* ================================================================= *)
(*  END GaussWallis.v                                                *)
(*  ∫₀^√n (1−x²/n)ⁿ dx = √n · W_{2n+1}, bounded and axiom-free.  With   *)
(*  Wallis_sq_asymp this drives ∫₀^√n e^{−x²} toward √π/2; only the     *)
(*  improper ∫₀^∞ side and the √-step remain.                         *)
(* ================================================================= *)
