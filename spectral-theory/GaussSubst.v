(* ================================================================= *)
(*  GaussSubst.v  —  Gaussian part-A stack, step 4b: the lower         *)
(*  substitution ∫₀^√n (1−x²/n)ⁿ dx = √n·∫₀^{π/2} cos^{2n+1}θ dθ.       *)
(*                                                                    *)
(*  The change of variables x = √n·sinθ (ContinuousCoV.cov_continuous)*)
(*  applied to the lower Gaussian flank.  With g θ = √n·sinθ           *)
(*  (scaled_sin, a C1_fun, increasing [0,π/2]→[0,√n]) and              *)
(*  f x = (1−x²/n)ⁿ:                                                   *)
(*     (1−(√n sinθ)²/n)ⁿ·√n cosθ = (cos²θ)ⁿ·√n cosθ = √n cos^{2n+1}θ,  *)
(*  since (√n)² = n and 1−sin²θ = cos²θ.  So                          *)
(*                                                                    *)
(*     ∫₀^√n (1−x²/n)ⁿ dx = √n·∫₀^{π/2} cos^{2n+1}θ dθ                  *)
(*                                                                    *)
(*  entirely on BOUNDED intervals, axiom-free.  (The RHS equals        *)
(*  √n·W_{2n+1} once ∫cos = ∫sin; the improper ∞-side and √π assembly  *)
(*  remain the wall.)  No new axioms (classical Reals only).          *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import ContinuousCoV.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  θ ↦ c·sinθ  as a C1_fun.                                         *)
(* ----------------------------------------------------------------- *)

Lemma scaled_sin_deriv : forall c x, derivable_pt_lim (fun t => c * sin t) x (c * cos x).
Proof. intros c x; exact (derivable_pt_lim_scal sin c x (cos x) (derivable_pt_lim_sin x)). Qed.

Lemma cont_scal_cos : forall c, continuity (fun t => c * cos t).
Proof. intros c x; apply (continuity_pt_scal cos c x); apply continuity_cos. Qed.

Definition scaled_sin (c : R) : C1_fun :=
  mkC1 (c1 := fun t => c * sin t)
       (diff0 := fun t => exist _ (c * cos t) (scaled_sin_deriv c t))
       (cont_scal_cos c).

Lemma scaled_sin_val : forall c t, scaled_sin c t = c * sin t.
Proof. reflexivity. Qed.
Lemma scaled_sin_der : forall c t, derive (scaled_sin c) (diff0 (scaled_sin c)) t = c * cos t.
Proof. reflexivity. Qed.

(* ----------------------------------------------------------------- *)
(*  Continuity of the integrands.                                    *)
(* ----------------------------------------------------------------- *)

Lemma cont_pow : forall (h : R -> R) k, continuity h -> continuity (fun x => (h x) ^ k).
Proof.
  intros h k Hh; induction k as [| k IH]; intro x; simpl;
    [ apply continuity_pt_const; intros a b; reflexivity
    | apply continuity_pt_mult; [ apply Hh | apply IH ] ].
Qed.

Lemma cont_id : continuity (fun x : R => x).
Proof. intro x; apply derivable_continuous_pt; exists 1; apply derivable_pt_lim_id. Qed.

Lemma cont_gaussp : forall n, continuity (fun x => (1 - x ^ 2 / INR n) ^ n).
Proof.
  intro n; apply cont_pow; intro x; apply continuity_pt_minus.
  - apply continuity_pt_const; intros a b; reflexivity.
  - apply (continuity_pt_mult (fun y => y ^ 2) (fun _ => / INR n) x).
    + apply (cont_pow (fun y => y) 2 cont_id).
    + apply continuity_pt_const; intros a b; reflexivity.
Qed.

Lemma c_sqr : forall n, 0 <= INR n -> (sqrt (INR n)) ^ 2 = INR n.
Proof. intros n Hn; simpl; rewrite Rmult_1_r; apply sqrt_sqrt; exact Hn. Qed.

(* ----------------------------------------------------------------- *)
(*  THE LOWER SUBSTITUTION.                                           *)
(* ----------------------------------------------------------------- *)

Theorem gauss_lower_subst : forall n, 0 < INR n ->
  forall (prX : Riemann_integrable (fun x => (1 - x ^ 2 / INR n) ^ n) 0 (sqrt (INR n)))
         (prC : Riemann_integrable (fun t => sqrt (INR n) * (cos t) ^ (2 * n + 1)) 0 (PI / 2)),
  RiemannInt prX = RiemannInt prC.
Proof.
  intros n Hn prX prC.
  set (c := sqrt (INR n)) in *.
  set (f := fun x : R => (1 - x ^ 2 / INR n) ^ n).
  set (g := scaled_sin c).
  assert (Hc0 : 0 <= c) by (unfold c; apply sqrt_pos).
  assert (Hc2 : c ^ 2 = INR n) by (unfold c; apply c_sqr; lra).
  assert (Hg0 : g 0 = 0) by (unfold g; rewrite scaled_sin_val, sin_0; ring).
  assert (HgP : g (PI / 2) = c) by (unfold g; rewrite scaled_sin_val, sin_PI2; ring).
  assert (Hab : (0 : R) <= PI / 2) by (pose proof PI2_RGT_0; lra).
  assert (Hmap : forall t, 0 <= t <= PI / 2 -> g 0 <= g t <= g (PI / 2)).
  { intros t [Hta Htb]; unfold g; rewrite !scaled_sin_val, sin_0, sin_PI2.
    split; (apply Rmult_le_compat_l; [ exact Hc0 | ]).
    - apply sin_ge_0; [ exact Hta | pose proof PI_RGT_0; lra ].
    - pose proof (SIN_bound t); lra. }
  assert (Hfcont : forall u, g 0 <= u <= g (PI / 2) -> continuity_pt f u)
    by (intros u _; apply (cont_gaussp n)).
  assert (prL : Riemann_integrable (fun t => f (g t) * derive g (diff0 g) t) 0 (PI / 2)).
  { apply continuity_implies_RiemannInt; [ exact Hab | intros t _ ]; apply continuity_pt_mult.
    - apply (continuity_pt_comp g f t);
        [ apply derivable_continuous_pt; apply (diff0 g) | apply (cont_gaussp n) ].
    - apply (cont1 g). }
  assert (prR : Riemann_integrable f (g 0) (g (PI / 2))).
  { apply continuity_implies_RiemannInt;
      [ rewrite Hg0, HgP; exact Hc0 | intros u _; apply (cont_gaussp n) ]. }
  (* the substituted integrand simplifies to c·cos^{2n+1} *)
  assert (HP18 : RiemannInt prL = RiemannInt prC).
  { apply RiemannInt_P18; [ exact Hab | intros t [Hta Htb] ].
    unfold f, g; rewrite scaled_sin_val, scaled_sin_der.
    assert (Hbase : 1 - (c * sin t) ^ 2 / INR n = (cos t) ^ 2).
    { replace ((c * sin t) ^ 2) with (c ^ 2 * (sin t) ^ 2) by ring.
      rewrite Hc2.
      replace (INR n * (sin t) ^ 2 / INR n) with ((sin t) ^ 2) by (field; lra).
      pose proof (sin2_cos2 t) as HP; unfold Rsqr in HP; nra. }
    rewrite Hbase, <- (pow_mult (cos t) 2 n).
    replace (2 * n + 1)%nat with (S (2 * n)) by lia.
    cbn [pow]; ring. }
  (* rebind the bounds g 0 = 0, g (PI/2) = c to match prX *)
  assert (Hbounds : RiemannInt prR = RiemannInt prX)
    by (revert prR; rewrite Hg0, HgP; intro prR; apply RiemannInt_P5).
  pose proof (cov_continuous g f 0 (PI / 2) Hab Hmap Hfcont prL prR) as Hcov.
  transitivity (RiemannInt prR); [ symmetry; exact Hbounds | ].
  transitivity (RiemannInt prL); [ symmetry; exact Hcov | exact HP18 ].
Qed.

Print Assumptions gauss_lower_subst.

(* ================================================================= *)
(*  END GaussSubst.v                                                 *)
(*  ∫₀^√n (1−x²/n)ⁿ dx = √n·∫₀^{π/2} cos^{2n+1}θ dθ, bounded and        *)
(*  axiom-free.  Combined with the pointwise lower bound and the       *)
(*  Wallis asymptotics, this drives ∫₀^√n e^{−x²} toward √π/2.         *)
(* ================================================================= *)
