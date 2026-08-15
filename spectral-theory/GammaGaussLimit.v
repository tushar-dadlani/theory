(* ================================================================= *)
(*  GammaGaussLimit.v   (the Gauss-limit representation of Gamma)       *)
(*                                                                    *)
(*  Content A: the Beta integral  betaI s N = int_0^1 u^{s-1}(1-u)^N du  *)
(*  and its closed form  betaI s N = N! / (s(s+1)...(s+N))  via IBP.     *)
(*                                                                    *)
(*  Mirrors GammaReal.gnear (ImproperCv0 near 0) and GammaRecur.v       *)
(*  (integration by parts on an improper integral via FTC_antideriv).   *)
(*                                                                    *)
(*  Axioms: standard classical-Reals only.                            *)
(* ================================================================= *)

From Stdlib Require Import Reals Rpower Lra Lia.
Require Import GammaReal MellinElem ImproperCv0 RpowerZero ZetaContinuation
        GammaFunction ContinuousCoV GammaExtend.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  the Beta integrand  u^{s-1} (1-u)^N  and its integral over (0,1]  *)
(* ----------------------------------------------------------------- *)
Definition bnk (s : R) (N : nat) (u : R) : R := Rpower u (s - 1) * (1 - u) ^ N.

Lemma cont_bnk : forall s N u, 0 < u -> continuity_pt (bnk s N) u.
Proof.
  intros s N u Hu. unfold bnk. apply continuity_pt_mult.
  - apply cont_Rpower_pos; exact Hu.
  - apply (continuity_pt_comp (fun u => 1 - u) (fun x => x ^ N) u).
    + apply continuity_pt_minus;
        [ apply continuity_pt_const; unfold constant; reflexivity
        | apply derivable_continuous_pt; exists 1; apply derivable_pt_lim_id ].
    + apply derivable_continuous_pt; apply derivable_pt_pow.
Qed.

Lemma Hf_bnk : forall s N, forall x y, 0 < x -> x <= y ->
  Riemann_integrable (bnk s N) x y.
Proof.
  intros s N x y Hx Hxy. apply continuity_implies_RiemannInt;
    [ exact Hxy | intros t Ht; apply cont_bnk; lra ].
Qed.

Lemma bnk_nonneg : forall s N u, 0 < u -> u <= 1 -> 0 <= bnk s N u.
Proof.
  intros s N u Hu Hu1. unfold bnk. apply Rmult_le_pos.
  - left; unfold Rpower; apply exp_pos.
  - apply pow_le; lra.
Qed.

(* betaI's partial integral over [x,1] is bounded by 1/s *)
Lemma bnk_bound : forall s N x (Hx : 0 < x) (Hx1 : x <= 1), 0 < s ->
  rint01 (bnk s N) (Hf_bnk s N) x <= / s.
Proof.
  intros s N x Hx Hx1 Hs.
  rewrite (rint01_val (bnk s N) (Hf_bnk s N) x Hx Hx1).
  apply Rle_trans with (RiemannInt (rpow_ri s x 1 Hx Hx1)).
  - apply RiemannInt_P19; [ exact Hx1 | intros t [Ht1 HtA]; unfold bnk ].
    rewrite <- (Rmult_1_r (Rpower t (s - 1))) at 2.
    apply Rmult_le_compat_l; [ left; unfold Rpower; apply exp_pos | ].
    apply Rle_trans with (1 ^ N); [ apply pow_incr; lra | rewrite pow1; apply Rle_refl ].
  - rewrite (rpow_pint s x Hx Hx1 (Rgt_not_eq _ _ Hs)), Rpower_base1.
    assert (0 <= Rpower x s) by (left; unfold Rpower; apply exp_pos).
    assert (0 < / s) by (apply Rinv_0_lt_compat; exact Hs).
    nra.
Qed.

Definition betaI_sig (s : R) (N : nat) (Hs : 0 < s) :
  { I : R | ImproperCv0 (bnk s N) (Hf_bnk s N) I }.
Proof.
  apply (improper_bounded_cv0 (bnk s N) (Hf_bnk s N)
           (fun x Hx Hx1 => bnk_nonneg s N x Hx Hx1)).
  exists (/ s); intros x Hx Hx1; apply bnk_bound; assumption.
Defined.

Definition betaI (s : R) (N : nat) (Hs : 0 < s) : R := proj1_sig (betaI_sig s N Hs).

Lemma betaI_spec : forall s N (Hs : 0 < s),
  ImproperCv0 (bnk s N) (Hf_bnk s N) (betaI s N Hs).
Proof. intros s N Hs. exact (proj2_sig (betaI_sig s N Hs)). Qed.

(* ----------------------------------------------------------------- *)
(*  the IBP antiderivative  F(u) = (1/s) u^s (1-u)^{S N}               *)
(*  with  F'(u) = bnk s (S N) u - (S N/s) bnk (s+1) N u                *)
(* ----------------------------------------------------------------- *)
Lemma Fanti_deriv : forall s N u, 0 < s -> 0 < u ->
  derivable_pt_lim (fun w => / s * (Rpower w s * (1 - w) ^ (S N))) u
    (bnk s (S N) u - INR (S N) / s * bnk (s + 1) N u).
Proof.
  intros s N u Hs Hu.
  assert (HA : derivable_pt_lim (fun w => Rpower w s) u (s * Rpower u (s - 1)))
    by (apply Rpower_deriv; exact Hu).
  assert (Hin : derivable_pt_lim (fun w => 1 - w) u (-1)).
  { replace (-1) with (0 - 1) by ring.
    apply (derivable_pt_lim_minus (fun _ => 1) (fun w => w) u 0 1);
      [ apply derivable_pt_lim_const | apply derivable_pt_lim_id ]. }
  assert (HB : derivable_pt_lim (fun w => (1 - w) ^ (S N)) u (INR (S N) * (1 - u) ^ N * (-1))).
  { apply (derivable_pt_lim_comp (fun w => 1 - w) (fun x => x ^ (S N)) u
             (-1) (INR (S N) * (1 - u) ^ N)).
    - exact Hin.
    - pose proof (derivable_pt_lim_pow (1 - u) (S N)) as Hp.
      simpl Init.Nat.pred in Hp. exact Hp. }
  assert (HAB : derivable_pt_lim (fun w => Rpower w s * (1 - w) ^ (S N)) u
                  (s * Rpower u (s - 1) * (1 - u) ^ (S N)
                   + Rpower u s * (INR (S N) * (1 - u) ^ N * (-1))))
    by (apply (derivable_pt_lim_mult (fun w => Rpower w s) (fun w => (1 - w) ^ (S N)) u
                 (s * Rpower u (s - 1)) (INR (S N) * (1 - u) ^ N * (-1))); [ exact HA | exact HB ]).
  pose proof (derivable_pt_lim_scal (fun w => Rpower w s * (1 - w) ^ (S N)) (/ s) u _ HAB) as HF.
  apply (derivable_pt_lim_ext (mult_real_fct (/ s) (fun w => Rpower w s * (1 - w) ^ (S N)))
           (fun w => / s * (Rpower w s * (1 - w) ^ (S N)))).
  - intro w; unfold mult_real_fct; reflexivity.
  - replace (bnk s (S N) u - INR (S N) / s * bnk (s + 1) N u)
      with (/ s * (s * Rpower u (s - 1) * (1 - u) ^ (S N)
                   + Rpower u s * (INR (S N) * (1 - u) ^ N * (-1)))).
    + exact HF.
    + unfold bnk. replace (s + 1 - 1) with s by ring. field. lra.
Qed.

Print Assumptions Fanti_deriv.
