(* ================================================================= *)
(*  TauberianBlock.v  --  the quantitative engine of Newman's          *)
(*  Tauberian squeeze.                                                 *)
(*                                                                    *)
(*  If psi overshoots at x  (psiR x >= lam*x, lam > 1) then MONOTONICITY*)
(*  of psi forces a block of area at least  lam - 1 - ln lam > 0  into  *)
(*  the integral over [x, lam*x]:                                      *)
(*                                                                    *)
(*      int_x^{lam x} (psiR t - t)/t^2 dt  >=  lam - 1 - ln lam        *)
(*                                                                    *)
(*  and dually for an undershoot.  Since that lower bound does NOT     *)
(*  shrink as x -> oo, it contradicts the Cauchy tail of a convergent  *)
(*  improper integral.  That contradiction is the squeeze.             *)
(*                                                                    *)
(*  NewmanBlock.block_int computes the block only when the numerator   *)
(*  constant equals the RIGHT endpoint; the undershoot case needs it   *)
(*  at the LEFT endpoint.  gen_block_int below does both at once.      *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import ContinuousCoV NewmanTauber NewmanBlock
        Chebyshev ChebyshevPsiR PsiRIntegrable.
Open Scope R_scope.

(* continuity of the comparison integrand, for an ARBITRARY constant *)
Lemma block_cont_c : forall c x, 0 < x ->
  continuity_pt (fun t => (c - t) / (t * t)) x.
Proof.
  intros c x Hx; apply continuity_pt_div.
  - apply continuity_pt_minus;
      [ apply continuity_pt_const; intros u v; reflexivity | apply cont_id ].
  - apply continuity_pt_mult; apply cont_id.
  - assert (0 < x * x) by nra; lra.
Qed.

Lemma cmp_integrable : forall c a b, 0 < a -> a <= b ->
  Riemann_integrable (fun t => (c - t) / (t * t)) a b.
Proof.
  intros c a b Ha Hab.
  destruct (Rle_lt_or_eq_dec a b Hab) as [Hlt | He];
    [ | rewrite <- He; apply RiemannInt_P7 ].
  apply RiemannInt_P6; [ exact Hlt | ].
  intros x Hx. apply block_cont_c. lra.
Qed.

(* the block value, constant anywhere *)
Lemma gen_block_int : forall (c a b : R), 0 < a -> a <= b ->
  forall (pr : Riemann_integrable (fun t => (c - t) / (t * t)) a b),
    RiemannInt pr = (- c / b - ln b) - (- c / a - ln a).
Proof.
  intros c a b Ha Hab pr.
  assert (Hanti : antiderivative (fun t => (c - t) / (t * t))
                    (fun u => - c / u - ln u) a b).
  { split; [ | exact Hab ]; intros x [Hx1 Hx2]; assert (Hxpos : 0 < x) by lra.
    assert (HGd : derivable_pt_lim (fun u => - c / u - ln u) x
                    ((c - x) / (x * x))).
    { replace ((c - x) / (x * x)) with (- (- c) / (x * x) - / x)
        by (field; lra).
      apply derivable_pt_lim_minus;
        [ apply (div_const_deriv (- c) x); lra
        | apply derivable_pt_lim_ln; exact Hxpos ]. }
    exists (exist _ ((c - x) / (x * x)) HGd); unfold derive_pt; simpl; reflexivity. }
  exact (FTC_antideriv (fun t => (c - t) / (t * t)) (fun u => - c / u - ln u)
           a b Hab (fun x Hx => block_cont_c c x ltac:(lra)) pr Hanti).
Qed.

(* ----------------------------------------------------------------- *)
(*  THE OVERSHOOT BLOCK                                                *)
(* ----------------------------------------------------------------- *)

Theorem block_lower : forall (x lam : R), 0 < x -> 1 <= lam ->
  lam * x <= psiR x ->
  forall (pr : Riemann_integrable tint x (lam * x)),
    lam - 1 - ln lam <= RiemannInt pr.
Proof.
  intros x lam Hx Hlam Hpsi pr.
  assert (Hlam0 : 0 < lam) by lra.
  assert (Hab : x <= lam * x) by nra.
  pose proof (cmp_integrable (lam * x) x (lam * x) Hx Hab) as prc.
  assert (Hval : RiemannInt prc = lam - 1 - ln lam).
  { rewrite (gen_block_int (lam * x) x (lam * x) Hx Hab prc).
    rewrite (ln_mult lam x Hlam0 Hx).
    replace (- (lam * x) / (lam * x)) with (-1) by (field; nra).
    replace (- (lam * x) / x) with (- lam) by (field; lra).
    lra. }
  rewrite <- Hval.
  apply RiemannInt_P19; [ exact Hab | ].
  intros t Ht.
  assert (Ht0 : 0 < t) by (destruct Ht; lra).
  assert (Htt : 0 < t * t) by nra.
  assert (Hp : lam * x <= psiR t).
  { apply Rle_trans with (psiR x); [ exact Hpsi | ].
    apply psiR_mono; [ lra | destruct Ht; lra ]. }
  unfold tint, Rdiv.
  apply Rmult_le_compat_r; [ left; apply Rinv_0_lt_compat; exact Htt | lra ].
Qed.

(* ----------------------------------------------------------------- *)
(*  THE UNDERSHOOT BLOCK                                               *)
(* ----------------------------------------------------------------- *)

Theorem block_upper : forall (x mu : R), 0 < x -> 0 < mu -> mu <= 1 ->
  psiR x <= mu * x ->
  forall (pr : Riemann_integrable tint (mu * x) x),
    RiemannInt pr <= - (mu - 1 - ln mu).
Proof.
  intros x mu Hx Hmu Hmu1 Hpsi pr.
  assert (Hax : 0 < mu * x) by nra.
  assert (Hab : mu * x <= x) by nra.
  pose proof (cmp_integrable (mu * x) (mu * x) x Hax Hab) as prc.
  assert (Hval : RiemannInt prc = - (mu - 1 - ln mu)).
  { rewrite (gen_block_int (mu * x) (mu * x) x Hax Hab prc).
    rewrite (ln_mult mu x Hmu Hx).
    replace (- (mu * x) / x) with (- mu) by (field; lra).
    replace (- (mu * x) / (mu * x)) with (-1) by (field; nra).
    lra. }
  rewrite <- Hval.
  apply RiemannInt_P19; [ exact Hab | ].
  intros t Ht.
  assert (Ht0 : 0 < t) by (destruct Ht; lra).
  assert (Htt : 0 < t * t) by nra.
  assert (Hp : psiR t <= mu * x).
  { apply Rle_trans with (psiR x); [ | exact Hpsi ].
    apply psiR_mono; [ lra | destruct Ht; lra ]. }
  unfold tint, Rdiv.
  apply Rmult_le_compat_r; [ left; apply Rinv_0_lt_compat; exact Htt | lra ].
Qed.

Print Assumptions block_lower.
Print Assumptions block_upper.
