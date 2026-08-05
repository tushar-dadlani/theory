(* ================================================================= *)
(*  MajorantSum.v  —  the summable majorant (Step 2d, v3b).            *)
(*                                                                    *)
(*  phi(t) = (ln t + 1)/t^2 is decreasing on [1,oo) (phi'(t) =         *)
(*  (-1-2 ln t)/t^3 <= 0), and with G(t) = (ln t + 2)/t (G'(t) =        *)
(*  -phi(t)) the MVT gives the termwise domination                     *)
(*      phi(m) <= G(m-1) - G(m),                                       *)
(*  so a telescoping induction bounds the partial sums UNIFORMLY:       *)
(*      Sum_{m=2}^{k+1} phi(m) <= G(1) - G(k+1) <= G(1) = 2.            *)
(*  Combined with |b(m)| <= 16 phi(m) (EulerMaclaurin.b_bound):         *)
(*      Sum_{m=2}^{y} |b(m)| <= 32                                     *)
(*  -- a uniform (N-independent) bound on the Euler-Maclaurin defect    *)
(*  sum, exactly what the Abel/total-variation assembly consumes.       *)
(*  No limits, no completeness.  Axiom-clean.                          *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia Arith List.
Require Import ChebyshevBound RealMobius EulerMaclaurin MobiusOverD.
Import ListNotations.
Open Scope R_scope.

Definition phi  (t : R) : R := (ln t + 1) / (t * t).
Definition Gfun (t : R) : R := (ln t + 2) / t.
Definition Gp   (t : R) : R := - (ln t + 1) / (t * t).
Definition phip (t : R) : R := (-1 - 2 * ln t) / (t * t * t).

(* G'(t) = -phi(t) *)
Lemma dG : forall t, 0 < t -> derivable_pt_lim Gfun t (Gp t).
Proof.
  intros t Ht.
  assert (Hf : derivable_pt_lim (fun y => ln y + 2) t (/ t)).
  { replace (/ t) with (/ t + 0) by ring.
    apply derivable_pt_lim_plus;
      [ apply derivable_pt_lim_ln; exact Ht | apply (derivable_pt_lim_const 2 t) ]. }
  assert (Hg : derivable_pt_lim (fun y => y) t 1) by apply derivable_pt_lim_id.
  pose proof (derivable_pt_lim_div (fun y => ln y + 2) (fun y => y) t (/ t) 1
                Hf Hg ltac:(lra)) as Hd.
  replace (Gp t) with ((/ t * t - 1 * (ln t + 2)) / (t)²)
    by (unfold Gp, Rsqr; field; lra).
  exact Hd.
Qed.

(* phi'(t) = phip(t) *)
Lemma dphi : forall t, 0 < t -> derivable_pt_lim phi t (phip t).
Proof.
  intros t Ht.
  assert (Hf : derivable_pt_lim (fun y => ln y + 1) t (/ t)).
  { replace (/ t) with (/ t + 0) by ring.
    apply derivable_pt_lim_plus;
      [ apply derivable_pt_lim_ln; exact Ht | apply (derivable_pt_lim_const 1 t) ]. }
  assert (Hg : derivable_pt_lim (fun y => y * y) t (1 * t + t * 1))
    by (apply (derivable_pt_lim_mult (fun y => y) (fun y => y) t 1 1);
        apply derivable_pt_lim_id).
  pose proof (derivable_pt_lim_div (fun y => ln y + 1) (fun y => y * y) t (/ t)
                (1 * t + t * 1) Hf Hg ltac:(nra)) as Hd.
  replace (phip t) with ((/ t * (t * t) - (1 * t + t * 1) * (ln t + 1)) / (t * t)²)
    by (unfold phip, Rsqr; field; lra).
  exact Hd.
Qed.

Lemma phip_nonpos : forall t, 1 <= t -> phip t <= 0.
Proof.
  intros t Ht; unfold phip, Rdiv.
  assert (0 <= ln t) by (rewrite <- ln_1; apply ln_le; lra).
  assert (0 < / (t * t * t)) by (apply Rinv_0_lt_compat; nra).
  nra.
Qed.

(* phi is nonincreasing on [1,oo) *)
Lemma phi_dec : forall x y, 1 <= x -> x <= y -> phi y <= phi x.
Proof.
  intros x y Hx Hxy; destruct (Rle_lt_or_eq_dec x y Hxy) as [Hlt|Heq];
    [ | subst; lra ].
  destruct (MVT_cor2 phi phip x y Hlt (fun c Hc => dphi c ltac:(lra))) as [eta [Heq He]].
  pose proof (phip_nonpos eta ltac:(lra)) as Hnp.
  nra.
Qed.

(* the termwise domination *)
Lemma majorant_step : forall m, (2 <= m)%nat ->
  phi (INR m) <= Gfun (INR (m - 1)) - Gfun (INR m).
Proof.
  intros m Hm.
  assert (Hm1 : 1 <= INR (m - 1)) by (apply (le_INR 1); lia).
  assert (Hstep : INR m = INR (m - 1) + 1) by (rewrite <- S_INR; f_equal; lia).
  set (a := INR (m - 1)) in *; set (c := INR m) in *.
  assert (Hac : a < c) by lra.
  destruct (MVT_cor2 Gfun Gp a c Hac (fun x Hx => dG x ltac:(lra))) as [xi [HG Hxi]].
  assert (Hca1 : c - a = 1) by lra.
  rewrite Hca1, Rmult_1_r in HG.
  assert (Hgp : Gp xi = - phi xi) by (unfold Gp, phi; field; nra).
  rewrite Hgp in HG.
  assert (phi c <= phi xi) by (apply phi_dec; lra).
  lra.
Qed.

Definition Bsum (k : nat) : R := Rls (seq 2 k) (fun m => phi (INR m)).

Lemma Bsum_tele : forall k, Bsum k <= Gfun 1 - Gfun (INR (k + 1)).
Proof.
  induction k as [|k IH].
  - unfold Bsum; replace (seq 2 0) with (@nil nat) by reflexivity; rewrite Rls_nil2.
    replace (0 + 1)%nat with 1%nat by lia; rewrite INR_1; lra.
  - unfold Bsum; rewrite seq_S, Rls_app, Rls_cons, Rls_nil2; fold (Bsum k).
    replace (S k + 1)%nat with (2 + k)%nat by lia.
    pose proof (majorant_step (2 + k)%nat ltac:(lia)) as mstep.
    replace (2 + k - 1)%nat with (k + 1)%nat in mstep by lia.
    lra.
Qed.

Theorem Bsum_bound : forall k, Bsum k <= 2.
Proof.
  intro k; eapply Rle_trans; [ apply Bsum_tele | ].
  assert (HG1 : Gfun 1 = 2)
    by (unfold Gfun; rewrite ln_1; unfold Rdiv; rewrite Rinv_1; ring).
  assert (HGk : 0 <= Gfun (INR (k + 1))).
  { assert (0 < INR (k + 1)) by (apply lt_0_INR; lia).
    assert (0 <= ln (INR (k + 1)))
      by (rewrite <- ln_1; apply ln_le; [ lra | apply (le_INR 1); lia ]).
    unfold Gfun, Rdiv; apply Rmult_le_pos; [ lra | left; apply Rinv_0_lt_compat; lra ]. }
  lra.
Qed.

(* the uniform bound on the Euler-Maclaurin defect sum *)
Theorem bdefect_sum_bound : forall y, Rls (seq 2 y) (fun m => Rabs (bdefect m)) <= 32.
Proof.
  intro y.
  eapply Rle_trans with
    (Rls (seq 2 y) (fun m => 16 * (ln (INR m) + 1) / (INR m * INR m))).
  - apply Rls_le; intros m Hm; apply in_seq in Hm; apply b_bound; lia.
  - rewrite (Rls_ext _ (fun m => 16 * (ln (INR m) + 1) / (INR m * INR m))
              (fun m => 16 * phi (INR m)) (seq 2 y))
      by (intros m Hm; apply in_seq in Hm; unfold phi; field; apply not_0_INR; lia).
    rewrite <- (Rls_scal _ 16 (fun m => phi (INR m)) (seq 2 y)).
    change (Rls (seq 2 y) (fun m => phi (INR m))) with (Bsum y).
    pose proof (Bsum_bound y); lra.
Qed.

Print Assumptions bdefect_sum_bound.

(* ================================================================= *)
(*  END MajorantSum.v  —  Sum_{m=2}^{k+1} phi(m) <= 2,                 *)
(*  Sum_{m=2}^{y} |b(m)| <= 32  (uniform, no limits).                 *)
(* ================================================================= *)
