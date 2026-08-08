(* ================================================================= *)
(*  CGeomCauchy.v  —  Milestone C, brick C2a-4b (completeness core):     *)
(*  a real sequence with geometrically-bounded increments converges,    *)
(*  with an explicit geometric rate.  This packages R-completeness for   *)
(*  the nested-triangle vertex sequences (applied to Re and Im).        *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Open Scope R_scope.

Lemma geom_cauchy_cv : forall (u : nat -> R) (M : R), 0 <= M ->
  (forall n, Rabs (u (S n) - u n) <= M * (/ 2) ^ n) ->
  { l : R | Un_cv u l /\ forall n, Rabs (u n - l) <= 2 * M * (/ 2) ^ n }.
Proof.
  intros u M HM Hincr.
  assert (Hpow : forall n, 0 <= (/ 2) ^ n) by (intro n; apply pow_le; lra).
  (* tight telescoping bound *)
  assert (Htele : forall n m, (n <= m)%nat ->
            Rabs (u m - u n) <= 2 * M * (/ 2) ^ n - 2 * M * (/ 2) ^ m).
  { intros n m Hnm; induction Hnm.
    - replace (u n - u n) with 0 by ring; rewrite Rabs_R0; lra.
    - apply Rle_trans with (Rabs (u (S m) - u m) + Rabs (u m - u n)).
      + replace (u (S m) - u n) with ((u (S m) - u m) + (u m - u n)) by ring;
          apply Rabs_triang.
      + apply Rle_trans with (M * (/ 2) ^ m + (2 * M * (/ 2) ^ n - 2 * M * (/ 2) ^ m));
          [ apply Rplus_le_compat; [ apply Hincr | exact IHHnm ] | ].
        assert (Hs : (/ 2) ^ (S m) = / 2 * (/ 2) ^ m) by (cbn [pow]; ring).
        rewrite Hs; nra. }
  (* Cauchy criterion *)
  assert (Hc : Cauchy_crit u).
  { intros eps Heps.
    destruct (pow_lt_1_zero (/ 2) ltac:(rewrite Rabs_pos_eq; lra)
               (eps / (2 * M + 1)) ltac:(apply Rdiv_lt_0_compat; lra)) as [N HN].
    assert (Hbound : forall p q, (p <= q)%nat -> (p >= N)%nat -> Rabs (u q - u p) < eps).
    { intros p q Hpq Hp.
      apply Rle_lt_trans with ((2 * M + 1) * (/ 2) ^ p).
      - pose proof (Htele p q Hpq); pose proof (Hpow q); pose proof (Hpow p); nra.
      - pose proof (HN p Hp) as Hp'; rewrite Rabs_pos_eq in Hp' by apply Hpow.
        replace eps with ((2 * M + 1) * (eps / (2 * M + 1))) by (field; lra).
        apply Rmult_lt_compat_l; [ lra | exact Hp' ]. }
    exists N; intros n m Hn Hm; unfold R_dist.
    destruct (Nat.le_ge_cases n m) as [Hnm | Hmn].
    - rewrite Rabs_minus_sym; apply Hbound; assumption.
    - apply Hbound; assumption. }
  destruct (R_complete u Hc) as [l Hl].
  exists l; split; [ exact Hl | ].
  intro n; apply Rnot_lt_le; intro Hcontra.
  set (eps := Rabs (u n - l) - 2 * M * (/ 2) ^ n).
  assert (Heps : 0 < eps) by (unfold eps; lra).
  destruct (Hl eps Heps) as [N HN2].
  set (m := Nat.max n N).
  assert (Hnm : (n <= m)%nat) by apply Nat.le_max_l.
  assert (HmN : (m >= N)%nat) by apply Nat.le_max_r.
  pose proof (HN2 m HmN) as Hm'; unfold R_dist in Hm'.
  pose proof (Htele n m Hnm) as Ht.
  assert (Htri : Rabs (u n - l) <= Rabs (u m - u n) + Rabs (u m - l)).
  { replace (u n - l) with (- (u m - u n) + (u m - l)) by ring.
    eapply Rle_trans; [ apply Rabs_triang | rewrite Rabs_Ropp; apply Rle_refl ]. }
  assert (H2Mm : 0 <= 2 * M * (/ 2) ^ m)
    by (apply Rmult_le_pos; [ lra | apply Hpow ]).
  unfold eps in *; lra.
Qed.

Print Assumptions geom_cauchy_cv.

(* ================================================================= *)
(*  END CGeomCauchy.v  —  geometric-rate completeness (C2a-4b).         *)
(* ================================================================= *)
