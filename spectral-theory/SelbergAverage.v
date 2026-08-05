(* ================================================================= *)
(*  SelbergAverage.v  —  RUNG 3a of the Erdos-Selberg limsup layer.     *)
(*                                                                    *)
(*  The "averaged Selberg inequality": normalise the Selberg           *)
(*  inequality by N to turn it into a SELF-REFERENTIAL average of the   *)
(*  normalised remainder                                               *)
(*      Vrem N := |Rem N| / N          (= |psi N - N| / N, in [0, Kup-1]) *)
(*                                                                    *)
(*  Dividing  selberg_Rabs  (|Rem N| ln N <= Sum Lam(d)|Rem(N/d)| + C N) *)
(*  by N and using  d * floor(N/d) <= N  (so Lam(d)/N <= Lam(d)/d after  *)
(*  reintroducing the scale N/d) gives                                  *)
(*                                                                    *)
(*    selberg_average :                                                *)
(*      Vrem N * ln N  <=  Sum_{d<=N} (Lam d / d) * Vrem (N/d)  +  C.    *)
(*                                                                    *)
(*  Since Sum_{d<=N} Lam(d)/d = ln N + O(1) (mertens_lam), the RHS is    *)
(*  (ln N)*(a Lam-weighted average of the values Vrem(N/d)) + O(1): the  *)
(*  self-referential bound the cancellation argument (Rung 3c) refines. *)
(*  Pure assembly from selberg_Rabs; axiom-clean.                       *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia Arith Lists.List.
Import ListNotations.
Require Import Chebyshev ChebyshevBound VonMangoldtGlobal RealMobius
        MobiusOverD SelbergEndgame ErdosSelberg.
Open Scope R_scope.

(* The normalised remainder. *)
Definition Vrem (N : nat) : R := Rabs (Rem N) / INR N.

Lemma Vrem_nonneg : forall N, 0 <= Vrem N.
Proof.
  intro N; unfold Vrem, Rdiv; apply Rmult_le_pos; [ apply Rabs_pos | ].
  destruct N as [| n].
  - replace (INR 0) with 0 by (simpl; ring); rewrite Rinv_0; apply Rle_refl.
  - left; apply Rinv_0_lt_compat; apply lt_0_INR; lia.
Qed.

Lemma Vrem_bound : forall N, (1 <= N)%nat -> Vrem N <= Kup - 1.
Proof.
  intros N HN; unfold Vrem.
  assert (HNpos : 0 < INR N) by (apply lt_0_INR; lia).
  apply Rmult_le_reg_r with (INR N); [ exact HNpos | ].
  unfold Rdiv; rewrite Rmult_assoc.
  rewrite Rinv_l by lra.
  rewrite Rmult_1_r; apply Rem_bound.
Qed.

(* ----------------------------------------------------------------- *)
(*  The averaged Selberg inequality.                                  *)
(* ----------------------------------------------------------------- *)

Theorem selberg_average : forall N, (1 <= N)%nat ->
  Vrem N * ln (INR N)
  <= Rls (seq 1 N) (fun d => Lam d / INR d * Vrem (N / d)%nat) + (88 + 3 * Kup + 1).
Proof.
  intros N HN.
  assert (HNpos : 0 < INR N) by (apply lt_0_INR; lia).
  assert (HNne : INR N <> 0) by lra.
  pose proof (selberg_Rabs N HN) as HS.
  assert (E1 : Vrem N * ln (INR N) = Rabs (Rem N) * ln (INR N) * / INR N)
    by (unfold Vrem; field; exact HNne).
  rewrite E1.
  apply Rle_trans with
    (/ INR N * (Rls (seq 1 N) (fun d => Lam d * Rabs (Rem (N / d)%nat))
                + (88 + 3 * Kup + 1) * INR N)).
  - rewrite (Rmult_comm (/ INR N)).
    apply Rmult_le_compat_r; [ left; apply Rinv_0_lt_compat; exact HNpos | exact HS ].
  - rewrite Rmult_plus_distr_l.
    replace (/ INR N * ((88 + 3 * Kup + 1) * INR N)) with (88 + 3 * Kup + 1)
      by (field; exact HNne).
    apply Rplus_le_compat_r.
    rewrite Rls_scal.
    apply Rls_le.
    intros d Hd; rewrite in_seq in Hd.
    assert (Hd1 : (1 <= d)%nat) by lia.
    assert (HdN : (d <= N)%nat) by lia.
    assert (Hdpos : 0 < INR d) by (apply lt_0_INR; lia).
    assert (Hq1 : (1 <= N / d)%nat).
    { pose proof (Nat.Div0.div_mod N d) as HM.
      pose proof (Nat.mod_upper_bound N d ltac:(lia)); nia. }
    assert (Hqpos : 0 < INR (N / d)) by (apply lt_0_INR; lia).
    assert (Hprod : INR d * INR (N / d)%nat <= INR N).
    { rewrite <- mult_INR; apply le_INR.
      pose proof (Nat.Div0.div_mod N d) as HM; lia. }
    assert (HA : 0 <= Lam d * Rabs (Rem (N / d)%nat))
      by (apply Rmult_le_pos; [ apply Lam_nonneg | apply Rabs_pos ]).
    unfold Vrem.
    replace (/ INR N * (Lam d * Rabs (Rem (N / d)%nat)))
      with (Lam d * Rabs (Rem (N / d)%nat) * / INR N) by ring.
    replace (Lam d / INR d * (Rabs (Rem (N / d)%nat) / INR (N / d)%nat))
      with (Lam d * Rabs (Rem (N / d)%nat) * / (INR d * INR (N / d)%nat))
      by (field; split; lra).
    apply Rmult_le_compat_l; [ exact HA | ].
    apply Rinv_le_contravar; [ apply Rmult_lt_0_compat; assumption | exact Hprod ].
Qed.

Print Assumptions selberg_average.

(* ================================================================= *)
(*  END SelbergAverage.v  —  RUNG 3a: the averaged Selberg inequality. *)
(* ================================================================= *)
