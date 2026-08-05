(* ================================================================= *)
(*  SmoothingLemma.v  —  Sum_{n<=N} Lam_2(n)/n = ln^2 N + O(ln N).      *)
(*                                                                    *)
(*  The "smoothing measure" for the Selberg log^2 average.  Writing     *)
(*  Lam_2 = Lam*log + Lam**Lam (its definition), the Lam*log piece and   *)
(*  the reindexed Lam**Lam piece share the sum Sum (Lam d/d) ln d, which  *)
(*  CANCELS -- so this needs no evaluation of Sum Lam(d)ln d/d (no        *)
(*  LogHarmonic).  Concretely:                                          *)
(*    - split Lam_2/n  (Rls_add);                                       *)
(*    - reindex Sum (1/n) Sum_{d|n} Lam d Lam(n/d) = Sum_d (Lam d/d)     *)
(*        msum(N/d)   (hyperbola_swap, mirroring conv_swap);            *)
(*    - msum(floor(N/d)) = ln N - ln d + O(1) per term                  *)
(*        (msum_log_diff: |.| <= Kup + ln 2, from mertens_lam and        *)
(*         floor(N/d) in ((N/d)/2, N/d]);                               *)
(*  giving  Sum Lam_2/n = ln N * msum N + O(ln N) = ln^2 N + O(ln N).    *)
(*  Axiom-clean.                                                         *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia Arith List.
Require Import Chebyshev ChebyshevBound VonMangoldtGlobal RealMobius
        MobiusOverD SelbergSymmetry SelbergSum MertensVonMangoldt.
Import ListNotations.
Open Scope R_scope.

Lemma Rls_scal_r : forall (l : list nat) (f : nat -> R) (c : R),
  Rls l (fun x => f x * c) = Rls l f * c.
Proof.
  induction l as [|a l IH]; intros f c; [ rewrite !Rls_nil2; ring | ].
  rewrite !Rls_cons, IH; ring.
Qed.

Lemma msum_Rls : forall m, msum m = Rls (seq 1 m) (fun d => Lam d / INR d).
Proof. reflexivity. Qed.

(* --------- the per-term estimate --------- *)
Lemma msum_log_diff : forall N d, (1 <= d)%nat -> (d <= N)%nat ->
  Rabs (msum (N / d)%nat - (ln (INR N) - ln (INR d))) <= Kup + ln 2.
Proof.
  intros N d Hd1 HdN.
  assert (Hd0 : 0 < INR d) by (apply lt_0_INR; lia).
  assert (HN0 : 0 < INR N) by (apply lt_0_INR; lia).
  set (m := (N / d)%nat).
  assert (Hm1 : (1 <= m)%nat)
    by (unfold m; pose proof (Nat.Div0.div_mod N d);
        pose proof (Nat.mod_upper_bound N d ltac:(lia)); nia).
  assert (Hm0 : 0 < INR m) by (apply lt_0_INR; lia).
  assert (Hlndiv : ln (INR N) - ln (INR d) = ln (INR N / INR d)).
  { unfold Rdiv; rewrite (ln_mult (INR N) (/ INR d) HN0 (Rinv_0_lt_compat _ Hd0)),
      (ln_Rinv (INR d) Hd0); ring. }
  rewrite Hlndiv.
  pose proof (mertens_lam m Hm1) as Hmert.
  assert (Hupper : INR m <= INR N / INR d).
  { apply Rmult_le_reg_r with (INR d); [ exact Hd0 | ].
    replace (INR N / INR d * INR d) with (INR N) by (field; lra).
    rewrite <- mult_INR; apply le_INR;
      unfold m; pose proof (Nat.Div0.div_mod N d); nia. }
  assert (Hlower : INR N / INR d < 2 * INR m).
  { apply Rmult_lt_reg_r with (INR d); [ exact Hd0 | ].
    replace (INR N / INR d * INR d) with (INR N) by (field; lra).
    replace (2 * INR m * INR d) with (INR (2 * m * d)) by (rewrite !mult_INR; simpl; ring).
    apply lt_INR; unfold m; pose proof (Nat.Div0.div_mod N d);
      pose proof (Nat.mod_upper_bound N d ltac:(lia)); nia. }
  assert (Hl1 : ln (INR m) <= ln (INR N / INR d)) by (apply ln_le; [ exact Hm0 | exact Hupper ]).
  assert (Hl2 : ln (INR N / INR d) <= ln (INR m) + ln 2).
  { apply Rle_trans with (ln (2 * INR m)).
    - apply ln_le; [ apply Rdiv_lt_0_compat; assumption | left; exact Hlower ].
    - rewrite (ln_mult 2 (INR m)) by lra; lra. }
  apply Rle_trans with
    (Rabs (msum m - ln (INR m)) + Rabs (ln (INR m) - ln (INR N / INR d))).
  - replace (msum m - ln (INR N / INR d))
      with ((msum m - ln (INR m)) + (ln (INR m) - ln (INR N / INR d))) by ring.
    apply Rabs_triang.
  - apply Rplus_le_compat; [ exact Hmert | ].
    rewrite Rabs_left1 by lra; lra.
Qed.

(* --------- split Lam_2/n --------- *)
Lemma lam2_over_n_split : forall N,
  Rls (seq 1 N) (fun n => Lam2 n / INR n)
  = Rls (seq 1 N) (fun n => Lam n * ln (INR n) / INR n)
    + Rls (seq 1 N) (fun n => / INR n * Rls (divisors n) (fun d => Lam d * Lam (n / d)%nat)).
Proof.
  intro N; rewrite <- Rls_add; apply Rls_ext; intros n _; unfold Lam2, Rdiv; ring.
Qed.

(* --------- reindex the Lam**Lam piece --------- *)
Lemma lamlam_over_n : forall N,
  Rls (seq 1 N) (fun n => / INR n * Rls (divisors n) (fun d => Lam d * Lam (n / d)%nat))
  = Rls (seq 1 N) (fun d => Lam d / INR d * msum (N / d)%nat).
Proof.
  intro N.
  transitivity (Rls (seq 1 N)
    (fun n => Rls (divisors n) (fun d => Lam d / INR d * (Lam (n / d)%nat / INR (n / d)%nat)))).
  { apply Rls_ext; intros n Hn; apply in_seq in Hn.
    rewrite Rls_scal; apply Rls_ext; intros d Hd.
    apply in_divisors in Hd; destruct Hd as [[Hd1 Hdn] [k Hk]].
    assert (Hnd : (n / d = k)%nat) by (rewrite Hk, Nat.div_mul; lia).
    assert (HINR : INR n = INR d * INR (n / d)%nat)
      by (rewrite <- mult_INR; f_equal; rewrite Hnd, Hk; ring).
    rewrite HINR; field; split; apply not_0_INR; [ rewrite Hnd | ]; lia. }
  rewrite (hyperbola_swap (fun d m => Lam d / INR d * (Lam m / INR m)) N).
  apply Rls_ext; intros d _.
  rewrite <- Rls_scal; reflexivity.
Qed.

(* --------- the smoothing bound --------- *)
Theorem lam2_over_n_bound : forall N, (1 <= N)%nat ->
  Rabs (Rls (seq 1 N) (fun n => Lam2 n / INR n) - ln (INR N) * ln (INR N))
  <= Kup * ln (INR N) + (Kup + ln 2) * (ln (INR N) + Kup).
Proof.
  intros N HN.
  assert (HN1 : 1 <= INR N) by (apply (le_INR 1); lia).
  assert (Hln0 : 0 <= ln (INR N)) by (rewrite <- ln_1; apply ln_le; lra).
  pose proof (mertens_lam N HN) as HmertN.
  set (errorterm := Rls (seq 1 N)
    (fun d => Lam d / INR d * (msum (N / d)%nat - (ln (INR N) - ln (INR d))))).
  (* main equation: Sum Lam_2/n = (Sum Lam d/d * ln N) + errorterm *)
  assert (Heq : Rls (seq 1 N) (fun n => Lam2 n / INR n)
              = Rls (seq 1 N) (fun d => Lam d / INR d * ln (INR N)) + errorterm).
  { unfold errorterm; rewrite lam2_over_n_split, lamlam_over_n, <- !Rls_add.
    apply Rls_ext; intros x Hx; apply in_seq in Hx; field; apply not_0_INR; lia. }
  rewrite Heq.
  assert (HP : Rls (seq 1 N) (fun d => Lam d / INR d * ln (INR N)) = ln (INR N) * msum N).
  { rewrite Rls_scal_r, msum_Rls; ring. }
  rewrite HP.
  (* bound the error sum *)
  assert (Herr : Rabs errorterm <= (Kup + ln 2) * msum N).
  { unfold errorterm; eapply Rle_trans; [ apply Rls_abs | ].
    eapply Rle_trans; [ apply Rls_le with (g := fun d => Lam d / INR d * (Kup + ln 2)) | ].
    - intros d Hd; apply in_seq in Hd.
      assert (Hdd : 0 <= Lam d / INR d)
        by (apply Rmult_le_pos; [ apply Lam_nonneg | left; apply Rinv_0_lt_compat; apply lt_0_INR; lia ]).
      rewrite Rabs_mult, (Rabs_right (Lam d / INR d)) by (apply Rle_ge; exact Hdd).
      apply Rmult_le_compat_l; [ exact Hdd | apply msum_log_diff; lia ].
    - rewrite Rls_scal_r, msum_Rls; apply Req_le; ring. }
  (* assemble *)
  replace (ln (INR N) * msum N + errorterm - ln (INR N) * ln (INR N))
    with ((ln (INR N) * (msum N - ln (INR N))) + errorterm) by ring.
  eapply Rle_trans; [ apply Rabs_triang | ].
  apply Rplus_le_compat.
  - rewrite Rabs_mult, (Rabs_right (ln (INR N))) by (apply Rle_ge; exact Hln0).
    rewrite (Rmult_comm Kup (ln (INR N)));
      apply Rmult_le_compat_l; [ exact Hln0 | exact HmertN ].
  - eapply Rle_trans; [ exact Herr | ].
    assert (Hl2p : 0 < ln 2) by (rewrite <- ln_1; apply ln_increasing; lra).
    apply Rmult_le_compat_l; [ unfold Kup; lra | ].
    apply Rle_trans with (ln (INR N) + Kup); [ | lra ].
    pose proof (Rle_abs (msum N - ln (INR N))); lra.
Qed.

Print Assumptions lam2_over_n_bound.

(* ================================================================= *)
(*  END SmoothingLemma.v  —  Sum Lam_2(n)/n = ln^2 N + O(ln N).         *)
(* ================================================================= *)
