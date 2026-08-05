(* ================================================================= *)
(*  StarInequality.v  —  the log^2 Selberg inequality (star).          *)
(*                                                                    *)
(*  Vrem(N) ln^2 N <= Sum_{k<=N} (Lam_2(k)/k) Vrem(N/k) + O(ln N),      *)
(*  obtained WITHOUT any degree-2 symmetry, by iterating the degree-1   *)
(*  inequality selberg_average and reindexing (selberg2_reindex); the   *)
(*  Lam*log terms cancel because (Lam*Lam) = Lam_2 - Lam*log.           *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia Arith List.
Require Import Chebyshev ChebyshevBound VonMangoldtGlobal RealMobius
        MobiusOverD SelbergEndgame SelbergAverage MertensVonMangoldt
        SelbergSymmetry SelbergIterate.
Import ListNotations.
Open Scope R_scope.

Lemma msum_Rls : forall m, msum m = Rls (seq 1 m) (fun d => Lam d / INR d).
Proof. reflexivity. Qed.

(* Engine step: iterate selberg_average at each floor(N/d) and sum. *)
Lemma selberg_iterate_bound : forall N, (1 <= N)%nat ->
  Rls (seq 1 N) (fun d => Lam d / INR d * (Vrem (N / d)%nat * ln (INR (N / d)%nat)))
  <= Rls (seq 1 N) (fun d => Lam d / INR d *
        Rls (seq 1 (N / d)%nat) (fun e => Lam e / INR e * Vrem (N / (d * e))%nat))
     + (88 + 3 * Kup + 1) * msum N.
Proof.
  intros N HN.
  replace ((88 + 3 * Kup + 1) * msum N)
    with (Rls (seq 1 N) (fun d => (88 + 3 * Kup + 1) * (Lam d / INR d)))
    by (rewrite msum_Rls, Rls_scal; reflexivity).
  rewrite <- Rls_add.
  apply Rls_le; intros d Hd; apply in_seq in Hd.
  assert (Hq1 : (1 <= N / d)%nat)
    by (pose proof (Nat.Div0.div_mod N d);
        pose proof (Nat.mod_upper_bound N d ltac:(lia)); nia).
  assert (Hdd : 0 <= Lam d / INR d)
    by (apply Rmult_le_pos; [ apply Lam_nonneg | left; apply Rinv_0_lt_compat; apply lt_0_INR; lia ]).
  replace (Lam d / INR d *
             Rls (seq 1 (N / d)%nat) (fun e => Lam e / INR e * Vrem (N / (d * e))%nat)
           + (88 + 3 * Kup + 1) * (Lam d / INR d))
    with (Lam d / INR d *
             (Rls (seq 1 (N / d)%nat) (fun e => Lam e / INR e * Vrem (N / (d * e))%nat)
              + (88 + 3 * Kup + 1))) by ring.
  apply Rmult_le_compat_l; [ exact Hdd | ].
  eapply Rle_trans; [ apply (selberg_average (N / d)%nat Hq1) | ].
  apply Rplus_le_compat_r, Req_le, Rls_ext.
  intros e He; apply in_seq in He; rewrite Nat.div_div by lia; reflexivity.
Qed.

Lemma Rls_minus' : forall (l : list nat) (f g : nat -> R),
  Rls l (fun x => f x - g x) = Rls l f - Rls l g.
Proof.
  induction l as [|a l IH]; intros f g; [ rewrite !Rls_nil2; ring | ].
  rewrite !Rls_cons, IH; ring.
Qed.

(* Reindex + Lam_2 substitution: the double sum = the Lam_2 sum minus the
   Lam*log sum (which will cancel against the log-gap expansion). *)
Lemma star_reindex : forall N, (1 <= N)%nat ->
  Rls (seq 1 N) (fun d => Lam d / INR d *
      Rls (seq 1 (N / d)%nat) (fun e => Lam e / INR e * Vrem (N / (d * e))%nat))
  = Rls (seq 1 N) (fun n => Lam2 n / INR n * Vrem (N / n)%nat)
    - Rls (seq 1 N) (fun n => Lam n * ln (INR n) / INR n * Vrem (N / n)%nat).
Proof.
  intros N HN.
  rewrite (selberg2_reindex N Vrem), <- Rls_minus'.
  apply Rls_ext; intros n Hn; apply in_seq in Hn.
  assert (Hconv : Rls (divisors n) (fun d => Lam d * Lam (n / d)%nat)
                  = Lam2 n - Lam n * ln (INR n)) by (unfold Lam2; ring).
  rewrite Hconv; field; apply not_0_INR; lia.
Qed.

(* The per-term log gap: |ln(floor(N/d)) - (ln N - ln d)| <= ln 2. *)
Lemma log_floor_diff : forall N d, (1 <= d)%nat -> (d <= N)%nat ->
  Rabs (ln (INR (N / d)%nat) - (ln (INR N) - ln (INR d))) <= ln 2.
Proof.
  intros N d Hd1 HdN.
  assert (Hd0 : 0 < INR d) by (apply lt_0_INR; lia).
  assert (HN0 : 0 < INR N) by (apply lt_0_INR; lia).
  assert (Hl2p : 0 < ln 2) by (rewrite <- ln_1; apply ln_increasing; lra).
  set (m := (N / d)%nat).
  assert (Hm1 : (1 <= m)%nat)
    by (unfold m; pose proof (Nat.Div0.div_mod N d);
        pose proof (Nat.mod_upper_bound N d ltac:(lia)); nia).
  assert (Hm0 : 0 < INR m) by (apply lt_0_INR; lia).
  assert (Hlndiv : ln (INR N) - ln (INR d) = ln (INR N / INR d)).
  { unfold Rdiv; rewrite (ln_mult (INR N) (/ INR d) HN0 (Rinv_0_lt_compat _ Hd0)),
      (ln_Rinv (INR d) Hd0); ring. }
  rewrite Hlndiv.
  assert (Hupper : INR m <= INR N / INR d).
  { apply Rmult_le_reg_r with (INR d); [ exact Hd0 | ].
    replace (INR N / INR d * INR d) with (INR N) by (field; lra).
    rewrite <- mult_INR; apply le_INR; unfold m; pose proof (Nat.Div0.div_mod N d); nia. }
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
  apply Rabs_le; split; lra.
Qed.

Print Assumptions selberg_iterate_bound.

(* ================================================================= *)
(*  END StarInequality.v (parts 1-3: engine + reindex + log-gap)      *)
(* ================================================================= *)
