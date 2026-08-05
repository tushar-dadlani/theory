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

Print Assumptions selberg_iterate_bound.

(* ================================================================= *)
(*  END StarInequality.v (part 1: the engine step)                    *)
(* ================================================================= *)
