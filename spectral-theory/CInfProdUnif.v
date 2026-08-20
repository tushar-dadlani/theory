(* ================================================================= *)
(*  CInfProdUnif.v  —  the infinite-product Cauchy tail bound with     *)
(*  the constants supplied as HYPOTHESES rather than read off the      *)
(*  limit.                                                             *)
(*                                                                    *)
(*    tail_bound_gen :  partial sums of dev f capped by TU,            *)
(*      the M-tail capped by tl                                        *)
(*        ==>  Cmod (Pprod f n - Pprod f M) <= exp TU * (exp tl - 1)   *)
(*             for every n >= M.                                       *)
(*                                                                    *)
(*  WHY.  CInfProd.tail_bound states the same estimate with T, the     *)
(*  EXACT limit of sum (dev f), in both slots.  For a family f = f_z    *)
(*  that is fatal: T and the partial sums both move with z, so the      *)
(*  bound is not uniform and cannot give locally uniform convergence.   *)
(*                                                                    *)
(*  But the proof only ever uses T twice -- through sum_dev_le_T, and   *)
(*  in the closing tail inequality.  Turning those two uses into        *)
(*  hypotheses costs nothing and makes the bound uniform in whatever    *)
(*  parameter f carries, provided TU and tl can be chosen free of it.   *)
(*                                                                    *)
(*  CInfProd.v is deliberately NOT modified: everything it exports      *)
(*  (Pprod_split, sumtail_eq, Pprod_mod_le, RPdev_le_exp,              *)
(*  Pprod_dev_bound) is reused as is, so the Gamma-Weierstrass chain    *)
(*  that depends on it stays untouched.  Axiom-clean.                  *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import ComplexField Cmodulus CSeries CInfProd.
Open Scope R_scope.

Lemma tail_bound_gen : forall (f : nat -> C) (TU tl : R) (M : nat),
  (forall N, sum_f_R0 (dev f) N <= TU) ->
  0 <= tl ->
  (forall k, sum_f_R0 (dev f) (S (M + k)) - sum_f_R0 (dev f) M <= tl) ->
  forall n, (M <= n)%nat ->
    Cmod (Cminus (Pprod f n) (Pprod f M)) <= exp TU * (exp tl - 1).
Proof.
  intros f TU tl M HTU Htl0 Htail n Hle.
  assert (Hpos : 0 <= exp tl - 1).
  { assert (1 <= exp tl) by (rewrite <- exp_0; apply exp_le; lra). lra. }
  destruct (Nat.eq_dec M n) as [Heq | Hne].
  - subst n. replace (Cminus (Pprod f M) (Pprod f M)) with C0 by ring.
    assert (H0 : Cmod C0 = 0) by (apply (proj2 (Cmod0 _)); reflexivity).
    rewrite H0. apply Rmult_le_pos; [ left; apply exp_pos | exact Hpos ].
  - assert (Hk : exists k, n = S (M + k)%nat) by (exists (n - M - 1)%nat; lia).
    destruct Hk as [k Hk]. subst n.
    rewrite Pprod_split.
    replace (Cminus (Cmul (Pprod f M) (Pprod (fun j => f (S (M + j))) k)) (Pprod f M))
       with (Cmul (Pprod f M) (Cminus (Pprod (fun j => f (S (M + j))) k) C1)) by ring.
    rewrite Cmod_mul.
    apply Rmult_le_compat.
    + apply Cmod_nonneg.
    + apply Cmod_nonneg.
    + eapply Rle_trans; [ apply Pprod_mod_le | ].
      eapply Rle_trans; [ apply (RPdev_le_exp (dev f) (dev_nonneg f) M) | ].
      apply exp_le. apply HTU.
    + eapply Rle_trans; [ apply (Pprod_dev_bound (fun j => f (S (M + j))) k) | ].
      apply Rplus_le_compat_r.
      eapply Rle_trans;
        [ apply (RPdev_le_exp (dev (fun j => f (S (M + j)))) (dev_nonneg _)) | ].
      apply exp_le.
      change (dev (fun j => f (S (M + j)))) with (fun j => dev f (S (M + j))).
      rewrite sumtail_eq. apply Htail.
Qed.

Print Assumptions tail_bound_gen.
