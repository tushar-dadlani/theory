(* ================================================================= *)
(*  SelbergIterate.v  —  the iterated-Selberg double-sum reindex.      *)
(*                                                                    *)
(*  The heart of the log^2 Selberg inequality (star).  Iterating the    *)
(*  degree-1 inequality once produces a double sum over d,e; reindexed  *)
(*  by k = d*e (hyperbola_swap) it becomes a single sum with the         *)
(*  self-convolution (Lam*Lam)(k) = Sum_{d|k} Lam d Lam(k/d):           *)
(*                                                                    *)
(*    selberg2_reindex : forall f,                                     *)
(*      Sum_{d<=N} (Lam d/d) Sum_{e<=N/d} (Lam e/e) f(N/(d e))          *)
(*      = Sum_{k<=N} ( (Lam*Lam)(k) / k ) f(N/k).                       *)
(*                                                                    *)
(*  Since (Lam*Lam)(k) = Lam_2(k) - Lam(k) ln k (the Lam_2 definition),  *)
(*  the log-weighted terms in the (star) derivation cancel exactly, so   *)
(*  (star) follows from selberg_average + Mertens WITHOUT any degree-2   *)
(*  symmetry formula.  Axiom-clean.                                     *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia Arith List.
Require Import Chebyshev ChebyshevBound VonMangoldtGlobal RealMobius
        MobiusOverD SelbergSum.
Import ListNotations.
Open Scope R_scope.

Lemma Rls_scal_r : forall (l : list nat) (g : nat -> R) (c : R),
  Rls l (fun x => g x * c) = Rls l g * c.
Proof.
  induction l as [|a l IH]; intros g c; [ rewrite !Rls_nil2; ring | ].
  rewrite !Rls_cons, IH; ring.
Qed.

Theorem selberg2_reindex : forall N (f : nat -> R),
  Rls (seq 1 N)
    (fun d => Lam d / INR d *
       Rls (seq 1 (N / d)%nat) (fun e => Lam e / INR e * f (N / (d * e))%nat))
  = Rls (seq 1 N)
    (fun n => Rls (divisors n) (fun d => Lam d * Lam (n / d)%nat) / INR n * f (N / n)%nat).
Proof.
  intros N f.
  transitivity (Rls (seq 1 N)
    (fun d => Rls (seq 1 (N / d)%nat)
       (fun e => Lam d / INR d * (Lam e / INR e) * f (N / (d * e))%nat))).
  { apply Rls_ext; intros d _; rewrite Rls_scal; apply Rls_ext; intros e _; ring. }
  rewrite <- (hyperbola_swap
    (fun d e => Lam d / INR d * (Lam e / INR e) * f (N / (d * e))%nat) N).
  apply Rls_ext; intros n Hn; apply in_seq in Hn; cbn beta.
  transitivity (Rls (divisors n)
    (fun d => Lam d * Lam (n / d)%nat * (/ INR n * f (N / n)%nat))).
  { apply Rls_ext; intros d Hd; apply in_divisors in Hd; destruct Hd as [[Hd1 Hdn] [k Hk]].
    assert (Hnd : (n / d = k)%nat) by (rewrite Hk, Nat.div_mul; lia).
    assert (Hprod : (d * (n / d) = n)%nat) by (rewrite Hnd, Hk; ring).
    assert (HINR : INR n = INR d * INR (n / d)%nat)
      by (rewrite <- mult_INR, Hprod; reflexivity).
    assert (Hd0 : INR d <> 0) by (apply not_0_INR; lia).
    assert (Hnd0 : INR (n / d)%nat <> 0) by (apply not_0_INR; rewrite Hnd; lia).
    assert (Hp0 : INR d * INR (n / d)%nat <> 0) by (rewrite <- HINR; apply not_0_INR; lia).
    rewrite Hprod, HINR; field; repeat split; assumption. }
  rewrite Rls_scal_r; unfold Rdiv; rewrite Rmult_assoc; reflexivity.
Qed.

Print Assumptions selberg2_reindex.

(* ================================================================= *)
(*  END SelbergIterate.v                                              *)
(* ================================================================= *)
