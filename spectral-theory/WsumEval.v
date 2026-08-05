(* ================================================================= *)
(*  WsumEval.v  —  the conv_swap main value (Step 2d, v3c/v4 core).     *)
(*                                                                    *)
(*  With g(m) = 2 ln m - 2, the Dirichlet convolution mu*g is           *)
(*      (mu*g)(n) = Sum_{d|n} mu(d)(2 ln(n/d) - 2) = 2 Lam(n) - 2[n=1]   *)
(*  (Lam_eq_mulog + mu_real_sum), so conv_swap gives                    *)
(*      Sum_{d<=N} (mu(d)/d) W(floor(N/d)) = Sum_{n<=N} (mu*g)(n)/n      *)
(*         = 2 Sum Lam(n)/n - 2 = 2 msum(N) - 2,                        *)
(*  W(y) = Ginv g y = Sum_{m<=y}(2 ln m - 2)/m.  With Mertens            *)
(*  |msum N - ln N| <= Kup this is  2 ln N + O(1)  -- the backbone of    *)
(*  P' = Sum (mu(d)/d) q(ln floor(N/d)) = 2 ln N + O(1).  Axiom-clean.   *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia Arith List ZArith.
Require Import DirichletConv VonMangoldtGlobal RealMobius MuLog
        SelbergSymmetry MobiusMertens MertensVonMangoldt ChebyshevBound.
Import ListNotations.
Open Scope R_scope.

Definition gfun (m : nat) : R := 2 * ln (INR m) - 2.

(* the convolution mu*g = 2 Lam - 2[.=1] *)
Lemma mu_conv_g : forall n, (1 <= n)%nat ->
  Rls (divisors n) (fun d => IZR (mu d) * gfun (n / d)%nat)
  = 2 * Lam n - 2 * (if Nat.eqb n 1 then 1 else 0).
Proof.
  intros n Hn; unfold gfun.
  rewrite (Rls_ext _ (fun d => IZR (mu d) * (2 * ln (INR (n / d)%nat) - 2))
             (fun d => 2 * (IZR (mu d) * ln (INR (n / d)%nat)) + (-2) * IZR (mu d))
             (divisors n)) by (intros; ring).
  rewrite Rls_add.
  rewrite <- (Rls_scal _ 2 (fun d => IZR (mu d) * ln (INR (n / d)%nat)) (divisors n)).
  rewrite <- (Rls_scal _ (-2) (fun d => IZR (mu d)) (divisors n)).
  rewrite <- (Lam_eq_mulog n Hn), (mu_real_sum n Hn).
  ring.
Qed.

Theorem Wsum_eval : forall N, (1 <= N)%nat ->
  Rls (seq 1 N) (fun d => IZR (mu d) / INR d * Ginv gfun (N / d)%nat)
  = 2 * msum N - 2.
Proof.
  intros N HN.
  rewrite (conv_swap gfun N).
  rewrite (Rls_ext _ _
             (fun n => / INR n * (2 * Lam n - 2 * (if Nat.eqb n 1 then 1 else 0)))
             (seq 1 N))
    by (intros n Hn; apply in_seq in Hn; rewrite (mu_conv_g n ltac:(lia)); reflexivity).
  rewrite (Rls_ext _ _
             (fun n => 2 * (Lam n / INR n)
                       + (-2) * (if Nat.eqb n 1 then / INR n else 0)) (seq 1 N))
    by (intros n Hn; apply in_seq in Hn;
        destruct (Nat.eqb n 1); field; apply not_0_INR; lia).
  rewrite Rls_add.
  rewrite <- (Rls_scal _ 2 (fun n => Lam n / INR n) (seq 1 N)).
  rewrite <- (Rls_scal _ (-2) (fun n => if Nat.eqb n 1 then / INR n else 0) (seq 1 N)).
  replace (Rls (seq 1 N) (fun n => Lam n / INR n)) with (msum N)
    by (unfold msum, Rsum, Rls; reflexivity).
  rewrite (Rls_ext _ (fun n => if Nat.eqb n 1 then / INR n else 0)
             (fun n => if Nat.eqb n 1 then 1 else 0) (seq 1 N)).
  2:{ intros n _; destruct (Nat.eqb_spec n 1) as [->|Hne];
      [ rewrite INR_1, Rinv_1; reflexivity | reflexivity ]. }
  rewrite (Rls_sift0 (seq 1 N) 1 1); [ ring | apply seq_NoDup | apply in_seq; lia ].
Qed.

(* ... hence 2 ln N + O(1), via Mertens *)
Theorem Wsum_bound : forall N, (1 <= N)%nat ->
  Rabs (Rls (seq 1 N) (fun d => IZR (mu d) / INR d * Ginv gfun (N / d)%nat)
        - 2 * ln (INR N)) <= 2 * Kup + 2.
Proof.
  intros N HN; rewrite (Wsum_eval N HN).
  pose proof (mertens_lam N HN) as Hm.
  pose proof (Rle_abs (msum N - ln (INR N))) as Ha.
  pose proof (Rle_abs (- (msum N - ln (INR N)))) as Hb; rewrite Rabs_Ropp in Hb.
  apply Rabs_le; split; lra.
Qed.

Print Assumptions Wsum_bound.

(* ================================================================= *)
(*  END WsumEval.v  —  Sum_{d<=N} (mu(d)/d) W(floor(N/d)) = 2 msum N - 2 *)
(*  = 2 ln N + O(1)   (|.| <= 2 Kup + 2 off 2 ln N).                    *)
(* ================================================================= *)
