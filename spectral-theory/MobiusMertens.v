(* ================================================================= *)
(*  MobiusMertens.v  —  the Mobius /d convolution swap (Step 2d, iv).   *)
(*                                                                    *)
(*  With G_g(y) := Sum_{m<=y} g(m)/m, the hyperbola swap gives the       *)
(*  exact identity                                                      *)
(*      Sum_{d<=N} (mu(d)/d) G_g(floor(N/d))                            *)
(*         = Sum_{n<=N} (1/n) * Sum_{d|n} mu(d) g(n/d)                   *)
(*         = Sum_{n<=N} (mu*g)(n)/n.                                    *)
(*  This is the engine that evaluates any Mobius-weighted /d sum by      *)
(*  reducing it to a Dirichlet convolution mu*g:                        *)
(*    - g = 1   : mu*1 = [n=1],   so the sum is exactly 1               *)
(*                (Sum_{d<=N} (mu(d)/d) H(floor(N/d)) = 1);             *)
(*    - g = log : mu*log = Lam,   so the sum is Sum Lam(n)/n (Mertens).  *)
(*  Axiom-clean.                                                        *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia Arith List ZArith.
Require Import DirichletConv VonMangoldtGlobal RealMobius MuLog
        SelbergSymmetry SelbergSum HarmonicSum.
Import ListNotations.
Open Scope R_scope.

Definition Ginv (g : nat -> R) (y : nat) : R := Rls (seq 1 y) (fun m => g m / INR m).

(* the exact convolution swap *)
Theorem conv_swap : forall (g : nat -> R) N,
  Rls (seq 1 N) (fun d => IZR (mu d) / INR d * Ginv g (N / d)%nat)
  = Rls (seq 1 N)
      (fun n => / INR n * Rls (divisors n) (fun d => IZR (mu d) * g (n / d)%nat)).
Proof.
  intros g N.
  transitivity (Rls (seq 1 N) (fun d => Rls (seq 1 (N / d)%nat)
                  (fun m => IZR (mu d) * g m / (INR d * INR m)))).
  { apply Rls_ext; intros d _.
    unfold Ginv; rewrite Rls_scal.
    apply Rls_ext; intros m _.
    unfold Rdiv; rewrite Rinv_mult; ring. }
  rewrite <- (hyperbola_swap (fun d m => IZR (mu d) * g m / (INR d * INR m)) N).
  apply Rls_ext; intros n Hn; apply in_seq in Hn.
  rewrite Rls_scal.
  apply Rls_ext; intros d Hd.
  apply in_divisors in Hd; destruct Hd as [[Hd1 Hdn] [k Hk]].
  assert (Hnd : (n / d = k)%nat) by (rewrite Hk, Nat.div_mul; lia).
  assert (Hprod : (d * (n / d) = n)%nat) by (rewrite Hnd, Hk; ring).
  rewrite <- mult_INR, Hprod; unfold Rdiv; ring.
Qed.

Print Assumptions conv_swap.

(* g = 1 :  mu * 1 = [n=1],  so the whole sum is exactly 1 *)
Corollary mob_mertens_one : forall N, (1 <= N)%nat ->
  Rls (seq 1 N) (fun d => IZR (mu d) / INR d * Harm (N / d)%nat) = 1.
Proof.
  intros N HN.
  rewrite (Rls_ext _ _
             (fun d => IZR (mu d) / INR d * Ginv (fun _ => 1) (N / d)%nat) (seq 1 N)).
  2:{ intros d _; f_equal; unfold Harm, Ginv; apply Rls_ext; intros m _;
      unfold Rdiv; rewrite Rmult_1_l; reflexivity. }
  rewrite (conv_swap (fun _ => 1) N).
  rewrite (Rls_ext _ _ (fun n => if Nat.eqb n 1 then 1 else 0) (seq 1 N)).
  2:{ intros n Hn; apply in_seq in Hn.
      rewrite (Rls_ext _ (fun d => IZR (mu d) * 1) (fun d => IZR (mu d)) (divisors n))
        by (intros; ring).
      rewrite (mu_real_sum n ltac:(lia)).
      destruct (Nat.eqb_spec n 1) as [->|Hne];
        [ rewrite INR_1; field | ring ]. }
  apply Rls_sift0; [ apply seq_NoDup | apply in_seq; lia ].
Qed.

Print Assumptions mob_mertens_one.

(* ================================================================= *)
(*  END MobiusMertens.v                                               *)
(*  Sum_{d<=N} (mu(d)/d) G_g(floor(N/d)) = Sum_{n<=N} (mu*g)(n)/n;      *)
(*  instance g=1:  Sum_{d<=N} (mu(d)/d) H(floor(N/d)) = 1.             *)
(* ================================================================= *)
