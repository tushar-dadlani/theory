(* ================================================================= *)
(*  CHyperbolaSwap.v  —  Milestone A / B3b: the C-valued hyperbola swap. *)
(*                                                                    *)
(*  The order-swap over the hyperbola for a C-valued kernel:            *)
(*     Sum_{n<=N} Sum_{d|n} F d (n/d) = Sum_{d<=N} Sum_{m<=N/d} F d m    *)
(*  is derived from the R-valued SelbergSum.hyperbola_swap componentwise *)
(*  via the Re_Cls / Im_Cls bridge (this is exactly why B3a exists):     *)
(*  push Re (resp. Im) through the nested Cls to nested Rls, apply the   *)
(*  real swap, then reassemble with Ceq.  This maps the convolution      *)
(*  partial sum Sum_{n<=N} (a*b)(n) to the hyperbolic region double sum. *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia Arith List.
Require Import ComplexField CListSum RealMobius VonMangoldtGlobal SelbergSum.
Import ListNotations.
Open Scope R_scope.

(* ---- push Re / Im through a nested Cls into a nested Rls ---- *)
Lemma Re_Cls_double : forall N (h : nat -> list nat) (G : nat -> nat -> C),
  Re (Cls (seq 1 N) (fun n => Cls (h n) (fun d => G n d)))
  = Rls (seq 1 N) (fun n => Rls (h n) (fun d => Re (G n d))).
Proof.
  intros N h G; rewrite Re_Cls; apply Rls_ext; intros n _; rewrite Re_Cls; reflexivity.
Qed.

Lemma Im_Cls_double : forall N (h : nat -> list nat) (G : nat -> nat -> C),
  Im (Cls (seq 1 N) (fun n => Cls (h n) (fun d => G n d)))
  = Rls (seq 1 N) (fun n => Rls (h n) (fun d => Im (G n d))).
Proof.
  intros N h G; rewrite Im_Cls; apply Rls_ext; intros n _; rewrite Im_Cls; reflexivity.
Qed.

(* ---- the hyperbola swap, C-valued ---- *)
Theorem Chyperbola_swap : forall (F : nat -> nat -> C) N,
  Cls (seq 1 N) (fun n => Cls (divisors n) (fun d => F d (n / d)%nat))
  = Cls (seq 1 N) (fun d => Cls (seq 1 (N / d)%nat) (fun m => F d m)).
Proof.
  intros F N; apply Ceq.
  - rewrite (Re_Cls_double N (fun n => divisors n) (fun n d => F d (n / d)%nat)).
    rewrite (Re_Cls_double N (fun d => seq 1 (N / d)%nat) (fun d m => F d m)).
    apply (hyperbola_swap (fun d m => Re (F d m)) N).
  - rewrite (Im_Cls_double N (fun n => divisors n) (fun n d => F d (n / d)%nat)).
    rewrite (Im_Cls_double N (fun d => seq 1 (N / d)%nat) (fun d m => F d m)).
    apply (hyperbola_swap (fun d m => Im (F d m)) N).
Qed.

Print Assumptions Chyperbola_swap.

(* ================================================================= *)
(*  END CHyperbolaSwap.v  —  Sum_{d|n} = Sum_{d*m<=N}, C-valued.        *)
(* ================================================================= *)
