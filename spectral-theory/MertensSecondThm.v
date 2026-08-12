(* ================================================================= *)
(*  MertensSecondThm.v                                                *)
(*                                                                    *)
(*  MERTENS' SECOND THEOREM (qualitative):                            *)
(*     sum_{p<=N} 1/p  =  ln ln N + O(1).                             *)
(*                                                                    *)
(*  Abel summation of mprime = sum_{p<=N}(ln p)/p (= ln N + O(1),     *)
(*  MertensTailBound.mertens_first_prime) against the weight 1/ln,    *)
(*  with the ln ln N produced by the iterated-log estimate            *)
(*  (MertensSecond.iterated_log_bracket).                             *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia Arith List.
Require Import ChebyshevBound ChebyshevPrime VonMangoldtGlobal PrimePowerReindex
        MertensVonMangoldt MertensPrime MertensSecond HarmonicSum.
Open Scope R_scope.

(* the mprime summand bb and the weight ff = 1/ln *)
Definition bb (n : nat) : R := tterm n / INR n.
Definition ff (n : nat) : R := / ln (INR n).

Lemma mprime_eq : forall N, mprime N = Rsum bb 1 N.
Proof. reflexivity. Qed.

Lemma mprime_succ : forall N, mprime (S N) = mprime N + bb (S N).
Proof. intro N; rewrite !mprime_eq; apply Rsum_succ. Qed.

(* the 1/p summand equals bb * ff  (also at non-primes and at 1) *)
Lemma prterm_eq : forall n, (1 <= n)%nat -> iterm n / INR n = bb n * ff n.
Proof.
  intros n Hn. unfold bb, ff, iterm, tterm.
  destruct (primeb n) eqn:E.
  - apply primeb_nprime in E.
    assert (Hn2 : (2 <= n)%nat) by (destruct E; lia).
    assert (Hln : ln (INR n) <> 0).
    { apply Rgt_not_eq. rewrite <- ln_1. apply ln_increasing;
        [ lra | rewrite <- INR_1; apply lt_INR; lia ]. }
    field. split; [ exact Hln | apply not_0_INR; lia ].
  - unfold Rdiv. rewrite !Rmult_0_l. ring.
Qed.

Lemma primeRecip_via_bb : forall N, primeRecip N = Rsum (fun n => bb n * ff n) 1 N.
Proof.
  intro N; unfold primeRecip. apply Rsum_ext.
  intros i Hi; apply in_seq in Hi; apply prterm_eq; lia.
Qed.

(* ----------------------------------------------------------------- *)
(*  ABEL SUMMATION (exact identity)                                  *)
(*    sum_{n=1}^{S M} bb n * ff n                                     *)
(*      = mprime(S M) * ff(S M)                                       *)
(*        - sum_{n=1}^{M} mprime n * (ff (S n) - ff n).               *)
(* ----------------------------------------------------------------- *)

Lemma abel_id : forall M,
  Rsum (fun n => bb n * ff n) 1 (S M)
  = mprime (S M) * ff (S M)
    - Rsum (fun n => mprime n * (ff (S n) - ff n)) 1 M.
Proof.
  induction M as [|M IH].
  - assert (Hm1 : mprime 1 = bb 1).
    { rewrite mprime_eq; unfold Rsum; cbn [seq map fold_right]; ring. }
    change (S 0) with 1%nat. rewrite Hm1.
    unfold Rsum; cbn [seq map fold_right]; ring.
  - rewrite (Rsum_succ (fun n => bb n * ff n) (S M)), IH.
    rewrite (Rsum_succ (fun n => mprime n * (ff (S n) - ff n)) M).
    rewrite (mprime_succ (S M)). ring.
Qed.

(* the exact identity on primeRecip *)
Theorem primeRecip_abel : forall M,
  primeRecip (S M)
  = mprime (S M) * ff (S M)
    - Rsum (fun n => mprime n * (ff (S n) - ff n)) 1 M.
Proof. intro M; rewrite primeRecip_via_bb; apply abel_id. Qed.
