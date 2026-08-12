(* ================================================================= *)
(*  MertensPrime.v                                                    *)
(*                                                                    *)
(*  MERTENS' FIRST THEOREM FOR PRIMES (the sum over primes proper),   *)
(*  bridged from the von Mangoldt Mertens sum.                        *)
(*                                                                    *)
(*  The existing MertensVonMangoldt.mertens_lam gives                  *)
(*      | sum_{d<=N} Lam(d)/d  -  ln N |  <=  Kup.                     *)
(*  Splitting Lam over d = p^k, the prime terms (k=1) form            *)
(*      mprime N = sum_{p<=N} (ln p)/p,                               *)
(*  and the remainder is the higher-prime-power tail                  *)
(*      ppTail N = sum_{p^k<=N, k>=2} (ln p)/p^k   >= 0.               *)
(*                                                                    *)
(*  PROVED unconditionally (Qed):                                     *)
(*    - tterm_le_Lam   : (ln p)[p prime] <= Lam d   (termwise)        *)
(*    - mprime_le_msum : mprime N <= msum N                           *)
(*    - mprime_upper   : mprime N <= ln N + Kup      (upper half)     *)
(*    - ppTail_nonneg  : 0 <= ppTail N                                *)
(*    - mertens_prime_of_tail : IF the higher-prime-power tail is      *)
(*        bounded, THEN | mprime N - ln N | <= Kup + C                 *)
(*        (Mertens' first theorem for primes).                         *)
(*                                                                    *)
(*  DEFERRED (stated, not proved):                                    *)
(*    - HigherPPTailBounded : the convergent-series bound on ppTail    *)
(*      (the one genuine analytic step of the split -- a geometric     *)
(*      per-prime tail summed against a p-series);                     *)
(*    - MertensSecond : sum_{p<=N} 1/p = ln ln N + M + o(1), obtained  *)
(*      from mprime = ln N + O(1) by Abel summation.  Target only.     *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia Arith List.
Require Import ChebyshevBound Chebyshev VonMangoldtGlobal Ell2Primes
        PrimePowerReindex ChebyshevPrime MertensVonMangoldt.
Import ListNotations.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  The prime-restricted Mertens sum  mprime N = sum_{p<=N} (ln p)/p  *)
(* ----------------------------------------------------------------- *)

Definition mprime (N : nat) : R := Rsum (fun d => tterm d / INR d) 1 N.

(* Termwise: the prime part is dominated by the full von Mangoldt term.*)
Lemma tterm_le_Lam : forall d, tterm d <= Lam d.
Proof.
  intro d; unfold tterm; destruct (primeb d) eqn:E.
  - apply primeb_nprime in E; rewrite (Lam_prime d E); apply Rle_refl.
  - apply Lam_nonneg.
Qed.

Lemma mprime_le_msum : forall N, mprime N <= msum N.
Proof.
  intro N; unfold mprime, msum. apply Rsum_le. intros d Hd; apply in_seq in Hd.
  unfold Rdiv. apply Rmult_le_compat_r.
  - apply Rlt_le, Rinv_0_lt_compat, lt_0_INR; lia.
  - apply tterm_le_Lam.
Qed.

(* Upper half of Mertens 1 for primes: sum_{p<=N}(ln p)/p <= ln N + Kup *)
Lemma mprime_upper : forall N, (1 <= N)%nat -> mprime N <= ln (INR N) + Kup.
Proof.
  intros N HN. pose proof (mertens_lam N HN) as Hm.
  pose proof (Rle_abs (msum N - ln (INR N))) as Hu.
  pose proof (mprime_le_msum N) as Hle. lra.
Qed.

(* ----------------------------------------------------------------- *)
(*  The higher-prime-power tail, and the conditional lower bound     *)
(* ----------------------------------------------------------------- *)

Definition ppTail (N : nat) : R := msum N - mprime N.

Lemma ppTail_nonneg : forall N, 0 <= ppTail N.
Proof. intro N; unfold ppTail; pose proof (mprime_le_msum N); lra. Qed.

(* The one deferred analytic input: the weighted higher-prime-power   *)
(* tail is bounded uniformly in N (a convergent series).              *)
Definition HigherPPTailBounded : Prop :=
  exists C, forall N, (1 <= N)%nat -> ppTail N <= C.

(* Reduction: a bounded tail yields Mertens' first theorem for primes. *)
Theorem mertens_prime_of_tail :
  HigherPPTailBounded ->
  exists C, forall N, (1 <= N)%nat -> Rabs (mprime N - ln (INR N)) <= C.
Proof.
  intros [C HC]. exists (Kup + C). intros N HN.
  pose proof (mertens_lam N HN) as Hm.
  pose proof (Rle_abs (msum N - ln (INR N))) as Hu.
  pose proof (Rle_abs (- (msum N - ln (INR N)))) as Hl. rewrite Rabs_Ropp in Hl.
  pose proof (HC N HN) as Ht. unfold ppTail in Ht.
  pose proof (mprime_le_msum N) as Hmp.
  apply Rabs_le. split; lra.
Qed.

(* ----------------------------------------------------------------- *)
(*  Mertens' second theorem, STATED as the next target               *)
(* ----------------------------------------------------------------- *)

(* sum_{p<=N} 1/p  (iterm p = 1 for primes, else 0)                    *)
Definition primeRecip (N : nat) : R := Rsum (fun d => iterm d / INR d) 1 N.

(* sum_{p<=N} 1/p = ln ln N + M + o(1); M the Meissel-Mertens constant. *)
(* Obtained from mprime = ln N + O(1) by Abel (partial) summation with  *)
(* weight 1/ln.  Target only -- not asserted true here.                *)
Definition MertensSecond : Prop :=
  exists M : R, Un_cv (fun N => primeRecip N - ln (ln (INR N))) M.
