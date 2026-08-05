(* ================================================================= *)
(*  PiUpperSplit.v  —  the counting bound for the sharp upper (Step 4b).*)
(*                                                                    *)
(*  Split pi(N) at a threshold M:  pi(N) = pi(M) + #{primes in (M,N]}.  *)
(*  If ln(INR n) >= L > 0 for all n in (M,N], then each prime p there    *)
(*  has 1 <= ln p / L, so                                               *)
(*      #{primes in (M,N]} <= (theta(N)-theta(M))/L <= theta(N)/L,       *)
(*  and pi(M) <= M, giving the deterministic split bound                *)
(*      pi(N) <= M + theta(N)/L   (pi_upper_split).                     *)
(*  No limits.  With M ~ N/(ln N)^2, L ~ ln N this yields the sharp      *)
(*  upper bound of PNT (assembled elsewhere).  Axiom-clean.            *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia Arith List.
Require Import Chebyshev ChebyshevBound PrimePowerReindex ChebyshevPrime.
Import ListNotations.
Open Scope R_scope.

Lemma pi_count_le_INR : forall M, pi_count M <= INR M.
Proof.
  intro M; rewrite pi_count_pin; apply le_INR; unfold pin.
  apply Nat.le_trans with (length (seq 1 M));
    [ apply filter_length_le | rewrite length_seq; apply Nat.le_refl ].
Qed.

Lemma pi_upper_split : forall N M L,
  (M <= N)%nat -> 0 < L ->
  (forall n, (M < n)%nat -> (n <= N)%nat -> L <= ln (INR n)) ->
  pi_count N <= INR M + theta N / L.
Proof.
  intros N M L HMN HL Hlb.
  rewrite pi_count_iterm.
  replace N with (M + (N - M))%nat at 1 by lia.
  rewrite Rsum_split.
  apply Rplus_le_compat.
  - change (Rsum iterm 1 M) with (pi_count M); apply pi_count_le_INR.
  - apply Rle_trans with (Rsum (fun n => tterm n / L) (1 + M) (N - M)).
    + apply Rsum_le; intros i Hi; apply in_seq in Hi.
      unfold iterm, tterm; destruct (primeb i) eqn:E.
      * apply Rmult_le_reg_r with L; [ exact HL | ].
        rewrite Rmult_1_l; unfold Rdiv; rewrite Rmult_assoc.
        rewrite Rinv_l by lra.
        rewrite Rmult_1_r; apply Hlb; lia.
      * unfold Rdiv; rewrite Rmult_0_l; apply Rle_refl.
    + rewrite (Rsum_ext (fun n => tterm n / L) (fun n => / L * tterm n) (1 + M) (N - M))
        by (intros; unfold Rdiv; ring).
      rewrite <- Rsum_scale.
      assert (Hsub : Rsum tterm (1 + M) (N - M) <= theta N).
      { unfold theta; replace N with (M + (N - M))%nat at 2 by lia; rewrite Rsum_split.
        assert (0 <= Rsum tterm 1 M) by (apply Rsum_nonneg; intros; apply tterm_nonneg); lra. }
      unfold Rdiv; rewrite (Rmult_comm (theta N)).
      apply Rmult_le_compat_l; [ left; apply Rinv_0_lt_compat; exact HL | exact Hsub ].
Qed.

Print Assumptions pi_upper_split.

(* ================================================================= *)
(*  END PiUpperSplit.v  —  pi(N) <= M + theta(N)/L.                     *)
(* ================================================================= *)
