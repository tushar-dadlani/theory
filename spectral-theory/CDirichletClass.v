(* ================================================================= *)
(*  CDirichletClass.v  --  divergence of the weighted class sum       *)
(*  forces INFINITELY MANY PRIMES in the class.                       *)
(*                                                                    *)
(*    (forall M, the sum sum_{n = r mod p, n <= N} Lambda(n) n^{-sig} *)
(*     eventually exceeds M)                                          *)
(*      ==>  forall B, exists a prime q > B with q = r mod p          *)
(*                                                                    *)
(*  This is the last step of Dirichlet's theorem, and it is where the *)
(*  prime-power correction earns its place: without it the divergence *)
(*  would only give infinitely many prime POWERS in the class, and     *)
(*  that is strictly weaker (for a fixed p the powers p^k cycle        *)
(*  through residues, so one prime can supply infinitely many prime    *)
(*  powers in a class).                                               *)
(*                                                                    *)
(*  The argument is a contradiction with NO analysis in it.  If every  *)
(*  prime in the class were <= B then, splitting Lambda over the class *)
(*  into its prime part and its rest,                                  *)
(*     prime part  <= sum_{k <= B} Lambda(k+1)          (a constant),  *)
(*     the rest    <= Kpp                (CPPowTail.ppow_tail_bound),  *)
(*  so the class sum would be bounded by CB + Kpp for EVERY sigma and  *)
(*  every N.  Instantiating the divergence hypothesis at sigma = 1 and *)
(*  M = CB + Kpp + 1 contradicts that -- sigma near 1 is not even      *)
(*  needed here, only sigma = 1.                                       *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia Arith List ZArith Znumtheory
     Classical_Prop.
Require Import VonMangoldtGlobal Ell2Primes Chebyshev ChebyshevPrime
        PrimePowerReindex CPPowTail CPhiZetaLower CLPhi0Lower CZetaTerm2 CLWeightAnti.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  Part A -- generic sum lemmas.                                      *)
(* ----------------------------------------------------------------- *)

Lemma sum_stab : forall f M N, (M <= N)%nat ->
  (forall k, (M < k)%nat -> f k = 0) -> sum_f_R0 f N = sum_f_R0 f M.
Proof.
  intros f M N HMN H. induction N as [| N IH].
  - replace M with 0%nat by lia. reflexivity.
  - destruct (Nat.eq_dec M (S N)) as [E | E]; [ rewrite E; reflexivity | ].
    rewrite tech5, (H (S N)) by lia. rewrite IH by lia. ring.
Qed.

Lemma sum_mono : forall f M N, (M <= N)%nat -> (forall k, 0 <= f k) ->
  sum_f_R0 f M <= sum_f_R0 f N.
Proof.
  intros f M N HMN H. induction N as [| N IH].
  - replace M with 0%nat by lia. apply Rle_refl.
  - destruct (Nat.eq_dec M (S N)) as [E | E]; [ rewrite E; apply Rle_refl | ].
    rewrite tech5. pose proof (H (S N)). pose proof (IH ltac:(lia)). lra.
Qed.

(* ----------------------------------------------------------------- *)
(*  Part B -- the class sum and its two parts.                         *)
(* ----------------------------------------------------------------- *)

Section Class.

Variable p m : nat.
Hypothesis Hp2 : (2 <= p)%nat.

Definition inclass (n : nat) : bool := ((n * m) mod p =? 1)%nat.

Definition Ares (sig : R) (k : nat) : R :=
  if inclass (S k) then Lam (S k) * Rpower (INR (S k)) (- sig) else 0.

Definition CB (B : nat) : R := sum_f_R0 (fun k => Lam (S k)) B.

Lemma CB_nonneg : forall B, 0 <= CB B.
Proof.
  intro B. unfold CB. induction B as [| B IH].
  - cbn [sum_f_R0]. apply Lam_nonneg.
  - rewrite tech5. pose proof (Lam_nonneg (S (S B))). lra.
Qed.

(* the small-prime part, at sigma = 1 *)
Definition smallp (B : nat) (k : nat) : R :=
  if (S k <=? B)%nat then Lam (S k) else 0.

Lemma smallp_nonneg : forall B k, 0 <= smallp B k.
Proof.
  intros B k. unfold smallp. destruct (S k <=? B)%nat;
    [ apply Lam_nonneg | apply Rle_refl ].
Qed.

Lemma smallp_bound : forall B N, sum_f_R0 (smallp B) N <= CB B.
Proof.
  intros B N.
  assert (Hstep : sum_f_R0 (smallp B) B <= CB B).
  { unfold CB. apply sum_Rle. intros k _. unfold smallp.
    destruct (S k <=? B)%nat; [ apply Rle_refl | apply Lam_nonneg ]. }
  destruct (le_lt_dec N B) as [Hle | Hgt].
  - eapply Rle_trans; [ | exact Hstep ].
    apply sum_mono; [ exact Hle | apply smallp_nonneg ].
  - rewrite (sum_stab (smallp B) B N ltac:(lia)); [ exact Hstep | ].
    intros k Hk. unfold smallp.
    replace (S k <=? B)%nat with false; [ reflexivity | ].
    symmetry. apply Nat.leb_gt. lia.
Qed.

(* ---- the split, under the assumption that all primes in the class are small *)

Lemma Ares_split : forall B k,
  (forall q, (B < q)%nat -> primeb q = true -> inclass q = false) ->
  Ares 1 k <= smallp B k + bpp (S k) * Rpower (INR (S k)) (- 1).
Proof.
  intros B k Hno.
  assert (Hx1 : 1 <= INR (S k)) by (rewrite <- INR_1; apply le_INR; lia).
  assert (HR : 0 < Rpower (INR (S k)) (- 1)) by (unfold Rpower; apply exp_pos).
  assert (HR1 : Rpower (INR (S k)) (- 1) <= 1).
  { rewrite (Rpower_neg1 (INR (S k))) by lra.
    rewrite <- Rinv_1. apply Rinv_le_contravar; lra. }
  assert (HL : 0 <= Lam (S k)) by apply Lam_nonneg.
  assert (HB : 0 <= bpp (S k)) by apply bpp_nonneg.
  unfold Ares. destruct (inclass (S k)) eqn:Ec; cbv iota.
  - destruct (primeb (S k)) eqn:Ep.
    + (* prime and in class, so <= B *)
      assert (Hle : (S k <= B)%nat).
      { destruct (le_lt_dec (S k) B) as [H | H]; [ exact H | ].
        exfalso. rewrite (Hno (S k) H Ep) in Ec. discriminate. }
      assert (Hsm : smallp B k = Lam (S k)).
      { unfold smallp. replace (S k <=? B)%nat with true
          by (symmetry; apply Nat.leb_le; exact Hle). reflexivity. }
      rewrite Hsm.
      assert (Hstep : Lam (S k) * Rpower (INR (S k)) (- 1) <= Lam (S k) * 1)
        by (apply Rmult_le_compat_l; [ exact HL | exact HR1 ]).
      assert (Hpos : 0 <= bpp (S k) * Rpower (INR (S k)) (- 1))
        by (apply Rmult_le_pos; [ exact HB | lra ]).
      apply Rle_trans with (Lam (S k) * 1); [ exact Hstep | ].
      rewrite Rmult_1_r. lra.
    + (* not prime : Lambda = bpp there *)
      assert (Hb : bpp (S k) = Lam (S k))
        by (unfold bpp, tterm; rewrite Ep; ring).
      rewrite Hb. pose proof (smallp_nonneg B k) as Hsn.
      apply Rle_trans with (0 + Lam (S k) * Rpower (INR (S k)) (- 1));
        [ rewrite Rplus_0_l; apply Rle_refl | ].
      apply Rplus_le_compat_r. exact Hsn.
  - pose proof (smallp_nonneg B k) as Hsn.
    assert (Hpos : 0 <= bpp (S k) * Rpower (INR (S k)) (- 1))
      by (apply Rmult_le_pos; [ exact HB | lra ]).
    apply Rplus_le_le_0_compat; [ exact Hsn | exact Hpos ].
Qed.

Theorem Ares_bounded : forall B N,
  (forall q, (B < q)%nat -> primeb q = true -> inclass q = false) ->
  sum_f_R0 (Ares 1) N <= CB B + Kpp.
Proof.
  intros B N Hno.
  eapply Rle_trans.
  - apply sum_Rle. intros k _. apply (Ares_split B k Hno).
  - assert (H11 : (1:R) <= 1) by apply Rle_refl.
    pose proof (smallp_bound B N) as Hs1.
    pose proof (ppow_tail_bound 1 N H11) as Hs2.
    assert (Hsp : sum_f_R0 (fun k => smallp B k
                     + bpp (S k) * Rpower (INR (S k)) (- 1)) N
                  = sum_f_R0 (smallp B) N
                    + sum_f_R0 (fun k => bpp (S k) * Rpower (INR (S k)) (- 1)) N).
    { rewrite <- sum_f_R0_plus. apply sum_eq. intros i _. reflexivity. }
    rewrite Hsp. apply Rplus_le_compat; [ exact Hs1 | exact Hs2 ].
Qed.

(* ---- THE conclusion ---- *)

Theorem class_has_large_prime :
  (forall M, exists N del, 0 < del /\
     forall sig, 1 <= sig -> sig <= 1 + del -> M <= sum_f_R0 (Ares sig) N) ->
  forall B, exists q, (B < q)%nat /\ primeb q = true /\ inclass q = true.
Proof.
  intros Hdiv B.
  apply NNPP. intro Hcon.
  assert (Hno : forall q, (B < q)%nat -> primeb q = true -> inclass q = false).
  { intros q Hq Hpq. destruct (inclass q) eqn:E; [ | reflexivity ].
    exfalso. apply Hcon. exists q. auto. }
  destruct (Hdiv (CB B + Kpp + 1)) as [N [del [Hdel HM]]].
  pose proof (HM 1 ltac:(lra) ltac:(lra)) as H1.
  pose proof (Ares_bounded B N Hno) as H2.
  lra.
Qed.

End Class.

Print Assumptions class_has_large_prime.

(* ================================================================= *)
(*  END CDirichletClass.v                                             *)
(* ================================================================= *)
