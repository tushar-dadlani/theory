(* ================================================================= *)
(*  DirichletPPow.v                                                  *)
(*                                                                    *)
(*  PRIME-POWER VALUES of μ, φ, τ, σ.  Since all four are             *)
(*  multiplicative, they are determined by their values on prime      *)
(*  powers; here are those values, computed within the convolution    *)
(*  ring.                                                             *)
(*                                                                    *)
(*  Key lemma (arith_ppow_split): for p prime and k ≥ 1, any f        *)
(*  satisfies  f(p^k) = (Σ_{d∣p^k} f) − (Σ_{d∣p^{k-1}} f),           *)
(*  because divisors(p^k) = {p^0,…,p^k} is divisors(p^{k-1}) with one  *)
(*  extra top element.  From it (using μ∗1=ε, φ∗1=id):                *)
(*     μ(p) = −1,   μ(p^k) = 0 (k≥2)                                  *)
(*     φ(p^k) = p^k − p^{k-1}                                         *)
(*     τ(p^k) = k+1,   σ(p^k) = Σ_{j=0}^k p^j                         *)
(*  AXIOM-FREE.                                                       *)
(* ================================================================= *)

From Stdlib Require Import ZArith Znumtheory Arith Lia List Permutation.
Import ListNotations.
Require Import HopfGroupTensor Totient DirichletConv DirichletMult DirichletDivisor JacobiRHS.
Open Scope Z_scope.

(* ================================================================= *)
(*  Sums over the divisors of a prime power                          *)
(* ================================================================= *)
Lemma ppow_pos : forall p k, prime (Z.of_nat p) -> (1 <= p ^ k)%nat.
Proof.
  intros p k Hp; assert (p <> 0)%nat by (pose proof (prime_ge_2 _ Hp); lia).
  pose proof (Nat.pow_nonzero p k H); lia.
Qed.

Lemma divisors_ppow_sum : forall p k f, prime (Z.of_nat p) ->
  sumf (divisors (p ^ k)) f = sumf (seq 0 (S k)) (fun j => f (p ^ j)%nat).
Proof.
  intros p k f Hp.
  rewrite (sumf_perm _ _ f (divisors_prime_pow p k Hp)), sumf_map; reflexivity.
Qed.

Lemma sumf_seq_last : forall k g, sumf (seq 0 (S k)) g = sumf (seq 0 k) g + g k.
Proof.
  intros k g; rewrite seq_S, Nat.add_0_l, sumf_app, sumf_cons'.
  change (sumf (@nil nat) g) with 0%Z; ring.
Qed.

Lemma arith_ppow_split : forall p k f, prime (Z.of_nat p) -> (1 <= k)%nat ->
  f (p ^ k)%nat = sumf (divisors (p ^ k)) f - sumf (divisors (p ^ (k - 1))) f.
Proof.
  intros p k f Hp Hk.
  rewrite (divisors_ppow_sum p k f Hp), (divisors_ppow_sum p (k - 1) f Hp).
  replace (S (k - 1))%nat with k by lia.
  rewrite (sumf_seq_last k (fun j => f (p ^ j)%nat)); cbn beta; ring.
Qed.

(* ================================================================= *)
(*  ε on prime powers                                                *)
(* ================================================================= *)
Lemma deps_ppow : forall p k, prime (Z.of_nat p) -> (1 <= k)%nat -> deps (p ^ k)%nat = 0.
Proof.
  intros p k Hp Hk; unfold deps.
  replace ((p ^ k)%nat =? 1)%nat with false; [ reflexivity | ].
  symmetry; apply Nat.eqb_neq.
  assert (2 <= p)%nat by (pose proof (prime_ge_2 _ Hp); lia).
  assert (1 < p ^ k)%nat by (apply Nat.pow_gt_1; lia). lia.
Qed.

(* ================================================================= *)
(*  μ on prime powers                                                *)
(* ================================================================= *)
Theorem mu_ppow : forall p k, prime (Z.of_nat p) -> (1 <= k)%nat ->
  mu (p ^ k)%nat = deps (p ^ k)%nat - deps (p ^ (k - 1))%nat.
Proof.
  intros p k Hp Hk.
  rewrite (arith_ppow_split p k mu Hp Hk),
          (Sigma_mu_div (p ^ k) (ppow_pos p k Hp)),
          (Sigma_mu_div (p ^ (k - 1)) (ppow_pos p (k - 1) Hp)); reflexivity.
Qed.

Corollary mu_p : forall p, prime (Z.of_nat p) -> mu p = -1.
Proof.
  intros p Hp; pose proof (mu_ppow p 1 Hp ltac:(lia)) as H.
  rewrite (deps_ppow p 1 Hp ltac:(lia)) in H; rewrite Nat.pow_1_r in H.
  replace (p ^ (1 - 1))%nat with 1%nat in H by reflexivity.
  change (deps 1%nat) with 1%Z in H; lia.
Qed.

Corollary mu_ppow_ge2 : forall p k, prime (Z.of_nat p) -> (2 <= k)%nat -> mu (p ^ k)%nat = 0.
Proof.
  intros p k Hp Hk.
  rewrite (mu_ppow p k Hp ltac:(lia)),
          (deps_ppow p k Hp ltac:(lia)), (deps_ppow p (k - 1) Hp ltac:(lia)); ring.
Qed.

(* ================================================================= *)
(*  φ on prime powers                                                *)
(* ================================================================= *)
Theorem phi_ppow : forall p k, prime (Z.of_nat p) -> (1 <= k)%nat ->
  dphi (p ^ k)%nat = Z.of_nat (p ^ k) - Z.of_nat (p ^ (k - 1)).
Proof.
  intros p k Hp Hk.
  assert (Hsum : forall m, (1 <= m)%nat -> sumf (divisors m) dphi = did m).
  { intros m Hm; rewrite <- (phi_done_eq_id m Hm), (dconv_as_div dphi done m Hm); unfold done.
    apply sumf_ext; intros d _; ring. }
  rewrite (arith_ppow_split p k dphi Hp Hk),
          (Hsum (p ^ k)%nat (ppow_pos p k Hp)), (Hsum (p ^ (k - 1))%nat (ppow_pos p (k - 1) Hp)).
  unfold did; reflexivity.
Qed.

Corollary phi_ppow_nat : forall p k, prime (Z.of_nat p) -> (1 <= k)%nat ->
  dphi (p ^ k)%nat = Z.of_nat (p ^ k - p ^ (k - 1)).
Proof.
  intros p k Hp Hk; rewrite (phi_ppow p k Hp Hk), Nat2Z.inj_sub; [ reflexivity | ].
  apply Nat.pow_le_mono_r; [ pose proof (prime_ge_2 _ Hp); lia | lia ].
Qed.

(* ================================================================= *)
(*  τ and σ on prime powers                                          *)
(* ================================================================= *)
Theorem tau_ppow : forall p k, prime (Z.of_nat p) -> dtau (p ^ k)%nat = Z.of_nat (S k).
Proof.
  intros p k Hp; rewrite (dtau_as_div (p ^ k) (ppow_pos p k Hp)).
  rewrite (Permutation_length (divisors_prime_pow p k Hp)), length_map, length_seq; reflexivity.
Qed.

Theorem sigma_ppow : forall p k, prime (Z.of_nat p) ->
  dsigma (p ^ k)%nat = sumf (seq 0 (S k)) (fun j => Z.of_nat (p ^ j)).
Proof.
  intros p k Hp; rewrite (dsigma_as_div (p ^ k) (ppow_pos p k Hp)).
  apply (divisors_ppow_sum p k (fun d => Z.of_nat d) Hp).
Qed.

Print Assumptions mu_p.
Print Assumptions mu_ppow_ge2.
Print Assumptions phi_ppow.
Print Assumptions tau_ppow.
Print Assumptions sigma_ppow.

(* ================================================================= *)
(*  END DirichletPPow.v                                              *)
(*  Prime-power values: μ(p)=−1, μ(p^k)=0 (k≥2), φ(p^k)=p^k−p^{k-1},  *)
(*  τ(p^k)=k+1, σ(p^k)=Σ_{j≤k} p^j.  Closed under the global context. *)
(* ================================================================= *)
