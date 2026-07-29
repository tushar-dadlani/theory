(* ================================================================= *)
(*  Ell2Primes.v  —  the PRIME interpretation of the von Mangoldt      *)
(*  operator's spectrum on ℓ².                                        *)
(*                                                                    *)
(*  The eigenvalues of D_Λ are the von Mangoldt values Λ(n).  Here we  *)
(*  read them off arithmetically:                                    *)
(*    • at a PRIME p:  Λ(p) = log p, so  D_Λ (e p) = (log p)·(e p),    *)
(*      with STRICTLY POSITIVE eigenvalue  (vm_prime_eigenvalue,       *)
(*      vm_diag_prime, vm_eigenvalue_pos);                           *)
(*    • the nonzero spectrum lives exactly on the prime powers:        *)
(*      Λ(n) ≠ 0  ⇒  n = p^k for a prime p                            *)
(*      (vm_spectrum_prime_power), and conversely Λ(p^k) = log p > 0   *)
(*      (vm_prime_pow_eigenvalue).                                    *)
(*  So the nonzero point spectrum of D_Λ is precisely {log p : p prime}.*)
(*                                                                    *)
(*  Axiom footprint: the von Mangoldt tree's standard set (classical-  *)
(*  Reals + functional extensionality + Classical_Prop.classic).      *)
(* ================================================================= *)

Require Import Ell2 Ell2Operator Ell2Basis Ell2Parseval Ell2VonMangoldt.
Require Import VonMangoldtGlobal.
From Stdlib Require Import Reals Lra Lia.
Open Scope R_scope.

(* Λ at a prime is log p *)
Lemma Lam_prime : forall p, nprime p -> Lam p = ln (INR p).
Proof.
  intros p Hp; rewrite <- (Nat.pow_1_r p) at 1; apply Lam_prime_pow; [ exact Hp | lia ].
Qed.

(* EIGENVECTOR at a prime:  D_Λ (e p) = (log p)·(e p) *)
Lemma vm_prime_eigenvalue : forall p, nprime p ->
  forall n, Dmul Lam (e p) n = (ln (INR p) * e p n)%R.
Proof. intros p Hp n; rewrite vm_eigen, (Lam_prime p Hp); reflexivity. Qed.

(* the diagonal matrix element at a prime is log p *)
Lemma vm_diag_prime : forall p, nprime p ->
  ip (Dmul Lam (e p)) (e p) (Ell2_vm_e p) (Ell2_e p) = ln (INR p).
Proof. intros p Hp; rewrite vm_diag, (Lam_prime p Hp); reflexivity. Qed.

(* prime eigenvalues are STRICTLY POSITIVE *)
Lemma vm_eigenvalue_pos : forall p, nprime p -> 0 < ln (INR p).
Proof.
  intros p [Hp2 _]; rewrite <- ln_1; apply ln_increasing;
    [ lra | rewrite <- INR_1; apply lt_INR; lia ].
Qed.

(* prime-power eigenvalue Λ(p^k) = log p > 0 *)
Lemma vm_prime_pow_eigenvalue : forall p k, nprime p -> (1 <= k)%nat ->
  Lam (p ^ k) = ln (INR p) /\ 0 < Lam (p ^ k).
Proof.
  intros p k Hp Hk; rewrite (Lam_prime_pow p k Hp Hk).
  split; [ reflexivity | apply vm_eigenvalue_pos; exact Hp ].
Qed.

(* NECESSITY: a nonzero eigenvalue forces a prime power *)
Lemma vm_spectrum_prime_power : forall n,
  Lam n <> 0 -> exists p k, nprime p /\ (1 <= k)%nat /\ n = (p ^ k)%nat.
Proof.
  intros n Hn.
  assert (Hn2 : (2 <= n)%nat).
  { destruct n as [| [| m]];
      [ exfalso; apply Hn; reflexivity | exfalso; apply Hn; apply Lam_1 | lia ]. }
  unfold Lam in Hn; destruct (is_pow n (spf n) n) eqn:E; [ | contradiction ].
  assert (Hp2 : (2 <= spf n)%nat) by (apply spf_ge2; exact Hn2).
  destruct (is_pow_true_pow n (spf n) n Hp2 E) as [k Hk].
  exists (spf n), k; split; [ | split ].
  - apply spf_nprime; exact Hn2.
  - destruct k; [ simpl in Hk; lia | lia ].
  - exact Hk.
Qed.

Print Assumptions vm_prime_eigenvalue.
Print Assumptions vm_spectrum_prime_power.

(* ================================================================= *)
(*  END Ell2Primes.v                                                 *)
(*  The nonzero point spectrum of the von Mangoldt operator D_Λ on ℓ² *)
(*  is exactly {log p : p prime}: each prime p contributes the        *)
(*  eigenvector e p with strictly-positive eigenvalue log p, and no    *)
(*  other n gives a nonzero eigenvalue unless it is a prime power.    *)
(* ================================================================= *)
