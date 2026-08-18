(* ================================================================= *)
(*  PrimorialDFTEuler.v  —  primorial DFT orthogonality tied into the   *)
(*  zeta Euler product.                                                 *)
(*                                                                    *)
(*  The DFT orthogonality of the N-th roots of unity is the finite-     *)
(*  Fourier form of DIVISIBILITY:                                       *)
(*                                                                    *)
(*    [N | n]  =  (1/N) . sum_{k<N} (w N)^{k n}                         *)
(*                                                                    *)
(*  (dft_indicator) — only the trivial additive character survives the  *)
(*  orthogonality sum.  Over one period the divisible residues have     *)
(*  density 1/p (period_divisible_sum: exactly the residue 0), so the   *)
(*  SIEVE KEEP-FRACTION at a prime p is 1 - 1/p, which is exactly the    *)
(*  RECIPROCAL of the s=1 Euler factor p/(p-1) = sum_j (1/p)^j          *)
(*  (keep_euler_inv + PrimeInfinities.prime_euler_factor).              *)
(*                                                                    *)
(*  Taking the primorial product of the per-prime keep-fractions gives  *)
(*    prod (1 - 1/p_i)  =  sieve_density k  =  1 / euler_prod k         *)
(*  (SieveDensity.sieve_counting_inverse), and for s>1 the un-sieved    *)
(*  Euler product prod 1/(1-p^{-s}) -> zeta(s)                          *)
(*  (EulerProductZetaS.euler_factor_s).                                 *)
(*                                                                    *)
(*  So: DFT orthogonality -> divisibility indicator -> sieved density   *)
(*  1/p -> keep-fraction 1-1/p = reciprocal of the Euler factor ->      *)
(*  primorial product = 1/euler_prod -> zeta's Euler product.           *)
(*                                                                    *)
(*  Axiom-clean (only the 4 standard classical-Reals axioms).           *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import ComplexField RootsOfUnity PrimeInfinities SieveDensity EulerProductZetaS.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  (w N)^n = 1  <->  N | n                                            *)
(* ----------------------------------------------------------------- *)

Lemma mod0_iff_div : forall N n, (0 < N)%nat -> (n mod N = 0 <-> Nat.divide N n)%nat.
Proof. intros N n _. apply Nat.Lcm0.mod_divide. Qed.

Lemma w_pow_div : forall N n, (0 < N)%nat -> Nat.divide N n -> Cpow (w N) n = C1.
Proof.
  intros N n HN [z Hz]. subst n.
  rewrite Nat.mul_comm, Cpow_mul, (w_pow_N N HN). apply Cpow_C1.
Qed.

Lemma w_pow_eq1_div : forall N n, (0 < N)%nat -> Cpow (w N) n = C1 -> Nat.divide N n.
Proof.
  intros N n HN H. assert (HN0 : N <> 0%nat) by lia.
  assert (Hcut : Cpow (w N) n = Cpow (w N) (n mod N)).
  { rewrite (Nat.div_mod n N HN0) at 1. rewrite Cpow_add.
    rewrite Cpow_mul, (w_pow_N N HN), Cpow_C1. ring. }
  rewrite Hcut in H.
  assert (Hr : (n mod N < N)%nat) by (apply Nat.mod_upper_bound; exact HN0).
  destruct (n mod N) as [| r'] eqn:Er.
  - apply mod0_iff_div; [ exact HN | exact Er ].
  - exfalso. assert (Hjr : (0 < S r' < N)%nat) by lia.
    exact (w_primitive N (S r') Hjr H).
Qed.

(* ----------------------------------------------------------------- *)
(*  DFT orthogonality = the divisibility indicator                    *)
(* ----------------------------------------------------------------- *)

Theorem dft_indicator : forall N n, (0 < N)%nat ->
  Csum (fun k => Cpow (w N) (k * n)) N
  = (if Nat.eqb (n mod N) 0 then RtoC (INR N) else C0).
Proof.
  intros N n HN.
  rewrite (Csum_ext (fun k => Cpow (w N) (k * n)) (fun k => Cpow (Cpow (w N) n) k) N).
  2:{ intro k. rewrite Nat.mul_comm, Cpow_mul. reflexivity. }
  rewrite (dft_orthogonality N n HN).
  destruct (Nat.eqb (n mod N) 0) eqn:E.
  - apply Nat.eqb_eq in E.
    destruct (Ceq_dec (Cpow (w N) n) C1) as [_ | Hne]; [ reflexivity | ].
    exfalso; apply Hne. apply w_pow_div; [ exact HN | apply mod0_iff_div; assumption ].
  - apply Nat.eqb_neq in E.
    destruct (Ceq_dec (Cpow (w N) n) C1) as [Heq | _]; [ | reflexivity ].
    exfalso; apply E. apply (proj2 (mod0_iff_div N n HN)).
    apply (w_pow_eq1_div N n HN Heq).
Qed.

(* ----------------------------------------------------------------- *)
(*  the sieved-out density over one period is 1/p (only residue 0)     *)
(* ----------------------------------------------------------------- *)

Lemma delta_period_sum : forall m,
  sum_f_R0 (fun n => if Nat.eqb n 0 then 1 else 0) m = 1.
Proof.
  induction m as [| m IH]; [ reflexivity | ].
  rewrite tech5, IH. change (if Nat.eqb (S m) 0 then 1 else 0) with 0. ring.
Qed.

(* the divisible residues in [0,p) sum (as an indicator) to 1: density 1/p *)
Theorem period_divisible_sum : forall p, (0 < p)%nat ->
  sum_f_R0 (fun n => if Nat.eqb (n mod p) 0 then 1 else 0) (pred p) = 1.
Proof.
  intros p Hp.
  rewrite (sum_eq (fun n => if Nat.eqb (n mod p) 0 then 1 else 0)
                  (fun n => if Nat.eqb n 0 then 1 else 0) (pred p)).
  - apply delta_period_sum.
  - intros i Hi. rewrite (Nat.mod_small i p) by lia. reflexivity.
Qed.

(* ----------------------------------------------------------------- *)
(*  keep-fraction 1 - 1/p = reciprocal of the s=1 Euler factor p/(p-1) *)
(* ----------------------------------------------------------------- *)

Definition keep (p : R) : R := 1 - / p.

Lemma keep_euler_inv : forall p, 2 <= p -> keep p * (p / (p - 1)) = 1.
Proof. intros p Hp. unfold keep. field. lra. Qed.

(* the keep-fraction is exactly the per-prime factor of the sieve density *)
Lemma keep_is_sieve_factor : forall (P : nat -> R) k,
  sieve_density P (S k) = sieve_density P k * keep (P k).
Proof. intros P k. reflexivity. Qed.

(* ----------------------------------------------------------------- *)
(*  Section Bridge : the nat prime enumeration Q, real primes INR(Q i) *)
(* ----------------------------------------------------------------- *)

Section Bridge.
Variable Q : nat -> nat.
Hypothesis HQ : forall i, (2 <= Q i)%nat.

Definition P (i : nat) : R := INR (Q i).

Lemma HP : forall i, 2 <= P i.
Proof.
  intro i. unfold P. replace 2 with (INR 2) by (simpl; ring).
  apply le_INR; apply HQ.
Qed.

Lemma Qpos : forall k, (0 < Q k)%nat.
Proof. intro k; pose proof (HQ k); lia. Qed.

(* ===== the whole tie, bundled ===== *)
Theorem primorial_dft_euler : forall s (Hs : 0 < s),
  (* 1. DFT orthogonality gives the divisibility indicator mod each prime *)
  (forall k n, Csum (fun j => Cpow (w (Q k)) (j * n)) (Q k)
             = if Nat.eqb (n mod Q k) 0 then RtoC (INR (Q k)) else C0)
  (* 2. the sieved-out residues have density 1/p (indicator sums to 1) *)
  /\ (forall k, sum_f_R0 (fun n => if Nat.eqb (n mod Q k) 0 then 1 else 0)
                         (pred (Q k)) = 1)
  (* 3. keep-fraction 1-1/p = reciprocal of the s=1 Euler factor p/(p-1) *)
  /\ (forall k, keep (P k) * (P k / (P k - 1)) = 1)
  (* 4. that Euler factor is the geometric sum sum_j (1/p)^j *)
  /\ (forall k, Un_cv (fun K => sum_f_R0 (fun j => (/ P k) ^ j) K) (P k / (P k - 1)))
  (* 5. primorial product of keep-fractions = 1 / euler_prod *)
  /\ (forall k, sieve_density P k * SieveDensity.euler_prod P k = 1)
  /\ (forall k, sieve_density P k = SieveDensity.denom P k / SieveDensity.primorial P k)
  (* 6. for s>0 the un-sieved (breadth) Euler factor is 1/(1-p^{-s}) *)
  /\ (forall k, Un_cv (fun K => sum_f_R0 (fun j => Rpower (P k) (- s) ^ j) K)
                      (/ (1 - Rpower (P k) (- s)))).
Proof.
  intros s Hs.
  split; [ intros k n; apply dft_indicator; apply Qpos | ].
  split; [ intros k; apply period_divisible_sum; apply Qpos | ].
  split; [ intros k; apply keep_euler_inv; apply HP | ].
  split; [ intros k; apply prime_euler_factor; apply HP | ].
  split; [ intros k; apply sieve_counting_inverse; exact HP | ].
  split; [ intros k; apply sieve_density_eq; exact HP | ].
  intros k; apply euler_factor_s; [ exact Hs | apply HP ].
Qed.

End Bridge.

Print Assumptions dft_indicator.
Print Assumptions primorial_dft_euler.
