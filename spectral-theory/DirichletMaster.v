(* ================================================================= *)
(*  DirichletMaster.v                                                 *)
(*                                                                    *)
(*  MASTER UMBRELLA THEOREM for the entire Dirichlet thread.          *)
(*                                                                    *)
(*  A single conjunction `dirichlet_theory` bundling the headline     *)
(*  results built across DirichletConv / DirichletMult /              *)
(*  DirichletDivisor / DirichletPPow / DirichletPeel / DirichletVexp* *)
(*  / DirichletVonMangoldtGen:                                        *)
(*                                                                    *)
(*    I.   The Dirichlet convolution RING (comm, assoc, unit ε,       *)
(*         bilinearity) and the divisor-sum form of ∗.                *)
(*    II.  MÖBIUS: μ ∗ 1 = ε, Möbius inversion, φ = id ∗ μ.           *)
(*    III. MULTIPLICATIVITY: ∗ preserves it; μ, φ, τ, σ, σ_k are      *)
(*         multiplicative.                                            *)
(*    IV.  PRIME-POWER VALUES: μ(p)=−1, μ(p^k)=0 (k≥2),               *)
(*         φ(p^k)=p^k−p^{k−1}, τ(p^k)=k+1; τ, σ as divisor sums.      *)
(*    V.   REDUCE-TO-PRIME-POWERS induction (mult_ind).               *)
(*    VI.  VON MANGOLDT (exp form): vexp(p^v)=p, vexp(ab)=1 for       *)
(*         coprime a,b≥2, and the general ∏_{d∣n} vexp(d) = n.        *)
(*                                                                    *)
(*  Everything is over ℕ / ℤ / lists — AXIOM-FREE.                   *)
(* ================================================================= *)

From Stdlib Require Import ZArith Znumtheory Arith Lia List.
Require Import HopfGroupTensor Totient.
Require Import DirichletConv DirichletMult DirichletDivisor DirichletPPow
        DirichletPeel DirichletVonMangoldt DirichletVexpSem DirichletVexpCoprime
        DirichletVonMangoldtGen.
Open Scope Z_scope.

Theorem dirichlet_theory :
  (* ---- I. the convolution ring ---- *)
  (forall f g n, dconv f g n = dconv g f n) /\
  (forall f g h n, (1 <= n)%nat -> dconv (dconv f g) h n = dconv f (dconv g h) n) /\
  (forall f n, (1 <= n)%nat -> dconv deps f n = f n) /\
  (forall f n, (1 <= n)%nat -> dconv f deps n = f n) /\
  (forall f g h n, dconv f (fun k => g k + h k) n = dconv f g n + dconv f h n) /\
  (forall f g h n, dconv (fun k => f k + g k) h n = dconv f h n + dconv g h n) /\
  (forall f g n, (1 <= n)%nat ->
      dconv f g n = sumf (divisors n) (fun d => f d * g (n / d)%nat)) /\
  (* ---- II. Möbius ---- *)
  (forall n, (1 <= n)%nat -> dconv mu done n = deps n) /\
  (forall f g, (forall n, (1 <= n)%nat -> g n = dconv f done n) ->
      forall n, (1 <= n)%nat -> f n = dconv g mu n) /\
  (forall n, (1 <= n)%nat -> dphi n = dconv did mu n) /\
  (forall n, (1 <= n)%nat -> dconv dphi done n = did n) /\
  (* ---- III. multiplicativity ---- *)
  (forall f g, multiplicative f -> multiplicative g -> multiplicative (dconv f g)) /\
  multiplicative mu /\
  multiplicative dphi /\
  multiplicative dtau /\
  multiplicative dsigma /\
  (forall k, multiplicative (dsigmak k)) /\
  (* ---- IV. prime-power values ---- *)
  (forall p, prime (Z.of_nat p) -> mu p = -1) /\
  (forall p k, prime (Z.of_nat p) -> (2 <= k)%nat -> mu (p ^ k)%nat = 0) /\
  (forall p k, prime (Z.of_nat p) -> (1 <= k)%nat ->
      dphi (p ^ k)%nat = Z.of_nat (p ^ k) - Z.of_nat (p ^ (k - 1))) /\
  (forall p k, prime (Z.of_nat p) -> dtau (p ^ k)%nat = Z.of_nat (S k)) /\
  (forall n, (1 <= n)%nat -> dtau n = Z.of_nat (length (divisors n))) /\
  (forall n, (1 <= n)%nat -> dsigma n = sumf (divisors n) (fun d => Z.of_nat d)) /\
  (* ---- V. reduce-to-prime-powers induction ---- *)
  (forall (P : nat -> Prop),
      P 1%nat ->
      (forall p v m, prime (Z.of_nat p) -> ~ Nat.divide p m ->
         (1 <= v)%nat -> (1 <= m)%nat -> P m -> P (p ^ v * m)%nat) ->
      forall n, (1 <= n)%nat -> P n) /\
  (* ---- VI. von Mangoldt (exp form) ---- *)
  (forall p v, prime (Z.of_nat p) -> (1 <= v)%nat -> vexp (p ^ v) = p) /\
  (forall a b, Nat.gcd a b = 1%nat -> (2 <= a)%nat -> (2 <= b)%nat -> vexp (a * b) = 1%nat) /\
  (forall n, (1 <= n)%nat -> vmprod n = n).
Proof.
  exact (conj dconv_comm
         (conj dconv_assoc
         (conj dconv_eps_l
         (conj dconv_eps_r
         (conj dconv_distrib_l
         (conj dconv_distrib_r
         (conj dconv_as_div
         (conj mu_one
         (conj mobius_inversion
         (conj phi_mobius
         (conj phi_done_eq_id
         (conj dconv_mult
         (conj mu_mult
         (conj phi_mult
         (conj dtau_mult
         (conj dsigma_mult
         (conj dsigmak_mult
         (conj mu_p
         (conj mu_ppow_ge2
         (conj phi_ppow
         (conj tau_ppow
         (conj dtau_as_div
         (conj dsigma_as_div
         (conj mult_ind
         (conj vexp_ppow
         (conj vexp_coprime
               vonmangoldt)))))))))))))))))))))))))).
Qed.

Print Assumptions dirichlet_theory.

(* ================================================================= *)
(*  END DirichletMaster.v                                            *)
(*  One umbrella (`dirichlet_theory`) for the Dirichlet convolution   *)
(*  thread: ring + Möbius + multiplicativity + prime-power values +   *)
(*  reduction induction + von Mangoldt.  Closed under the global      *)
(*  context (axiom-free).                                            *)
(* ================================================================= *)
