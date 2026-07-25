(* ================================================================= *)
(*  DirichletMod4.v                                                  *)
(*                                                                    *)
(*  DIRICHLET, THE CASE n = 4:  infinitely many primes ≡ 1 (mod 4).  *)
(*                                                                    *)
(*      for every m, there is a prime q with m < q and q ≡ 1 (mod 4).*)
(*                                                                    *)
(*  Proof (fully elementary, via x²+1 and the order lemma):          *)
(*  set a := 2·m!, N := a²+1.  A prime divisor q of N satisfies       *)
(*    • q > m       (else q | m! | a, and q | a²+1, so q | 1)         *)
(*    • q odd       (N is odd, since a is even)                       *)
(*    • q | a⁴−1    (a⁴−1 = (a²+1)(a²−1))                             *)
(*    • q ∤ a, q ∤ a²−1, q ∤ a−1   (else q | 2, forcing q = 2)        *)
(*  so by OrderPrimeMod.order_prime_mod the order of a mod q is 4,    *)
(*  hence 4 | q−1, i.e. q ≡ 1 (mod 4).  AXIOM-FREE.                  *)
(* ================================================================= *)

From Stdlib Require Import ZArith Znumtheory Arith Lia Factorial.
Require Import EuclidPrimes OrderPrimeMod.
Open Scope nat_scope.

Theorem dirichlet_1_mod_4 : forall m, exists q,
  prime (Z.of_nat q) /\ m < q /\ q mod 4 = 1.
Proof.
  intro m.
  set (a := 2 * fact m).
  assert (Hfge : 1 <= fact m) by (pose proof (lt_O_fact m); lia).
  assert (Ha2 : 2 <= a) by (unfold a; lia).
  (* a is even, hence a² is even, hence N = a²+1 is odd *)
  assert (H2a : Nat.divide 2 a) by (exists (fact m); unfold a; ring).
  destruct H2a as [p Hp].
  assert (H2aa : Nat.divide 2 (a ^ 2)) by
    (exists (p * a); rewrite Nat.pow_2_r, Hp; ring).
  set (N := a ^ 2 + 1).
  assert (HN2 : 2 <= N) by (unfold N; assert (2 <= a ^ 2) by (rewrite Nat.pow_2_r; nia); lia).
  destruct H2aa as [k Hk].                                   (* a² = k*2 *)
  assert (HNodd : N mod 2 = 1).
  { unfold N; rewrite Hk; replace (k * 2 + 1) with (1 + k * 2) by lia.
    rewrite Nat.Div0.mod_add; reflexivity. }
  (* a prime divisor q of N *)
  destruct (nat_prime_divisor N HN2) as [q [Hq Hqd]].
  assert (Hq2 : 2 <= q) by (pose proof (prime_ge_2 _ Hq); lia).
  assert (HqN : Nat.divide q (a ^ 2 + 1)) by (unfold N in Hqd; exact Hqd).
  (* q is odd *)
  assert (Hqne2 : q <> 2).
  { intro He; subst q; destruct Hqd as [c Hc].
    assert (N mod 2 = 0) by (rewrite Hc, Nat.Div0.mod_mul; reflexivity); lia. }
  (* q ∤ a *)
  assert (Hqa : ~ Nat.divide q a).
  { intro Hd.
    assert (Haa : Nat.divide q (a ^ 2)) by
      (destruct Hd as [c Hc]; exists (c * a); rewrite Nat.pow_2_r, Hc; ring).
    assert (H1 : Nat.divide q 1).
    { replace 1 with ((a ^ 2 + 1) - a ^ 2) by lia.
      apply Nat.divide_sub_r; [ exact HqN | exact Haa ]. }
    apply Nat.divide_1_r in H1; lia. }
  (* q > m *)
  assert (Hgt : m < q).
  { destruct (Nat.le_gt_cases q m) as [Hle | ]; [ exfalso | assumption ].
    apply Hqa.
    assert (Hqf : Nat.divide q (fact m)) by (apply divide_fact; lia).
    apply (Nat.divide_trans q (fact m) a); [ exact Hqf | exists 2; unfold a; ring ]. }
  (* q | a⁴ − 1 *)
  assert (Hq4 : Nat.divide q (a ^ 4 - 1)).
  { assert (Hid : a ^ 4 - 1 = (a ^ 2 + 1) * (a ^ 2 - 1)).
    { assert (E : a ^ 4 = a ^ 2 * a ^ 2) by (rewrite <- Nat.pow_add_r; reflexivity).
      assert (1 <= a ^ 2) by (rewrite Nat.pow_2_r; nia); nia. }
    rewrite Hid; destruct HqN as [c Hc]; exists (c * (a ^ 2 - 1)).
    rewrite Hc; ring. }
  (* q ∤ a² − 1  (else q | (a²+1)−(a²−1) = 2) *)
  assert (Hna2 : ~ Nat.divide q (a ^ 2 - 1)).
  { intro Hd.
    assert (Hd2 : Nat.divide q 2).
    { replace 2 with ((a ^ 2 + 1) - (a ^ 2 - 1)) by (assert (1 <= a ^ 2) by (rewrite Nat.pow_2_r; nia); lia).
      apply Nat.divide_sub_r; [ exact HqN | exact Hd ]. }
    pose proof (Nat.divide_pos_le q 2 ltac:(lia) Hd2); lia. }
  (* assemble *)
  exists q; split; [ exact Hq | split; [ exact Hgt | ] ].
  assert (Hdvd4 : Nat.divide 4 (q - 1)).
  { apply (order_prime_mod q a 4 Hq Hqa ltac:(lia) Hq4).
    intros d Hd Hd4.
    assert (Hcase : d = 1 \/ d = 2).
    { destruct Hd as [j Hj]; destruct d as [|[|[|[|d']]]].
      - exfalso; nia.
      - left; reflexivity.
      - right; reflexivity.
      - exfalso; nia.
      - exfalso; lia. }
    destruct Hcase as [-> | ->].
    - intro Hd1; rewrite Nat.pow_1_r in Hd1; apply Hna2.
      assert (Hfac : a ^ 2 - 1 = (a - 1) * (a + 1)) by
        (rewrite Nat.pow_2_r; assert (1 <= a) by lia; nia).
      rewrite Hfac; destruct Hd1 as [c Hc]; exists (c * (a + 1)); rewrite Hc; ring.
    - exact Hna2. }
  destruct Hdvd4 as [j Hj].
  replace q with (1 + j * 4) by lia.
  rewrite Nat.Div0.mod_add; reflexivity.
Qed.

Print Assumptions dirichlet_1_mod_4.

(* ================================================================= *)
(*  END DirichletMod4.v                                              *)
(*  Infinitely many primes ≡ 1 (mod 4): for every m a prime q > m     *)
(*  with q ≡ 1 (mod 4), via a prime divisor of (2·m!)² + 1 and the    *)
(*  order lemma.  Closed under the global context (axiom-free).       *)
(* ================================================================= *)
