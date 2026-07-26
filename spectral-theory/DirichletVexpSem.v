(* ================================================================= *)
(*  DirichletVexpSem.v                                               *)
(*                                                                    *)
(*  SEMANTIC LEMMAS about the computable vexp (= exp∘Λ), on prime      *)
(*  powers.  Proves vexp(p^v) = p and ∏_{d∣p^k} vexp(d) = p^k — i.e.  *)
(*  the von Mangoldt identity ON PRIME POWERS, now fully proven        *)
(*  (upgrading DirichletVonMangoldt's reflective check for this case). *)
(*                                                                    *)
(*  The work is reasoning about the computable definitions            *)
(*  (`least_factor` = a `find`, `strip` = a fuel recursion) via the    *)
(*  divisor-of-a-prime-power fact JacobiRHS.div_prime_pow.  AXIOM-FREE.*)
(* ================================================================= *)

From Stdlib Require Import ZArith Znumtheory Arith Lia List Permutation.
Import ListNotations.
Require Import Totient JacobiRHS DirichletVonMangoldt.
Open Scope nat_scope.

(* ================================================================= *)
(*  helpers on the computable primitives                             *)
(* ================================================================= *)
Lemma le_pow : forall p v, 2 <= p -> v <= p ^ v.
Proof.
  induction v as [|v IH]; intro Hp; [ simpl; lia | ].
  change (p ^ S v) with (p * p ^ v).
  assert (1 <= p ^ v) by (apply Nat.neq_0_lt_0, Nat.pow_nonzero; lia).
  specialize (IH Hp); nia.
Qed.

Lemma strip_pow : forall v fuel p, 2 <= p -> v <= fuel -> strip fuel (p ^ v) p = 1.
Proof.
  induction v as [|v IH]; intros fuel p Hp Hvf.
  - destruct fuel as [|f]; [ reflexivity | ].
    cbn [strip Nat.pow].
    replace (1 mod p =? 0) with false;
      [ reflexivity | symmetry; apply Nat.eqb_neq; rewrite Nat.mod_1_l by lia; lia ].
  - destruct fuel as [|f]; [ lia | ].
    cbn [strip]; change (p ^ S v) with (p * p ^ v).
    replace ((p * p ^ v) mod p =? 0) with true.
    + replace ((p * p ^ v) / p) with (p ^ v) by (rewrite Nat.mul_comm, Nat.div_mul; lia).
      apply IH; [ exact Hp | lia ].
    + symmetry; apply Nat.eqb_eq; rewrite Nat.mul_comm; apply Nat.Div0.mod_mul.
Qed.

Lemma find_first : forall (g : nat -> bool) l1 x l2,
  (forall y, In y l1 -> g y = false) -> g x = true -> find g (l1 ++ x :: l2) = Some x.
Proof.
  induction l1 as [|a l1 IH]; intros x l2 Hl1 Hx; simpl.
  - rewrite Hx; reflexivity.
  - rewrite (Hl1 a (or_introl eq_refl)); apply IH; [ intros y Hy; apply Hl1; right; exact Hy | exact Hx ].
Qed.

Lemma seq_split_at : forall p n, 2 <= p <= n ->
  seq 2 (n - 1) = seq 2 (p - 2) ++ p :: seq (S p) (n - p).
Proof.
  intros p n [Hp Hpn].
  replace (n - 1) with ((p - 2) + S (n - p)) by lia.
  rewrite seq_app; replace (2 + (p - 2)) with p by lia; cbn [seq]; reflexivity.
Qed.

Lemma least_factor_least : forall n p, 2 <= p <= n -> Nat.divide p n ->
  (forall d, 2 <= d < p -> ~ Nat.divide d n) -> least_factor n = p.
Proof.
  intros n p Hpr Hdvd Hless; unfold least_factor.
  rewrite (seq_split_at p n Hpr), find_first.
  - reflexivity.
  - intros y Hy; apply in_seq in Hy; apply Nat.eqb_neq; intro Hmod.
    apply Nat.Lcm0.mod_divide in Hmod; apply (Hless y); [ lia | exact Hmod ].
  - apply Nat.eqb_eq; rewrite Nat.Lcm0.mod_divide; exact Hdvd.
Qed.

(* ================================================================= *)
(*  vexp on prime powers                                             *)
(* ================================================================= *)
Lemma least_factor_ppow : forall p v, prime (Z.of_nat p) -> 1 <= v -> least_factor (p ^ v) = p.
Proof.
  intros p v Hp Hv; assert (Hp2 : 2 <= p) by (pose proof (prime_ge_2 _ Hp); lia).
  apply least_factor_least.
  - split; [ exact Hp2 | apply Nat.le_trans with (p ^ 1);
      [ rewrite Nat.pow_1_r; lia | apply Nat.pow_le_mono_r; lia ] ].
  - exists (p ^ (v - 1)); replace v with (S (v - 1)) at 1 by lia; cbn [Nat.pow]; ring.
  - intros d [Hd2 Hdp] Hddvd.
    destruct (div_prime_pow p v d Hp Hddvd) as [j [Hj Hdj]]; subst d.
    destruct j as [|j']; [ cbn [Nat.pow] in Hd2; lia | ].
    assert (p <= p ^ S j') by (apply Nat.le_trans with (p ^ 1);
      [ rewrite Nat.pow_1_r; lia | apply Nat.pow_le_mono_r; lia ]); lia.
Qed.

Lemma vexp_1 : vexp 1 = 1. Proof. reflexivity. Qed.

Theorem vexp_ppow : forall p v, prime (Z.of_nat p) -> 1 <= v -> vexp (p ^ v) = p.
Proof.
  intros p v Hp Hv; assert (Hp2 : 2 <= p) by (pose proof (prime_ge_2 _ Hp); lia).
  assert (Hpv : 2 <= p ^ v) by (apply Nat.le_trans with (p ^ 1);
    [ rewrite Nat.pow_1_r; lia | apply Nat.pow_le_mono_r; lia ]).
  unfold vexp.
  replace (p ^ v <=? 1) with false by (symmetry; apply Nat.leb_gt; lia).
  rewrite (least_factor_ppow p v Hp Hv), (strip_pow v (p ^ v) p Hp2 (le_pow p v Hp2)).
  reflexivity.
Qed.

(* ================================================================= *)
(*  product toolkit and the prime-power von Mangoldt identity        *)
(* ================================================================= *)
Lemma prodf_cons : forall (a : nat) l f, prodf (a :: l) f = f a * prodf l f.
Proof. reflexivity. Qed.

Lemma prodf_perm : forall (l l' : list nat) f, Permutation l l' -> prodf l f = prodf l' f.
Proof.
  intros l l' f H; induction H.
  - reflexivity.
  - rewrite !prodf_cons, IHPermutation; reflexivity.
  - rewrite !prodf_cons; ring.
  - rewrite IHPermutation1, IHPermutation2; reflexivity.
Qed.

Lemma prodf_map : forall (l : list nat) (g : nat -> nat) f,
  prodf (map g l) f = prodf l (fun x => f (g x)).
Proof.
  intros l g f; induction l as [|a l IH]; [ reflexivity | cbn [map]; rewrite !prodf_cons, IH; reflexivity ].
Qed.

Lemma prodf_ext : forall (l : list nat) f g,
  (forall k, In k l -> f k = g k) -> prodf l f = prodf l g.
Proof.
  induction l as [|a l IH]; intros f g H; [ reflexivity | ].
  rewrite !prodf_cons, (H a (or_introl eq_refl)), (IH f g); [ reflexivity | ].
  intros k Hk; apply H; right; exact Hk.
Qed.

Lemma prodf_const : forall (l : list nat) c, prodf l (fun _ => c) = c ^ length l.
Proof.
  intros l c; induction l as [|a l IH]; [ reflexivity | rewrite prodf_cons, IH; reflexivity ].
Qed.

Theorem vmprod_ppow : forall p v, prime (Z.of_nat p) -> 1 <= v -> vmprod (p ^ v) = p ^ v.
Proof.
  intros p v Hp Hv; unfold vmprod.
  rewrite (prodf_perm _ _ vexp (divisors_prime_pow p v Hp)), prodf_map.
  change (seq 0 (S v)) with (0 :: seq 1 v).
  rewrite prodf_cons, Nat.pow_0_r, vexp_1.
  rewrite (prodf_ext (seq 1 v) (fun j => vexp (p ^ j)) (fun _ => p)).
  - rewrite prodf_const, length_seq; lia.
  - intros j Hj; apply in_seq in Hj; apply vexp_ppow; [ exact Hp | lia ].
Qed.

Print Assumptions vexp_ppow.
Print Assumptions vmprod_ppow.

(* ================================================================= *)
(*  END DirichletVexpSem.v                                           *)
(*  vexp(p^v) = p and ∏_{d∣p^k} vexp(d) = p^k, both proven.  Closed   *)
(*  under the global context (axiom-free).                           *)
(* ================================================================= *)
