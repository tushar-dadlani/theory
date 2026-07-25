(* ================================================================= *)
(*  DirichletAP.v                                                    *)
(*                                                                    *)
(*  DIRICHLET (the ≡ 1 case, general n):                             *)
(*      for every n ≥ 1 there are INFINITELY MANY primes q ≡ 1 (mod n)*)
(*      — i.e. for every bound B a prime q > B with n ∣ q − 1.        *)
(*                                                                    *)
(*  Proof: fix n, B.  Let A = n·M! with M large.  The cyclotomic      *)
(*  value Φ_n(A) is ≥ 2 (monic growth), so it has a prime divisor q.  *)
(*  Since Φ_n(A) ≡ Φ_n(0) = ±1 (mod A), q ∤ A; as n ∣ A and every     *)
(*  prime ≤ B divides M! ∣ A, we get q ∤ n and q > B.  By             *)
(*  PrimeDivisorPhi.phi_primitive a has order exactly n mod q, so     *)
(*  OrderPrimeMod.order_prime_mod gives n ∣ q − 1.  AXIOM-FREE.       *)
(* ================================================================= *)

From Stdlib Require Import ZArith Znumtheory Arith Lia Factorial List.
Import ListNotations.
Require Import IntPoly PolyDiv PolyDivComp PolyDivQuot Totient Cyclotomic CyclotomicProd
        IntPolyDerivResp PrimeDivisorPhi OrderPrimeMod EuclidPrimes.
Open Scope Z_scope.

(* ================================================================= *)
(*  Sum of absolute values of the coefficients                       *)
(* ================================================================= *)
Fixpoint sumabs (p : poly) : Z :=
  match p with [] => 0 | c :: p' => Z.abs c + sumabs p' end.

Lemma sumabs_nonneg : forall p, 0 <= sumabs p.
Proof. induction p as [|c p IH]; simpl; [ lia | pose proof (Z.abs_nonneg c); lia ]. Qed.

Lemma sumabs_padd_le : forall p q, sumabs (padd p q) <= sumabs p + sumabs q.
Proof.
  induction p as [|a p IH]; intro q.
  - simpl; pose proof (sumabs_nonneg q); lia.
  - destruct q as [|b q].
    + simpl; pose proof (sumabs_nonneg p); lia.
    + simpl; pose proof (IH q); pose proof (Z.abs_triangle a b); lia.
Qed.

Lemma sumabs_pneg : forall p, sumabs (pneg p) = sumabs p.
Proof.
  induction p as [|c p IH]; [ reflexivity | ].
  cbn [pneg map sumabs]; rewrite Z.abs_opp.
  change (map Z.opp p) with (pneg p); rewrite IH; reflexivity.
Qed.

Lemma sumabs_psub_le : forall p q, sumabs (psub p q) <= sumabs p + sumabs q.
Proof.
  intros p q; unfold psub.
  eapply Z.le_trans; [ apply sumabs_padd_le | rewrite sumabs_pneg; lia ].
Qed.

Lemma sumabs_pmonom : forall d, sumabs (pmonom d) = 1.
Proof. induction d as [|d IH]; simpl; [ reflexivity | rewrite IH; reflexivity ]. Qed.

(* ================================================================= *)
(*  1 <= a  ⟹  1 <= a^k                                             *)
(* ================================================================= *)
Lemma one_le_pow : forall a k, 1 <= a -> 1 <= a ^ Z.of_nat k.
Proof.
  intros a k Ha; induction k as [|k IH].
  - change (Z.of_nat 0) with 0%Z; rewrite Z.pow_0_r; lia.
  - rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia; nia.
Qed.

(* ================================================================= *)
(*  |eval p a| bounded by sumabs·a^k when deg p ≤ k                   *)
(* ================================================================= *)
Lemma abs_eval_degle : forall p a k, 1 <= a ->
  (forall j, (k < j)%nat -> coeff p j = 0) ->
  Z.abs (eval p a) <= sumabs p * a ^ Z.of_nat k.
Proof.
  intros p a; induction p as [|c p' IH]; intros k Ha Hk.
  - change (sumabs []) with 0%Z; rewrite Z.mul_0_l.
    change (eval [] a) with 0%Z; rewrite Z.abs_0; apply Z.le_refl.
  - destruct k as [|k'].
    + assert (Hp0 : forall i, coeff p' i = 0).
      { intro i; specialize (Hk (S i) ltac:(lia));
        change (coeff (c :: p') (S i)) with (coeff p' i) in Hk; exact Hk. }
      assert (Hev : eval p' a = 0) by (apply peval_all_zero; exact Hp0).
      simpl; rewrite Hev, Z.mul_0_r, Z.add_0_r, ?Z.mul_1_r.
      pose proof (sumabs_nonneg p'); pose proof (Z.abs_nonneg c); lia.
    + assert (Hp' : forall j, (k' < j)%nat -> coeff p' j = 0).
      { intros j Hj; specialize (Hk (S j) ltac:(lia));
        change (coeff (c :: p') (S j)) with (coeff p' j) in Hk; exact Hk. }
      specialize (IH k' Ha Hp').
      assert (Hpow : 1 <= a ^ Z.of_nat (S k')) by (apply one_le_pow; lia).
      assert (Ha_pow : a * a ^ Z.of_nat k' = a ^ Z.of_nat (S k')).
      { rewrite Nat2Z.inj_succ, Z.pow_succ_r by (apply Zle_0_nat); ring. }
      assert (H1 : a * Z.abs (eval p' a) <= sumabs p' * a ^ Z.of_nat (S k')).
      { rewrite <- Ha_pow; nia. }
      assert (H2 : Z.abs c <= Z.abs c * a ^ Z.of_nat (S k')).
      { pose proof (Z.abs_nonneg c); nia. }
      simpl eval; simpl sumabs.
      eapply Z.le_trans; [ apply Z.abs_triangle | ].
      rewrite Z.abs_mul, (Z.abs_eq a) by lia.
      nia.
Qed.

(* ================================================================= *)
(*  A monic polynomial of degree ≥ 1 is ≥ 2 for large arguments      *)
(* ================================================================= *)
Lemma monic_eval_lower : forall p d a,
  monic p d -> (1 <= d)%nat -> sumabs p + 3 <= a -> 2 <= eval p a.
Proof.
  intros p d a [Hlead Hdeg] Hd Ha.
  assert (Hsp : 0 <= sumabs p) by apply sumabs_nonneg.
  assert (Ha1 : 1 <= a) by lia.
  set (low := psub p (pmonom d)).
  assert (Hev : eval p a = eval low a + a ^ Z.of_nat d).
  { unfold low; rewrite eval_sub, eval_monom; ring. }
  assert (Hlowdeg : forall j, (Nat.pred d < j)%nat -> coeff low j = 0).
  { intros j Hj; unfold low; rewrite coeff_psub.
    destruct (Nat.eq_dec j d) as [->|Hne].
    - rewrite Hlead, coeff_pmonom_eq; ring.
    - rewrite (Hdeg j), coeff_pmonom_hi; [ ring | lia | lia ]. }
  pose proof (abs_eval_degle low a (Nat.pred d) Ha1 Hlowdeg) as Hb.
  assert (Hsl : sumabs low <= sumabs p + 1).
  { unfold low; eapply Z.le_trans; [ apply sumabs_psub_le | rewrite sumabs_pmonom; lia ]. }
  set (P := a ^ Z.of_nat (Nat.pred d)).
  assert (HP1 : 1 <= P) by (unfold P; apply one_le_pow; lia).
  assert (Had : a ^ Z.of_nat d = a * P).
  { unfold P; replace (Z.of_nat d) with (Z.succ (Z.of_nat (Nat.pred d))).
    - rewrite Z.pow_succ_r by (apply Zle_0_nat); ring.
    - rewrite <- Nat2Z.inj_succ; f_equal; lia. }
  apply Z.abs_le in Hb; destruct Hb as [Hb1 _].
  assert (Hlo2 : - ((sumabs p + 1) * P) <= eval low a) by nia.
  rewrite Hev, Had; nia.
Qed.

(* ================================================================= *)
(*  eval p a ≡ eval p 0 (mod a)  and  Φ_n(0) = ±1                     *)
(* ================================================================= *)
Lemma a_dvd_eval_sub : forall p a, (a | eval p a - eval p 0).
Proof.
  intros [|c p'] a; simpl.
  - exists 0; ring.
  - exists (eval p' a); ring.
Qed.

Lemma phi0_unit : forall n, (1 <= n)%nat ->
  eval (Phi n) 0 = 1 \/ eval (Phi n) 0 = -1.
Proof.
  intros n Hn.
  pose proof (cyclotomic_prod_Z n Hn 0%Z) as H.
  rewrite eval_Xn1 in H; rewrite Z.pow_0_l in H by lia.
  assert (Hdiv : (eval (Phi n) 0 | 1)).
  { exists (- eval (Dprod n) 0).
    assert (Hm : eval (Phi n) 0 * eval (Dprod n) 0 = -1) by lia. nia. }
  apply Z.divide_1_r in Hdiv; exact Hdiv.
Qed.

(* ================================================================= *)
(*  nat ↔ ℤ divisibility bridges                                     *)
(* ================================================================= *)
Lemma dvd_nat_Z : forall x y, Nat.divide x y -> (Z.of_nat x | Z.of_nat y).
Proof. intros x y [k Hk]; exists (Z.of_nat k); rewrite Hk, Nat2Z.inj_mul; reflexivity. Qed.

Lemma dvd_Z_nat : forall x y, (Z.of_nat x | Z.of_nat y) -> Nat.divide x y.
Proof.
  intros x y [c Hc]; destruct x as [|x'].
  - simpl in Hc; rewrite Z.mul_0_r in Hc.
    assert (y = 0)%nat by lia; subst; exists 0%nat; reflexivity.
  - assert (Hc0 : 0 <= c).
    { assert (Hpos : 0 < Z.of_nat (S x')) by (rewrite Nat2Z.inj_succ; lia).
      pose proof (Nat2Z.is_nonneg y); nia. }
    exists (Z.to_nat c); apply Nat2Z.inj.
    rewrite Nat2Z.inj_mul, Z2Nat.id by lia; exact Hc.
Qed.

Lemma le_fact : forall m, (m <= fact m)%nat.
Proof.
  induction m as [|m IH]; simpl; [ lia | pose proof (lt_O_fact m); nia ].
Qed.

(* ================================================================= *)
(*  THE THEOREM: infinitely many primes ≡ 1 (mod n)                  *)
(* ================================================================= *)
Theorem dirichlet_primes_1_mod_n : forall n, (1 <= n)%nat ->
  forall B, exists q, prime (Z.of_nat q) /\ (B < q)%nat /\ Nat.divide n (q - 1).
Proof.
  intros n Hn B.
  set (s := Z.to_nat (sumabs (Phi n))).
  set (M := (B + s + 3)%nat).
  set (A := (n * fact M)%nat).
  assert (HfactM : (1 <= fact M)%nat) by (pose proof (lt_O_fact M); lia).
  assert (HA1 : (1 <= A)%nat) by (unfold A; nia).
  assert (HnA : Nat.divide n A) by (exists (fact M); unfold A; ring).
  (* A is large enough for the growth bound *)
  assert (Hsz : Z.of_nat s = sumabs (Phi n)) by (unfold s; apply Z2Nat.id; apply sumabs_nonneg).
  assert (HAbig : sumabs (Phi n) + 3 <= Z.of_nat A).
  { pose proof (le_fact M) as HfM.
    assert (HAf : (fact M <= A)%nat) by (unfold A; nia).
    assert (HMs : (s + 3 <= M)%nat) by (unfold M; lia).
    rewrite <- Hsz; lia. }
  (* g := Φ_n(A) ≥ 2 *)
  set (a := Z.of_nat A).
  assert (Hg2 : 2 <= eval (Phi n) a).
  { apply (monic_eval_lower (Phi n) (phi n) a
             (cyclotomic_monic n Hn) (phi_ge_1 n Hn) HAbig). }
  set (g := eval (Phi n) a).
  (* a prime divisor q of g (via its natural value) *)
  set (gN := Z.to_nat g).
  assert (HgNz : Z.of_nat gN = g) by (unfold gN; apply Z2Nat.id; lia).
  assert (HgN2 : (2 <= gN)%nat) by lia.
  destruct (nat_prime_divisor gN HgN2) as [q [Hq Hqd]].
  assert (Hq2 : (2 <= q)%nat) by (pose proof (prime_ge_2 _ Hq); lia).
  (* q | g  in ℤ *)
  assert (Hqg : (Z.of_nat q | g)).
  { rewrite <- HgNz; apply dvd_nat_Z; exact Hqd. }
  (* q ∤ A  (since g ≡ Φ_n(0) = ±1 mod A) *)
  assert (HqnA : ~ Nat.divide q A).
  { intro Hd.
    assert (HqZA : (Z.of_nat q | a)) by (unfold a; apply dvd_nat_Z; exact Hd).
    assert (Hsub : (a | g - eval (Phi n) 0)) by (unfold g, a; apply a_dvd_eval_sub).
    assert (Hqc : (Z.of_nat q | eval (Phi n) 0)).
    { replace (eval (Phi n) 0) with (g - (g - eval (Phi n) 0)) by ring.
      apply Z.divide_sub_r; [ exact Hqg | ].
      apply (Z.divide_trans _ a _ HqZA Hsub). }
    assert (Habs1 : (Z.of_nat q | 1)).
    { destruct (phi0_unit n Hn) as [E|E]; rewrite E in Hqc.
      - exact Hqc.
      - destruct Hqc as [k Hk]; exists (- k); rewrite Z.mul_opp_l, <- Hk; ring. }
    apply Z.divide_1_r in Habs1; pose proof (prime_ge_2 _ Hq); destruct Habs1; lia. }
  (* q > B *)
  assert (HqB : (B < q)%nat).
  { destruct (Nat.le_gt_cases q B) as [Hle|]; [ exfalso | assumption ].
    apply HqnA.
    assert (Hqf : Nat.divide q (fact M)) by (apply divide_fact; unfold M; lia).
    apply (Nat.divide_trans q (fact M) A); [ exact Hqf | exists n; unfold A; ring ]. }
  (* q ∤ n *)
  assert (HqnN : ~ Nat.divide q n).
  { intro Hd; apply HqnA; apply (Nat.divide_trans q n A Hd HnA). }
  (* order of a mod q is n  ⟹  n | q − 1 *)
  exists q; split; [ exact Hq | split; [ exact HqB | ] ].
  (* build order_prime_mod's hypotheses over nat *)
  assert (HqaZ : ~ (Z.of_nat q | a)).
  { intro Hd; apply HqnA; unfold a in Hd; apply (dvd_Z_nat q A Hd). }
  assert (HqnZ : ~ (Z.of_nat q | Z.of_nat n)).
  { intro Hd; apply HqnN; apply (dvd_Z_nat q n Hd). }
  assert (Hqan1 : Nat.divide q (A ^ n - 1)).
  { apply dvd_Z_nat.
    assert (Hpe : (1 <= A ^ n)%nat) by (rewrite <- (Nat.pow_1_l n); apply Nat.pow_le_mono_l; lia).
    rewrite Nat2Z.inj_sub by lia; rewrite Nat2Z.inj_pow; simpl (Z.of_nat 1).
    fold a; apply (Z.divide_trans _ g _ Hqg).
    apply (Phi_dvd_pow n Hn a). }
  assert (Hprim : forall d, Nat.divide d n -> (d < n)%nat -> ~ Nat.divide q (A ^ d - 1)).
  { intros d Hdd Hdlt Hcon.
    assert (Hpe : (1 <= A ^ d)%nat) by (rewrite <- (Nat.pow_1_l d); apply Nat.pow_le_mono_l; lia).
    apply (phi_primitive (Z.of_nat q) a n Hq HqaZ Hn Hqg HqnZ d Hdd Hdlt).
    apply dvd_nat_Z in Hcon.
    rewrite Nat2Z.inj_sub in Hcon by lia; rewrite Nat2Z.inj_pow in Hcon; simpl (Z.of_nat 1) in Hcon.
    fold a in Hcon; exact Hcon. }
  apply (order_prime_mod q A n Hq HqnA Hn Hqan1 Hprim).
Qed.

Print Assumptions dirichlet_primes_1_mod_n.

(* ================================================================= *)
(*  END DirichletAP.v                                                *)
(*  Dirichlet's theorem, ≡ 1 case: for every n ≥ 1 there are          *)
(*  infinitely many primes q ≡ 1 (mod n).  Closed under the global    *)
(*  context (axiom-free).                                            *)
(* ================================================================= *)
