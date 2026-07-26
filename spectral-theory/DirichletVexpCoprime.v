(* ================================================================= *)
(*  DirichletVexpCoprime.v                                           *)
(*                                                                    *)
(*  The remaining SEMANTIC LEMMA for the computable vexp:              *)
(*        vexp(a·b) = 1   for coprime a, b ≥ 2                        *)
(*  (a non-prime-power has vexp = 1).  This completes the             *)
(*  specification of vexp on top of DirichletVexpSem.vexp_ppow.       *)
(*                                                                    *)
(*  Needs two new facts about the computable primitives:              *)
(*   • find-min: least_factor n is ≤ every divisor ≥ 2 (least_factor_ *)
(*     min), so the least prime factor is genuinely least;            *)
(*   • strip-reverse: strip n n q = 1 ⟹ n is a power of q.           *)
(*  Together with prime_dvd_pow (a prime dividing a power divides the  *)
(*  base) these force any prime factor of a and of b to equal         *)
(*  least_factor(ab) — impossible when a,b are coprime.  AXIOM-FREE.  *)
(* ================================================================= *)

From Stdlib Require Import ZArith Znumtheory Arith Lia List.
Import ListNotations.
Require Import Totient PrimeFactorizationExists DirichletVonMangoldt DirichletPeel.
Open Scope nat_scope.

Lemma dvd_Z_nat : forall x y, (Z.of_nat x | Z.of_nat y) -> Nat.divide x y.
Proof.
  intros x y [c Hc]; destruct x as [|x'].
  - simpl in Hc; rewrite Z.mul_0_r in Hc; assert (y = 0) by lia; subst; exists 0; reflexivity.
  - assert (Hc0 : (0 <= c)%Z) by
      (assert (0 < Z.of_nat (S x'))%Z by (rewrite Nat2Z.inj_succ; lia);
       pose proof (Nat2Z.is_nonneg y); nia).
    exists (Z.to_nat c); apply Nat2Z.inj; rewrite Nat2Z.inj_mul, Z2Nat.id by lia; exact Hc.
Qed.

(* ================================================================= *)
(*  find returns the least satisfying element of an increasing seq    *)
(* ================================================================= *)
Lemma find_seq_least : forall len a g x, find g (seq a len) = Some x ->
  forall y, In y (seq a len) -> g y = true -> x <= y.
Proof.
  induction len as [|len IH]; intros a g x Hf y Hy Hgy; [ inversion Hy | ].
  simpl in Hf, Hy; destruct (g a) eqn:Hga.
  - injection Hf as ->; destruct Hy as [->|Hy]; [ lia | apply in_seq in Hy; lia ].
  - destruct Hy as [->|Hy]; [ rewrite Hga in Hgy; discriminate | apply (IH (S a) g x Hf y Hy Hgy) ].
Qed.

Lemma least_factor_min : forall n e, 2 <= n -> 2 <= e -> Nat.divide e n -> least_factor n <= e.
Proof.
  intros n e Hn He Hdvd.
  assert (Hen : e <= n) by (apply Nat.divide_pos_le; [ lia | exact Hdvd ]).
  assert (Hein : In e (seq 2 (n - 1))) by (apply in_seq; lia).
  assert (Hge : (n mod e =? 0) = true) by (apply Nat.eqb_eq; rewrite Nat.Lcm0.mod_divide; exact Hdvd).
  assert (Hgn : (n mod n =? 0) = true) by (apply Nat.eqb_eq; apply Nat.Div0.mod_same).
  assert (Hinn : In n (seq 2 (n - 1))) by (apply in_seq; lia).
  unfold least_factor; destruct (find (fun d => n mod d =? 0) (seq 2 (n - 1))) as [q|] eqn:E.
  - apply (find_seq_least (n - 1) 2 (fun d => n mod d =? 0) q E e Hein Hge).
  - pose proof (find_none _ _ E n Hinn) as H; cbn beta in H; rewrite Hgn in H; discriminate.
Qed.

Lemma least_factor_ge2 : forall n, 2 <= n -> 2 <= least_factor n.
Proof.
  intros n Hn.
  assert (Hgn : (n mod n =? 0) = true) by (apply Nat.eqb_eq; apply Nat.Div0.mod_same).
  assert (Hinn : In n (seq 2 (n - 1))) by (apply in_seq; lia).
  unfold least_factor; destruct (find (fun d => n mod d =? 0) (seq 2 (n - 1))) as [q|] eqn:E.
  - pose proof (find_some _ _ E) as [Hqin _]; apply in_seq in Hqin; lia.
  - pose proof (find_none _ _ E n Hinn) as H; cbn beta in H; rewrite Hgn in H; discriminate.
Qed.

(* ================================================================= *)
(*  strip-reverse:  strip n n q = 1  ⟹  n is a power of q            *)
(* ================================================================= *)
Lemma strip_reverse : forall fuel n q, 2 <= q -> 1 <= n -> strip fuel n q = 1 -> exists k, n = q ^ k.
Proof.
  induction fuel as [|f IH]; intros n q Hq Hn Hs; simpl in Hs.
  - exists 0; simpl; lia.
  - destruct (Nat.eqb_spec (n mod q) 0) as [Hmod|Hmod].
    + apply Nat.Lcm0.mod_divide in Hmod.
      assert (Hnq : 1 <= n / q) by (destruct Hmod as [c Hc]; rewrite Hc, Nat.div_mul; nia).
      destruct (IH (n / q) q Hq Hnq Hs) as [k' Hk'].
      exists (S k'); destruct Hmod as [c Hc]; rewrite Hc, Nat.div_mul in Hk' by lia.
      simpl; rewrite Hc, Hk'; ring.
    + exists 0; simpl; lia.
Qed.

(* ================================================================= *)
(*  a prime dividing a power divides the base                        *)
(* ================================================================= *)
Lemma prime_dvd_mult_nat : forall r a b, prime (Z.of_nat r) ->
  Nat.divide r (a * b) -> Nat.divide r a \/ Nat.divide r b.
Proof.
  intros r a b Hr Hd; apply dvd_nat_Z in Hd; rewrite Nat2Z.inj_mul in Hd.
  destruct (prime_mult (Z.of_nat r) Hr _ _ Hd) as [H|H]; [ left | right ]; apply dvd_Z_nat; exact H.
Qed.

Lemma prime_dvd_pow : forall r a k, prime (Z.of_nat r) -> Nat.divide r (a ^ k) -> Nat.divide r a.
Proof.
  intros r a k Hr; induction k as [|k IH]; intro Hd.
  - exfalso; simpl in Hd; apply Nat.divide_1_r in Hd; pose proof (prime_ge_2 _ Hr); lia.
  - change (a ^ S k) with (a * a ^ k) in Hd.
    destruct (prime_dvd_mult_nat r a (a ^ k) Hr Hd) as [H|H]; [ exact H | apply IH; exact H ].
Qed.

Lemma prime_factor_ex : forall a, 2 <= a -> exists r, prime (Z.of_nat r) /\ Nat.divide r a /\ 2 <= r.
Proof.
  intros a Ha; assert (Ha1 : (1 < Z.of_nat a)%Z) by lia.
  destruct (has_prime_divisor (Z.of_nat a) Ha1) as [r' [Hr' Hr'a]].
  pose proof (prime_ge_2 _ Hr') as Hr2.
  set (rn := Z.to_nat r'); assert (Hrn : Z.of_nat rn = r') by (unfold rn; apply Z2Nat.id; lia).
  exists rn; rewrite Hrn; split; [ exact Hr' | split; [ apply dvd_Z_nat; rewrite Hrn; exact Hr'a | lia ] ].
Qed.

(* ================================================================= *)
(*  vexp(a·b) = 1 for coprime a,b ≥ 2                                *)
(* ================================================================= *)
Theorem vexp_coprime : forall a b, Nat.gcd a b = 1 -> 2 <= a -> 2 <= b -> vexp (a * b) = 1.
Proof.
  intros a b Hco Ha Hb.
  assert (Hab2 : 2 <= a * b) by nia.
  unfold vexp; replace (a * b <=? 1) with false by (symmetry; apply Nat.leb_gt; lia).
  set (q := least_factor (a * b)).
  destruct (Nat.eqb_spec (strip (a * b) (a * b) q) 1) as [Hs|Hs]; [ exfalso | reflexivity ].
  assert (Hq2 : 2 <= q) by (unfold q; apply least_factor_ge2; exact Hab2).
  destruct (strip_reverse (a * b) (a * b) q Hq2 ltac:(lia) Hs) as [k Hk].
  destruct (prime_factor_ex a Ha) as [r [Hr [Hra Hr2]]].
  destruct (prime_factor_ex b Hb) as [s [Hs' [Hsb Hs2]]].
  assert (Hrab : Nat.divide r (a * b)) by (apply (Nat.divide_trans r a); [ exact Hra | exists b; ring ]).
  assert (Hsab : Nat.divide s (a * b)) by (apply (Nat.divide_trans s b); [ exact Hsb | exists a; ring ]).
  assert (Hrq : Nat.divide r q) by (apply (prime_dvd_pow r q k Hr); rewrite <- Hk; exact Hrab).
  assert (Hsq : Nat.divide s q) by (apply (prime_dvd_pow s q k Hs'); rewrite <- Hk; exact Hsab).
  assert (Hrqe : r = q) by (apply Nat.le_antisymm;
    [ apply Nat.divide_pos_le; [ lia | exact Hrq ]
    | unfold q; apply least_factor_min; [ exact Hab2 | exact Hr2 | exact Hrab ] ]).
  assert (Hsqe : s = q) by (apply Nat.le_antisymm;
    [ apply Nat.divide_pos_le; [ lia | exact Hsq ]
    | unfold q; apply least_factor_min; [ exact Hab2 | exact Hs2 | exact Hsab ] ]).
  assert (Hrb : Nat.divide r b) by (rewrite Hrqe, <- Hsqe; exact Hsb).
  assert (Hr1 : Nat.divide r 1) by (rewrite <- Hco; apply Nat.gcd_greatest; [ exact Hra | exact Hrb ]).
  apply Nat.divide_1_r in Hr1; lia.
Qed.

Print Assumptions vexp_coprime.

(* ================================================================= *)
(*  END DirichletVexpCoprime.v                                       *)
(*  vexp(a·b) = 1 for coprime a,b ≥ 2 — the last vexp semantic lemma. *)
(*  Closed under the global context (axiom-free).                    *)
(* ================================================================= *)
