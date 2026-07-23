(* ================================================================= *)
(*  ZmodOrder.v                                                      *)
(*                                                                    *)
(*  PHASE 4a of the Dirichlet-mod-p build: multiplicative ORDER of a   *)
(*  unit mod a prime, and its basic theory (leastness, divisibility).  *)
(*                                                                    *)
(*    pw p a k := a^k mod p     (power mod p)                          *)
(*    ord p a  := least k >= 1 with pw p a k = 1  (found in [1,p-1])    *)
(*                                                                    *)
(*    ord_period : pw p a (ord p a) = 1                               *)
(*    ord_least  : 1<=k -> pw p a k = 1 -> ord p a <= k               *)
(*    ord_divides: pw p a k = 1 -> ord p a | k                        *)
(*    ord_div_pm1: ord p a | (p-1)          (via Fermat)              *)
(*    pow_inj_below : the powers a^0..a^(ord-1) are distinct          *)
(*                                                                    *)
(*  Foundation for the order-counting primitive-root proof (Phase 4b). *)
(*  Axiom-free: constructive nat + Znumtheory via ZmodPStar.          *)
(* ================================================================= *)

From Stdlib Require Import ZArith Znumtheory Arith Lia List.
Require Import ZmodPStar.
Import ListNotations.
Open Scope nat_scope.

(* ----------------------------------------------------------------- *)
(*  Power mod p                                                      *)
(* ----------------------------------------------------------------- *)

Definition pw (p a k : nat) : nat := (a ^ k) mod p.

Lemma pow_mod : forall m b n, (b ^ n) mod m = ((b mod m) ^ n) mod m.
Proof.
  intros m b n; induction n as [|n IH]; simpl; [ reflexivity | ].
  rewrite (Nat.Div0.mul_mod b (b ^ n)), IH.
  rewrite (Nat.Div0.mul_mod (b mod m) ((b mod m) ^ n)), Nat.Div0.mod_mod; reflexivity.
Qed.

Lemma pw_0 : forall p a, 2 <= p -> pw p a 0 = 1.
Proof. intros p a Hp; unfold pw; simpl; apply Nat.mod_small; lia. Qed.

Lemma pw_1 : forall p m, 2 <= p -> pw p 1 m = 1.
Proof. intros p m Hp; unfold pw; rewrite Nat.pow_1_l; apply Nat.mod_small; lia. Qed.

Lemma pw_add : forall p a i j, pw p a (i + j) = ((pw p a i) * (pw p a j)) mod p.
Proof. intros p a i j; unfold pw; rewrite Nat.pow_add_r, Nat.Div0.mul_mod; reflexivity. Qed.

Lemma pw_mul_exp : forall p a i j, pw p a (i * j) = pw p (pw p a i) j.
Proof. intros p a i j; unfold pw; rewrite Nat.pow_mul_r, (pow_mod p (a ^ i) j); reflexivity. Qed.

Lemma not_div_pow : forall p a i, prime (Z.of_nat p) -> ~ Nat.divide p a -> ~ Nat.divide p (a ^ i).
Proof.
  intros p a i Hp Ha; induction i as [|i IH]; simpl.
  - intro Hd; destruct Hd as [k Hk]; destruct Hp as [Hgt _]; destruct k; simpl in Hk; lia.
  - intro Hd; destruct (prime_mult_nat p a (a ^ i) Hp Hd); [ apply Ha | apply IH ]; assumption.
Qed.

Lemma pw_pow_ord_mul : forall p a d m, 2 <= p -> pw p a d = 1 -> pw p a (d * m) = 1.
Proof. intros p a d m Hp Hd; rewrite pw_mul_exp, Hd; apply pw_1; exact Hp. Qed.

Lemma pw_cancel : forall p a i j, prime (Z.of_nat p) -> ~ Nat.divide p a -> i <= j ->
  pw p a i = pw p a j -> pw p a (j - i) = 1.
Proof.
  intros p a i j Hp Ha Hij Heq.
  assert (Hp2 : 2 <= p) by (destruct Hp; lia).
  assert (Hai : ~ Nat.divide p (a ^ i)) by (apply not_div_pow; assumption).
  assert (Hc : (a ^ i * 1) mod p = (a ^ i * a ^ (j - i)) mod p).
  { rewrite Nat.mul_1_r, <- Nat.pow_add_r; replace (i + (j - i)) with j by lia; exact Heq. }
  pose proof (cancel_mod p (a ^ i) 1 (a ^ (j - i)) Hp Hai Hc) as Hcan.
  unfold pw; rewrite Nat.mod_small in Hcan by lia; symmetry; exact Hcan.
Qed.

(* ----------------------------------------------------------------- *)
(*  The order (least positive period)                                *)
(* ----------------------------------------------------------------- *)

Fixpoint firstsat (f : nat -> bool) (l : list nat) : nat :=
  match l with [] => 0 | x :: l' => if f x then x else firstsat f l' end.

Lemma firstsat_sat : forall f l, existsb f l = true ->
  f (firstsat f l) = true /\ In (firstsat f l) l.
Proof.
  intros f l; induction l as [|x l IH]; simpl; intro H; [ discriminate | ].
  destruct (f x) eqn:E.
  - split; [ exact E | left; reflexivity ].
  - simpl in H; destruct (IH H) as [Hs Hin]; split; [ exact Hs | right; exact Hin ].
Qed.

Lemma firstsat_min : forall f s n k, f k = true -> (s <= k < s + n) ->
  firstsat f (seq s n) <= k.
Proof.
  intros f s n; revert s; induction n as [|n IH]; intros s k Hk Hrange; [ lia | ].
  cbn [seq firstsat]; destruct (f s) eqn:E; [ lia | ].
  apply IH; [ exact Hk | assert (s <> k) by (intro; subst; rewrite Hk in E; discriminate); lia ].
Qed.

Definition ord (p a : nat) : nat := firstsat (fun k => pw p a k =? 1) (seq 1 (p - 1)).

Lemma ord_facts : forall p a, prime (Z.of_nat p) -> 1 <= a <= p - 1 ->
  pw p a (ord p a) = 1 /\ In (ord p a) (seq 1 (p - 1)).
Proof.
  intros p a Hp Ha.
  assert (Hex : existsb (fun k => pw p a k =? 1) (seq 1 (p - 1)) = true).
  { apply existsb_exists; exists (p - 1); split.
    - apply in_seq; destruct Hp; lia.
    - apply Nat.eqb_eq; unfold pw; apply fermat; assumption. }
  destruct (firstsat_sat _ _ Hex) as [Hs Hin]; split;
    [ apply Nat.eqb_eq; exact Hs | exact Hin ].
Qed.

Lemma ord_period : forall p a, prime (Z.of_nat p) -> 1 <= a <= p - 1 -> pw p a (ord p a) = 1.
Proof. intros p a Hp Ha; apply (ord_facts p a Hp Ha). Qed.

Lemma ord_pos : forall p a, prime (Z.of_nat p) -> 1 <= a <= p - 1 -> 1 <= ord p a.
Proof. intros p a Hp Ha; destruct (ord_facts p a Hp Ha) as [_ Hin]; apply in_seq in Hin; lia. Qed.

Lemma ord_ub : forall p a, prime (Z.of_nat p) -> 1 <= a <= p - 1 -> ord p a <= p - 1.
Proof. intros p a Hp Ha; destruct (ord_facts p a Hp Ha) as [_ Hin]; apply in_seq in Hin; lia. Qed.

Lemma ord_least : forall p a k, prime (Z.of_nat p) -> 1 <= a <= p - 1 ->
  1 <= k -> pw p a k = 1 -> ord p a <= k.
Proof.
  intros p a k Hp Ha Hk1 Hpk.
  destruct (le_gt_dec k (p - 1)) as [Hle|Hgt].
  - unfold ord; apply firstsat_min; [ apply Nat.eqb_eq; exact Hpk | destruct Hp; lia ].
  - apply Nat.le_trans with (p - 1); [ apply ord_ub; assumption | lia ].
Qed.

Lemma ord_divides : forall p a k, prime (Z.of_nat p) -> 1 <= a <= p - 1 ->
  pw p a k = 1 -> Nat.divide (ord p a) k.
Proof.
  intros p a k Hp Ha Hpk.
  assert (Hp2 : 2 <= p) by (destruct Hp; lia).
  assert (Hd1 : 1 <= ord p a) by (apply ord_pos; assumption).
  assert (Hmod : pw p a (k mod ord p a) = 1).
  { assert (Hstep : pw p a k = pw p a (k mod ord p a)).
    { rewrite (Nat.div_mod_eq k (ord p a)) at 1.
      rewrite pw_add, pw_pow_ord_mul by (try exact Hp2; apply ord_period; assumption).
      rewrite Nat.mul_1_l; unfold pw at 1; rewrite Nat.Div0.mod_mod; reflexivity. }
    rewrite Hpk in Hstep; symmetry; exact Hstep. }
  destruct (Nat.eq_dec (k mod ord p a) 0) as [E|E].
  - apply Nat.Lcm0.mod_divide; exact E.
  - exfalso.
    assert (Hle : ord p a <= k mod ord p a) by (apply ord_least; [ assumption | assumption | lia | exact Hmod ]).
    pose proof (Nat.mod_upper_bound k (ord p a) ltac:(lia)); lia.
Qed.

Lemma ord_div_pm1 : forall p a, prime (Z.of_nat p) -> 1 <= a <= p - 1 ->
  Nat.divide (ord p a) (p - 1).
Proof.
  intros p a Hp Ha; apply ord_divides; [ assumption | assumption | ].
  unfold pw; apply fermat; assumption.
Qed.

(* the powers a^0, ..., a^(ord-1) are pairwise distinct mod p *)
Lemma pow_inj_below : forall p a i j, prime (Z.of_nat p) -> 1 <= a <= p - 1 ->
  i < ord p a -> j < ord p a -> pw p a i = pw p a j -> i = j.
Proof.
  intros p a i j Hp Ha Hi Hj Heq.
  assert (Ha' : ~ Nat.divide p a) by (apply unit_not_div; exact Ha).
  destruct (le_gt_dec i j) as [Hle|Hgt].
  - assert (H1 : pw p a (j - i) = 1) by (apply pw_cancel; assumption).
    destruct (Nat.eq_dec (j - i) 0) as [E|E]; [ lia | ].
    exfalso; assert (ord p a <= j - i) by (apply ord_least; [ assumption | assumption | lia | exact H1 ]); lia.
  - assert (H1 : pw p a (i - j) = 1) by (apply pw_cancel; [ assumption | assumption | lia | symmetry; exact Heq ]).
    destruct (Nat.eq_dec (i - j) 0) as [E|E]; [ lia | ].
    exfalso; assert (ord p a <= i - j) by (apply ord_least; [ assumption | assumption | lia | exact H1 ]); lia.
Qed.

Print Assumptions ord_div_pm1.

(* ================================================================= *)
(*  END ZmodOrder.v  (Phase 4a)                                      *)
(*  Multiplicative order mod p: leastness (ord_least), divisibility    *)
(*  (ord_divides, ord_div_pm1), and distinctness of the powers below   *)
(*  the order (pow_inj_below).  Axiom-free.  Feeds the order-counting   *)
(*  primitive-root proof (Phase 4b).                                  *)
(* ================================================================= *)
