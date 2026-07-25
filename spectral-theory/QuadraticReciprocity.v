(* ================================================================= *)
(*  QuadraticReciprocity.v                                           *)
(*                                                                    *)
(*  THE LAW OF QUADRATIC RECIPROCITY:  for distinct odd primes p, q,  *)
(*                                                                    *)
(*      (q/p) * (p/q) = (-1)^( ((p-1)/2) * ((q-1)/2) ).              *)
(*                                                                    *)
(*  Assembled from Eisenstein's refinement (a/p) = (-1)^(sum          *)
(*  floor(k*a/p)) applied in both directions, and the lattice-point   *)
(*  count sum floor(k*q/p) + sum floor(k*p/q) = ((p-1)/2)((q-1)/2).   *)
(*  AXIOM-FREE.                                                       *)
(* ================================================================= *)

From Stdlib Require Import ZArith Znumtheory Arith Lia List.
Require Import ZmodPStar ZmodOrder LegendreSymbol GaussLemma EisensteinLemma ReciprocityCount.
Open Scope nat_scope.

(* distinct primes do not divide each other *)
Lemma distinct_primes_ndvd : forall p q,
  prime (Z.of_nat p) -> prime (Z.of_nat q) -> p <> q -> ~ Nat.divide p q.
Proof.
  intros p q Hp Hq Hpq Hd.
  pose proof (prime_ge_2 _ Hp); pose proof (prime_ge_2 _ Hq).
  apply Hpq; apply Nat2Z.inj.
  assert (Hdz : (Z.of_nat p | Z.of_nat q))
    by (destruct Hd as [c Hc]; exists (Z.of_nat c); rewrite Hc, Nat2Z.inj_mul; ring).
  destruct (prime_divisors (Z.of_nat q) Hq (Z.of_nat p) Hdz) as [E|[E|[E|E]]]; lia.
Qed.

(* ================================================================= *)
(*  THE MAIN THEOREM                                                 *)
(* ================================================================= *)

Theorem quadratic_reciprocity : forall p q,
  prime (Z.of_nat p) -> prime (Z.of_nat q) -> p <> q ->
  p mod 2 = 1 -> q mod 2 = 1 ->
  (legendre p q * legendre q p)%Z = ((-1) ^ Z.of_nat (hlf p * hlf q))%Z.
Proof.
  intros p q Hp Hq Hpq Hpo Hqo.
  assert (Hnpq : ~ Nat.divide p q) by (apply distinct_primes_ndvd; assumption).
  assert (Hnqp : ~ Nat.divide q p)
    by (apply distinct_primes_ndvd; [ exact Hq | exact Hp | intro E; apply Hpq; symmetry; exact E ]).
  rewrite (legendre_eisenstein p q Hp Hpo Hnpq Hqo).
  rewrite (legendre_eisenstein q p Hq Hqo Hnqp Hpo).
  (* Tsum p q = fsum p q  (definitionally) *)
  change (Tsum p q) with (fsum p q); change (Tsum q p) with (fsum q p).
  rewrite <- Z.pow_add_r by lia.
  rewrite <- Nat2Z.inj_add, (reciprocity_count p q Hp Hq Hpq Hpo Hqo).
  reflexivity.
Qed.

Print Assumptions quadratic_reciprocity.

(* ================================================================= *)
(*  THE FIRST SUPPLEMENT:  (-1/p) = (-1)^((p-1)/2)                   *)
(* ================================================================= *)

(* congruent bases give congruent powers *)
Lemma Zpow_mod_cong : forall a b n m,
  (a mod n = b mod n)%Z -> (a ^ Z.of_nat m mod n = b ^ Z.of_nat m mod n)%Z.
Proof.
  intros a b n m H; induction m as [|m IH]; [ reflexivity | ].
  rewrite Nat2Z.inj_succ, !Z.pow_succ_r by lia.
  rewrite Zmult_mod, H, IH, <- Zmult_mod; reflexivity.
Qed.

Theorem first_supplement : forall p, prime (Z.of_nat p) -> p mod 2 = 1 ->
  legendre p (p - 1) = ((-1) ^ Z.of_nat (hlf p))%Z.
Proof.
  intros p Hp Hpo.
  assert (Hp3 : 3 <= p)
    by (destruct (Nat.eq_dec p 2) as [->|Hne]; [ discriminate Hpo | pose proof (prime_ge_2 _ Hp); lia ]).
  assert (Hnd : ~ Nat.divide p (p - 1)) by (apply unit_not_div; lia).
  apply (sign_mod_inj p _ _ Hp3).
  - apply legendre_pm1; exact Hnd.
  - apply (neg1_pow_pm1 p Hpo).
  - rewrite <- (legendre_euler p (p - 1) Hp Hpo Hnd).
    unfold pw; rewrite Nat2Z.inj_mod, Zmod_mod, Nat2Z.inj_pow, Nat2Z.inj_sub by lia.
    apply (Zpow_mod_cong _ _ _ (hlf p)).
    rewrite <- (Z_mod_plus_full (-1) 1 (Z.of_nat p)); f_equal; lia.
Qed.

(* ================================================================= *)
(*  THE SECOND SUPPLEMENT:  (2/p) = (-1)^((p^2-1)/8)                 *)
(* ================================================================= *)

(* for a = 2, every k in [1,(p-1)/2] has (k*2) mod p = 2*k *)
Lemma res_two : forall p k, p mod 2 = 1 -> 2 <= p -> 1 <= k <= hlf p ->
  res p 2 k = 2 * k.
Proof.
  intros p k Hpo Hp2 Hk; unfold res.
  pose proof (two_hlf p Hpo Hp2) as HH.
  rewrite Nat.mul_comm; apply Nat.mod_small; lia.
Qed.

(* the Gauss count for a = 2:  mu p 2 = (p-1)/2 - ((p-1)/2)/2 *)
Lemma mu_two : forall p, prime (Z.of_nat p) -> p mod 2 = 1 ->
  mu p 2 = hlf p - (hlf p) / 2.
Proof.
  intros p Hp Hpo.
  assert (Hp2 : 2 <= p) by (pose proof (prime_ge_2 _ Hp); lia).
  pose proof (two_hlf p Hpo Hp2) as HH.
  unfold mu.
  rewrite (filter_ext_in nat (fun k => negb (res p 2 k <=? hlf p))
             (fun k => negb (k <=? (hlf p) / 2)) (seq 1 (hlf p))).
  - pose proof (filter_length (fun k => k <=? (hlf p) / 2) (seq 1 (hlf p))) as HL.
    rewrite count_le, length_seq in HL.
    rewrite Nat.min_l in HL by (apply Nat.Div0.div_le_upper_bound; lia).
    lia.
  - intros k Hk; apply in_seq in Hk.
    rewrite (res_two p k Hpo Hp2 ltac:(lia)); f_equal.
    apply Bool.eq_iff_eq_true; rewrite !Nat.leb_le.
    split; intro.
    + apply Nat.div_le_lower_bound; lia.
    + pose proof (Nat.Div0.mul_div_le (hlf p) 2); nia.
Qed.

(* (p^2-1)/8 = h*(h+1)/2  with h = (p-1)/2 *)
Lemma sq_over_8 : forall p, p mod 2 = 1 -> 2 <= p ->
  (p * p - 1) / 8 = (hlf p * (hlf p + 1)) / 2.
Proof.
  intros p Hpo Hp2; pose proof (two_hlf p Hpo Hp2) as HH.
  assert (Hpp : p * p - 1 = 4 * (hlf p * (hlf p + 1))) by nia.
  rewrite Hpp; change 8 with (4 * 2).
  rewrite <- Nat.Div0.div_div, (Nat.mul_comm 4 (hlf p * (hlf p + 1))), Nat.div_mul by lia.
  reflexivity.
Qed.

(* parity: mu p 2  and  (p^2-1)/8  agree mod 2 *)
(* Nat.even x is read off (2*x) mod 4 *)
Lemma even_2x : forall x, Nat.even x = ((2 * x) mod 4 =? 0).
Proof.
  intro x; destruct (Nat.even x) eqn:E.
  - apply Nat.even_spec in E; destruct E as [k Hk]; subst.
    symmetry; apply Nat.eqb_eq; replace (2 * (2 * k)) with (k * 4) by lia; apply Nat.Div0.mod_mul.
  - assert (Ho : Nat.Odd x) by (apply Nat.odd_spec; rewrite <- Nat.negb_even, E; reflexivity).
    destruct Ho as [k Hk]; subst; symmetry; apply Nat.eqb_neq.
    replace (2 * (2 * k + 1)) with (2 + k * 4) by lia.
    rewrite Nat.Div0.mod_add, (Nat.mod_small 2 4) by lia; discriminate.
Qed.

Lemma hmod4 : forall h, (h + h mod 2) mod 4 = (h * (h + 1)) mod 4.
Proof.
  intro h.
  pose proof (Nat.div_mod_eq h 4) as Hh.
  set (q := h / 4) in *; set (r := h mod 4) in *.
  assert (Hr : r < 4) by (subst r; apply Nat.mod_upper_bound; lia).
  assert (Hm2 : h mod 2 = r mod 2)
    by (rewrite Hh; replace (4*q+r) with (r + 2*q*2) by lia; rewrite Nat.Div0.mod_add; reflexivity).
  rewrite Hm2, Hh.
  rewrite (Nat.Div0.add_mod (4*q+r) (r mod 2) 4), (Nat.Div0.mul_mod (4*q+r) (4*q+r+1) 4).
  assert (E1 : (4*q+r) mod 4 = r)
    by (replace (4*q+r) with (r + q*4) by lia; rewrite Nat.Div0.mod_add, (Nat.mod_small r 4) by lia; reflexivity).
  assert (E2 : (4*q+r+1) mod 4 = (r+1) mod 4)
    by (replace (4*q+r+1) with ((r+1) + q*4) by lia; rewrite Nat.Div0.mod_add; reflexivity).
  rewrite E1, E2.
  destruct r as [|[|[|[|r']]]]; try lia; reflexivity.
Qed.

Lemma parity_h : forall h, Nat.even (h - h / 2) = Nat.even (h * (h + 1) / 2).
Proof.
  intro h.
  assert (Ha : 2 * (h - h / 2) = h + h mod 2)
    by (pose proof (Nat.div_mod_eq h 2); pose proof (Nat.mod_upper_bound h 2 ltac:(lia)); lia).
  assert (Hmod : (h * (h + 1)) mod 2 = 0).
  { destruct (Nat.Even_or_Odd h) as [[m Hm]|[m Hm]]; rewrite Hm.
    - replace (2 * m * (2 * m + 1)) with (m * (2 * m + 1) * 2) by lia; apply Nat.Div0.mod_mul.
    - replace ((2 * m + 1) * (2 * m + 1 + 1)) with ((2 * m + 1) * (m + 1) * 2) by lia;
        apply Nat.Div0.mod_mul. }
  assert (Hb : 2 * (h * (h + 1) / 2) = h * (h + 1))
    by (pose proof (Nat.div_mod_eq (h * (h + 1)) 2); lia).
  rewrite (even_2x (h - h/2)), (even_2x (h*(h+1)/2)), Ha, Hb, hmod4; reflexivity.
Qed.

Lemma mu_two_parity : forall p, prime (Z.of_nat p) -> p mod 2 = 1 ->
  Nat.even (mu p 2) = Nat.even ((p * p - 1) / 8).
Proof.
  intros p Hp Hpo.
  assert (Hp2 : 2 <= p) by (pose proof (prime_ge_2 _ Hp); lia).
  rewrite (mu_two p Hp Hpo), (sq_over_8 p Hpo Hp2); apply parity_h.
Qed.

Theorem second_supplement : forall p, prime (Z.of_nat p) -> p mod 2 = 1 ->
  legendre p 2 = ((-1) ^ Z.of_nat ((p * p - 1) / 8))%Z.
Proof.
  intros p Hp Hpo.
  assert (Hp2 : 2 <= p) by (pose proof (prime_ge_2 _ Hp); lia).
  assert (Hnd : ~ Nat.divide p 2).
  { intro Hd; pose proof (Nat.divide_pos_le p 2 ltac:(lia) Hd).
    destruct (Nat.eq_dec p 2) as [->|Hne]; [ discriminate Hpo | lia ]. }
  rewrite (legendre_gauss p 2 Hp Hpo Hnd).
  apply neg1_pow_same, mu_two_parity; assumption.
Qed.

(* ================================================================= *)
(*  END QuadraticReciprocity.v                                       *)
(*  (q/p)*(p/q) = (-1)^(((p-1)/2)((q-1)/2)) for distinct odd primes,  *)
(*  from Eisenstein's refinement + the lattice-point count.          *)
(*  Closed under the global context (axiom-free).                    *)
(* ================================================================= *)
