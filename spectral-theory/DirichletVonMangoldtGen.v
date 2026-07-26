(* ================================================================= *)
(*  DirichletVonMangoldtGen.v                                        *)
(*                                                                    *)
(*  THE GENERAL VON MANGOLDT IDENTITY, fully proven:                  *)
(*        ∏_{d ∣ n} vexp(d) = n     (n ≥ 1).                         *)
(*                                                                    *)
(*  Proof by `mult_ind` (DirichletPeel): the case n = p^v · m         *)
(*  (p prime, p ∤ m) uses the coprime divisor bijection to split the  *)
(*  product, `vexp_ppow` (vexp(p^i)=p) and `vexp_coprime`             *)
(*  (vexp(p^i·b)=1 for b ≥ 2 coprime) to evaluate each factor.        *)
(*  AXIOM-FREE.                                                       *)
(* ================================================================= *)

From Stdlib Require Import ZArith Znumtheory Arith Lia List Permutation.
Import ListNotations.
Require Import Totient JacobiRHS DirichletMult DirichletVonMangoldt
        DirichletVexpSem DirichletVexpCoprime DirichletPeel.
Open Scope nat_scope.

(* ================================================================= *)
(*  product toolkit                                                   *)
(* ================================================================= *)
(* product over a list of pairs (list_prod lands in list (nat*nat)) *)
Definition prodp (l : list (nat * nat)) (f : nat * nat -> nat) : nat :=
  fold_right (fun k acc => f k * acc) 1 l.

Lemma prodp_cons : forall a l f, prodp (a :: l) f = f a * prodp l f. Proof. reflexivity. Qed.

Lemma prodp_app : forall l1 l2 f, prodp (l1 ++ l2) f = prodp l1 f * prodp l2 f.
Proof.
  intros l1 l2 f; induction l1 as [|a l1 IH]; [ simpl; ring | ].
  rewrite <- app_comm_cons, !prodp_cons, IH; ring.
Qed.

Lemma prodf_map_pair : forall (L : list (nat * nat)) g f,
  prodf (map g L) f = prodp L (fun ab => f (g ab)).
Proof.
  intros L g f; induction L as [|a L IH]; [ reflexivity | ].
  cbn [map]; rewrite prodf_cons, prodp_cons, IH; reflexivity.
Qed.

Lemma prodp_map_from_nat : forall (l : list nat) (k : nat -> nat * nat) h,
  prodp (map k l) h = prodf l (fun x => h (k x)).
Proof.
  intros l k h; induction l as [|a l IH]; [ reflexivity | ].
  cbn [map]; rewrite prodp_cons, prodf_cons, IH; reflexivity.
Qed.

Lemma prodp_list_prod : forall (l1 l2 : list nat) h,
  prodp (list_prod l1 l2) h = prodf l1 (fun a => prodf l2 (fun b => h (a, b))).
Proof.
  intros l1 l2 h; induction l1 as [|a l1 IH]; [ reflexivity | ].
  simpl list_prod; rewrite prodp_app, prodp_map_from_nat, prodf_cons, IH; reflexivity.
Qed.

Lemma prodf_single_nz : forall (l : list nat) m h, NoDup l -> In m l ->
  (forall b, In b l -> b <> m -> h b = 1) -> prodf l h = h m.
Proof.
  induction l as [|a l IH]; intros m h Hnd Hin Hz; [ inversion Hin | ].
  rewrite prodf_cons; inversion Hnd as [|x xs Hna Hnd']; subst.
  destruct (Nat.eq_dec a m) as [->|Hne].
  - rewrite (prodf_ext l h (fun _ => 1)).
    + rewrite prodf_const, Nat.pow_1_l, Nat.mul_1_r; reflexivity.
    + intros b Hb; apply Hz; [ right; exact Hb | intro Heq; subst; contradiction ].
  - destruct Hin as [->|Hin]; [ contradiction | ].
    rewrite (Hz a (or_introl eq_refl) Hne), (IH m h Hnd' Hin);
      [ ring | intros b Hb Hbm; apply Hz; [ right; exact Hb | exact Hbm ] ].
Qed.

(* ================================================================= *)
(*  a prime power is coprime to a number the prime does not divide    *)
(* ================================================================= *)
Lemma gcd_ppow_coprime : forall p v m, prime (Z.of_nat p) -> ~ Nat.divide p m -> Nat.gcd (p ^ v) m = 1.
Proof.
  intros p v m Hp Hpm.
  destruct (div_prime_pow p v (Nat.gcd (p ^ v) m) Hp (Nat.gcd_divide_l _ _)) as [j [Hj Hg]].
  destruct j as [|j'].
  - simpl in Hg; exact Hg.
  - exfalso; apply Hpm; apply (Nat.divide_trans p (Nat.gcd (p ^ v) m) m).
    + rewrite Hg; exists (p ^ j'); simpl; ring.
    + apply Nat.gcd_divide_r.
Qed.

(* ================================================================= *)
(*  ∏_{b∣m} vexp(p^j · b) = p   for 1 ≤ j ≤ v, p ∤ m                 *)
(* ================================================================= *)
Lemma inner_prod : forall p j v m, prime (Z.of_nat p) -> ~ Nat.divide p m ->
  1 <= j -> j <= v -> 1 <= m -> prodf (divisors m) (fun b => vexp (p ^ j * b)) = p.
Proof.
  intros p j v m Hp Hpm Hj Hjv Hm.
  assert (Hp2 : 2 <= p) by (pose proof (prime_ge_2 _ Hp); lia).
  assert (Hgc : Nat.gcd (p ^ v) m = 1) by (apply gcd_ppow_coprime; assumption).
  rewrite (prodf_single_nz (divisors m) 1 (fun b => vexp (p ^ j * b))).
  - rewrite Nat.mul_1_r; apply vexp_ppow; [ exact Hp | exact Hj ].
  - apply divisors_nodup.
  - apply in_divisors; split; [ lia | apply Nat.mod_1_r ].
  - intros b Hb Hb1; apply in_divisors in Hb; destruct Hb as [[Hb1' Hbm] Hbmod].
    apply Nat.Lcm0.mod_divide in Hbmod.
    apply vexp_coprime.
    + apply (gcd_of_div (p ^ v) m); [ exact Hgc | | exact Hbmod ].
      exists (p ^ (v - j)); replace v with ((v - j) + j) at 1 by lia; rewrite Nat.pow_add_r; ring.
    + apply Nat.le_trans with (p ^ 1);
        [ rewrite Nat.pow_1_r; lia | apply Nat.pow_le_mono_r; lia ].
    + lia.
Qed.

(* ================================================================= *)
(*  the multiplicative step and the general identity                  *)
(* ================================================================= *)
Lemma vmprod_step : forall p v m, prime (Z.of_nat p) -> ~ Nat.divide p m ->
  1 <= v -> 1 <= m -> vmprod m = m -> vmprod (p ^ v * m) = p ^ v * m.
Proof.
  intros p v m Hp Hpm Hv Hm HIH.
  assert (Hp2 : 2 <= p) by (pose proof (prime_ge_2 _ Hp); lia).
  assert (Hgc : Nat.gcd (p ^ v) m = 1) by (apply gcd_ppow_coprime; assumption).
  assert (Hpv1 : 1 <= p ^ v) by (apply Nat.neq_0_lt_0, Nat.pow_nonzero; lia).
  unfold vmprod.
  rewrite (prodf_perm _ _ vexp (divisors_mul_perm (p ^ v) m Hgc Hpv1 Hm)).
  rewrite (prodf_map_pair (list_prod (divisors (p ^ v)) (divisors m)) (fun ab => fst ab * snd ab) vexp).
  rewrite prodp_list_prod.
  transitivity (prodf (divisors (p ^ v)) (fun a => prodf (divisors m) (fun b => vexp (a * b)))).
  { apply prodf_ext; intros a _; apply prodf_ext; intros b _; cbn [fst snd]; reflexivity. }
  rewrite (prodf_perm _ _ _ (divisors_prime_pow p v Hp)), prodf_map.
  change (seq 0 (S v)) with (0 :: seq 1 v); rewrite prodf_cons.
  replace (prodf (divisors m) (fun b => vexp (p ^ 0 * b))) with m.
  2:{ symmetry; transitivity (vmprod m).
      - unfold vmprod; apply prodf_ext; intros b _; rewrite Nat.pow_0_r, Nat.mul_1_l; reflexivity.
      - exact HIH. }
  rewrite (prodf_ext (seq 1 v) _ (fun _ => p)).
  2:{ intros j Hj; apply in_seq in Hj; apply (inner_prod p j v m Hp Hpm); lia. }
  rewrite prodf_const, length_seq; ring.
Qed.

Theorem vonmangoldt : forall n, 1 <= n -> vmprod n = n.
Proof.
  apply mult_ind.
  - reflexivity.
  - intros p v m Hp Hpm Hv Hm HIH; apply (vmprod_step p v m Hp Hpm Hv Hm HIH).
Qed.

Print Assumptions vonmangoldt.

(* ================================================================= *)
(*  END DirichletVonMangoldtGen.v                                    *)
(*  ∏_{d∣n} vexp(d) = n, fully proven for all n ≥ 1 (the von          *)
(*  Mangoldt identity, exp form).  Closed under the global context.   *)
(* ================================================================= *)
