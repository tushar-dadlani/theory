(* ================================================================= *)
(*  MobiusINFSeam.v  —  the INFProduct <-> DirichletConv seam.          *)
(*                                                                    *)
(*  The n-fold sign monoid {I,N,F}^n (INFProduct) is the F-free /       *)
(*  squarefree truncation of the Mobius function of DirichletConv:      *)
(*  for a smooth number  s = prod_i p_i^{k_i}  (distinct primes p_i),   *)
(*                                                                    *)
(*      DirichletConv.mu s  =  val_n (map sym_of [k_1;...;k_n])         *)
(*                          =  prod_i mu_pp(k_i).                       *)
(*                                                                    *)
(*  So one F (a repeated prime, k_i >= 2) sends both sides to 0 -- the  *)
(*  squarefree veto -- and the {I,N} part is exactly mu on squarefree   *)
(*  smooth numbers.  This ties INFProduct.val_n_mu to the genuine       *)
(*  Mobius function via DirichletMult multiplicativity + mu on prime    *)
(*  powers (DirichletPPow).  Axiom-free.                               *)
(* ================================================================= *)

From Stdlib Require Import Arith Lia List ZArith Znumtheory.
Require Import ZmodPStar DirichletVonMangoldtGen DirichletConv DirichletMult
        DirichletPPow MobiusReciprocal INFMonoid INFProduct.
Import ListNotations.
Open Scope nat_scope.

(* the smooth number  prod_i (p_i)^{k_i}  from a list of (prime,exponent) *)
Definition smooth (pks : list (nat * nat)) : nat :=
  fold_right (fun pk acc => (fst pk) ^ (snd pk) * acc) 1 pks.

(* ---- the atomic seam:  mu(p^k) = mu_pp k  for all k ---- *)
Lemma mu_ppow_eq_mu_pp : forall p k, prime (Z.of_nat p) -> mu (p ^ k) = mu_pp k.
Proof.
  intros p k Hp; destruct k as [|[|k]].
  - change (p ^ 0) with 1; change (mu_pp 0) with 1%Z; apply mu_1.
  - rewrite Nat.pow_1_r, (mu_p p Hp); reflexivity.
  - rewrite (mu_ppow_ge2 p (S (S k)) Hp ltac:(lia)); reflexivity.
Qed.

(* ---- prime divides a prime power only through its base ---- *)
Lemma prime_div_ppow : forall p q e,
  prime (Z.of_nat p) -> Nat.divide p (q ^ e) -> Nat.divide p q.
Proof.
  intros p q e Hp; induction e as [|e IH]; simpl; intro Hdiv.
  - apply Nat.divide_1_r in Hdiv; subst p.
    pose proof (prime_ge_2 _ Hp); lia.
  - destruct (prime_mult_nat p q (q ^ e) Hp Hdiv) as [H | H]; [ exact H | apply IH; exact H ].
Qed.

(* ---- a prime distinct from the base primes does not divide the smooth number ---- *)
Lemma not_div_smooth : forall p pks,
  prime (Z.of_nat p) ->
  Forall (fun pk => prime (Z.of_nat (fst pk))) pks ->
  ~ In p (map fst pks) ->
  ~ Nat.divide p (smooth pks).
Proof.
  intros p pks Hp; induction pks as [|[q e] pks IH]; intros HF Hnin Hdiv.
  - change (smooth []) with 1 in Hdiv.
    apply Nat.divide_1_r in Hdiv; subst p; pose proof (prime_ge_2 _ Hp); lia.
  - change (smooth ((q, e) :: pks)) with (q ^ e * smooth pks) in Hdiv.
    destruct (prime_mult_nat p (q ^ e) (smooth pks) Hp Hdiv) as [Hq | Hrest].
    + apply (prime_div_ppow p q e Hp) in Hq.
      pose proof (Forall_inv HF) as Hqp; simpl in Hqp.
      assert (HZ : (Z.of_nat p | Z.of_nat q)%Z)
        by (destruct Hq as [c Hc]; exists (Z.of_nat c); rewrite Hc, Nat2Z.inj_mul; reflexivity).
      apply (prime_div_prime _ _ Hp Hqp) in HZ; apply Nat2Z.inj in HZ.
      apply Hnin; simpl; left; exact (eq_sym HZ).
    + apply (IH (Forall_inv_tail HF));
        [ intro H; apply Hnin; simpl; right; exact H | exact Hrest ].
Qed.

Lemma smooth_pos : forall pks,
  Forall (fun pk => prime (Z.of_nat (fst pk))) pks -> 1 <= smooth pks.
Proof.
  induction pks as [|[p k] pks IH]; intro HF; simpl; [ lia | ].
  pose proof (ppow_pos p k (Forall_inv HF)) as Hpk.
  pose proof (IH (Forall_inv_tail HF)) as Hs.
  apply Nat.le_trans with (1 * 1); [ lia | apply Nat.mul_le_mono; assumption ].
Qed.

(* ---- the product seam:  mu(smooth pks) = prod_i mu_pp(k_i) ---- *)
Theorem mu_smooth_eq : forall pks,
  Forall (fun pk => prime (Z.of_nat (fst pk))) pks -> NoDup (map fst pks) ->
  mu (smooth pks) = fold_right (fun pk acc => (mu_pp (snd pk) * acc)%Z) 1%Z pks.
Proof.
  induction pks as [|[p k] pks IH]; intros HF Hnd; simpl; [ apply mu_1 | ].
  simpl in Hnd. inversion Hnd as [| x xs Hnin Hnd']; subst.
  assert (Hp : prime (Z.of_nat p)) by (apply (Forall_inv HF)).
  assert (Hcop : Nat.gcd (p ^ k) (smooth pks) = 1)
    by (apply gcd_ppow_coprime;
        [ exact Hp | apply not_div_smooth; [ exact Hp | apply (Forall_inv_tail HF) | exact Hnin ] ]).
  rewrite (mu_mult_prod (p ^ k) (smooth pks) (ppow_pos p k Hp)
             (smooth_pos pks (Forall_inv_tail HF)) Hcop).
  rewrite (mu_ppow_eq_mu_pp p k Hp), (IH (Forall_inv_tail HF) Hnd'); reflexivity.
Qed.

(* ---- THE SEAM:  mu of a smooth number = val_n of the exponent word ---- *)
Theorem mu_smooth_val_n : forall pks,
  Forall (fun pk => prime (Z.of_nat (fst pk))) pks -> NoDup (map fst pks) ->
  mu (smooth pks) = val_n (map sym_of (map snd pks)).
Proof.
  intros pks HF Hnd. rewrite (mu_smooth_eq pks HF Hnd), val_n_mu, map_map.
  clear HF Hnd. induction pks as [|[p k] pks IH]; simpl; [ reflexivity | rewrite IH; reflexivity ].
Qed.

Print Assumptions mu_smooth_val_n.

(* ================================================================= *)
(*  END MobiusINFSeam.v  (the {I,N,F}^n word IS mu of the smooth        *)
(*  number it encodes; one F = squarefree veto = mu vanishing.)         *)
(* ================================================================= *)
