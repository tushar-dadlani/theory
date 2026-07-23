(* ================================================================= *)
(*  PolyRootsFp.v                                                    *)
(*                                                                    *)
(*  PHASE 3 of the Dirichlet-mod-p build: the field-theoretic heart.  *)
(*  A degree-d polynomial over F_p has at most d roots, hence          *)
(*                                                                    *)
(*     dth_roots_bound :  #{ a in [1,p-1] : a^d mod p = 1 }  <=  d.    *)
(*                                                                    *)
(*  Minimal polynomial theory over Z (little-endian coefficient        *)
(*  lists), synthetic division (sdiv, Ruffini's rule, exact over Z),   *)
(*  the factor theorem mod p, and the Lagrange roots bound by strong    *)
(*  induction on the degree, using that F_p is an integral domain      *)
(*  (prime_mult).  Invariant: nonzero leading coefficient.            *)
(*                                                                    *)
(*  Axiom-free: constructive Z/nat + Znumtheory (no classical logic).  *)
(* ================================================================= *)

From Stdlib Require Import ZArith Znumtheory Arith Lia List Bool.
Import ListNotations.
Open Scope Z_scope.

Fixpoint peval (P : list Z) (x : Z) : Z :=
  match P with [] => 0 | a :: P' => a + x * peval P' x end.

Fixpoint sdiv (P : list Z) (r : Z) : list Z :=
  match P with
  | [] => []
  | a :: P' => match P' with [] => [] | _ => peval P' r :: sdiv P' r end
  end.

Lemma sdiv_spec : forall P r x,
  peval P x = peval P r + (x - r) * peval (sdiv P r) x.
Proof.
  induction P as [|a P' IH]; intros r x.
  - simpl; ring.
  - destruct P' as [|b P''].
    + simpl; ring.
    + change (peval (a :: b :: P'') x) with (a + x * peval (b :: P'') x).
      change (peval (a :: b :: P'') r) with (a + r * peval (b :: P'') r).
      change (sdiv (a :: b :: P'') r) with (peval (b :: P'') r :: sdiv (b :: P'') r).
      change (peval (peval (b :: P'') r :: sdiv (b :: P'') r) x)
        with (peval (b :: P'') r + x * peval (sdiv (b :: P'') r) x).
      rewrite (IH r x); ring.
Qed.

Lemma sdiv_len : forall P r, length (sdiv P r) = pred (length P).
Proof.
  induction P as [|a P' IH]; intro r; [ reflexivity | ].
  destruct P' as [|b P'']; [ reflexivity | ].
  specialize (IH r).
  change (sdiv (a :: b :: P'') r) with (peval (b :: P'') r :: sdiv (b :: P'') r).
  simpl length in *; lia.
Qed.

Lemma last_cons : forall (a : Z) l d, l <> [] -> last (a :: l) d = last l d.
Proof. intros a l d Hl; destruct l; [ contradiction | reflexivity ]. Qed.

Lemma sdiv_lead : forall P r, (2 <= length P)%nat -> last (sdiv P r) 0 = last P 0.
Proof.
  induction P as [|a P' IH]; intros r Hlen; [ simpl in Hlen; lia | ].
  destruct P' as [|b P'']; [ simpl in Hlen; lia | ].
  change (sdiv (a :: b :: P'') r) with (peval (b :: P'') r :: sdiv (b :: P'') r).
  destruct P'' as [|c P'''].
  - simpl; ring.
  - rewrite last_cons.
    + rewrite (IH r) by (simpl; lia); rewrite last_cons by discriminate; reflexivity.
    + change (sdiv (b :: c :: P''') r) with (peval (c :: P''') r :: sdiv (c :: P''') r);
        discriminate.
Qed.

Lemma factor_mod : forall p P r, p <> 0 -> peval P r mod p = 0 ->
  forall x, (peval P x) mod p = ((x - r) * peval (sdiv P r) x) mod p.
Proof.
  intros p P r Hp Hr x.
  rewrite (sdiv_spec P r x), Zplus_mod, Hr, Z.add_0_l, Zmod_mod; reflexivity.
Qed.

Lemma filter_none : forall (P : Z -> bool) (l : list Z),
  (forall x, P x = false) -> filter P l = [].
Proof. intros P l H; induction l as [|a l IH]; simpl; [ reflexivity | rewrite H; exact IH ]. Qed.

(* ----------------------------------------------------------------- *)
(*  THE ROOTS BOUND  (Lagrange)                                      *)
(* ----------------------------------------------------------------- *)

Lemma roots_le : forall p, prime (Z.of_nat p) -> forall n P cand,
  NoDup cand -> (forall x, In x cand -> 0 <= x < Z.of_nat p) ->
  (length P <= S n)%nat -> last P 0 mod Z.of_nat p <> 0 ->
  (length (filter (fun x => ((peval P x) mod Z.of_nat p =? 0)%Z) cand) <= n)%nat.
Proof.
  intros p Hp.
  assert (Hq0 : Z.of_nat p <> 0) by (destruct Hp; lia).
  induction n as [|m IH]; intros P cand Hnd Hcand Hlen Hlast.
  - destruct P as [|a [|b P1]]; [ exfalso; apply Hlast; apply Zmod_0_l | | simpl in Hlen; lia ].
    simpl in Hlast.
    assert (Hnone : filter (fun x => ((peval [a] x) mod Z.of_nat p =? 0)%Z) cand = []).
    { apply filter_none; intro x; apply Z.eqb_neq.
      replace (peval [a] x) with a by (simpl; ring); exact Hlast. }
    rewrite Hnone; apply Nat.le_0_l.
  - remember (filter (fun x => ((peval P x) mod Z.of_nat p =? 0)%Z) cand) as L eqn:HL.
    destruct L as [|r rest]; [ simpl; apply Nat.le_0_l | ].
    assert (Hr : In r (filter (fun x => ((peval P x) mod Z.of_nat p =? 0)%Z) cand))
      by (rewrite <- HL; left; reflexivity).
    apply filter_In in Hr; destruct Hr as [Hrcand Hrroot]; apply Z.eqb_eq in Hrroot.
    assert (Hlen2 : (2 <= length P)%nat).
    { destruct P as [|a [|b P1]].
      - exfalso; apply Hlast; apply Zmod_0_l.
      - exfalso; simpl in Hlast; replace (peval [a] r) with a in Hrroot by (simpl; ring);
          apply Hlast; exact Hrroot.
      - simpl; lia. }
    rewrite HL.
    apply Nat.le_trans with
      (length (r :: filter (fun x => ((peval (sdiv P r) x) mod Z.of_nat p =? 0)%Z) cand)).
    + apply NoDup_incl_length; [ apply NoDup_filter; exact Hnd | ].
      intros x Hx; apply filter_In in Hx; destruct Hx as [Hxcand Hxroot]; apply Z.eqb_eq in Hxroot.
      rewrite (factor_mod (Z.of_nat p) P r Hq0 Hrroot x) in Hxroot.
      apply Z.mod_divide in Hxroot; [ | exact Hq0 ].
      destruct (prime_mult (Z.of_nat p) Hp _ _ Hxroot) as [Hd|Hd].
      * left; destruct Hd as [k Hk];
          pose proof (Hcand x Hxcand); pose proof (Hcand r Hrcand);
          assert (k = 0) by (destruct (Z.lt_trichotomy k 0) as [?|[?|?]];
            [ exfalso; nia | assumption | exfalso; nia ]);
          subst k; lia.
      * right; apply filter_In; split;
          [ exact Hxcand | apply Z.eqb_eq, (proj2 (Z.mod_divide _ (Z.of_nat p) Hq0)); exact Hd ].
    + simpl length; apply le_n_S.
      apply (IH (sdiv P r) cand Hnd Hcand);
        [ rewrite sdiv_len; lia | rewrite sdiv_lead by exact Hlen2; exact Hlast ].
Qed.

(* ----------------------------------------------------------------- *)
(*  The polynomial X^d - 1                                           *)
(* ----------------------------------------------------------------- *)

Lemma peval_monomial : forall k x, peval (repeat 0 k ++ [1]) x = x ^ (Z.of_nat k).
Proof.
  induction k as [|k IH]; intro x.
  - cbn [repeat app peval]; change (Z.of_nat 0) with 0%Z; rewrite Z.pow_0_r; ring.
  - change (repeat 0 (S k) ++ [1]) with (0 :: (repeat 0 k ++ [1])).
    change (peval (0 :: (repeat 0 k ++ [1])) x) with (0 + x * peval (repeat 0 k ++ [1]) x).
    rewrite IH, Nat2Z.inj_succ, Z.pow_succ_r by lia; ring.
Qed.

Definition xdm1 (d : nat) : list Z := (-1) :: (repeat 0 (d - 1) ++ [1]).

Lemma peval_xdm1 : forall d x, (1 <= d)%nat -> peval (xdm1 d) x = x ^ (Z.of_nat d) - 1.
Proof.
  intros d x Hd; unfold xdm1.
  change (peval ((-1) :: (repeat 0 (d - 1) ++ [1])) x)
    with (-1 + x * peval (repeat 0 (d - 1) ++ [1]) x).
  rewrite peval_monomial.
  replace (Z.of_nat d) with (Z.succ (Z.of_nat (d - 1))) by lia.
  rewrite Z.pow_succ_r by lia; ring.
Qed.

Lemma len_xdm1 : forall d, (1 <= d)%nat -> length (xdm1 d) = S d.
Proof.
  intros d Hd; unfold xdm1; simpl length; rewrite length_app, repeat_length; simpl; lia.
Qed.

Lemma last_xdm1 : forall d, last (xdm1 d) 0 = 1.
Proof.
  intro d; unfold xdm1; rewrite last_cons.
  - rewrite last_last; reflexivity.
  - destruct (d - 1)%nat; simpl; discriminate.
Qed.

(* ----------------------------------------------------------------- *)
(*  nat <-> Z bridge                                                 *)
(* ----------------------------------------------------------------- *)

Lemma NoDup_map_inj : forall (A B : Type) (f : A -> B) (l : list A),
  (forall x y, In x l -> In y l -> f x = f y -> x = y) -> NoDup l -> NoDup (map f l).
Proof.
  intros A B f l; induction l as [|a l IH]; intros Hinj Hnd; simpl; [ constructor | ].
  rewrite NoDup_cons_iff in Hnd; destruct Hnd as [Hna Hnd].
  rewrite NoDup_cons_iff; split.
  - intro Hin; apply in_map_iff in Hin; destruct Hin as [y [Hfy Hy]].
    assert (a = y) by (apply Hinj; [ left; reflexivity | right; exact Hy | symmetry; exact Hfy ]).
    subst y; contradiction.
  - apply IH; [ intros x y Hx Hy; apply Hinj; right; assumption | exact Hnd ].
Qed.

Lemma length_filter_map : forall (f : nat -> Z) (g : Z -> bool) (l : list nat),
  length (filter g (map f l)) = length (filter (fun a => g (f a)) l).
Proof.
  intros f g l; induction l as [|a l IH]; simpl; [ reflexivity | ].
  destruct (g (f a)); simpl; rewrite IH; reflexivity.
Qed.

Lemma mod_pred_nat : forall X p, (1 <= X)%nat -> (2 <= p)%nat ->
  ((X - 1) mod p = 0 <-> X mod p = 1)%nat.
Proof.
  intros X p HX Hp; split; intro Hh.
  - apply Nat.Lcm0.mod_divide in Hh; destruct Hh as [k Hk].
    assert (HX2 : (X = 1 + k * p)%nat) by lia.
    rewrite HX2, Nat.Div0.mod_add, Nat.mod_small by lia; reflexivity.
  - apply (proj2 (Nat.Lcm0.mod_divide (X - 1) p)); exists (X / p)%nat.
    pose proof (Nat.div_mod_eq X p); nia.
Qed.

Theorem dth_roots_bound : forall p d, prime (Z.of_nat p) -> (1 <= d)%nat ->
  (length (filter (fun a => ((a ^ d) mod p =? 1)%nat) (seq 1 (p - 1))) <= d)%nat.
Proof.
  intros p d Hp Hd.
  assert (Hp2 : (2 <= p)%nat) by (destruct Hp; lia).
  apply Nat.le_trans with
    (length (filter (fun x => ((peval (xdm1 d) x) mod Z.of_nat p =? 0)%Z)
                    (map Z.of_nat (seq 1 (p - 1))))).
  - rewrite length_filter_map.
    rewrite (filter_ext_in
      (fun a => ((peval (xdm1 d) (Z.of_nat a)) mod Z.of_nat p =? 0)%Z)
      (fun a => ((a ^ d) mod p =? 1)%nat) (seq 1 (p - 1))).
    + apply Nat.le_refl.
    + intros a Ha; apply in_seq in Ha.
      assert (Ha1 : (1 <= a ^ d)%nat)
        by (rewrite <- (Nat.pow_1_l d); apply Nat.pow_le_mono_l; lia).
      apply Bool.eq_iff_eq_true; rewrite Z.eqb_eq, Nat.eqb_eq.
      rewrite peval_xdm1 by exact Hd; rewrite <- Nat2Z.inj_pow.
      replace (Z.of_nat (a ^ d) - 1)%Z with (Z.of_nat (a ^ d - 1))
        by (rewrite Nat2Z.inj_sub by exact Ha1; reflexivity).
      rewrite <- Nat2Z.inj_mod.
      rewrite <- (mod_pred_nat (a ^ d) p Ha1 Hp2).
      split; intro HH; lia.
  - apply (roots_le p Hp d (xdm1 d) (map Z.of_nat (seq 1 (p - 1)))).
    + apply NoDup_map_inj; [ intros x y _ _ E; apply Nat2Z.inj; exact E | apply seq_NoDup ].
    + intros x Hx; apply in_map_iff in Hx as [a [Hxa Hain]]; apply in_seq in Hain.
      rewrite <- Hxa; lia.
    + rewrite len_xdm1 by exact Hd; lia.
    + rewrite last_xdm1; simpl; rewrite Z.mod_1_l by lia; discriminate.
Qed.

Print Assumptions dth_roots_bound.

(* ================================================================= *)
(*  END PolyRootsFp.v  (Phase 3)                                     *)
(*  A degree-d polynomial over F_p has <= d roots (roots_le), hence    *)
(*  x^d = 1 has <= d solutions mod p (dth_roots_bound).  Axiom-free.   *)
(*  Feeds the order-counting primitive-root proof (Phase 4).          *)
(* ================================================================= *)
