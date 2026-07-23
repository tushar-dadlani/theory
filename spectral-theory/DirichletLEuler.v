(* ================================================================= *)
(*  DirichletLEuler.v                                                *)
(*                                                                    *)
(*  The finite DIRICHLET L-FUNCTION and its EULER PRODUCT, built on    *)
(*  the genuine Dirichlet characters mod p (DirichletModP).           *)
(*                                                                    *)
(*  The reason an L-series factors over primes is that a Dirichlet     *)
(*  character is COMPLETELY MULTIPLICATIVE:                           *)
(*                                                                    *)
(*     chi(m n) = chi(m) chi(n)          (dchar_mul)                   *)
(*     chi(q^k) = chi(q)^k               (dchar_pow)                   *)
(*                                                                    *)
(*  -- proved here from scratch, via the discrete-log homomorphism     *)
(*  (dlog(uv) = dlog u + dlog v  mod (p-1)) and the periodicity of      *)
(*  the (p-1)-th root of unity.  This closes the "complete             *)
(*  multiplicativity" bullet that DirichletModP only advertised.       *)
(*                                                                    *)
(*  Consequences (over the custom complex field C):                   *)
(*    - LOCAL EULER FACTOR at a prime q:                              *)
(*        L_q(x) = sum_{k<K} chi(q^k) x^k = sum_{k<K} (chi(q) x)^k      *)
(*      with the geometric closed form                                *)
(*        (1 - chi(q) x) * L_q(x) = 1 - (chi(q) x)^K   (-> 1/(1-chi(q)x))*)
(*    - the finite EULER PRODUCT (multi-prime, primon-gas form ported   *)
(*      to C): the state-sum of the twisted Boltzmann weights equals    *)
(*      the PRODUCT of the local Euler factors,                        *)
(*        sum_{states} prod_q (chi(q) x_q)^{k_q}  =  prod_q L_q(x_q).   *)
(*                                                                    *)
(*  Read with x_q = q^{-s} and K -> infinity, prod_q L_q = L(s,chi) =   *)
(*  sum_n chi(n) n^{-s}: the Dirichlet L Euler product.  Assembling the *)
(*  infinite product / the state<->integer (unique-factorisation)      *)
(*  bijection stays prose; the finite identities here are proved.      *)
(*                                                                    *)
(*  Uses the classical Reals axioms (quarantined, via C / trig).      *)
(* ================================================================= *)

From Stdlib Require Import ZArith Znumtheory Arith Lia List Bool Permutation Reals.
Require Import ZmodPStar ZmodOrder PrimitiveRoot.
Require Import ComplexField RootsOfUnity DFTInversion DFTConvolution CharactersModN DirichletModP.
Import ListNotations.
Open Scope nat_scope.

(* ================================================================= *)
(*  1.  DISCRETE-LOG HOMOMORPHISM  (dlog(uv) = dlog u + dlog v mod)    *)
(* ================================================================= *)

(* firstsat over a bounded list stays inside the bound *)
Lemma firstsat_lt : forall f l n, (0 < n)%nat -> (forall x, In x l -> x < n) ->
  firstsat f l < n.
Proof.
  intros f l n Hn Hbound; induction l as [|x l IH]; cbn [firstsat].
  - exact Hn.
  - destruct (f x); [ apply Hbound; left; reflexivity | ].
    apply IH; intros y Hy; apply Hbound; right; exact Hy.
Qed.

Lemma dlog_lt : forall p g m, 2 <= p -> dlog p g m < p - 1.
Proof.
  intros p g m Hp; unfold dlog; apply firstsat_lt; [ lia | ].
  intros x Hx; apply in_seq in Hx; lia.
Qed.

(* the power map is periodic with period ord = p-1 (like Cpow_w_mod) *)
Lemma pw_mod : forall p g k, prime (Z.of_nat p) -> 1 <= g <= p - 1 -> ord p g = p - 1 ->
  pw p g k = pw p g (k mod (p - 1)).
Proof.
  intros p g k Hp Hg Hord; assert (Hp2 : 2 <= p) by (destruct Hp; lia).
  assert (Hpg : pw p g (p - 1) = 1) by (rewrite <- Hord; apply ord_period; assumption).
  rewrite (Nat.div_mod_eq k (p - 1)) at 1.
  rewrite pw_add, (pw_pow_ord_mul p g (p - 1) (k / (p - 1)) Hp2 Hpg), Nat.mul_1_l.
  unfold pw; rewrite Nat.Div0.mod_mod; reflexivity.
Qed.

(* dlog carries multiplication of units to addition mod (p-1) *)
Lemma dlog_mul : forall p g u v, prime (Z.of_nat p) -> 1 <= g <= p - 1 -> ord p g = p - 1 ->
  1 <= u <= p - 1 -> 1 <= v <= p - 1 ->
  dlog p g ((u * v) mod p) = (dlog p g u + dlog p g v) mod (p - 1).
Proof.
  intros p g u v Hp Hg Hord Hu Hv; assert (Hp2 : 2 <= p) by (destruct Hp; lia).
  (* (u*v) mod p is itself a unit *)
  assert (Hnu : ~ Nat.divide p u) by (apply unit_not_div; exact Hu).
  assert (Hnv : ~ Nat.divide p v) by (apply unit_not_div; exact Hv).
  assert (Huv : 1 <= (u * v) mod p <= p - 1).
  { split; [ | pose proof (Nat.mod_upper_bound (u * v) p ltac:(lia)); lia ].
    destruct ((u * v) mod p) eqn:E; [ | lia ].
    exfalso; assert (Hd : Nat.divide p (u * v))
      by (apply (proj1 (Nat.Lcm0.mod_divide (u * v) p)); exact E).
    destruct (prime_mult_nat p u v Hp Hd); [ apply Hnu | apply Hnv ]; assumption. }
  (* the two exponents agree after applying pw g, and both are < p-1 *)
  apply (pow_inj_below p g _ _ Hp Hg);
    [ rewrite Hord; apply dlog_lt; exact Hp2
    | rewrite Hord; apply Nat.mod_upper_bound; lia | ].
  rewrite (dlog_inv p g ((u * v) mod p) Hp Hg Hord Huv).
  rewrite <- pw_mod by assumption.
  rewrite pw_add, (dlog_inv p g u Hp Hg Hord Hu), (dlog_inv p g v Hp Hg Hord Hv).
  reflexivity.
Qed.

(* ================================================================= *)
(*  2.  COMPLETE MULTIPLICATIVITY OF THE DIRICHLET CHARACTER          *)
(* ================================================================= *)

Theorem dchar_mul : forall p g a m n,
  prime (Z.of_nat p) -> 1 <= g <= p - 1 -> ord p g = p - 1 ->
  dchar p g a (m * n) = Cmul (dchar p g a m) (dchar p g a n).
Proof.
  intros p g a m n Hp Hg Hord; assert (Hp2 : 2 <= p) by (destruct Hp; lia).
  unfold dchar.
  destruct (m mod p =? 0) eqn:Em; destruct (n mod p =? 0) eqn:En.
  - (* p | m and p | n *)
    replace ((m * n) mod p =? 0) with true; [ ring | ].
    symmetry; apply Nat.eqb_eq, (proj2 (Nat.Lcm0.mod_divide (m * n) p)).
    destruct (proj1 (Nat.Lcm0.mod_divide m p) (proj1 (Nat.eqb_eq _ _) Em)) as [c Hc].
    exists (c * n); rewrite Hc; ring.
  - (* p | m *)
    replace ((m * n) mod p =? 0) with true; [ ring | ].
    symmetry; apply Nat.eqb_eq, (proj2 (Nat.Lcm0.mod_divide (m * n) p)).
    destruct (proj1 (Nat.Lcm0.mod_divide m p) (proj1 (Nat.eqb_eq _ _) Em)) as [c Hc].
    exists (c * n); rewrite Hc; ring.
  - (* p | n *)
    replace ((m * n) mod p =? 0) with true; [ ring | ].
    symmetry; apply Nat.eqb_eq, (proj2 (Nat.Lcm0.mod_divide (m * n) p)).
    destruct (proj1 (Nat.Lcm0.mod_divide n p) (proj1 (Nat.eqb_eq _ _) En)) as [c Hc].
    exists (m * c); rewrite Hc; ring.
  - (* both units *)
    apply Nat.eqb_neq in Em; apply Nat.eqb_neq in En.
    assert (Hu : 1 <= m mod p <= p - 1)
      by (pose proof (Nat.mod_upper_bound m p ltac:(lia)); lia).
    assert (Hv : 1 <= n mod p <= p - 1)
      by (pose proof (Nat.mod_upper_bound n p ltac:(lia)); lia).
    replace ((m * n) mod p =? 0) with false.
    2:{ symmetry; apply Nat.eqb_neq; intro Hmod0.
        assert (Hd : Nat.divide p (m * n))
          by (apply (proj1 (Nat.Lcm0.mod_divide (m * n) p)); exact Hmod0).
        destruct (prime_mult_nat p m n Hp Hd) as [Hpm|Hpn];
          [ apply Em | apply En ];
          apply (proj2 (Nat.Lcm0.mod_divide _ p)); assumption. }
    (* dlog((m*n) mod p) = (dlog(m mod p) + dlog(n mod p)) mod (p-1) *)
    assert (Hdl : dlog p g ((m * n) mod p)
                  = (dlog p g (m mod p) + dlog p g (n mod p)) mod (p - 1)).
    { rewrite (Nat.Div0.mul_mod m n p); apply dlog_mul; assumption. }
    rewrite Hdl, <- Cpow_add.
    rewrite <- Nat.mul_add_distr_l.
    assert (Hpos : (0 < p - 1)%nat) by lia.
    rewrite (Cpow_w_mod (p - 1) (a * ((dlog p g (m mod p) + dlog p g (n mod p)) mod (p - 1))) Hpos).
    rewrite (Cpow_w_mod (p - 1) (a * (dlog p g (m mod p) + dlog p g (n mod p))) Hpos).
    f_equal; apply Nat.Div0.mul_mod_idemp_r.
Qed.

(* chi(q^k) = chi(q)^k *)
Theorem dchar_pow : forall p g a q k,
  prime (Z.of_nat p) -> 1 <= g <= p - 1 -> ord p g = p - 1 ->
  dchar p g a (q ^ k) = Cpow (dchar p g a q) k.
Proof.
  intros p g a q k Hp Hg Hord; induction k as [|k IH]; cbn [Nat.pow Cpow].
  - apply dchar_1; assumption.
  - rewrite (dchar_mul p g a q (q ^ k) Hp Hg Hord), IH; reflexivity.
Qed.

(* ================================================================= *)
(*  3.  THE LOCAL EULER FACTOR  L_q(x) = sum_{k<K} chi(q^k) x^k        *)
(* ================================================================= *)

Definition Llocal (p g a q : nat) (x : C) (K : nat) : C :=
  Csum (fun k => Cmul (dchar p g a (q ^ k)) (Cpow x k)) K.

(* the character twist collapses the local factor to a geometric series *)
Lemma Llocal_geom : forall p g a q x K,
  prime (Z.of_nat p) -> 1 <= g <= p - 1 -> ord p g = p - 1 ->
  Llocal p g a q x K = Csum (fun k => Cpow (Cmul (dchar p g a q) x) k) K.
Proof.
  intros p g a q x K Hp Hg Hord; unfold Llocal.
  apply Csum_ext; intro k.
  rewrite (dchar_pow p g a q k Hp Hg Hord), Cpow_Cmul; reflexivity.
Qed.

(* the geometric closed form: (1 - chi(q) x) * L_q(x) = 1 - (chi(q) x)^K *)
Theorem local_euler_factor : forall p g a q x K,
  prime (Z.of_nat p) -> 1 <= g <= p - 1 -> ord p g = p - 1 ->
  Cmul (Cminus C1 (Cmul (dchar p g a q) x)) (Llocal p g a q x K)
  = Cminus C1 (Cpow (Cmul (dchar p g a q) x) K).
Proof.
  intros p g a q x K Hp Hg Hord.
  rewrite (Llocal_geom p g a q x K Hp Hg Hord).
  pose proof (geom_sum (Cmul (dchar p g a q) x) K) as HG.
  replace (Cmul (Cminus C1 (Cmul (dchar p g a q) x))
                (Csum (fun k => Cpow (Cmul (dchar p g a q) x) k) K))
    with (Copp (Cmul (Cminus (Cmul (dchar p g a q) x) C1)
                     (Csum (fun k => Cpow (Cmul (dchar p g a q) x) k) K)))
    by ring.
  rewrite HG; ring.
Qed.

(* ================================================================= *)
(*  4.  THE FINITE EULER PRODUCT OVER C  (primon gas, ported)         *)
(* ================================================================= *)

Definition Cwsum (l : list C) : C := fold_right Cadd C0 l.
Definition Cwprod (l : list C) : C := fold_right Cmul C1 l.

Fixpoint Cweight (xs : list C) (ks : list nat) : C :=
  match xs, ks with
  | x :: xs', k :: ks' => Cmul (Cpow x k) (Cweight xs' ks')
  | _, _ => C1
  end.

Fixpoint statesC (xs : list C) (K : nat) : list (list nat) :=
  match xs with
  | [] => [ [] ]
  | _ :: xs' => flat_map (fun k => map (cons k) (statesC xs' K)) (seq 0 K)
  end.

Lemma Cwsum_app : forall l1 l2, Cwsum (l1 ++ l2) = Cadd (Cwsum l1) (Cwsum l2).
Proof.
  intros l1 l2; unfold Cwsum; induction l1 as [|a l1 IH]; cbn [fold_right app];
    [ ring | rewrite IH; ring ].
Qed.

Lemma Cwsum_map_scale_l : forall (A : Type) (c : C) (f : A -> C) (l : list A),
  Cwsum (map (fun a => Cmul c (f a)) l) = Cmul c (Cwsum (map f l)).
Proof.
  intros A c f; unfold Cwsum; induction l as [|a l IH]; cbn [map fold_right];
    [ ring | rewrite IH; ring ].
Qed.

Lemma Cwsum_map_scale_r : forall (A : Type) (c : C) (f : A -> C) (l : list A),
  Cwsum (map (fun a => Cmul (f a) c) l) = Cmul (Cwsum (map f l)) c.
Proof.
  intros A c f; unfold Cwsum; induction l as [|a l IH]; cbn [map fold_right];
    [ ring | rewrite IH; ring ].
Qed.

Lemma Cwsum_map_ext : forall (A : Type) (f h : A -> C) (l : list A),
  (forall a, f a = h a) -> Cwsum (map f l) = Cwsum (map h l).
Proof.
  intros A f h l Hfh; unfold Cwsum; induction l as [|a l IH]; cbn [map fold_right];
    [ reflexivity | rewrite Hfh, IH; reflexivity ].
Qed.

Lemma Cwsum_map_flat_map :
  forall (A B : Type) (g : B -> C) (h : A -> list B) (L : list A),
    Cwsum (map g (flat_map h L))
    = Cwsum (map (fun a => Cwsum (map g (h a))) L).
Proof.
  intros A B g h; induction L as [|a L IH]; cbn [flat_map map];
    [ reflexivity | ].
  rewrite map_app, Cwsum_app, IH; unfold Cwsum; reflexivity.
Qed.

Lemma inner_factor_C : forall x xs' K k,
  Cwsum (map (Cweight (x :: xs')) (map (cons k) (statesC xs' K)))
  = Cmul (Cpow x k) (Cwsum (map (Cweight xs') (statesC xs' K))).
Proof.
  intros x xs' K k; rewrite map_map.
  rewrite <- (Cwsum_map_scale_l (list nat) (Cpow x k) (Cweight xs') (statesC xs' K)).
  apply Cwsum_map_ext; intro ks; reflexivity.
Qed.

(* single-mode partition function = truncated geometric series *)
Lemma single_mode : forall x K,
  Csum (fun k => Cpow x k) K = Cwsum (map (fun k => Cpow x k) (seq 0 K)).
Proof. intros x K; rewrite Csum_fold; reflexivity. Qed.

Theorem euler_product_C : forall xs K,
  Cwsum (map (Cweight xs) (statesC xs K))
  = Cwprod (map (fun x => Csum (fun k => Cpow x k) K) xs).
Proof.
  induction xs as [|x xs' IH]; intro K.
  - cbn [statesC map Cweight Cwsum Cwprod fold_right]; ring.
  - cbn [statesC].
    rewrite Cwsum_map_flat_map.
    rewrite (Cwsum_map_ext nat
               (fun k => Cwsum (map (Cweight (x :: xs')) (map (cons k) (statesC xs' K))))
               (fun k => Cmul (Cpow x k) (Cwsum (map (Cweight xs') (statesC xs' K))))
               (seq 0 K)
               (fun k => inner_factor_C x xs' K k)).
    rewrite (Cwsum_map_scale_r nat
               (Cwsum (map (Cweight xs') (statesC xs' K))) (fun k => Cpow x k) (seq 0 K)).
    rewrite <- single_mode.
    cbn [Cwprod map fold_right]; fold (Cwprod (map (fun x0 => Csum (fun k => Cpow x0 k) K) xs')).
    rewrite IH; ring.
Qed.

(* ================================================================= *)
(*  5.  THE DIRICHLET L EULER PRODUCT                                *)
(* ================================================================= *)

(* the character-twisted fugacity of a prime q with fugacity x *)
Definition twist (p g a : nat) (qx : nat * C) : C :=
  Cmul (dchar p g a (fst qx)) (snd qx).

Theorem dirichlet_L_euler_product : forall p g a (qxs : list (nat * C)) K,
  prime (Z.of_nat p) -> 1 <= g <= p - 1 -> ord p g = p - 1 ->
  Cwsum (map (Cweight (map (twist p g a) qxs)) (statesC (map (twist p g a) qxs) K))
  = Cwprod (map (fun qx => Llocal p g a (fst qx) (snd qx) K) qxs).
Proof.
  intros p g a qxs K Hp Hg Hord.
  rewrite euler_product_C, map_map.
  f_equal; apply map_ext; intro qx.
  unfold twist; rewrite <- (Llocal_geom p g a (fst qx) (snd qx) K Hp Hg Hord); reflexivity.
Qed.

(* ----------------------------------------------------------------- *)
(*  MASTER THEOREM                                                   *)
(* ----------------------------------------------------------------- *)

Theorem dirichlet_L_function : forall p, prime (Z.of_nat p) ->
  exists g, 1 <= g <= p - 1 /\ ord p g = p - 1 /\
    (* complete multiplicativity: the reason L has an Euler product *)
    (forall a m n, dchar p g a (m * n) = Cmul (dchar p g a m) (dchar p g a n))
    /\ (forall a q k, dchar p g a (q ^ k) = Cpow (dchar p g a q) k)
    (* local Euler factor: (1 - chi(q) x) * L_q(x) = 1 - (chi(q) x)^K *)
    /\ (forall a q x K,
          Cmul (Cminus C1 (Cmul (dchar p g a q) x)) (Llocal p g a q x K)
          = Cminus C1 (Cpow (Cmul (dchar p g a q) x) K))
    (* the finite Euler product: state-sum = product of local factors *)
    /\ (forall a qxs K,
          Cwsum (map (Cweight (map (twist p g a) qxs)) (statesC (map (twist p g a) qxs) K))
          = Cwprod (map (fun qx => Llocal p g a (fst qx) (snd qx) K) qxs)).
Proof.
  intros p Hp; destruct (units_cyclic p Hp) as [g [Hgu Hgord]].
  exists g; repeat split; [ lia | lia | exact Hgord | | | | ].
  - intros a m n; apply dchar_mul; [ assumption | lia | exact Hgord ].
  - intros a q k; apply dchar_pow; [ assumption | lia | exact Hgord ].
  - intros a q x K; apply local_euler_factor; [ assumption | lia | exact Hgord ].
  - intros a qxs K; apply dirichlet_L_euler_product; [ assumption | lia | exact Hgord ].
Qed.

Print Assumptions dirichlet_L_function.

(* ================================================================= *)
(*  END DirichletLEuler.v                                            *)
(*  Complete multiplicativity of the Dirichlet character mod p        *)
(*  (dchar_mul, dchar_pow), the local Euler factor with its geometric  *)
(*  closed form, and the finite Euler product over the custom C        *)
(*  (state-sum = product of local factors).  This is the Euler-product *)
(*  side of the Dirichlet L-function L(s,chi) = prod_q (1-chi(q)q^-s)^-1 *)
(*  at the finite level.  Uses the classical Reals axioms (quarantined)*)
(* ================================================================= *)
