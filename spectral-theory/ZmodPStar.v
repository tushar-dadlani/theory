(* ================================================================= *)
(*  ZmodPStar.v                                                      *)
(*                                                                    *)
(*  PHASE 1 of the Dirichlet-mod-p build: the multiplicative group    *)
(*  (Z/pZ)^* of units mod a prime p, and FERMAT'S LITTLE THEOREM.     *)
(*                                                                    *)
(*     fermat : 1 <= a <= p-1 ->  a^(p-1) mod p = 1.                  *)
(*                                                                    *)
(*  Units are the residues in [1, p-1] (for prime p, exactly the      *)
(*  nonzero residues).  We prove closure of multiplication mod p, the  *)
(*  mod-p cancellation law (cancel_mod, via Gauss), and Fermat by the  *)
(*  classical argument: x |-> (a x) mod p PERMUTES the units           *)
(*  (units_perm, via NoDup_Permutation_bis + injectivity), so the      *)
(*  product of the units is fixed mod p:                              *)
(*     a^(p-1) * (p-1)!  ==  (p-1)!   (mod p),                        *)
(*  and (p-1)! is a unit, so it cancels.                              *)
(*                                                                    *)
(*  Axiom-free: constructive Z / nat + Znumtheory (no classical logic). *)
(*  The nat<->Z primality bridge (prime_mult_nat) is via `mod`.        *)
(* ================================================================= *)

From Stdlib Require Import ZArith Znumtheory Arith Lia List Permutation.
Require Import ProfiniteCRT.   (* sub_of_mod_eq, mod_eq_sub over Z (axiom-free) *)
Import ListNotations.
Open Scope nat_scope.

(* ----------------------------------------------------------------- *)
(*  nat <-> Z primality bridge                                       *)
(* ----------------------------------------------------------------- *)

Lemma Zof_nat_divide_inv : forall p a,
  (Z.of_nat p | Z.of_nat a)%Z -> Nat.divide p a.
Proof.
  intros p a Hd.
  destruct (Nat.eq_dec p 0) as [->|Hp0].
  - destruct Hd as [q Hq]; simpl in Hq.
    assert (a = 0) by nia; subst a; exists 0; reflexivity.
  - assert (Hbne : Z.of_nat p <> 0%Z) by lia.
    apply (proj1 (Nat.Lcm0.mod_divide a p)), Nat2Z.inj.
    rewrite Nat2Z.inj_mod.
    apply (proj2 (Z.mod_divide (Z.of_nat a) (Z.of_nat p) Hbne)); exact Hd.
Qed.

Lemma prime_mult_nat : forall p a b, prime (Z.of_nat p) ->
  Nat.divide p (a * b) -> Nat.divide p a \/ Nat.divide p b.
Proof.
  intros p a b Hp Hdiv.
  assert (HZ : (Z.of_nat p | Z.of_nat a * Z.of_nat b)%Z).
  { destruct Hdiv as [k Hk]. exists (Z.of_nat k).
    rewrite <- Nat2Z.inj_mul, Hk, Nat2Z.inj_mul; ring. }
  destruct (prime_mult _ Hp _ _ HZ) as [H|H];
    [ left | right ]; apply Zof_nat_divide_inv; exact H.
Qed.

Lemma unit_not_div : forall p x, 1 <= x <= p - 1 -> ~ Nat.divide p x.
Proof. intros p x [Hx1 Hx2] [k Hk]; subst x; destruct k; simpl in *; lia. Qed.

(* ----------------------------------------------------------------- *)
(*  Multiplicative cancellation mod p  (via Gauss)                   *)
(* ----------------------------------------------------------------- *)

Lemma cancel_mod : forall p c x y, prime (Z.of_nat p) -> ~ Nat.divide p c ->
  (c * x) mod p = (c * y) mod p -> x mod p = y mod p.
Proof.
  intros p c x y Hp Hc H.
  assert (Hp0 : Z.of_nat p <> 0%Z) by (destruct Hp; lia).
  assert (HZ : ((Z.of_nat c * Z.of_nat x) mod Z.of_nat p
              = (Z.of_nat c * Z.of_nat y) mod Z.of_nat p)%Z).
  { rewrite <- !Nat2Z.inj_mul, <- !Nat2Z.inj_mod, H; reflexivity. }
  assert (Hdvd : (Z.of_nat p | Z.of_nat c * (Z.of_nat x - Z.of_nat y))%Z).
  { rewrite Z.mul_sub_distr_l; apply sub_of_mod_eq; [ exact Hp0 | exact HZ ]. }
  assert (Hrp : rel_prime (Z.of_nat p) (Z.of_nat c)).
  { apply prime_rel_prime; [ exact Hp | intro Hd; apply Hc; apply Zof_nat_divide_inv; exact Hd ]. }
  assert (Hxy : (Z.of_nat p | Z.of_nat x - Z.of_nat y)%Z)
    by (apply (Gauss _ (Z.of_nat c) _ Hdvd Hrp)).
  assert (HM : (Z.of_nat x mod Z.of_nat p = Z.of_nat y mod Z.of_nat p)%Z)
    by (apply mod_eq_sub; [ exact Hp0 | exact Hxy ]).
  rewrite <- !Nat2Z.inj_mod in HM; apply Nat2Z.inj; exact HM.
Qed.

(* ----------------------------------------------------------------- *)
(*  Closure of multiplication mod p on units                         *)
(* ----------------------------------------------------------------- *)

Lemma mulmod_in_units : forall p a x, prime (Z.of_nat p) ->
  ~ Nat.divide p a -> ~ Nat.divide p x -> 1 <= (a * x) mod p <= p - 1.
Proof.
  intros p a x Hp Ha Hx.
  assert (Hp2 : 2 <= p) by (destruct Hp; lia).
  assert (Hne : (a * x) mod p <> 0).
  { intro H0. rewrite (Nat.Lcm0.mod_divide (a * x) p) in H0.
    destruct (prime_mult_nat p a x Hp H0); [ apply Ha | apply Hx ]; assumption. }
  pose proof (Nat.mod_upper_bound (a * x) p ltac:(lia)); lia.
Qed.

Lemma mulmod_inj : forall p a x y, prime (Z.of_nat p) -> ~ Nat.divide p a ->
  1 <= x <= p - 1 -> 1 <= y <= p - 1 -> (a * x) mod p = (a * y) mod p -> x = y.
Proof.
  intros p a x y Hp Ha Hx Hy H.
  assert (Hp2 : 2 <= p) by (destruct Hp; lia).
  pose proof (cancel_mod p a x y Hp Ha H) as Hm.
  rewrite (Nat.mod_small x p), (Nat.mod_small y p) in Hm by lia; exact Hm.
Qed.

(* ----------------------------------------------------------------- *)
(*  Generic list helpers (product permutation-invariance, injectivity) *)
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

Lemma fold_mul_perm : forall l1 l2, Permutation l1 l2 ->
  fold_right Nat.mul 1 l1 = fold_right Nat.mul 1 l2.
Proof.
  intros l1 l2 Hp; induction Hp; simpl;
    [ reflexivity | rewrite IHHp; reflexivity | ring | rewrite IHHp1, IHHp2; reflexivity ].
Qed.

Lemma prod_map_mod : forall p (g : nat -> nat) l,
  (fold_right Nat.mul 1 (map (fun x => g x mod p) l)) mod p
  = (fold_right Nat.mul 1 (map g l)) mod p.
Proof.
  intros p g l; induction l as [|x l IH]; cbn [map fold_right]; [ reflexivity | ].
  rewrite Nat.Div0.mul_mod_idemp_l, <- (Nat.Div0.mul_mod_idemp_r (g x)), IH,
          Nat.Div0.mul_mod_idemp_r; reflexivity.
Qed.

Lemma prod_scale : forall a l,
  fold_right Nat.mul 1 (map (fun x => a * x) l)
  = a ^ (length l) * fold_right Nat.mul 1 l.
Proof.
  intros a l; induction l as [|x l IH]; cbn [map fold_right length Nat.pow];
    [ ring | rewrite IH; ring ].
Qed.

(* ----------------------------------------------------------------- *)
(*  x |-> (a x) mod p permutes the units [1, p-1]                     *)
(* ----------------------------------------------------------------- *)

Lemma units_perm : forall p a, prime (Z.of_nat p) -> ~ Nat.divide p a ->
  Permutation (map (fun x => (a * x) mod p) (seq 1 (p - 1))) (seq 1 (p - 1)).
Proof.
  intros p a Hp Ha.
  assert (Hp2 : 2 <= p) by (destruct Hp; lia).
  apply NoDup_Permutation_bis.
  - apply NoDup_map_inj; [ | apply seq_NoDup ].
    intros x y Hx Hy Hxy; apply in_seq in Hx; apply in_seq in Hy.
    apply (mulmod_inj p a x y Hp Ha); [ lia | lia | exact Hxy ].
  - rewrite length_map; lia.
  - intros z Hz; apply in_map_iff in Hz as [x [Hx Hxin]]; apply in_seq in Hxin.
    apply in_seq; rewrite <- Hx.
    assert (Hxu : ~ Nat.divide p x) by (apply unit_not_div; lia).
    pose proof (mulmod_in_units p a x Hp Ha Hxu); lia.
Qed.

(* ----------------------------------------------------------------- *)
(*  (p-1)! is coprime to p                                           *)
(* ----------------------------------------------------------------- *)

Lemma prime_div_prod : forall p l, prime (Z.of_nat p) ->
  Nat.divide p (fold_right Nat.mul 1 l) -> Exists (fun x => Nat.divide p x) l.
Proof.
  intros p l Hp; induction l as [|x l IH]; cbn [fold_right]; intro Hd.
  - exfalso; destruct Hd as [k Hk]; destruct Hp as [Hgt _]; destruct k; simpl in Hk; lia.
  - destruct (prime_mult_nat p x (fold_right Nat.mul 1 l) Hp Hd) as [H|H];
      [ apply Exists_cons_hd; exact H | apply Exists_cons_tl; apply IH; exact H ].
Qed.

Lemma Pi_coprime : forall p, prime (Z.of_nat p) ->
  ~ Nat.divide p (fold_right Nat.mul 1 (seq 1 (p - 1))).
Proof.
  intros p Hp Hd.
  apply prime_div_prod in Hd; [ | exact Hp ].
  apply Exists_exists in Hd; destruct Hd as [x [Hin Hx]].
  apply in_seq in Hin; apply (unit_not_div p x); [ lia | exact Hx ].
Qed.

(* ----------------------------------------------------------------- *)
(*  FERMAT'S LITTLE THEOREM                                          *)
(* ----------------------------------------------------------------- *)

Theorem fermat : forall p a, prime (Z.of_nat p) -> 1 <= a <= p - 1 ->
  (a ^ (p - 1)) mod p = 1.
Proof.
  intros p a Hp Ha.
  assert (Hp2 : 2 <= p) by (destruct Hp; lia).
  assert (Ha' : ~ Nat.divide p a) by (apply unit_not_div; exact Ha).
  set (Pi := fold_right Nat.mul 1 (seq 1 (p - 1))).
  assert (Hkey : ((a ^ (p - 1)) * Pi) mod p = Pi mod p).
  { assert (HA : fold_right Nat.mul 1 (map (fun x => (a * x) mod p) (seq 1 (p - 1))) = Pi)
      by (unfold Pi; apply fold_mul_perm; apply units_perm; assumption).
    assert (HB : (fold_right Nat.mul 1 (map (fun x => (a * x) mod p) (seq 1 (p - 1)))) mod p
                 = ((a ^ (p - 1)) * Pi) mod p).
    { rewrite (prod_map_mod p (fun x => a * x) (seq 1 (p - 1))), prod_scale, length_seq.
      unfold Pi; reflexivity. }
    rewrite HA in HB; symmetry; exact HB. }
  assert (Hc : (Pi * (a ^ (p - 1))) mod p = (Pi * 1) mod p)
    by (rewrite Nat.mul_1_r, (Nat.mul_comm Pi (a ^ (p - 1))); exact Hkey).
  pose proof (cancel_mod p Pi (a ^ (p - 1)) 1 Hp (Pi_coprime p Hp) Hc) as Hf.
  rewrite Hf, Nat.mod_small by lia; reflexivity.
Qed.

Print Assumptions fermat.

(* ================================================================= *)
(*  END ZmodPStar.v  (Phase 1)                                       *)
(*  The units mod a prime p form a group under (. * .) mod p          *)
(*  (mulmod_in_units closure, cancel_mod cancellation), and Fermat's   *)
(*  little theorem a^(p-1) = 1 (mod p) holds.  Foundation for the      *)
(*  primitive-root / Dirichlet-character build.  Axiom-free.          *)
(* ================================================================= *)
