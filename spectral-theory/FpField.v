(* ================================================================= *)
(*  FpField.v                                                        *)
(*                                                                    *)
(*  A NATURAL NUMBER AS A FIELD: the prime p turns [0..p-1] into the   *)
(*  finite field F_p = Z/pZ, and the exploratory triad                *)
(*                                                                    *)
(*        1/x         x          x^x                                  *)
(*                                                                    *)
(*  all live inside it as powers of x:                                *)
(*                                                                    *)
(*    1/x  = x^(p-2) mod p   (finv)   -- the inverse IS a power,       *)
(*                                       and x * (1/x) = 1 is Fermat.  *)
(*    x    = x^1                                                       *)
(*    x^x  = x^x mod p        (selfpow) -- self-exponentiation.        *)
(*                                                                    *)
(*  So the triad is  pw p x  at the three exponents  {p-2, 1, x},      *)
(*  and (p-2)+1 = p-1 is exactly why  (1/x)*x = 1  (fermat).           *)
(*                                                                    *)
(*  Passing to the DISCRETE LOG base a primitive root g (dlog), with   *)
(*  L = dlog x, the triad becomes the log-space triad on the exponents *)
(*                                                                    *)
(*        1/x : L*(p-2) = -L      x : L        x^x : x*L    (mod p-1)  *)
(*                                                                    *)
(*  -- reciprocal is negation, self-power is scaling by x; and L = 0   *)
(*  (i.e. x = 1) collapses all three to 1 (the vanishing point).       *)
(*                                                                    *)
(*  Everything reuses the from-scratch cyclicity tower (fermat, pw,    *)
(*  units_cyclic, dlog).  Axiom-free ("Closed under the global         *)
(*  context").                                                        *)
(* ================================================================= *)

From Stdlib Require Import ZArith Znumtheory Arith Lia List Bool Permutation Reals.
Require Import ZmodPStar ZmodOrder PrimitiveRoot DirichletModP.
Open Scope nat_scope.

(* ================================================================= *)
(*  1.  THE FIELD INVERSE  1/x = x^(p-2) mod p   (via Fermat)         *)
(* ================================================================= *)

Definition finv (p x : nat) : nat := pw p x (p - 2).

Theorem inv_correct : forall p x, prime (Z.of_nat p) -> 1 <= x <= p - 1 ->
  (x * finv p x) mod p = 1.
Proof.
  intros p x Hp Hx; assert (Hp2 : 2 <= p) by (destruct Hp; lia).
  unfold finv, pw.
  rewrite Nat.Div0.mul_mod_idemp_r.
  replace (x * x ^ (p - 2)) with (x ^ (p - 1))
    by (replace (p - 1) with (1 + (p - 2)) by lia;
        rewrite Nat.pow_add_r, Nat.pow_1_r; reflexivity).
  apply fermat; assumption.
Qed.

(* the inverse is itself a unit *)
Lemma finv_unit : forall p x, prime (Z.of_nat p) -> 1 <= x <= p - 1 ->
  1 <= finv p x <= p - 1.
Proof.
  intros p x Hp Hx; assert (Hp2 : 2 <= p) by (destruct Hp; lia).
  unfold finv, pw; split.
  - assert (Hnd : ~ Nat.divide p (x ^ (p - 2)))
      by (apply not_div_pow; [ assumption | apply unit_not_div; exact Hx ]).
    destruct (x ^ (p - 2) mod p) eqn:E; [ | lia ].
    exfalso; apply Hnd, (proj1 (Nat.Lcm0.mod_divide _ p)); exact E.
  - pose proof (Nat.mod_upper_bound (x ^ (p - 2)) p ltac:(lia)); lia.
Qed.

(* ================================================================= *)
(*  2.  SELF-POWER  x^x mod p,  and the x = 1 collapse point          *)
(* ================================================================= *)

Definition selfpow (p x : nat) : nat := pw p x x.

Lemma finv_1    : forall p, 2 <= p -> finv p 1 = 1.
Proof. intros p Hp; unfold finv; apply pw_1; exact Hp. Qed.

Lemma selfpow_1 : forall p, 2 <= p -> selfpow p 1 = 1.
Proof. intros p Hp; unfold selfpow; apply pw_1; exact Hp. Qed.

(* the triad collapses to the single point 1 at x = 1 *)
Theorem triad_collapse : forall p, 2 <= p -> finv p 1 = 1 /\ 1 = 1 /\ selfpow p 1 = 1.
Proof. intros p Hp; repeat split; [ apply finv_1 | apply selfpow_1 ]; exact Hp. Qed.

(* ================================================================= *)
(*  3.  THE TRIAD AS POWERS OF x:  exponents {p-2, 1, x}             *)
(* ================================================================= *)

Lemma pw_x_1 : forall p x, 2 <= p -> 1 <= x <= p - 1 -> pw p x 1 = x.
Proof. intros p x Hp Hx; unfold pw; rewrite Nat.pow_1_r; apply Nat.mod_small; lia. Qed.

(* 1/x, x, x^x are pw p x at {p-2, 1, x}; and (p-2)+1 = p-1 gives 1/x * x = 1 *)
Theorem triad_powers_of_x : forall p x, prime (Z.of_nat p) -> 1 <= x <= p - 1 ->
     finv p x = pw p x (p - 2)
  /\ x = pw p x 1
  /\ selfpow p x = pw p x x
  /\ (finv p x * x) mod p = 1.
Proof.
  intros p x Hp Hx; assert (Hp2 : 2 <= p) by (destruct Hp; lia).
  split; [ reflexivity | ].
  split; [ symmetry; apply pw_x_1; [ exact Hp2 | exact Hx ] | ].
  split; [ reflexivity | ].
  rewrite Nat.mul_comm; apply inv_correct; assumption.
Qed.

(* ================================================================= *)
(*  4.  THE DISCRETE-LOG TRIAD  {L*(p-2), L, x*L} (mod p-1)          *)
(* ================================================================= *)

(* powers of a unit are periodic mod p-1 (Fermat gives period p-1) *)
Lemma pw_mod_pm1 : forall p a k, prime (Z.of_nat p) -> 1 <= a <= p - 1 ->
  pw p a k = pw p a (k mod (p - 1)).
Proof.
  intros p a k Hp Ha; assert (Hp2 : 2 <= p) by (destruct Hp; lia).
  assert (Hper : pw p a (p - 1) = 1) by (unfold pw; apply fermat; assumption).
  rewrite (Nat.div_mod_eq k (p - 1)) at 1.
  rewrite pw_add, (pw_pow_ord_mul p a (p - 1) (k / (p - 1)) Hp2 Hper), Nat.mul_1_l.
  unfold pw; rewrite Nat.Div0.mod_mod; reflexivity.
Qed.

(* with L = dlog x (base a primitive root g), the triad's discrete logs  *)
(* are  1/x : L*(p-2),  x : L,  x^x : x*L   (all mod p-1).               *)
Theorem dlog_triad : forall p g x,
  prime (Z.of_nat p) -> 1 <= g <= p - 1 -> ord p g = p - 1 -> 1 <= x <= p - 1 ->
     dlog p g x = dlog p g x
  /\ dlog p g (finv p x)    = (dlog p g x * (p - 2)) mod (p - 1)
  /\ dlog p g (selfpow p x) = (dlog p g x * x)       mod (p - 1).
Proof.
  intros p g x Hp Hg Hord Hx; assert (Hp2 : 2 <= p) by (destruct Hp; lia).
  set (L := dlog p g x).
  assert (Hxg : pw p g L = x) by (apply dlog_inv; assumption).
  split; [ reflexivity | ].
  (* finv p x = pw p g (L*(p-2)) *)
  assert (Hi : finv p x = pw p g (L * (p - 2)))
    by (unfold finv; rewrite pw_mul_exp, Hxg; reflexivity).
  (* selfpow p x = pw p g (L*x) *)
  assert (Hs : selfpow p x = pw p g (L * x))
    by (unfold selfpow; rewrite pw_mul_exp, Hxg; reflexivity).
  split.
  - rewrite Hi, (pw_mod_pm1 p g (L * (p - 2)) Hp Hg), dlog_pow;
      [ reflexivity | assumption | assumption | assumption | apply Nat.mod_upper_bound; lia ].
  - rewrite Hs, (pw_mod_pm1 p g (L * x) Hp Hg), dlog_pow;
      [ reflexivity | assumption | assumption | assumption | apply Nat.mod_upper_bound; lia ].
Qed.

(* ----------------------------------------------------------------- *)
(*  MASTER: F_p realises the triad 1/x, x, x^x                        *)
(* ----------------------------------------------------------------- *)

Theorem Fp_field_triad : forall p, prime (Z.of_nat p) ->
  (* the inverse is a power and x*(1/x) = 1 (Fermat) *)
     (forall x, 1 <= x <= p - 1 -> (x * finv p x) mod p = 1)
  /\ (forall x, 1 <= x <= p - 1 -> 1 <= finv p x <= p - 1)
  (* the triad are powers of x at exponents {p-2, 1, x} *)
  /\ (forall x, 1 <= x <= p - 1 ->
        finv p x = pw p x (p - 2) /\ x = pw p x 1 /\ selfpow p x = pw p x x)
  (* collapse at x = 1 *)
  /\ (finv p 1 = 1 /\ selfpow p 1 = 1)
  (* discrete-log triad against a primitive root *)
  /\ (exists g, 1 <= g <= p - 1 /\ ord p g = p - 1 /\
        forall x, 1 <= x <= p - 1 ->
          dlog p g (finv p x)    = (dlog p g x * (p - 2)) mod (p - 1)
       /\ dlog p g (selfpow p x) = (dlog p g x * x)       mod (p - 1)).
Proof.
  intros p Hp; assert (Hp2 : 2 <= p) by (destruct Hp; lia).
  split; [ intros x Hx; apply inv_correct; assumption | ].
  split; [ intros x Hx; apply finv_unit; assumption | ].
  split.
  { intros x Hx; destruct (triad_powers_of_x p x Hp Hx) as [H1 [H2 [H3 _]]].
    split; [ exact H1 | split; [ exact H2 | exact H3 ] ]. }
  split; [ split; [ apply finv_1 | apply selfpow_1 ]; exact Hp2 | ].
  destruct (units_cyclic p Hp) as [g [Hg Hord]].
  exists g; split; [ lia | ]; split; [ exact Hord | ].
  intros x Hx; destruct (dlog_triad p g x Hp ltac:(lia) Hord Hx) as [_ [Hf Hsp]].
  split; [ exact Hf | exact Hsp ].
Qed.

Print Assumptions Fp_field_triad.

(* ================================================================= *)
(*  END FpField.v                                                    *)
(*  F_p = Z/pZ realises the triad 1/x = x^(p-2) (inverse via Fermat), *)
(*  x, and x^x; the three are pw p x at exponents {p-2,1,x}, and in    *)
(*  discrete-log space {L*(p-2), L, x*L} mod p-1 -- reciprocal =        *)
(*  negation, self-power = scaling by x, collapsing to 1 at x = 1.     *)
(*  Reuses the from-scratch cyclicity tower.  Closed under the global   *)
(*  context.                                                          *)
(* ================================================================= *)
