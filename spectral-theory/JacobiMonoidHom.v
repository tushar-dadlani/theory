(* ================================================================= *)
(*  JacobiMonoidHom.v  —  Brick 4, primorial case: the Jacobi symbol    *)
(*  as the universal quadratic quotient over a product of odd primes.   *)
(*                                                                    *)
(*  For a squarefree odd modulus n = p_1···p_k (in particular an odd    *)
(*  primorial), the Jacobi symbol is the product of the Legendre        *)
(*  symbols, valued in the sign monoid {I,N,F}:                         *)
(*      jacobi [p_1;...;p_k] a  =  op_i (leg_sym p_i a).                 *)
(*  It is COMPLETELY MULTIPLICATIVE in a (jacobi (a*b) = op (jacobi a)   *)
(*  (jacobi b)), its {I,N,F}-value is the integer Jacobi symbol         *)
(*  (val o jacobi = prod of legendres), and it VANISHES (= F) exactly    *)
(*  when some prime divides a -- i.e. gcd(a,n) > 1.  So {I,N,F} is the   *)
(*  universal quadratic quotient of M_n for squarefree odd n, extending  *)
(*  Brick 4 (one prime) to the primorial.  Axiom-free.                  *)
(* ================================================================= *)

From Stdlib Require Import Arith Lia List ZArith Znumtheory.
Require Import ZmodOrder LegendreSymbol LegendreMonoidHom INFMonoid.
Import ListNotations.
Open Scope nat_scope.

(* ---- leg_sym depends only on a mod p, hence is completely multiplicative ---- *)
Lemma pw_base_mod : forall p a k, pw p (a mod p) k = pw p a k.
Proof.
  intros p a k; unfold pw; induction k as [|k IH]; simpl; [ reflexivity | ].
  rewrite Nat.Div0.mul_mod, IH, Nat.Div0.mod_mod, <- Nat.Div0.mul_mod; reflexivity.
Qed.

Lemma leg_sym_mod : forall p a, leg_sym p a = leg_sym p (a mod p).
Proof.
  intros p a; unfold leg_sym.
  rewrite Nat.Div0.mod_mod, (pw_base_mod p a (hlf p)); reflexivity.
Qed.

Lemma leg_sym_mult_all : forall p, prime (Z.of_nat p) -> p mod 2 = 1 ->
  forall a b, leg_sym p (a * b) = op (leg_sym p a) (leg_sym p b).
Proof.
  intros p Hp Hodd a b.
  assert (Hpne : p <> 0) by (pose proof (prime_ge_2 _ Hp); lia).
  assert (Hma : a mod p < p) by (apply Nat.mod_upper_bound; exact Hpne).
  assert (Hmb : b mod p < p) by (apply Nat.mod_upper_bound; exact Hpne).
  rewrite (leg_sym_mod p (a * b)), Nat.Div0.mul_mod,
    (leg_sym_hom p Hp Hodd (a mod p) (b mod p) Hma Hmb),
    <- (leg_sym_mod p a), <- (leg_sym_mod p b); reflexivity.
Qed.

Lemma leg_sym_F_iff : forall p a, leg_sym p a = F <-> a mod p = 0.
Proof.
  intros p a; unfold leg_sym; destruct (Nat.eqb_spec (a mod p) 0) as [He | Hne].
  - split; [ intros _; exact He | reflexivity ].
  - destruct (pw p a (hlf p) =? 1); split;
      solve [ discriminate | intro H; exfalso; apply Hne; exact H ].
Qed.

(* ---- the Jacobi symbol as a fold of Legendre symbols ---- *)
Definition jacobi (ps : list nat) (a : nat) : Sym :=
  fold_right (fun p acc => op (leg_sym p a) acc) I ps.

(* an interchange law for the commutative monoid {I,N,F} (finite check) *)
Lemma op_interchange : forall a b c d,
  op (op a b) (op c d) = op (op a c) (op b d).
Proof. intros a b c d; destruct a, b, c, d; reflexivity. Qed.

Lemma op_F_iff : forall x y, op x y = F <-> x = F \/ y = F.
Proof.
  intros x y; split.
  - destruct x, y; simpl; intro H; auto; try discriminate.
  - intros [H | H]; subst; [ apply F_absorb_l | apply F_absorb_r ].
Qed.

(* ---- (1) value:  val o jacobi = product of Legendre symbols ---- *)
Theorem jacobi_val : forall ps a,
  val (jacobi ps a) = fold_right (fun p acc => (legendre p a * acc)%Z) 1%Z ps.
Proof.
  induction ps as [|p ps IH]; intro a; simpl; [ reflexivity | ].
  rewrite val_hom, leg_sym_val, IH; reflexivity.
Qed.

(* ---- (2) complete multiplicativity in a ---- *)
Theorem jacobi_mult : forall ps,
  Forall (fun p => prime (Z.of_nat p) /\ p mod 2 = 1) ps ->
  forall a b, jacobi ps (a * b) = op (jacobi ps a) (jacobi ps b).
Proof.
  induction ps as [|p ps IH]; intros HF a b; simpl; [ reflexivity | ].
  destruct (Forall_inv HF) as [Hp Hodd]. pose proof (Forall_inv_tail HF) as HFrest.
  rewrite (leg_sym_mult_all p Hp Hodd a b), (IH HFrest a b); apply op_interchange.
Qed.

(* ---- (3) vanishing:  jacobi = F  iff  some prime divides a ---- *)
Theorem jacobi_F_iff : forall ps a,
  jacobi ps a = F <-> exists p, In p ps /\ a mod p = 0.
Proof.
  induction ps as [|p ps IH]; intro a; simpl.
  - split; [ discriminate | intros [q [[] _]] ].
  - rewrite op_F_iff, (leg_sym_F_iff p a), IH; split.
    + intros [Hp | [q [Hin Hq]]];
        [ exists p; split; [ left; reflexivity | exact Hp ]
        | exists q; split; [ right; exact Hin | exact Hq ] ].
    + intros [q [[Heq | Hin] Hq]];
        [ left; subst q; exact Hq | right; exists q; split; assumption ].
Qed.

(* ----------------------------------------------------------------- *)
(*  MASTER THEOREM:  {I,N,F} is the universal quadratic quotient of     *)
(*  M_n for squarefree odd n = product of the odd primes in ps.         *)
(* ----------------------------------------------------------------- *)
Theorem jacobi_universal_quotient : forall ps,
  Forall (fun p => prime (Z.of_nat p) /\ p mod 2 = 1) ps ->
  (forall a, val (jacobi ps a)
             = fold_right (fun p acc => (legendre p a * acc)%Z) 1%Z ps)
  /\ (forall a b, jacobi ps (a * b) = op (jacobi ps a) (jacobi ps b))
  /\ (forall a, jacobi ps a = F <-> exists p, In p ps /\ a mod p = 0).
Proof.
  intros ps HF; split; [ intro a; apply jacobi_val | ].
  split; [ intros a b; apply jacobi_mult; exact HF | intro a; apply jacobi_F_iff ].
Qed.

Print Assumptions jacobi_universal_quotient.

(* ================================================================= *)
(*  END JacobiMonoidHom.v  (Brick 4, primorial case: the Jacobi symbol  *)
(*  is the completely-multiplicative monoid hom M_n ->> {I,N,F} for      *)
(*  squarefree odd n; {I,N,F} is its universal quadratic quotient.)      *)
(* ================================================================= *)
