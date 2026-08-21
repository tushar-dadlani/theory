(* ================================================================= *)
(*  CEisensteinCubicMul.v  —  the cubic residue symbol is a CHARACTER. *)
(*                                                                    *)
(*    cuberoot        : being one of 1, om, om^2                       *)
(*    cuberoot_mul    : mu_3 is closed under multiplication            *)
(*    epow_mul_dist   : (a.b)^n = a^n . b^n                            *)
(*    cuberoot_unique : the symbol is a well-defined VALUE             *)
(*    pi_ndvd_mul     : pi divides neither factor => not the product   *)
(*    cubic_symbol_mul : chi(alpha.beta) = chi(alpha) . chi(beta)      *)
(*                                                                    *)
(*  MULTIPLICATIVITY IS THE EASY HALF -- epow distributes over emul in *)
(*  any commutative ring, and econg_mul carries that through the       *)
(*  congruence.  The work is on either side of it.                     *)
(*                                                                    *)
(*  BEFORE: the symbol has to be a VALUE, not just a class.  Two cube  *)
(*  roots congruent to the same x must be equal, and that is exactly   *)
(*  cube_roots_distinct read contrapositively -- six off-diagonal      *)
(*  cases, each contradicting one of the three distinctness facts.     *)
(*  Without this the equation chi(alpha.beta) = chi(alpha).chi(beta)   *)
(*  would not even typecheck as an equation between elements.          *)
(*                                                                    *)
(*  AFTER: the product of two cube roots must again be one of the      *)
(*  three, or the statement is not closed.  Nine concrete cases; the   *)
(*  interesting ones are om . om^2 = 1 and om^2 . om^2 = om, both of   *)
(*  which are om^3 = 1 in disguise.                                    *)
(*                                                                    *)
(*  pi_ndvd_mul is irred_prime read contrapositively, and is what      *)
(*  guarantees alpha.beta HAS a symbol at all.  Axiom-free.            *)
(* ================================================================= *)

From Stdlib Require Import ZArith Znumtheory Arith Lia Ring.
Require Import ZmodPStar
        CEisenstein CEisensteinUnits CEisensteinDiv CEisensteinGcd
        CEisensteinSplit CEisensteinUFD CEisensteinResidue CEisensteinFermat.
Open Scope Z_scope.

Definition cuberoot (z : Eis) : Prop :=
  z = eone \/ z = eom \/ z = emul eom eom.

(* ----------------------------------------------------------------- *)
(*  A.  mu_3 is closed under multiplication                            *)
(* ----------------------------------------------------------------- *)
Lemma cuberoot_mul : forall u v, cuberoot u -> cuberoot v -> cuberoot (emul u v).
Proof.
  intros u v [-> | [-> | ->]] [-> | [-> | ->]]; unfold cuberoot.
  - left.  unfold emul, eone; cbn [ea eb]; apply Eis_eq; ring.
  - right; left.  unfold emul, eone, eom; cbn [ea eb]; apply Eis_eq; ring.
  - right; right. unfold emul, eone, eom; cbn [ea eb]; apply Eis_eq; ring.
  - right; left.  unfold emul, eone, eom; cbn [ea eb]; apply Eis_eq; ring.
  - right; right. reflexivity.
  - left.  unfold emul, eone, eom; cbn [ea eb]; apply Eis_eq; ring.
  - right; right. unfold emul, eone, eom; cbn [ea eb]; apply Eis_eq; ring.
  - left.  unfold emul, eone, eom; cbn [ea eb]; apply Eis_eq; ring.
  - right; left.  unfold emul, eone, eom; cbn [ea eb]; apply Eis_eq; ring.
Qed.

(* ----------------------------------------------------------------- *)
(*  B.  powers distribute                                              *)
(* ----------------------------------------------------------------- *)
Lemma epow_mul_dist : forall a b n, epow (emul a b) n = emul (epow a n) (epow b n).
Proof.
  intros a b n. induction n as [| n IH]; cbn [epow].
  - ring.
  - rewrite IH. ring.
Qed.

(* ----------------------------------------------------------------- *)
(*  C.  the symbol is a well-defined value                             *)
(* ----------------------------------------------------------------- *)
Theorem cuberoot_unique : forall pi p x u u',
  enorm pi = p -> 7 <= p ->
  cuberoot u -> cuberoot u' -> econg pi x u -> econg pi x u' -> u = u'.
Proof.
  intros pi p x u u' Hn Hp Hu Hu' Hxu Hxu'.
  destruct (cube_roots_distinct pi p Hn Hp) as [D1 [D2 D3]].
  assert (Huu' : econg pi u u')
    by (apply (econg_trans pi u x u'); [ apply econg_sym; exact Hxu | exact Hxu' ]).
  destruct Hu as [-> | [-> | ->]]; destruct Hu' as [-> | [-> | ->]];
    try reflexivity.
  - exfalso. apply D1. apply econg_sym. exact Huu'.
  - exfalso. apply D2. apply econg_sym. exact Huu'.
  - exfalso. apply D1. exact Huu'.
  - exfalso. apply D3. apply econg_sym. exact Huu'.
  - exfalso. apply D2. exact Huu'.
  - exfalso. apply D3. exact Huu'.
Qed.

(* ----------------------------------------------------------------- *)
(*  D.  the product of two nondivisibles is a nondivisible             *)
(* ----------------------------------------------------------------- *)
Lemma pi_ndvd_mul : forall pi alpha beta, eirred pi ->
  ~ edvd pi alpha -> ~ edvd pi beta -> ~ edvd pi (emul alpha beta).
Proof.
  intros pi alpha beta Hirr Ha Hb Hab.
  destruct (irred_prime pi alpha beta Hirr Hab) as [H | H];
    [ exact (Ha H) | exact (Hb H) ].
Qed.

(* ----------------------------------------------------------------- *)
(*  E.  MULTIPLICATIVITY                                               *)
(* ----------------------------------------------------------------- *)
Lemma cubic_symbol_mul_cong : forall pi alpha beta (n : nat) u v,
  econg pi (epow alpha n) u -> econg pi (epow beta n) v ->
  econg pi (epow (emul alpha beta) n) (emul u v).
Proof.
  intros pi alpha beta n u v Ha Hb.
  rewrite epow_mul_dist. apply econg_mul; assumption.
Qed.

Theorem cubic_symbol_mul : forall (p : nat) (pi : Eis) (t : Z) (alpha beta u v w : Eis),
  prime (Z.of_nat p) -> (7 <= p)%nat -> Nat.divide 3 (p - 1)%nat ->
  enorm pi = Z.of_nat p ->
  edvd pi (esub (eZ t) eom) ->
  ~ edvd pi alpha -> ~ edvd pi beta ->
  cuberoot u -> cuberoot v -> cuberoot w ->
  econg pi (epow alpha ((p - 1) / 3)) u ->
  econg pi (epow beta ((p - 1) / 3)) v ->
  econg pi (epow (emul alpha beta) ((p - 1) / 3)) w ->
  w = emul u v.
Proof.
  intros p pi t alpha beta u v w Hp Hp7 Hd Hn Ht Ha Hb Hu Hv Hw Hca Hcb Hcw.
  apply (cuberoot_unique pi (Z.of_nat p) (epow (emul alpha beta) ((p - 1) / 3))
           w (emul u v) Hn ltac:(lia) Hw (cuberoot_mul u v Hu Hv) Hcw).
  apply cubic_symbol_mul_cong; assumption.
Qed.

(* the symbol of a product EXISTS and equals the product of the symbols *)
Corollary cubic_symbol_mul_exists :
  forall (p : nat) (pi : Eis) (t : Z) (alpha beta u v : Eis),
  prime (Z.of_nat p) -> (7 <= p)%nat -> Nat.divide 3 (p - 1)%nat ->
  enorm pi = Z.of_nat p ->
  edvd pi (esub (eZ t) eom) ->
  ~ edvd pi alpha -> ~ edvd pi beta ->
  cuberoot u -> cuberoot v ->
  econg pi (epow alpha ((p - 1) / 3)) u ->
  econg pi (epow beta ((p - 1) / 3)) v ->
  cuberoot (emul u v)
  /\ econg pi (epow (emul alpha beta) ((p - 1) / 3)) (emul u v).
Proof.
  intros p pi t alpha beta u v Hp Hp7 Hd Hn Ht Ha Hb Hu Hv Hca Hcb.
  split; [ apply cuberoot_mul; assumption | ].
  apply cubic_symbol_mul_cong; assumption.
Qed.

Print Assumptions cuberoot_unique.
Print Assumptions cubic_symbol_mul.
