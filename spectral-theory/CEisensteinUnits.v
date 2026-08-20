(* ================================================================= *)
(*  CEisensteinUnits.v  —  units and divisibility in Z[omega].         *)
(*                                                                    *)
(*    econj        : the conjugate, a + b om  |->  (a-b) - b om        *)
(*    emul_econj   : z . conj z = N(z)        (as an element of Z[om]) *)
(*    eunit_iff    : z is a unit  <->  N(z) = 1                        *)
(*    eunits_six   : the units are exactly +-1, +-om, +-om^2           *)
(*    edvd_norm    : d | z  =>  N(d) | N(z)   in Z                     *)
(*    norm_prime_irred : N(z) prime  =>  z is irreducible              *)
(*                                                                    *)
(*  The norm is what makes all of this mechanical.  It turns a         *)
(*  question about Z[omega] -- where there is no order and no obvious  *)
(*  induction -- into a question about nonnegative integers, where     *)
(*  there is both.  Each of the four main results is that translation  *)
(*  applied once:                                                      *)
(*                                                                    *)
(*    unit                  <-> N = 1                                  *)
(*    divisibility          ->  divisibility of norms                  *)
(*    N prime               ->  irreducible                            *)
(*                                                                    *)
(*  ONE DIRECTION OF eunit_iff IS CONSTRUCTIVE and the other is not    *)
(*  quite: N(z) = 1 gives the inverse explicitly, namely conj z,       *)
(*  because z . conj z = N(z) exactly.  That identity is the reason    *)
(*  the conjugate is worth defining at all -- it is the inverse        *)
(*  whenever there is one.                                             *)
(*                                                                    *)
(*  eunits_six comes from 4N = (2a-b)^2 + 3b^2 again: N = 1 forces     *)
(*  3b^2 <= 4, hence b in {-1,0,1}, and each case leaves a quadratic   *)
(*  in a with two roots.  Six in total, which is the right answer --   *)
(*  Z[omega] has six units, unlike Z[i]'s four, and that extra factor  *)
(*  of om is exactly the cube root the whole layer is built on.        *)
(*  Axiom-clean.                                                       *)
(* ================================================================= *)

From Stdlib Require Import ZArith Znumtheory Lia.
Require Import CEisenstein.
Open Scope Z_scope.

(* ----------------------------------------------------------------- *)
(*  A.  the conjugate, and z . conj z = N(z)                           *)
(* ----------------------------------------------------------------- *)
Definition econj (z : Eis) : Eis := mkEis (ea z - eb z) (- eb z).

Lemma emul_econj : forall z, emul z (econj z) = mkEis (enorm z) 0.
Proof.
  intros [a b]. unfold emul, econj, enorm; cbn [ea eb].
  apply Eis_eq; ring.
Qed.

Lemma enorm_econj : forall z, enorm (econj z) = enorm z.
Proof. intros [a b]. unfold enorm, econj; cbn [ea eb]. ring. Qed.

Lemma enorm_eone : enorm eone = 1.
Proof. unfold enorm, eone; cbn [ea eb]. ring. Qed.

(* ----------------------------------------------------------------- *)
(*  B.  units                                                          *)
(* ----------------------------------------------------------------- *)
Definition eunit (z : Eis) : Prop := exists u, emul z u = eone.

Theorem eunit_norm : forall z, eunit z -> enorm z = 1.
Proof.
  intros z [u Hu].
  assert (H : enorm z * enorm u = 1)
    by (rewrite <- enorm_mul, Hu; apply enorm_eone).
  pose proof (enorm_nonneg z). pose proof (enorm_nonneg u).
  destruct (Z.mul_eq_1 _ _ H) as [Hc | Hc]; lia.
Qed.

Theorem norm_eunit : forall z, enorm z = 1 -> eunit z.
Proof.
  intros z H. exists (econj z).
  rewrite emul_econj, H. unfold eone. reflexivity.
Qed.

Theorem eunit_iff : forall z, eunit z <-> enorm z = 1.
Proof. intro z. split; [ apply eunit_norm | apply norm_eunit ]. Qed.

(* the six units:  +-1, +-om, +-om^2  *)
Theorem eunits_six : forall z, eunit z ->
  z = mkEis 1 0 \/ z = mkEis (-1) 0
  \/ z = mkEis 0 1 \/ z = mkEis 0 (-1)
  \/ z = mkEis 1 1 \/ z = mkEis (-1) (-1).
Proof.
  intros z Hu. apply eunit_norm in Hu.
  pose proof (enorm_four z) as H4. rewrite Hu in H4.
  destruct z as [a b]; cbn [ea eb] in *.
  assert (Hb : b = -1 \/ b = 0 \/ b = 1) by nia.
  unfold enorm in Hu; cbn [ea eb] in Hu.
  destruct Hb as [Hb | [Hb | Hb]]; subst b.
  - assert (Ha : a = 0 \/ a = -1) by nia.
    destruct Ha; subst a; [ right; right; right; left | right; right; right; right; right ];
      reflexivity.
  - assert (Ha : a = 1 \/ a = -1) by nia.
    destruct Ha; subst a; [ left | right; left ]; reflexivity.
  - assert (Ha : a = 0 \/ a = 1) by nia.
    destruct Ha; subst a; [ right; right; left | right; right; right; right; left ];
      reflexivity.
Qed.

(* om itself is a unit, and om^2 is its inverse *)
Corollary eom_unit : eunit eom.
Proof. apply norm_eunit. unfold enorm, eom; cbn [ea eb]. ring. Qed.

(* ----------------------------------------------------------------- *)
(*  C.  divisibility                                                   *)
(* ----------------------------------------------------------------- *)
Definition edvd (d z : Eis) : Prop := exists q, z = emul d q.

Lemma edvd_refl : forall z, edvd z z.
Proof. intro z. exists eone. rewrite emul_comm, emul_1. reflexivity. Qed.

Lemma edvd_trans : forall x y z, edvd x y -> edvd y z -> edvd x z.
Proof.
  intros x y z [q Hq] [r Hr]. exists (emul q r).
  rewrite Hr, Hq, emul_assoc. reflexivity.
Qed.

Theorem edvd_norm : forall d z, edvd d z -> (enorm d | enorm z).
Proof.
  intros d z [q Hq]. exists (enorm q).
  rewrite Hq, enorm_mul. ring.
Qed.

(* units divide everything, and are exactly the divisors of 1 *)
Theorem eunit_edvd : forall u z, eunit u -> edvd u z.
Proof.
  intros u z [v Hv]. exists (emul v z).
  rewrite <- emul_assoc, Hv, emul_1. reflexivity.
Qed.

Theorem edvd_eone : forall z, edvd z eone <-> eunit z.
Proof.
  intro z. split.
  - intros [q Hq]. exists q. symmetry. exact Hq.
  - intros [u Hu]. exists u. symmetry. exact Hu.
Qed.

(* ----------------------------------------------------------------- *)
(*  D.  a prime norm forces irreducibility                             *)
(* ----------------------------------------------------------------- *)
Theorem norm_prime_irred : forall z d q,
  prime (enorm z) -> z = emul d q -> eunit d \/ eunit q.
Proof.
  intros z d q Hp Hz.
  assert (Hn : enorm d * enorm q = enorm z)
    by (rewrite Hz, enorm_mul; reflexivity).
  assert (Hdvd : (enorm d | enorm z)) by (exists (enorm q); lia).
  pose proof (prime_divisors _ Hp _ Hdvd) as Hcases.
  pose proof (enorm_nonneg d) as Hd0. pose proof (enorm_nonneg q) as Hq0.
  destruct Hp as [Hgt _].
  destruct Hcases as [H | [H | [H | H]]].
  - lia.
  - left. apply norm_eunit. exact H.
  - right. apply norm_eunit. rewrite H in Hn. nia.
  - lia.
Qed.

Print Assumptions eunit_iff.
Print Assumptions eunits_six.
Print Assumptions norm_prime_irred.
