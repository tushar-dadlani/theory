(* ================================================================= *)
(*  CEisensteinDiv.v  —  EUCLIDEAN DIVISION in Z[omega].               *)
(*                                                                    *)
(*    EisRing : Z[omega] registered as a commutative ring              *)
(*    equo, erem : quotient and remainder                              *)
(*    euclid  : z = d.q + r  with  N(r) < N(d)      (d <> 0)           *)
(*                                                                    *)
(*  Z[omega] is Euclidean for the norm, and the proof is the lattice   *)
(*  one: divide in the FIELD, round to the nearest lattice point, and  *)
(*  bound the error by the covering radius.  Written over Z it never   *)
(*  leaves the integers -- rather than forming z/d, one forms          *)
(*  t = z . conj d, whose coordinates are integers, and rounds t/n     *)
(*  coordinatewise with n = N(d).                                      *)
(*                                                                    *)
(*  ROUNDING TO NEAREST, over Z, is (2A + n) / (2n) with Coq's floor   *)
(*  division.  Its defining property comes straight from Z.div_mod:    *)
(*  writing 2A + n = 2n.q + m with 0 <= m < 2n gives 2(A - n q) = m - n *)
(*  hence -n <= 2(A - n q) < n.  That is exactly a half-step bound,    *)
(*  with no case analysis on signs.                                    *)
(*                                                                    *)
(*  THE KEY IDENTITY is d.s = (n,0).r, where s is the rounding error   *)
(*  and r the remainder.  With the ring registered it is one ring      *)
(*  call, once d . conj d has been folded back to (n,0).  Taking norms *)
(*  turns it into N(s) = n.N(r), so a bound on the error bounds the    *)
(*  remainder.                                                          *)
(*                                                                    *)
(*  THE CONSTANT IS 3/4, not 1/2 as over Z[i]: each coordinate is off  *)
(*  by at most a half step, and N(x + y om) = x^2 - xy + y^2 at        *)
(*  x, y = 1/2 gives 1/4 + 1/4 + 1/4.  Comfortably below 1, which is   *)
(*  all that is needed -- the hexagonal lattice is in fact better than *)
(*  the square one here, but the crude bound already suffices.         *)
(*  Axiom-clean.                                                       *)
(* ================================================================= *)

From Stdlib Require Import ZArith Znumtheory Lia Ring.
Require Import CEisenstein CEisensteinUnits.
Open Scope Z_scope.

Definition esub (z w : Eis) : Eis := eadd z (eopp w).

(* ----------------------------------------------------------------- *)
(*  A.  Z[omega] is a commutative ring                                 *)
(* ----------------------------------------------------------------- *)
Lemma emul_distr_l : forall x y z, emul (eadd x y) z = eadd (emul x z) (emul y z).
Proof.
  intros [a b] [c d] [e f]; unfold emul, eadd; cbn [ea eb];
    apply Eis_eq; ring.
Qed.

Lemma EisRing : ring_theory ezero eone eadd emul esub eopp (@eq Eis).
Proof.
  constructor.
  - exact eadd_0.
  - exact eadd_comm.
  - intros x y z. symmetry. apply eadd_assoc.
  - exact emul_1.
  - exact emul_comm.
  - intros x y z. symmetry. apply emul_assoc.
  - exact emul_distr_l.
  - intros x y. reflexivity.
  - exact eadd_opp.
Qed.

Add Ring EisR : EisRing.

(* ----------------------------------------------------------------- *)
(*  B.  rounding to nearest, over Z                                    *)
(* ----------------------------------------------------------------- *)
Definition rnd (A n : Z) : Z := (2 * A + n) / (2 * n).

Lemma rnd_bound : forall A n, 0 < n ->
  - n <= 2 * (A - n * rnd A n) /\ 2 * (A - n * rnd A n) < n.
Proof.
  intros A n Hn. unfold rnd.
  set (m := (2 * A + n) mod (2 * n)).
  assert (Hmod : 2 * A + n = 2 * n * ((2 * A + n) / (2 * n)) + m)
    by (unfold m; apply Z.div_mod; lia).
  assert (Hrange : 0 <= m < 2 * n)
    by (unfold m; apply Z.mod_pos_bound; lia).
  lia.
Qed.

(* ----------------------------------------------------------------- *)
(*  C.  quotient and remainder                                         *)
(* ----------------------------------------------------------------- *)
Definition equo (z d : Eis) : Eis :=
  mkEis (rnd (ea (emul z (econj d))) (enorm d))
        (rnd (eb (emul z (econj d))) (enorm d)).

Definition erem (z d : Eis) : Eis := esub z (emul d (equo z d)).

Lemma euclid_eq : forall z d, z = eadd (emul d (equo z d)) (erem z d).
Proof. intros z d. unfold erem, esub. ring. Qed.

(* the norm of a rational integer *)
Lemma enorm_scalar : forall n, enorm (mkEis n 0) = n * n.
Proof. intro n. unfold enorm; cbn [ea eb]. ring. Qed.

Lemma emul_scalar : forall n q, emul (mkEis n 0) q = mkEis (n * ea q) (n * eb q).
Proof. intros n [qa qb]. unfold emul; cbn [ea eb]. apply Eis_eq; ring. Qed.

(* ----------------------------------------------------------------- *)
(*  D.  THE DIVISION THEOREM                                           *)
(* ----------------------------------------------------------------- *)
Theorem euclid : forall z d, d <> ezero ->
  z = eadd (emul d (equo z d)) (erem z d) /\ enorm (erem z d) < enorm d.
Proof.
  intros z d Hd. split; [ apply euclid_eq | ].
  set (n := enorm d).
  assert (Hn : 0 < n).
  { assert (Hnn : 0 <= n) by apply enorm_nonneg.
    assert (Hne : n <> 0) by (intro Hc; apply Hd; apply enorm_zero; exact Hc).
    lia. }
  set (t := emul z (econj d)).
  set (q := equo z d).
  set (s := esub t (emul (mkEis n 0) q)).
  set (r := erem z d).
  (* the rounding error, coordinatewise *)
  assert (Hs : s = mkEis (ea t - n * ea q) (eb t - n * eb q)).
  { unfold s, esub, eadd, eopp. rewrite emul_scalar. cbn [ea eb].
    apply Eis_eq; ring. }
  (* the key identity  d . s = (n,0) . r *)
  assert (Hkey : emul d s = emul (mkEis n 0) r).
  { unfold s, r, erem, t, q, n. rewrite <- (emul_econj d). ring. }
  (* norms *)
  assert (Hnorm : n * enorm s = n * n * enorm r).
  { assert (E : enorm (emul d s) = enorm (emul (mkEis n 0) r))
      by (rewrite Hkey; reflexivity).
    rewrite !enorm_mul, enorm_scalar in E. exact E. }
  (* the half-step bounds *)
  destruct (rnd_bound (ea t) n Hn) as [Ha1 Ha2].
  destruct (rnd_bound (eb t) n Hn) as [Hb1 Hb2].
  assert (Hqa : ea q = rnd (ea t) n) by reflexivity.
  assert (Hqb : eb q = rnd (eb t) n) by reflexivity.
  set (sa := ea t - n * ea q). set (sb := eb t - n * eb q).
  assert (Hsa : - n <= 2 * sa < n) by (unfold sa; rewrite Hqa; lia).
  assert (Hsb : - n <= 2 * sb < n) by (unfold sb; rewrite Hqb; lia).
  assert (Hns : enorm s = sa * sa - sa * sb + sb * sb)
    by (rewrite Hs; unfold enorm, sa, sb; cbn [ea eb]; ring).
  (* sa, sb are let-bound to terms containing Z.div; make them opaque
     before any nonlinear reasoning, or nia will try to unfold them *)
  clearbody sa sb.
  (* 4 N(s) <= 3 n^2 : each coordinate is within half a step *)
  assert (Hsq : 0 <= (sa + sb) * (sa + sb)) by apply Z.square_nonneg.
  assert (Hbound : 4 * enorm s <= 3 * (n * n)) by (rewrite Hns; nia).
  (* transport through N(s) = n N(r), cancelling n each time *)
  assert (Hns3 : enorm s = n * enorm r).
  { apply (Z.mul_reg_l _ _ n); [ lia | rewrite Hnorm; ring ]. }
  rewrite Hns3 in Hbound.
  assert (Hr : 4 * enorm r <= 3 * n).
  { apply (proj2 (Z.mul_le_mono_pos_l (4 * enorm r) (3 * n) n Hn)). nia. }
  pose proof (enorm_nonneg r) as Hr0.
  lia.
Qed.

Print Assumptions euclid.
