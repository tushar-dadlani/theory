(* ================================================================= *)
(*  CEisensteinGcd.v  —  BEZOUT and Euclid's lemma in Z[omega].        *)
(*                                                                    *)
(*    ebezout    : any z, d have a common divisor g with               *)
(*                   g = u.z + v.d   and   every common divisor | g    *)
(*    irred_prime: an irreducible element is PRIME --                  *)
(*                   pi | x.y  =>  pi | x  or  pi | y                  *)
(*                                                                    *)
(*  BEZOUT IS PROVED, NOT COMPUTED.  A gcd FUNCTION would need         *)
(*  well-founded recursion on the norm and all the plumbing that       *)
(*  brings; the existential statement carries the entire mathematical  *)
(*  content and is proved by ordinary induction on a nat BOUND for     *)
(*  N(d), which euclid makes strictly decrease.  Nothing downstream    *)
(*  wants to evaluate a gcd, so nothing is lost.                       *)
(*                                                                    *)
(*  The induction is the classical one: on d = 0 the answer is z       *)
(*  itself, and otherwise z = d.q + r replaces (z,d) by (d,r) with     *)
(*  N(r) < N(d).  The Bezout coefficients transport by                 *)
(*      u.d + v.r = u.d + v.(z - d.q) = v.z + (u - v.q).d,             *)
(*  which is the only actual computation in the proof.                 *)
(*                                                                    *)
(*  IRRED_PRIME is what Bezout is for.  The two branches are the       *)
(*  familiar ones: writing pi = g.h for the gcd g of pi and x, either  *)
(*  g is a unit -- and Bezout scaled by its inverse gives              *)
(*  1 = u.pi + v.x, hence y = u.pi.y + v.(x.y), and pi divides both    *)
(*  terms -- or h is a unit, and then pi divides g, which divides x.   *)
(*  This is the step that makes unique factorization possible.         *)
(*  Axiom-clean.                                                       *)
(* ================================================================= *)

From Stdlib Require Import ZArith Znumtheory Lia Ring.
Require Import CEisenstein CEisensteinUnits CEisensteinDiv.
Open Scope Z_scope.

(* ----------------------------------------------------------------- *)
(*  A.  divisibility closure properties                                *)
(* ----------------------------------------------------------------- *)
(* equality in Z[omega] is decidable -- two integer coordinates *)
Lemma Eis_dec : forall z w : Eis, {z = w} + {z <> w}.
Proof.
  intros [a b] [c d].
  destruct (Z.eq_dec a c) as [Hac | Hac];
    destruct (Z.eq_dec b d) as [Hbd | Hbd];
    [ left; subst; reflexivity
    | right; intro H; inversion H; contradiction ..].
Qed.

Lemma emul_0 : forall z, emul z ezero = ezero.
Proof. intro z. ring. Qed.

Lemma edvd_zero : forall c, edvd c ezero.
Proof. intro c. exists ezero. rewrite emul_0. reflexivity. Qed.

Lemma edvd_add : forall c x y, edvd c x -> edvd c y -> edvd c (eadd x y).
Proof.
  intros c x y [p Hp] [q Hq]. exists (eadd p q).
  rewrite Hp, Hq. ring.
Qed.

Lemma edvd_sub : forall c x y, edvd c x -> edvd c y -> edvd c (esub x y).
Proof.
  intros c x y [p Hp] [q Hq]. exists (esub p q).
  rewrite Hp, Hq. unfold esub. ring.
Qed.

Lemma edvd_mul_r : forall c x y, edvd c x -> edvd c (emul x y).
Proof.
  intros c x y [p Hp]. exists (emul p y). rewrite Hp. ring.
Qed.

(* ----------------------------------------------------------------- *)
(*  B.  Bezout                                                         *)
(* ----------------------------------------------------------------- *)
Definition Bez (z d : Eis) : Prop :=
  exists g u v,
    edvd g z /\ edvd g d
    /\ g = eadd (emul u z) (emul v d)
    /\ (forall c, edvd c z -> edvd c d -> edvd c g).

Lemma Bez_zero_r : forall z, Bez z ezero.
Proof.
  intro z. exists z, eone, ezero.
  repeat split.
  - apply edvd_refl.
  - apply edvd_zero.
  - ring.
  - intros c Hc _. exact Hc.
Qed.

Lemma ebezout_aux : forall (k : nat) (z d : Eis),
  (Z.to_nat (enorm d) <= k)%nat -> Bez z d.
Proof.
  induction k as [| k IH]; intros z d Hk.
  - (* N(d) = 0, so d = 0 *)
    assert (Hd : d = ezero).
    { apply enorm_zero. pose proof (enorm_nonneg d) as H0.
      assert (Z.to_nat (enorm d) = 0)%nat by lia.
      lia. }
    rewrite Hd. apply Bez_zero_r.
  - destruct (Eis_dec d ezero) as [Hd | Hd].
    + rewrite Hd. apply Bez_zero_r.
    + (* divide, and recurse on (d, r) *)
      destruct (euclid z d Hd) as [Hz Hn].
      set (q := equo z d). set (r := erem z d).
      fold q r in Hz. fold r in Hn.
      assert (Hrk : (Z.to_nat (enorm r) <= k)%nat).
      { pose proof (enorm_nonneg r) as Hr0. pose proof (enorm_nonneg d) as Hd0.
        apply (proj1 (Z2Nat.inj_lt _ _ Hr0 Hd0)) in Hn. lia. }
      destruct (IH d r Hrk) as [g [u [v [Hgd [Hgr [Hg Huniv]]]]]].
      exists g, v, (esub u (emul v q)).
      repeat split.
      * (* g | z, since z = d q + r *)
        rewrite Hz. apply edvd_add; [ apply edvd_mul_r; exact Hgd | exact Hgr ].
      * exact Hgd.
      * (* u d + v r = v z + (u - v q) d *)
        assert (Hr : r = esub z (emul d q)) by (unfold r, erem; reflexivity).
        rewrite Hg, Hr. unfold esub. ring.
      * intros c Hcz Hcd.
        apply Huniv; [ exact Hcd | ].
        assert (Hr : r = esub z (emul d q)) by (unfold r, erem; reflexivity).
        rewrite Hr. apply edvd_sub; [ exact Hcz | apply edvd_mul_r; exact Hcd ].
Qed.

Theorem ebezout : forall z d, Bez z d.
Proof. intros z d. apply (ebezout_aux (Z.to_nat (enorm d))). lia. Qed.

(* ----------------------------------------------------------------- *)
(*  C.  irreducible implies prime                                      *)
(* ----------------------------------------------------------------- *)
Definition eirred (pi : Eis) : Prop :=
  ~ eunit pi /\ pi <> ezero
  /\ forall d q, pi = emul d q -> eunit d \/ eunit q.

Theorem irred_prime : forall pi x y, eirred pi ->
  edvd pi (emul x y) -> edvd pi x \/ edvd pi y.
Proof.
  intros pi x y [Hnu [Hn0 Hirr]] Hdvd.
  destruct (ebezout pi x) as [g [u [v [Hgp [Hgx [Hg Huniv]]]]]].
  destruct Hgp as [h Hh].
  destruct (Hirr g h Hh) as [Hgu | Hhu].
  - (* g is a unit: Bezout scaled gives 1 = u' pi + v' x *)
    right.
    destruct Hgu as [gi Hgi].
    destruct Hdvd as [w Hw].
    exists (eadd (emul (emul u gi) y) (emul (emul v gi) w)).
    (* y = (u gi) pi y + (v gi) (x y),  and x y = pi w *)
    assert (Hone : eadd (emul (emul u gi) pi) (emul (emul v gi) x) = eone).
    { rewrite <- Hgi, Hg. ring. }
    assert (Hy : y = eadd (emul (emul (emul u gi) y) pi)
                          (emul (emul v gi) (emul x y))).
    { transitivity (emul (eadd (emul (emul u gi) pi) (emul (emul v gi) x)) y);
        [ rewrite Hone; ring | ring ]. }
    rewrite Hy at 1. rewrite Hw. ring.
  - (* h is a unit: pi divides g, which divides x *)
    left.
    destruct Hhu as [hi Hhi].
    apply (edvd_trans pi g x); [ | exact Hgx ].
    exists hi. rewrite Hh.
    assert (Hgg : emul (emul g h) hi = g) by (rewrite emul_assoc, Hhi; ring).
    rewrite Hgg. reflexivity.
Qed.

Print Assumptions ebezout.
Print Assumptions irred_prime.
