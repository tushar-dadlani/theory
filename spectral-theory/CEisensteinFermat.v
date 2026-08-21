(* ================================================================= *)
(*  CEisensteinFermat.v  —  FERMAT mod pi, and the cubic residue       *)
(*  symbol DEFINED rather than merely characterised.                   *)
(*                                                                    *)
(*    epow_add / epow_mul : exponent laws                              *)
(*    eZ_sub / eZ_mul / epow_eZ : Z -> Z[om] is a ring homomorphism    *)
(*    pi_dvd_p            : pi divides p, since p = pi . conj pi       *)
(*    norm_prime_eirred   : N(pi) prime => pi irreducible              *)
(*    efermat             : alpha^(p-1) = 1 (mod pi), pi not | alpha   *)
(*    cubic_symbol        : alpha^((p-1)/3) is congruent to EXACTLY    *)
(*                          ONE of 1, om, om^2                         *)
(*                                                                    *)
(*  Fermat transfers from Z because the residue field IS Z/p.  The     *)
(*  only care needed is to reduce alpha to a SMALL integer before      *)
(*  invoking ZmodPStar.fermat, which wants 1 <= a <= p-1: taking       *)
(*  r = m mod p and going alpha = m = r (mod pi) does it, and then     *)
(*  fermat applies to r directly.  Going the other way -- keeping m    *)
(*  and reducing the power -- would want a lemma of the form           *)
(*  (a^b) mod n = ((a mod n)^b) mod n, which this Stdlib does not      *)
(*  have; reducing the BASE first avoids needing it at all.            *)
(*                                                                    *)
(*  With Fermat, cubic_symbol_unique stops being a statement about     *)
(*  hypothetical cube roots and becomes a definition: alpha^((p-1)/3)  *)
(*  IS a cube root of unity mod pi -- its cube is alpha^(p-1) -- so it *)
(*  lands in exactly one of the three classes, and that class is the   *)
(*  cubic residue symbol of alpha.                                     *)
(*                                                                    *)
(*  Axiom-free, like the rest of the arithmetic tower.                 *)
(* ================================================================= *)

From Stdlib Require Import ZArith Znumtheory Arith Lia Ring.
Require Import ZmodPStar ZmodOrder PrimitiveRoot
        CEisenstein CEisensteinUnits CEisensteinDiv CEisensteinGcd
        CEisensteinSplit CEisensteinUFD CEisensteinResidue.
Open Scope Z_scope.

(* ----------------------------------------------------------------- *)
(*  A.  exponent laws, and Z -> Z[om] as a ring map                    *)
(* ----------------------------------------------------------------- *)
Lemma epow_add : forall z m n, epow z (m + n)%nat = emul (epow z m) (epow z n).
Proof.
  intros z m n. induction m as [| m IH]; cbn [epow Nat.add].
  - ring.
  - rewrite IH. ring.
Qed.

Lemma epow_mul : forall z m n, epow z (m * n)%nat = epow (epow z m) n.
Proof.
  intros z m n. induction n as [| n IH].
  - rewrite Nat.mul_0_r. cbn [epow]. reflexivity.
  - replace (m * S n)%nat with (m + m * n)%nat by lia.
    rewrite epow_add, IH. cbn [epow]. reflexivity.
Qed.

Lemma eZ_sub : forall x y, eZ (x - y) = esub (eZ x) (eZ y).
Proof.
  intros x y. unfold eZ, esub, eadd, eopp; cbn [ea eb].
  apply Eis_eq; ring.
Qed.

Lemma eZ_mul : forall x y, eZ (x * y) = emul (eZ x) (eZ y).
Proof.
  intros x y. unfold eZ, emul; cbn [ea eb]. apply Eis_eq; ring.
Qed.

Lemma eZ_one : eZ 1 = eone.
Proof. unfold eZ, eone. reflexivity. Qed.

Lemma epow_eZ : forall m (n : nat), epow (eZ m) n = eZ (m ^ Z.of_nat n).
Proof.
  intros m n. induction n as [| n IH]; cbn [epow].
  - rewrite <- eZ_one. reflexivity.
  - rewrite IH, <- eZ_mul. f_equal.
    rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. reflexivity.
Qed.

(* ----------------------------------------------------------------- *)
(*  B.  pi divides p, and a prime norm forces irreducibility           *)
(* ----------------------------------------------------------------- *)
Lemma pi_dvd_p : forall pi p, enorm pi = p -> edvd pi (eZ p).
Proof.
  intros pi p Hn. exists (econj pi). rewrite emul_econj, Hn. reflexivity.
Qed.

Lemma norm_prime_eirred : forall pi p, prime p -> enorm pi = p -> eirred pi.
Proof.
  intros pi p Hp Hn. destruct Hp as [Hgt Hrel] eqn:E.
  repeat split.
  - intro Hu. apply eunit_norm in Hu. lia.
  - intro Hc. apply enorm_zero in Hc. lia.
  - intros d q Hdq. apply (norm_prime_irred pi d q); [ rewrite Hn; exact Hp | exact Hdq ].
Qed.

(* ----------------------------------------------------------------- *)
(*  C.  FERMAT mod pi                                                  *)
(* ----------------------------------------------------------------- *)
Theorem efermat : forall (p : nat) (pi : Eis) (t : Z) (alpha : Eis),
  prime (Z.of_nat p) -> (2 <= p)%nat ->
  enorm pi = Z.of_nat p ->
  edvd pi (esub (eZ t) eom) ->
  ~ edvd pi alpha ->
  econg pi (epow alpha (p - 1)) eone.
Proof.
  intros p pi t alpha Hp Hp2 Hn Ht Hna.
  set (P := Z.of_nat p).
  assert (HP : 2 <= P) by (unfold P; lia).
  pose proof (pi_dvd_p pi P Hn) as Hpip.
  (* alpha is congruent to an integer m *)
  pose proof (cong_int pi t alpha Ht) as Hm.
  set (m := ea alpha + eb alpha * t).
  (* and m is congruent to its residue r, which lies in [1, p-1] *)
  set (r := m mod P).
  assert (Hr : 0 <= r < P) by (unfold r; apply Z.mod_pos_bound; lia).
  assert (Hmr : (P | m - r)) by (exists (m / P); unfold r; rewrite Z.mod_eq; lia).
  assert (Hcongmr : econg pi (eZ m) (eZ r)).
  { unfold econg. rewrite <- eZ_sub.
    apply (proj2 (int_cong_iff pi P (m - r) Hp Hn Hpip)). exact Hmr. }
  assert (Halr : econg pi alpha (eZ r))
    by (apply (econg_trans pi alpha (eZ m) (eZ r)); assumption).
  (* r is not divisible by p, else pi would divide alpha *)
  assert (Hr0 : r <> 0).
  { intro Hc. apply Hna.
    assert (Hz : econg pi alpha (eZ 0)) by (rewrite <- Hc; exact Halr).
    destruct Hz as [w Hw]. exists w.
    unfold esub, eZ, eadd, eopp in Hw; cbn [ea eb] in Hw.
    rewrite <- Hw. destruct alpha as [aa ab]; apply Eis_eq; cbn [ea eb]; ring. }
  (* Fermat in Z, applied to the small representative *)
  set (a := Z.to_nat r).
  assert (Ha : Z.of_nat a = r) by (unfold a; apply Z2Nat.id; lia).
  assert (Harange : (1 <= a <= p - 1)%nat) by (unfold P in *; lia).
  pose proof (fermat p a Hp Harange) as Hfer.
  assert (HfZ : (r ^ Z.of_nat (p - 1)) mod P = 1).
  { apply (f_equal Z.of_nat) in Hfer.
    rewrite Nat2Z.inj_mod, Nat2Z.inj_pow, Ha in Hfer. exact Hfer. }
  (* hence p divides r^(p-1) - 1 *)
  assert (Hdvd1 : (P | r ^ Z.of_nat (p - 1) - 1)).
  { apply Z.mod_divide; [ lia | ].
    rewrite Zminus_mod, HfZ, Z.mod_1_l by lia. reflexivity. }
  (* transport back *)
  apply (econg_trans pi _ (epow (eZ r) (p - 1)) _).
  - apply econg_pow. exact Halr.
  - rewrite epow_eZ. unfold econg. rewrite <- eZ_one, <- eZ_sub.
    apply (proj2 (int_cong_iff pi P _ Hp Hn Hpip)). exact Hdvd1.
Qed.

(* ----------------------------------------------------------------- *)
(*  D.  THE CUBIC RESIDUE SYMBOL                                       *)
(* ----------------------------------------------------------------- *)
Theorem cubic_symbol : forall (p : nat) (pi : Eis) (t : Z) (alpha : Eis),
  prime (Z.of_nat p) -> (7 <= p)%nat -> Nat.divide 3 (p - 1)%nat ->
  enorm pi = Z.of_nat p ->
  edvd pi (esub (eZ t) eom) ->
  ~ edvd pi alpha ->
  let x := epow alpha ((p - 1) / 3) in
  (econg pi x eone /\ ~ econg pi x eom /\ ~ econg pi x (emul eom eom))
  \/ (econg pi x eom /\ ~ econg pi x eone /\ ~ econg pi x (emul eom eom))
  \/ (econg pi x (emul eom eom) /\ ~ econg pi x eone /\ ~ econg pi x eom).
Proof.
  intros p pi t alpha Hp Hp7 Hd Hn Ht Hna x.
  assert (Hirr : eirred pi)
    by (apply (norm_prime_eirred pi (Z.of_nat p)); [ exact Hp | exact Hn ]).
  destruct Hd as [k Hk].
  assert (Hk3 : ((p - 1) / 3 = k)%nat) by (rewrite Hk; apply Nat.div_mul; lia).
  (* x^3 = alpha^(p-1) = 1 mod pi *)
  assert (Hcube : econg pi (epow x 3) eone).
  { unfold x. rewrite Hk3, <- epow_mul, <- Hk.
    apply (efermat p pi t alpha Hp ltac:(lia) Hn Ht Hna). }
  apply (cubic_symbol_unique pi (Z.of_nat p) x Hirr Hn ltac:(lia) Hcube).
Qed.

Print Assumptions efermat.
Print Assumptions cubic_symbol.
