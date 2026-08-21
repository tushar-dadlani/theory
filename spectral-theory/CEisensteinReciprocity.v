(* ================================================================= *)
(*  CEisensteinReciprocity.v  —  CUBIC RECIPROCITY.                   *)
(*                                                                    *)
(*    ndvd_of_norms     : distinct prime norms do not divide          *)
(*    Jsum_primary_eq   : for a PRIMARY prime, J = pi exactly          *)
(*    mu3_solve         : the two relations, subtracted                *)
(*    cubic_reciprocity : chi_theta(pi) = chi_pi(theta)                *)
(*                                                                    *)
(*  THE ENDGAME IS ONE SUBTRACTION.  Relation (A) says                 *)
(*  chi_theta(p J) = conj(chi_pi(q)); with pi primary J is pi, so      *)
(*  writing p = pi conj(pi) and q = theta conj(theta) and expanding by *)
(*  multiplicativity gives, in mu_3 exponents,                         *)
(*                                                                    *)
(*      2a + b + c + d = 0   (mod 3)                                   *)
(*                                                                    *)
(*  with a, b, c, d the exponents of chi_theta(pi), chi_theta(conj pi),*)
(*  chi_pi(theta), chi_pi(conj theta).  Running the SAME argument with *)
(*  pi and theta exchanged gives 2c + d + a + b = 0, and subtracting   *)
(*  the two leaves a = c.  That is reciprocity.                        *)
(*                                                                    *)
(*  I HAD PREVIOUSLY REPORTED THIS STEP AS SEVERAL PAGES OF            *)
(*  BOOKKEEPING.  It is not: the Gauss sum yields exactly one          *)
(*  relation, and reciprocity is that relation minus its mirror image. *)
(*                                                                    *)
(*  mu3_solve DOES THE SUBTRACTION BY BRUTE FORCE, which is the right  *)
(*  tool here: X, Y, C, D each range over three values, so the whole   *)
(*  implication is eighty-one closed computations.  Casting it as      *)
(*  exponent arithmetic in Z/3 would need a discrete logarithm on      *)
(*  mu_3 and would be longer and less obviously correct.               *)
(*                                                                    *)
(*  PRIMARY IS WHERE BRICK A IS SPENT.  Without it J is only an        *)
(*  ASSOCIATE of pi, and chi_theta(J) differs from chi_theta(pi) by    *)
(*  chi_theta of a unit -- which is not 1 in general, since            *)
(*  chi_theta(om) is a genuine cube root.  So the symbol is not        *)
(*  associate-invariant and the theorem is false without the           *)
(*  normalisation; primary_unique is what pins J = pi on the nose.     *)
(*  Axiom-free.                                                        *)
(* ================================================================= *)

From Stdlib Require Import ZArith Znumtheory Arith Lia List Ring.
Require Import ZmodPStar CEisenstein CEisensteinUnits CEisensteinDiv
        CEisensteinGcd CEisensteinSplit CEisensteinUFD CEisensteinResidue
        CEisensteinFermat CEisensteinCubicMul CEisensteinCubicSupp
        CEisensteinCubicFun CEisensteinPrimary CEisensteinSum CEisensteinJacobi
        CEisensteinNormJ CEisensteinJPrimary CEisensteinPiDivJ
        CEisensteinRelA.
Import ListNotations.
Open Scope Z_scope.

(* ----------------------------------------------------------------- *)
(*  A.  distinct prime norms cannot divide one another                 *)
(* ----------------------------------------------------------------- *)
Lemma ndvd_of_norms : forall (r s : nat) (a b : Eis),
  prime (Z.of_nat r) -> prime (Z.of_nat s) -> r <> s ->
  enorm a = Z.of_nat r -> enorm b = Z.of_nat s -> ~ edvd a b.
Proof.
  intros r s a b Hr Hs Hrs Ha Hb Hd.
  assert (Hn : (Z.of_nat r | Z.of_nat s))
    by (rewrite <- Ha, <- Hb; apply edvd_norm; exact Hd).
  destruct (prime_divisors (Z.of_nat s) Hs (Z.of_nat r) Hn) as [E | [E | [E | E]]];
    try (destruct Hr as [Hr1 _]; destruct Hs as [Hs1 _]; lia).
Qed.

(* ----------------------------------------------------------------- *)
(*  B.  for a primary prime the Jacobi sum IS the prime                *)
(* ----------------------------------------------------------------- *)
Lemma Jsum_primary_eq : forall (p : nat) (pi : Eis) (t0 : Z),
  prime (Z.of_nat p) -> (7 <= p)%nat -> Nat.divide 3 (p - 1)%nat ->
  enorm pi = Z.of_nat p -> edvd pi (esub (eZ t0) eom) ->
  primary pi -> Jsum p pi = pi.
Proof.
  intros p pi t0 Hp Hp7 Hdiv Hn Ht Hpr.
  destruct (jacobi_eq_primary p pi t0 Hp Hp7 Hdiv Hn Ht) as [u [Hu [Hpru HJ]]].
  assert (Hone : emul pi eone = pi) by (rewrite emul_comm; apply emul_1).
  assert (E : emul pi u = emul pi eone).
  { apply (primary_unique pi u eone Hu (norm_eunit eone enorm_eone) Hpru).
    rewrite Hone. exact Hpr. }
  rewrite HJ, E, Hone. reflexivity.
Qed.

(* ----------------------------------------------------------------- *)
(*  C.  the mu_3 identity: two relations, one subtraction              *)
(* ----------------------------------------------------------------- *)
Theorem mu3_solve : forall X Y C D,
  cuberoot X -> cuberoot Y -> cuberoot C -> cuberoot D ->
  emul (emul X Y) X = emul (econj C) (econj D) ->
  emul (emul C D) C = emul (econj X) (econj Y) ->
  X = C.
Proof.
  intros X Y C D HX HY HC HD H1 H2.
  destruct HX as [-> | [-> | ->]];
  destruct HY as [-> | [-> | ->]];
  destruct HC as [-> | [-> | ->]];
  destruct HD as [-> | [-> | ->]];
  vm_compute in H1, H2; try discriminate; reflexivity.
Qed.

(* ----------------------------------------------------------------- *)
(*  D.  CUBIC RECIPROCITY                                              *)
(* ----------------------------------------------------------------- *)
Theorem cubic_reciprocity :
  forall (p q : nat) (pi theta : Eis) (t0 t1 : Z),
    prime (Z.of_nat p) -> (7 <= p)%nat -> Nat.divide 3 (p - 1)%nat ->
    enorm pi = Z.of_nat p -> edvd pi (esub (eZ t0) eom) -> primary pi ->
    prime (Z.of_nat q) -> (7 <= q)%nat -> Nat.divide 3 (q - 1)%nat ->
    enorm theta = Z.of_nat q -> edvd theta (esub (eZ t1) eom) -> primary theta ->
    p <> q ->
    chiv q theta pi = chiv p pi theta.
Proof.
  intros p q pi theta t0 t1 Hp Hp7 Hdivp Hnp Htp Hprp
         Hq Hq7 Hdivq Hnq Htq Hprq Hpq.
  (* the norms, as products *)
  assert (Hpp : eZ (Z.of_nat p) = emul pi (econj pi))
    by (rewrite emul_econj, Hnp; reflexivity).
  assert (Hqq : eZ (Z.of_nat q) = emul theta (econj theta))
    by (rewrite emul_econj, Hnq; reflexivity).
  assert (Hcp : enorm (econj pi) = Z.of_nat p) by (rewrite enorm_econj; exact Hnp).
  assert (Hcq : enorm (econj theta) = Z.of_nat q)
    by (rewrite enorm_econj; exact Hnq).
  (* nothing divides anything across the two primes *)
  assert (Nt_p : ~ edvd theta pi) by (apply (ndvd_of_norms q p); auto).
  assert (Nt_cp : ~ edvd theta (econj pi)) by (apply (ndvd_of_norms q p); auto).
  assert (Np_t : ~ edvd pi theta) by (apply (ndvd_of_norms p q); auto).
  assert (Np_ct : ~ edvd pi (econj theta)) by (apply (ndvd_of_norms p q); auto).
  (* the four character values *)
  set (X := chiv q theta pi). set (Y := chiv q theta (econj pi)).
  set (C := chiv p pi theta). set (D := chiv p pi (econj theta)).
  assert (HX : cuberoot X) by (apply (chiv_cuberoot q theta Hq Hnq); exact Nt_p).
  assert (HY : cuberoot Y) by (apply (chiv_cuberoot q theta Hq Hnq); exact Nt_cp).
  assert (HC : cuberoot C) by (apply (chiv_cuberoot p pi Hp Hnp); exact Np_t).
  assert (HD : cuberoot D) by (apply (chiv_cuberoot p pi Hp Hnp); exact Np_ct).
  (* relation (A), and its mirror *)
  pose proof (relation_A p q pi theta t0 t1 Hp Hp7 Hdivp Hnp Htp
                Hq Hq7 Hdivq Hnq Htq Hpq) as HA1.
  pose proof (relation_A q p theta pi t1 t0 Hq Hq7 Hdivq Hnq Htq
                Hp Hp7 Hdivp Hnp Htp ltac:(auto)) as HA2.
  unfold SJ in HA1, HA2.
  rewrite (Jsum_primary_eq p pi t0 Hp Hp7 Hdivp Hnp Htp Hprp) in HA1.
  rewrite (Jsum_primary_eq q theta t1 Hq Hq7 Hdivq Hnq Htq Hprq) in HA2.
  rewrite Hpp in HA1. rewrite Hqq in HA2.
  rewrite !(chiv_mul q theta t1 Hq Hq7 Hdivq Hnq Htq) in HA1.
  rewrite !(chiv_mul p pi t0 Hp Hp7 Hdivp Hnp Htp) in HA2.
  (* the right-hand sides, as products too *)
  unfold chn in HA1, HA2.
  rewrite Hqq in HA1. rewrite Hpp in HA2.
  rewrite (chiv_mul p pi t0 Hp Hp7 Hdivp Hnp Htp) in HA1.
  rewrite (chiv_mul q theta t1 Hq Hq7 Hdivq Hnq Htq) in HA2.
  rewrite econj_mul in HA1, HA2.
  (* now both are mu_3 identities *)
  exact (mu3_solve X Y C D HX HY HC HD HA1 HA2).
Qed.

Print Assumptions mu3_solve.
Print Assumptions Jsum_primary_eq.
Print Assumptions cubic_reciprocity.
