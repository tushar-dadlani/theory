(* ================================================================= *)
(*  CEisensteinCubicSupp.v  —  supplementary laws for the cubic symbol.*)
(*                                                                    *)
(*    epow_om_mod3        : om^n depends only on n mod 3               *)
(*    epow_om_cuberoot    : every power of om is a cube root           *)
(*    pi_ndvd_unit        : an irreducible divides no unit             *)
(*    cubic_symbol_omega  : chi_pi(om) = om^{((p-1)/3) mod 3}          *)
(*    cubic_symbol_cube   : chi_pi(beta^3) = 1                         *)
(*    cubic_symbol_one    : chi_pi(1) = 1                              *)
(*                                                                    *)
(*  THE FIRST SUPPLEMENTARY LAW IS ALMOST DEFINITIONAL, and that is    *)
(*  the point.  chi_pi(alpha) is characterised as the cube root        *)
(*  congruent to alpha^{(p-1)/3}; when alpha is om itself, that power  *)
(*  is ALREADY a cube root, so no congruence has to be resolved -- the *)
(*  symbol is that power on the nose.  Reducing the exponent mod 3     *)
(*  then makes it depend only on p mod 9, which is the form the law is *)
(*  usually quoted in.                                                 *)
(*                                                                    *)
(*  cubic_symbol_cube is the easy half of Euler's criterion: a cube    *)
(*  has symbol 1, because (beta^3)^{(p-1)/3} = beta^{p-1} = 1 by       *)
(*  Fermat.  The converse -- symbol 1 implies a cube -- needs the      *)
(*  cyclic structure of (Z[om]/pi)^* and is NOT proved here.           *)
(*                                                                    *)
(*  THE SECOND SUPPLEMENTARY LAW, chi_pi(1-om), is not here either.    *)
(*  It depends on pi mod 9 rather than mod 3, and the standard proofs  *)
(*  go through Gauss or Jacobi sums in Z[om], which this development   *)
(*  does not have.  Axiom-free.                                        *)
(* ================================================================= *)

From Stdlib Require Import ZArith Znumtheory Arith Lia Ring.
Require Import ZmodPStar
        CEisenstein CEisensteinUnits CEisensteinDiv CEisensteinGcd
        CEisensteinSplit CEisensteinUFD CEisensteinUnique
        CEisensteinResidue CEisensteinFermat CEisensteinCubicMul.
Open Scope Z_scope.

(* ----------------------------------------------------------------- *)
(*  A.  powers of om                                                   *)
(* ----------------------------------------------------------------- *)
Lemma epow_eone : forall n : nat, epow eone n = eone.
Proof.
  induction n as [| n IH]; cbn [epow]; [ reflexivity | rewrite IH; ring ].
Qed.

Lemma epow_om_3 : epow eom 3 = eone.
Proof. cbn [epow]. unfold emul, eom, eone; cbn [ea eb]. apply Eis_eq; ring. Qed.

Lemma epow_om_mod3 : forall n : nat, epow eom n = epow eom (n mod 3).
Proof.
  intro n.
  assert (E : (n = 3 * (n / 3) + n mod 3)%nat) by apply Nat.Div0.div_mod.
  assert (H : epow eom (3 * (n / 3) + n mod 3)%nat = epow eom (n mod 3)).
  { rewrite epow_add, epow_mul, epow_om_3, epow_eone. ring. }
  rewrite <- H. f_equal. exact E.
Qed.

Lemma epow_om_cuberoot : forall n : nat, cuberoot (epow eom n).
Proof.
  intro n. rewrite epow_om_mod3.
  assert (Hlt : (n mod 3 < 3)%nat) by (apply Nat.mod_upper_bound; lia).
  destruct (n mod 3)%nat as [| [| [| k]]] eqn:E; try lia; unfold cuberoot.
  - left. cbn [epow]. reflexivity.
  - right; left. cbn [epow]. ring.
  - right; right. cbn [epow]. ring.
Qed.

(* ----------------------------------------------------------------- *)
(*  B.  an irreducible divides no unit                                 *)
(* ----------------------------------------------------------------- *)
Lemma pi_ndvd_unit : forall pi u, eirred pi -> eunit u -> ~ edvd pi u.
Proof.
  intros pi u Hirr Hu Hd.
  exact (proj1 Hirr (edvd_unit_unit pi u Hu Hd)).
Qed.

(* ----------------------------------------------------------------- *)
(*  C.  FIRST SUPPLEMENTARY LAW:  chi_pi(om) = om^{(p-1)/3}            *)
(* ----------------------------------------------------------------- *)
Theorem cubic_symbol_omega : forall (p : nat) (pi : Eis) (w : Eis),
  prime (Z.of_nat p) -> (7 <= p)%nat ->
  enorm pi = Z.of_nat p ->
  cuberoot w ->
  econg pi (epow eom ((p - 1) / 3)) w ->
  w = epow eom (((p - 1) / 3) mod 3).
Proof.
  intros p pi w Hp Hp7 Hn Hw Hc.
  apply (cuberoot_unique pi (Z.of_nat p) (epow eom ((p - 1) / 3))
           w (epow eom (((p - 1) / 3) mod 3)) Hn ltac:(lia) Hw).
  - apply epow_om_cuberoot.
  - exact Hc.
  - rewrite <- epow_om_mod3. apply econg_refl.
Qed.

(* om really does have a symbol: pi cannot divide a unit *)
Corollary pi_ndvd_omega : forall pi, eirred pi -> ~ edvd pi eom.
Proof. intros pi Hirr. apply pi_ndvd_unit; [ exact Hirr | apply eom_unit ]. Qed.

(* ----------------------------------------------------------------- *)
(*  D.  cubes have symbol 1  (the easy half of Euler's criterion)      *)
(* ----------------------------------------------------------------- *)
Theorem cubic_symbol_cube : forall (p : nat) (pi : Eis) (t : Z) (beta : Eis),
  prime (Z.of_nat p) -> (7 <= p)%nat -> Nat.divide 3 (p - 1)%nat ->
  enorm pi = Z.of_nat p ->
  edvd pi (esub (eZ t) eom) ->
  ~ edvd pi beta ->
  econg pi (epow (epow beta 3) ((p - 1) / 3)) eone.
Proof.
  intros p pi t beta Hp Hp7 Hd Hn Ht Hb.
  destruct Hd as [k Hk].
  assert (Hk3 : ((p - 1) / 3 = k)%nat) by (rewrite Hk; apply Nat.div_mul; lia).
  rewrite Hk3, <- epow_mul.
  replace (3 * k)%nat with (p - 1)%nat by lia.
  apply (efermat p pi t beta Hp ltac:(lia) Hn Ht Hb).
Qed.

Theorem cubic_symbol_one : forall (p : nat) (pi : Eis) (k : nat),
  econg pi (epow eone k) eone.
Proof. intros p pi k. rewrite epow_eone. apply econg_refl. Qed.

Print Assumptions cubic_symbol_omega.
Print Assumptions cubic_symbol_cube.
