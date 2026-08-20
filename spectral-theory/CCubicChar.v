(* ================================================================= *)
(*  CCubicChar.v  —  the CUBIC Dirichlet character and its Gauss sum.  *)
(*                                                                    *)
(*    w_pow_third : (w N)^{N/3} = om            (3 | N)                *)
(*    chi3        := dchar p g ((p-1)/3)                               *)
(*    chi3_om     : chi3 p g n = om^{dlog p g n}                       *)
(*    chi3_cube   : (chi3 p g n)^3 = 1          (p does not divide n)  *)
(*    chi3_values : chi3 p g n is 1, om, or om^2                       *)
(*    cubic_gauss_sum_abs : |g(chi3)|^2 = p     (p = 1 mod 3, p >= 7)  *)
(*                                                                    *)
(*  DirichletModP and GaussSum have been general in the character all  *)
(*  along -- dchar p g a0 for any a0, and gauss_sum_abs for any        *)
(*  0 < a0 < p-1.  QuadraticGaussSum takes a0 = (p-1)/2.  The cubic    *)
(*  instance a0 = (p-1)/3 had never been taken, so nothing in the repo *)
(*  had order 3 anywhere.                                              *)
(*                                                                    *)
(*  WHAT MAKES IT CUBIC, precisely, is w_pow_third.  dchar is built    *)
(*  from w (p-1), a root of unity of order p-1, and raising it to      *)
(*  (p-1)/3 lands exactly on om: e^{2 pi i/(p-1)} to the (p-1)/3 is    *)
(*  e^{2 pi i/3}.  So the character's values are literally powers of   *)
(*  om, and chi3_cube / chi3_values are then immediate from om^3 = 1   *)
(*  and om^n = om^{n mod 3}.  Without COmega this character would      *)
(*  still exist but nothing could be SAID about its order.             *)
(*                                                                    *)
(*  The Gauss sum needs no new analysis: gauss_sum_abs is already      *)
(*  general, so the cubic case is a side condition check, and          *)
(*  p >= 7 is exactly what makes 0 < (p-1)/3 < p-1 -- 7 being the      *)
(*  smallest prime that is 1 mod 3.  Axiom-clean.                      *)
(* ================================================================= *)

From Stdlib Require Import ZArith Znumtheory Arith Lia List Bool Reals Lra.
Require Import ZmodPStar ZmodOrder PrimitiveRoot DirichletModP
        ComplexField RootsOfUnity GaussSum COmega COmegaOrth.
Open Scope nat_scope.

(* ----------------------------------------------------------------- *)
(*  A.  the (N/3)-th power of a primitive N-th root IS om              *)
(* ----------------------------------------------------------------- *)
Lemma INR3 : INR 3 = 3%R.
Proof. simpl. lra. Qed.

Lemma w_pow_third : forall N, Nat.divide 3 N -> (0 < N)%nat ->
  Cpow (w N) (N / 3) = om.
Proof.
  intros N Hd HN. destruct Hd as [q Hq].
  assert (Hq0 : (0 < q)%nat) by lia.
  assert (Hdiv : (N / 3 = q)%nat) by (rewrite Hq; apply Nat.div_mul; lia).
  assert (HqR : INR q <> 0%R) by (apply not_0_INR; lia).
  assert (HNR : INR N = (INR q * 3)%R)
    by (rewrite Hq, mult_INR, INR3; reflexivity).
  unfold om, w. rewrite Hdiv, de_moivre.
  assert (Harg : (INR q * (2 * PI / INR N))%R = (2 * PI / INR 3)%R).
  { rewrite HNR, INR3. field. exact HqR. }
  rewrite Harg. reflexivity.
Qed.

(* ----------------------------------------------------------------- *)
(*  B.  the cubic character                                            *)
(* ----------------------------------------------------------------- *)
Definition chi3 (p g n : nat) : C := dchar p g ((p - 1) / 3) n.

Lemma chi3_om : forall p g n, Nat.divide 3 (p - 1) -> (0 < p - 1)%nat ->
  (n mod p <> 0)%nat ->
  chi3 p g n = Cpow om (dlog p g (n mod p)).
Proof.
  intros p g n Hd Hp Hn. unfold chi3, dchar.
  replace (n mod p =? 0)%nat with false
    by (symmetry; apply Nat.eqb_neq; exact Hn).
  rewrite Cpow_mul, (w_pow_third (p - 1) Hd Hp). reflexivity.
Qed.

(* the defining property: the character has ORDER 3 *)
Theorem chi3_cube : forall p g n, Nat.divide 3 (p - 1) -> (0 < p - 1)%nat ->
  (n mod p <> 0)%nat ->
  Cpow (chi3 p g n) 3 = C1.
Proof.
  intros p g n Hd Hp Hn.
  rewrite (chi3_om p g n Hd Hp Hn), <- Cpow_mul.
  replace (dlog p g (n mod p) * 3)%nat with (3 * dlog p g (n mod p))%nat by lia.
  rewrite Cpow_mul, om_pow3, Cpow_C1. reflexivity.
Qed.

(* and its values are exactly the cube roots of unity *)
Theorem chi3_values : forall p g n, Nat.divide 3 (p - 1) -> (0 < p - 1)%nat ->
  (n mod p <> 0)%nat ->
  chi3 p g n = C1 \/ chi3 p g n = om \/ chi3 p g n = Cmul om om.
Proof.
  intros p g n Hd Hp Hn.
  rewrite (chi3_om p g n Hd Hp Hn), om_pow_mod.
  assert (Hlt : (dlog p g (n mod p) mod 3 < 3)%nat)
    by (apply Nat.mod_upper_bound; lia).
  destruct (dlog p g (n mod p) mod 3)%nat as [|[|[|k]]] eqn:E; try lia.
  - left. cbn [Cpow]. reflexivity.
  - right; left. cbn [Cpow]. ring.
  - right; right. cbn [Cpow]. ring.
Qed.

(* ----------------------------------------------------------------- *)
(*  C.  the CUBIC GAUSS SUM                                            *)
(* ----------------------------------------------------------------- *)
Theorem cubic_gauss_sum_abs : forall p, prime (Z.of_nat p) ->
  Nat.divide 3 (p - 1) -> 7 <= p ->
  exists g, 1 <= g <= p - 1 /\ ord p g = p - 1 /\
    Cmul (gauss p g ((p - 1) / 3)) (Cconj (gauss p g ((p - 1) / 3)))
    = RtoC (INR p).
Proof.
  intros p Hp Hd Hp7.
  apply gauss_sum_abs; [ exact Hp | ].
  split.
  - apply Nat.div_str_pos. lia.
  - apply Nat.div_lt; lia.
Qed.

Print Assumptions w_pow_third.
Print Assumptions chi3_cube.
Print Assumptions cubic_gauss_sum_abs.
