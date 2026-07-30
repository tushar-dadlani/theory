(* ================================================================= *)
(*  PadicValuation.v  —  a COMPUTABLE p-adic valuation and the         *)
(*  computable factorisation code (peel ps m) = m.                    *)
(*                                                                    *)
(*  PrimeFactorizationExists only has factorisation EXISTENCE as a     *)
(*  Prop (code_surj, via well-founded recursion) — no extractable      *)
(*  exponent tuple.  This file supplies the computational content:    *)
(*                                                                    *)
(*    vp p m  = the p-adic valuation of m        (fuel = Z.to_nat m);  *)
(*    peel ps m = the exponent tuple of m over the prime list ps;      *)
(*    peel_code : code ps (peel ps m) = m        (ps-smooth m > 0).    *)
(*                                                                    *)
(*  So the factorisation of a ps-smooth number is now a genuine        *)
(*  FUNCTION, not just an existence proof.  Axiom-free over Z.         *)
(* ================================================================= *)

Require Import PrimeFactorizationN PrimeFactorizationExists.
From Stdlib Require Import ZArith Znumtheory Lia List.
Import ListNotations.
Open Scope Z_scope.

(* ----------------------------------------------------------------- *)
(*  The fuel-bounded valuation and its correctness.                  *)
(* ----------------------------------------------------------------- *)

Fixpoint vpf (fuel : nat) (p m : Z) : nat :=
  match fuel with
  | O => O
  | S f => if Z.eqb (m mod p) 0 then S (vpf f p (m / p)) else O
  end.

Definition vp (p m : Z) : nat := vpf (Z.to_nat m) p m.

Lemma vpf_S_div : forall f p m, m mod p = 0 -> vpf (S f) p m = S (vpf f p (m / p)).
Proof. intros f p m H; cbn [vpf]; rewrite (proj2 (Z.eqb_eq (m mod p) 0) H); reflexivity. Qed.

Lemma vpf_S_0 : forall f p m, m mod p <> 0 -> vpf (S f) p m = O.
Proof.
  intros f p m H; cbn [vpf].
  destruct (m mod p =? 0) eqn:E; [ apply Z.eqb_eq in E; contradiction | reflexivity ].
Qed.

Lemma vpf_correct : forall fuel p m, 2 <= p -> 0 < m -> (Z.to_nat m <= fuel)%nat ->
  exists m', m = p ^ Z.of_nat (vpf fuel p m) * m' /\ ~ (p | m') /\ 0 < m'.
Proof.
  induction fuel as [| f IH]; intros p m Hp Hm Hfuel.
  - exfalso.
    assert (Hid : Z.of_nat (Z.to_nat m) = m) by (apply Z2Nat.id; lia).
    assert (Z.to_nat m = 0)%nat by lia.
    rewrite H in Hid; simpl in Hid; lia.
  - destruct (Z.eq_dec (m mod p) 0) as [E | E].
    + rewrite (vpf_S_div f p m E).
      assert (Hp0 : p <> 0) by lia.
      assert (Hm1 : m = p * (m / p))
        by (pose proof (Z_div_mod_eq_full m p) as Hd; rewrite E in Hd; lia).
      set (m1 := m / p) in *.
      assert (Hm1pos : 0 < m1) by nia.
      assert (Hf1 : (Z.to_nat m1 < Z.to_nat m)%nat) by (apply Z2Nat.inj_lt; nia).
      assert (Hfuel1 : (Z.to_nat m1 <= f)%nat) by lia.
      destruct (IH p m1 Hp Hm1pos Hfuel1) as [m' [Hval [Hnd Hpos]]].
      exists m'; split; [ | split; [ exact Hnd | exact Hpos ] ].
      rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
      rewrite Hm1; rewrite Hval at 1; ring.
    + rewrite (vpf_S_0 f p m E).
      exists m; split;
        [ change (Z.of_nat O) with 0%Z; rewrite Z.pow_0_r; ring | split; [ | exact Hm ] ].
      intro Hpm; apply E, (proj2 (Z.mod_divide m p ltac:(lia))), Hpm.
Qed.

Lemma vp_correct : forall p m, 2 <= p -> 0 < m ->
  exists m', m = p ^ Z.of_nat (vp p m) * m' /\ ~ (p | m') /\ 0 < m'.
Proof. intros p m Hp Hm; apply vpf_correct; [ exact Hp | exact Hm | lia ]. Qed.

(* ----------------------------------------------------------------- *)
(*  The factorisation function and its correctness.                  *)
(* ----------------------------------------------------------------- *)

Fixpoint peel (ps : list Z) (m : Z) : list nat :=
  match ps with
  | [] => []
  | p :: ps' => vp p m :: peel ps' (m / p ^ Z.of_nat (vp p m))
  end.

Lemma peel_length : forall ps m, length (peel ps m) = length ps.
Proof. induction ps as [| p ps' IH]; intro m; simpl; [ reflexivity | rewrite IH; reflexivity ]. Qed.

Lemma peel_code : forall ps m, Forall prime ps -> NoDup ps -> 0 < m ->
  (forall q, prime q -> (q | m) -> In q ps) ->
  code ps (peel ps m) = m.
Proof.
  induction ps as [| p ps' IH]; intros m Hpr Hnd Hm Hsm.
  - cbn [peel code].
    destruct (Z.eq_dec m 1) as [-> | Hn1]; [ reflexivity | ].
    exfalso; assert (H1m : 1 < m) by lia.
    destruct (has_prime_divisor m H1m) as [q [Hq Hqm]].
    specialize (Hsm q Hq Hqm); inversion Hsm.
  - inversion Hpr as [| ? ? Hp Hpr']; subst.
    inversion Hnd as [| ? ? Hpni Hnd']; subst.
    assert (Hp2 : 2 <= p) by (destruct Hp as [Hp1 _]; lia).
    destruct (vp_correct p m Hp2 Hm) as [m1 [Hval [Hndp Hpos1]]].
    assert (Hpv0 : p ^ Z.of_nat (vp p m) <> 0)
      by (apply Z.pow_nonzero; lia).
    assert (Hdiv : m / p ^ Z.of_nat (vp p m) = m1).
    { rewrite Hval at 1; rewrite (Z.mul_comm (p ^ Z.of_nat (vp p m)) m1);
        apply Z.div_mul; exact Hpv0. }
    cbn [peel code]; rewrite Hdiv.
    assert (Hsm1 : forall q, prime q -> (q | m1) -> In q ps').
    { intros q Hq Hqm1.
      assert (Hqm : (q | m)) by (rewrite Hval; apply Z.divide_mul_r; exact Hqm1).
      destruct (Hsm q Hq Hqm) as [Heq | Hin]; [ | exact Hin ].
      subst q; exfalso; apply Hndp; exact Hqm1. }
    rewrite (IH m1 Hpr' Hnd' Hpos1 Hsm1); symmetry; exact Hval.
Qed.

Print Assumptions vp_correct.
Print Assumptions peel_code.

(* ================================================================= *)
(*  END PadicValuation.v                                             *)
(*  vp / peel give the factorisation of a ps-smooth positive as a      *)
(*  computable FUNCTION with code ps (peel ps m) = m — the             *)
(*  constructive content behind ProductFormulaQ's existence.          *)
(* ================================================================= *)
