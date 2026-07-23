(* ================================================================= *)
(*  AlgebraicOrthogonality.v                                         *)
(*                                                                    *)
(*  MAKING THE "INESSENTIAL R" PRECISE.                              *)
(*                                                                    *)
(*  The DFT / character orthogonality is not analytic -- it is the     *)
(*  geometric-series identity in disguise, and needs only a FIELD      *)
(*  containing an N-th root of unity, never the reals.  We prove it    *)
(*  once, ABSTRACTLY, over an arbitrary field with an abstract root    *)
(*  w (w^N = 1):                                                      *)
(*                                                                    *)
(*     w^m = 1   =>   sum_{k<N} w^(k m) = N.1                          *)
(*     w^m <> 1  =>   sum_{k<N} w^(k m) = 0                            *)
(*                                                                    *)
(*  `algebraic_orthogonality` is AXIOM-FREE ("Closed under the global  *)
(*  context") -- pure field algebra, no R, no C, no trig.             *)
(*                                                                    *)
(*  Then we exhibit our analytic model C = R[i] with w = exp(2 pi i/N) *)
(*  as ONE instantiation.  The same vanishing law, stated over C for   *)
(*  an ABSTRACT root omega (omega^N = 1), still avoids the order/trig  *)
(*  axiom (c_orth_vanish: only the 2 field-of-R axioms).  Supplying    *)
(*  the analytic w via w_pow_N (c_orth_w) is exactly what adds the      *)
(*  third, order-based axiom.  So the R-dependence of the character    *)
(*  theory is cosmetic: the mathematics is axiom-free algebra; R (and  *)
(*  its axioms) enter only through the analytic realisation of w.      *)
(* ================================================================= *)

From Stdlib Require Import Setoid Ring Field Arith Lia.

(* ================================================================= *)
(*  PART 1.  ORTHOGONALITY OVER AN ABSTRACT FIELD  (axiom-free)       *)
(* ================================================================= *)

Section Abstract.
  Variable A : Type.
  Variables (z o : A) (ad ml sb dv : A -> A -> A) (op iv : A -> A).
  Hypothesis FT : field_theory z o ad ml sb op dv iv (@eq A).
  Add Ring AbsR : (F_R FT).
  Add Field AbsF : FT.

  Fixpoint apow (a : A) (n : nat) : A :=
    match n with O => o | S k => ml a (apow a k) end.
  Fixpoint asum (f : nat -> A) (n : nat) : A :=
    match n with O => z | S k => ad (asum f k) (f k) end.
  Definition ofnat (n : nat) : A := asum (fun _ => o) n.

  Lemma apow_add : forall a m n, apow a (m + n) = ml (apow a m) (apow a n).
  Proof. intros a m n; induction m as [|m IH]; cbn [apow Nat.add]; [ ring | rewrite IH; ring ]. Qed.

  Lemma apow_mul : forall a m n, apow a (m * n) = apow (apow a m) n.
  Proof.
    intros a m n; induction n as [|n IH].
    - rewrite Nat.mul_0_r; reflexivity.
    - rewrite Nat.mul_succ_r, apow_add, IH; cbn [apow]; ring.
  Qed.

  Lemma apow_o : forall n, apow o n = o.
  Proof. induction n as [|n IH]; cbn [apow]; [ reflexivity | rewrite IH; ring ]. Qed.

  Lemma asum_ext : forall f g n, (forall k, f k = g k) -> asum f n = asum g n.
  Proof.
    intros f g n H; induction n as [|n IH]; cbn [asum];
      [ reflexivity | rewrite IH, H; reflexivity ].
  Qed.

  (* the geometric series:  (a - 1) * sum_{k<n} a^k = a^n - 1 *)
  Lemma ageom : forall a n, ml (sb a o) (asum (fun k => apow a k) n) = sb (apow a n) o.
  Proof.
    intros a n; induction n as [|n IH]; cbn [asum apow].
    - ring.
    - replace (ml (sb a o) (ad (asum (fun k => apow a k) n) (apow a n)))
        with (ad (ml (sb a o) (asum (fun k => apow a k) n)) (ml (sb a o) (apow a n))) by ring.
      rewrite IH; ring.
  Qed.

  (* cancel a nonzero factor in a field *)
  Lemma acancel : forall a b, a <> z -> ml a b = z -> b = z.
  Proof.
    intros a b Ha H; replace b with (ml (iv a) (ml a b)) by (field; exact Ha).
    rewrite H; ring.
  Qed.

  Variables (w : A) (N : nat).
  Hypothesis Hpow : apow w N = o.       (* w is an N-th root of unity *)

  (* if w^m = 1, every term is 1, so the sum is N * 1 *)
  Lemma orth_triv : forall m, apow w m = o -> asum (fun k => apow w (k * m)) N = ofnat N.
  Proof.
    intros m Hm; unfold ofnat; apply asum_ext; intro k.
    rewrite (Nat.mul_comm k m), apow_mul, Hm, apow_o; reflexivity.
  Qed.

  (* if w^m <> 1, the geometric series forces the sum to 0 *)
  Lemma orth_zero : forall m, apow w m <> o -> asum (fun k => apow w (k * m)) N = z.
  Proof.
    intros m Hm.
    assert (Hsum : asum (fun k => apow w (k * m)) N = asum (fun k => apow (apow w m) k) N)
      by (apply asum_ext; intro k; rewrite (Nat.mul_comm k m), apow_mul; reflexivity).
    rewrite Hsum.
    apply (acancel (sb (apow w m) o)).
    - intro Hc; apply Hm.
      replace (apow w m) with (ad (sb (apow w m) o) o) by ring; rewrite Hc; ring.
    - pose proof (ageom (apow w m) N) as HG.
      assert (HbN : apow (apow w m) N = o)
        by (rewrite <- apow_mul, (Nat.mul_comm m N), apow_mul, Hpow, apow_o; reflexivity).
      rewrite HbN in HG; replace (sb o o) with z in HG by ring; exact HG.
  Qed.

  Theorem algebraic_orthogonality :
       (forall a n, ml (sb a o) (asum (fun k => apow a k) n) = sb (apow a n) o)
    /\ (forall m, apow w m = o  -> asum (fun k => apow w (k * m)) N = ofnat N)
    /\ (forall m, apow w m <> o -> asum (fun k => apow w (k * m)) N = z).
  Proof. split; [ exact ageom | split; [ exact orth_triv | exact orth_zero ] ]. Qed.

End Abstract.

(* THE POINT: pure field algebra, zero axioms. *)
Print Assumptions algebraic_orthogonality.

(* ================================================================= *)
(*  PART 2.  THE ANALYTIC MODEL C = R[i] IS ONE INSTANTIATION         *)
(* ================================================================= *)

Require Import ComplexField RootsOfUnity.
Open Scope nat_scope.

(* The SAME vanishing law, concretely over C, for an ABSTRACT root      *)
(* omega with omega^N = 1 -- makes NO reference to w / cos / sin.       *)
(* Its footprint is only the 2 field-of-R axioms (no order axiom).      *)
Lemma c_orth_vanish : forall omega N m, (0 < N)%nat ->
  Cpow omega N = C1 -> Cpow omega m <> C1 ->
  Csum (fun k => Cpow omega (k * m)) N = C0.
Proof.
  intros omega N m HN HoN Hom.
  assert (Hsum : Csum (fun k => Cpow omega (k * m)) N
               = Csum (fun k => Cpow (Cpow omega m) k) N)
    by (apply Csum_ext; intro k; rewrite (Nat.mul_comm k m), Cpow_mul; reflexivity).
  rewrite Hsum.
  assert (Hne : Cminus (Cpow omega m) C1 <> C0).
  { intro Hc; apply Hom.
    replace (Cpow omega m) with (Cadd (Cminus (Cpow omega m) C1) C1) by ring;
      rewrite Hc; ring. }
  assert (HbN : Cpow (Cpow omega m) N = C1)
    by (rewrite <- Cpow_mul, (Nat.mul_comm m N), Cpow_mul, HoN, Cpow_C1; reflexivity).
  (* (omega^m - 1) * S = omega^(mN) - 1 = 1 - 1 = 0, and omega^m - 1 <> 0 *)
  assert (HS : Cmul (Cminus (Cpow omega m) C1) (Csum (fun k => Cpow (Cpow omega m) k) N) = C0).
  { pose proof (geom_sum (Cpow omega m) N) as HG;
      rewrite HbN in HG; replace (Cminus C1 C1) with C0 in HG by ring; exact HG. }
  (* cancel the nonzero factor *)
  replace (Csum (fun k => Cpow (Cpow omega m) k) N)
    with (Cmul (Cinv (Cminus (Cpow omega m) C1))
               (Cmul (Cminus (Cpow omega m) C1) (Csum (fun k => Cpow (Cpow omega m) k) N)))
    by (field; exact Hne).
  rewrite HS; ring.
Qed.

(* The analytic w = exp(2 pi i / N) is merely one such omega.  Supplying *)
(* w_pow_N (an ANALYTIC fact) recovers the DFT vanishing law -- and THIS *)
(* instantiation is where the order/trig axiom (sig_not_dec) enters.     *)
Corollary c_orth_w : forall N m, (0 < N)%nat -> Cpow (w N) m <> C1 ->
  Csum (fun k => Cpow (w N) (k * m)) N = C0.
Proof. intros N m HN Hm; apply (c_orth_vanish (w N) N m HN (w_pow_N N HN) Hm). Qed.

(* The precise contrast, as axiom footprints: *)
Print Assumptions c_orth_vanish.   (* only the 2 field-of-R axioms *)
Print Assumptions c_orth_w.        (* + sig_not_dec: the analytic realisation *)

(* ================================================================= *)
(*  END AlgebraicOrthogonality.v                                     *)
(*  DFT / character orthogonality is pure field algebra:               *)
(*  `algebraic_orthogonality` proves it over an abstract field with an  *)
(*  abstract root of unity, AXIOM-FREE.  The reals are inessential --   *)
(*  `c_orth_vanish` shows the same law over C needs no order/trig       *)
(*  axiom, and `c_orth_w` shows that axiom appears only when the        *)
(*  root is realised analytically as exp(2 pi i/N) (w_pow_N).           *)
(* ================================================================= *)
