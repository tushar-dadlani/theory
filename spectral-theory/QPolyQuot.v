(* ================================================================= *)
(*  QPolyQuot.v  —  AN AXIOM-FREE PRIMITIVE N-th ROOT OF UNITY.       *)
(*                                                                    *)
(*  The algebraic root ζ that replaces the transcendental            *)
(*  `RootsOfUnity.w N = cos(2π/N)+i·sin(2π/N)` (which carries the      *)
(*  classical-ℝ quarantine axioms via ComplexField).  We work in the  *)
(*  cyclotomic quotient R = ℚ[x]/(Φ_N), presented as a SETOID on      *)
(*  `qpoly` with equality `req a b := Φ_N | (a − b)` (the repo's       *)
(*  `qdivides` is functional, which makes the quotient laws cheap).    *)
(*                                                                    *)
(*  ζ := x.  We prove, ENTIRELY axiom-free, reusing the ℚ[X] tower:    *)
(*    • zeta_pow_N       : ζ^N = 1   (Φ_N | X^N−1)                    *)
(*    • zeta_pow_sub_unit: ζ^m−1 is a UNIT for 0<m<N                  *)
(*    • zeta_primitive   : ζ^m ≠ 1 for 0<m<N                          *)
(*    • wc_w_1           : ζ^{N−1}·ζ = 1  (the inverse root)          *)
(*    • one_neq_zero_R   : 1 ≠ 0 in R                                 *)
(*                                                                    *)
(*  The KEY is that primitivity needs NO irreducibility of Φ_N: the   *)
(*  unit `ζ^m−1` comes from Bézout coprimality of Φ_N and X^m−1,       *)
(*  which follows from `X^N−1` being SQUAREFREE (`qsqfree_Xn1`) via    *)
(*  the factorisation X^N−1 = Φ_N·D_N and `qsqfree_mul_copr`, plus the *)
(*  gcd descent d|X^m−1 ⇒ d|X^{gcd(m,N)}−1 | D_N.                     *)
(*                                                                    *)
(*  AXIOM-FREE (Closed under the global context).  This is Stage 1 of *)
(*  de-quarantining the DFT cluster (see docs/BRIDGES.md).           *)
(* ================================================================= *)

From Stdlib Require Import QArith Qcanon List Lia Arith.
Import ListNotations.
Require Import IntPoly QPoly QPolyDiv QPolyMul QPolyDeg QPolyGcd QPolyRoot
        QPolyCoprime QPolyProdDvd QPolyTransfer QPolySqfree QPolyEmbed
        QProd Totient Cyclotomic CyclotomicProd.
Open Scope Qc_scope.

Section CycloRoot.
  Variable N : nat.
  Hypothesis HN1 : (1 <= N)%nat.

  Definition PhiN : qpoly := emb (Phi N).
  Definition DN   : qpoly := emb (Dprod N).

  (* the quotient equality: Φ_N divides a − b *)
  Definition req (a b : qpoly) : Prop := qdivides PhiN (qsub a b).

  (* the root ζ = x, its powers, and their evaluation *)
  Definition zeta : qpoly := qmonom 1.
  Fixpoint rpow (a : qpoly) (n : nat) : qpoly :=
    match n with O => [1] | S k => qmul a (rpow a k) end.

  Lemma qeval_rpow_zeta : forall m x, qeval (rpow zeta m) x = x ^ m.
  Proof.
    induction m as [|m IH]; intro x.
    - cbn [rpow qeval Qcpower]; ring.
    - cbn [rpow Qcpower]; rewrite qeval_mul, IH; unfold zeta;
        rewrite qeval_monom; cbn [Qcpower]; ring.
  Qed.

  Lemma qeval_one : forall x, qeval [1] x = 1.
  Proof. intro x; cbn [qeval]; ring. Qed.

  Lemma qeval_zsub1 : forall m x, qeval (qsub (rpow zeta m) [1]) x = x ^ m - 1.
  Proof. intros m x; rewrite qeval_sub, qeval_rpow_zeta, qeval_one; reflexivity. Qed.

  (* --- small functional-divisibility helpers --- *)
  Lemma dvd_mul_l : forall a s, qdivides PhiN s -> qdivides PhiN (qmul a s).
  Proof.
    intros a s [r Hr]; exists (qmul a r); intro x.
    rewrite !qeval_mul, Hr; ring.
  Qed.
  Lemma dvd_sub : forall a b, qdivides PhiN a -> qdivides PhiN b -> qdivides PhiN (qsub a b).
  Proof.
    intros a b [ra Hra] [rb Hrb]; exists (qsub ra rb); intro x.
    rewrite !qeval_sub, Hra, Hrb; ring.
  Qed.

  (* ========== monic / nonzero facts about the two factors ========== *)
  Lemma PhiN_monic : qmonic PhiN (phi N).
  Proof. apply emb_monic, cyclotomic_monic; exact HN1. Qed.
  Lemma DN_monic : qmonic DN (N - phi N).
  Proof. apply emb_monic, Dprod_monic; exact HN1. Qed.
  Lemma PhiN_nz : qnorm PhiN <> [].
  Proof. apply (qmonic_qnorm_nz PhiN (phi N)), PhiN_monic. Qed.
  Lemma DN_nz : qnorm DN <> [].
  Proof. apply (qmonic_qnorm_nz DN (N - phi N)), DN_monic. Qed.

  (* ========== FACT 1 : Φ_N | X^N − 1 ========== *)
  Lemma PhiN_dvd_XN : qdivides PhiN (qXn1 N).
  Proof. apply (Phi_dvd_own N HN1), cyclotomic_prod; exact HN1. Qed.

  (* ========== FACT 2 : X^N − 1 = Φ_N · D_N (as functions) ========== *)
  Lemma XN_factor : forall x, qeval (qXn1 N) x = qeval (qmul PhiN DN) x.
  Proof.
    intro x. unfold PhiN, DN.
    rewrite <- emb_pmul, <- emb_Xn1.
    revert x; apply qeval_ext_Z; intro a.
    rewrite !qeval_emb; f_equal.
    rewrite eval_mul; apply cyclotomic_prod_Z; exact HN1.
  Qed.

  (* ========== FACT 3 : Φ_N and D_N are coprime ========== *)
  Lemma copr_Phi_D : qcopr PhiN DN.
  Proof.
    apply qsqfree_mul_copr; [ | apply PhiN_nz | apply DN_nz ].
    apply (qsqfree_ext (qXn1 N) (qmul PhiN DN) XN_factor).
    apply qsqfree_Xn1; exact HN1.
  Qed.

  (* ========== FACT 4 : X^{gcd(m,N)} − 1 | D_N  (0<m<N) ========== *)
  Lemma gcd_proper : forall m, (0 < m < N)%nat ->
    (1 <= Nat.gcd m N)%nat /\ Nat.divide (Nat.gcd m N) N /\ (Nat.gcd m N < N)%nat.
  Proof.
    intros m [Hm HmN]. assert (Hg1 : (1 <= Nat.gcd m N)%nat).
    { destruct (Nat.gcd m N) eqn:E; [ | lia ].
      apply Nat.gcd_eq_0 in E; lia. }
    split; [ exact Hg1 | ]. split; [ apply Nat.gcd_divide_r | ].
    assert (Hgm : Nat.divide (Nat.gcd m N) m) by apply Nat.gcd_divide_l.
    assert (Nat.gcd m N <= m)%nat by (apply Nat.divide_pos_le; [ lia | exact Hgm ]); lia.
  Qed.

  Lemma Xgcd_dvd_D : forall m, (0 < m < N)%nat ->
    qdivides (qXn1 (Nat.gcd m N)) DN.
  Proof.
    intros m Hm. destruct (gcd_proper m Hm) as [Hg1 [HgN Hglt]].
    set (g := Nat.gcd m N) in *.
    (* qXn1 g ≡ qprod (divisors g);  D_N ≡ qprod (properdivs N) *)
    apply (qdivides_ext_l (qprod (divisors g)) (qXn1 g) DN).
    { intro x; symmetry; apply cyclotomic_prod; exact Hg1. }
    apply (qdivides_ext_r (qprod (divisors g)) (qprod (properdivs N)) DN).
    { intro x; unfold DN; symmetry; apply emb_Dprod. }
    apply qdivides_qprod_incl.
    - apply divisors_incl_properdivs; [ exact HgN | exact Hglt ].
    - apply divisors_nodup.
    - apply properdivs_nodup.
  Qed.

  (* ========== FACT 5 : Φ_N and X^m − 1 coprime (0<m<N) ========== *)
  Lemma copr_Phi_Xm : forall m, (0 < m < N)%nat -> qcopr PhiN (qXn1 m).
  Proof.
    intros m Hm d HdPhi HdXm.
    assert (HdXN : qdivides d (qXn1 N))
      by (apply (qdivides_trans d PhiN (qXn1 N) HdPhi PhiN_dvd_XN)).
    assert (HdG : qdivides d (qXn1 (Nat.gcd m N)))
      by (apply qdiv_gcd; [ exact HdXm | exact HdXN ]).
    assert (HdD : qdivides d DN)
      by (apply (qdivides_trans d (qXn1 (Nat.gcd m N)) DN HdG (Xgcd_dvd_D m Hm))).
    apply (copr_Phi_D d HdPhi HdD).
  Qed.

  (* ========== the Stage-1 deliverables ========== *)

  (* ζ^N = 1 *)
  Theorem zeta_pow_N : req (rpow zeta N) [1].
  Proof.
    unfold req. apply (qdivides_ext_r PhiN (qXn1 N) (qsub (rpow zeta N) [1])).
    - intro x; rewrite qeval_Xn1, qeval_zsub1; reflexivity.
    - exact PhiN_dvd_XN.
  Qed.

  (* ζ^m − 1 is a unit for 0 < m < N *)
  Theorem zeta_pow_sub_unit : forall m, (0 < m < N)%nat ->
    exists u, req (qmul u (qsub (rpow zeta m) [1])) [1].
  Proof.
    intros m Hm.
    destruct (coprime_bezout PhiN (qXn1 m) (copr_Phi_Xm m Hm)) as [u [v Huv]].
    exists v. unfold req. exists (qneg u); intro x.
    rewrite qeval_sub, qeval_mul, qeval_zsub1, qeval_one, qeval_neg.
    specialize (Huv x); rewrite qeval_Xn1 in Huv.
    (* Huv : qeval u x * qeval PhiN x + qeval v x * (x^m − 1) = 1 *)
    set (A := x ^ m - 1) in *.
    rewrite <- Huv; ring.
  Qed.

  (* 1 ≠ 0 in R : Φ_N (degree ≥ 1) cannot divide the constant 1 *)
  Theorem one_neq_zero_R : ~ qdivides PhiN [1].
  Proof.
    intro H.
    assert (Hdeg0 : qdegle PhiN 0)
      by (apply (divides_const_deg0 PhiN 1 qc_one_neq_zero); exact H).
    pose proof (qdegle_qdeg PhiN 0 Hdeg0) as Hle.
    rewrite (qmonic_qdeg PhiN (phi N) PhiN_monic) in Hle.
    pose proof (phi_ge_1 N HN1) as Hge; lia.
  Qed.

  (* ζ^m ≠ 1 for 0 < m < N *)
  Theorem zeta_primitive : forall m, (0 < m < N)%nat -> ~ req (rpow zeta m) [1].
  Proof.
    intros m Hm Hdvd. unfold req in Hdvd.
    destruct (zeta_pow_sub_unit m Hm) as [u Hu]. unfold req in Hu.
    (* Hdvd : Φ_N | (ζ^m − 1);  Hu : Φ_N | (u·(ζ^m−1) − 1) *)
    set (s := qsub (rpow zeta m) [1]) in *.
    apply one_neq_zero_R.
    (* Φ_N | 1, since 1 = u·s − (u·s − 1) and Φ_N divides both *)
    apply (qdivides_ext_r PhiN (qsub (qmul u s) (qsub (qmul u s) [1])) [1]).
    - intro x; rewrite !qeval_sub, qeval_one; ring.
    - apply dvd_sub; [ apply dvd_mul_l; exact Hdvd | exact Hu ].
  Qed.

  (* the inverse root wc := ζ^{N−1}, with wc·ζ = 1 *)
  Definition wc : qpoly := rpow zeta (N - 1).
  Theorem wc_w_1 : req (qmul wc zeta) [1].
  Proof.
    unfold req, wc. apply (qdivides_ext_r PhiN (qXn1 N) (qsub (qmul (rpow zeta (N-1)) zeta) [1])).
    - intro x. rewrite qeval_Xn1, qeval_sub, qeval_mul, qeval_rpow_zeta, qeval_one.
      unfold zeta; rewrite qeval_monom; cbn [Qcpower].
      replace N with (S (N - 1))%nat at 1 by lia; cbn [Qcpower]; ring.
    - exact PhiN_dvd_XN.
  Qed.

End CycloRoot.

Print Assumptions zeta_primitive.
Print Assumptions zeta_pow_N.
Print Assumptions zeta_pow_sub_unit.

(* ================================================================= *)
(*  END QPolyQuot.v                                                  *)
(*  An axiom-free primitive N-th root of unity ζ in ℚ[x]/(Φ_N):      *)
(*  ζ^N=1, ζ^m−1 a unit and ζ^m≠1 for 0<m<N, wc·ζ=1, 1≠0.  No        *)
(*  irreducibility needed — primitivity rests on squarefreeness of   *)
(*  X^N−1.  Closed under the global context.                         *)
(* ================================================================= *)
