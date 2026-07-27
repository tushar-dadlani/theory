(* ================================================================= *)
(*  CycloOrthogonality.v  —  ROOTS-OF-UNITY ORTHOGONALITY at ζ.       *)
(*                                                                    *)
(*  Stage 2 of the axiom-free DFT.  Working in R = ℚ[x]/(Φ_N) with    *)
(*  the primitive root ζ from QPolyQuot, we prove the orthogonality   *)
(*  the DFT rests on — WITHOUT instantiating the abstract field       *)
(*  `AlgebraicOrthogonality.algebraic_orthogonality` (which needs Φ_N *)
(*  irreducible).  Instead we cancel by the EXPLICIT unit ζ^m−1 from   *)
(*  `zeta_pow_sub_unit`:                                              *)
(*                                                                    *)
(*    (ζ^m − 1) · Σ_{k<N} ζ^{km} = ζ^{mN} − 1 = (ζ^N)^m − 1 ≡ 0,       *)
(*                                                                    *)
(*  and since ζ^m−1 is a unit for 0<m<N, the sum itself vanishes.      *)
(*                                                                    *)
(*    • cyclo_orth_vanish : 0<m<N → Σ_{k<N} ζ^{km} ≡ 0                *)
(*    • orth_diag         : Σ_{k<N} 1 ≡ N·1                           *)
(*    • r_orthogonality   : Σ_{k<N} ζ^{k·d} ≡ (d=0 ? N·1 : 0)  (d<N)  *)
(*                                                                    *)
(*  AXIOM-FREE (Closed under the global context).                    *)
(* ================================================================= *)

From Stdlib Require Import QArith Qcanon List Lia Arith ZArith.
Import ListNotations.
Require Import QPoly QPolyEmbed QPolyCoeffPIT QPolyQuot.
Open Scope Qc_scope.

(* --- small Qc power facts --- *)
Lemma Qcpow_add : forall (t : Qc) a b, t ^ (a + b) = t ^ a * t ^ b.
Proof.
  intros t a b; induction a as [|a IH]; cbn [Nat.add Qcpower]; [ ring | rewrite IH; ring ].
Qed.
Lemma Qcpow_mul : forall (t : Qc) i j, t ^ (i * j) = (t ^ i) ^ j.
Proof.
  intros t i j; induction j as [|j IH]; cbn [Qcpower].
  - rewrite Nat.mul_0_r; reflexivity.
  - rewrite Nat.mul_succ_r, Qcpow_add, IH; ring.
Qed.
Lemma Qcpow_1_l : forall m, (1 : Qc) ^ m = 1.
Proof. induction m as [|m IH]; cbn [Qcpower]; [ reflexivity | rewrite IH; ring ]. Qed.

Lemma qeval_nil : forall x, qeval [] x = 0.
Proof. reflexivity. Qed.

(* qnat is Z2Qc on Z.of_nat, and steps by 1 *)
Lemma qnat_is_Z2Qc : forall n, qnat n = Z2Qc (Z.of_nat n).
Proof. reflexivity. Qed.
Lemma qnat_succ : forall n, qnat (S n) = qnat n + 1.
Proof.
  intro n; rewrite !qnat_is_Z2Qc, Nat2Z.inj_succ; unfold Z.succ.
  rewrite Z2Qc_add, Z2Qc_1; reflexivity.
Qed.

Section CycloOrth.
  Variable N : nat.
  Hypothesis HN1 : (1 <= N)%nat.

  Notation R := (req N).

  (* the sum Σ_{k<n} f(k) in R *)
  Fixpoint rsum (f : nat -> qpoly) (n : nat) : qpoly :=
    match n with O => [] | S k => qadd (rsum f k) (f k) end.

  Definition ofnatR : qpoly := qconst (qnat N).

  (* ================= req toolkit ================= *)
  Lemma req_of_qeval : forall a b, (forall x, qeval a x = qeval b x) -> R a b.
  Proof.
    intros a b H; exists []; intro x; rewrite qeval_sub, (H x), qeval_nil; ring.
  Qed.
  Lemma req_refl : forall a, R a a.
  Proof. intro a; apply req_of_qeval; reflexivity. Qed.
  Lemma req_sym : forall a b, R a b -> R b a.
  Proof.
    intros a b [r Hr]; exists (qneg r); intro x.
    rewrite qeval_sub, qeval_neg; specialize (Hr x); rewrite qeval_sub in Hr.
    replace (qeval b x - qeval a x) with (- (qeval a x - qeval b x)) by ring.
    rewrite Hr; ring.
  Qed.
  Lemma req_trans : forall a b c, R a b -> R b c -> R a c.
  Proof.
    intros a b c [r1 H1] [r2 H2]; exists (qadd r1 r2); intro x.
    specialize (H1 x); specialize (H2 x); rewrite qeval_sub in H1, H2.
    rewrite qeval_sub, qeval_add.
    replace (qeval a x - qeval c x)
       with ((qeval a x - qeval b x) + (qeval b x - qeval c x)) by ring.
    rewrite H1, H2; ring.
  Qed.
  Lemma req_qmul_l : forall a b c, R a b -> R (qmul c a) (qmul c b).
  Proof.
    intros a b c [r Hr]; exists (qmul c r); intro x.
    rewrite qeval_sub, !qeval_mul; specialize (Hr x); rewrite qeval_sub in Hr.
    replace (qeval c x * qeval a x - qeval c x * qeval b x)
       with (qeval c x * (qeval a x - qeval b x)) by ring.
    rewrite Hr; ring.
  Qed.
  Lemma req_qmul_r : forall a b c, R a b -> R (qmul a c) (qmul b c).
  Proof.
    intros a b c [r Hr]; exists (qmul r c); intro x.
    rewrite qeval_sub, !qeval_mul; specialize (Hr x); rewrite qeval_sub in Hr.
    replace (qeval a x * qeval c x - qeval b x * qeval c x)
       with ((qeval a x - qeval b x) * qeval c x) by ring.
    rewrite Hr; ring.
  Qed.
  Lemma req_qmul : forall a b c d, R a b -> R c d -> R (qmul a c) (qmul b d).
  Proof.
    intros a b c d Hab Hcd.
    apply (req_trans (qmul a c) (qmul b c) (qmul b d)).
    - apply req_qmul_r; exact Hab.
    - apply req_qmul_l; exact Hcd.
  Qed.
  Lemma req_qadd : forall a a' b b', R a a' -> R b b' -> R (qadd a b) (qadd a' b').
  Proof.
    intros a a' b b' [r1 H1] [r2 H2]; exists (qadd r1 r2); intro x.
    rewrite qeval_sub, !qeval_add.
    specialize (H1 x); specialize (H2 x); rewrite qeval_sub in H1, H2.
    replace (qeval a x + qeval b x - (qeval a' x + qeval b' x))
       with ((qeval a x - qeval a' x) + (qeval b x - qeval b' x)) by ring.
    rewrite H1, H2; ring.
  Qed.
  Lemma req_rpow : forall a b k, R a b -> R (rpow a k) (rpow b k).
  Proof.
    intros a b k H; induction k as [|k IH]; cbn [rpow].
    - apply req_refl.
    - apply req_qmul; [ exact H | exact IH ].
  Qed.
  Lemma req_rsum : forall f g n, (forall k, R (f k) (g k)) -> R (rsum f n) (rsum g n).
  Proof.
    intros f g n H; induction n as [|n IH]; cbn [rsum].
    - apply req_refl.
    - apply req_qadd; [ exact IH | apply H ].
  Qed.
  Lemma req_sub_nil : forall a b, R a b -> R (qsub a b) [].
  Proof.
    intros a b [r Hr]; exists r; intro x.
    rewrite qeval_sub, qeval_nil, (Hr x); ring.
  Qed.

  (* ================= exact evaluation facts ================= *)
  Lemma qeval_rpow : forall a n x, qeval (rpow a n) x = (qeval a x) ^ n.
  Proof.
    intros a n x; induction n as [|n IH]; cbn [rpow Qcpower].
    - rewrite qeval_one; reflexivity.
    - rewrite qeval_mul, IH; ring.
  Qed.

  (* geometric series over ℚ, at ζ:  (ζ^m−1)·Σ_{k<n} ζ^{km} = (x^m)^n − 1 *)
  Lemma qgeom_zeta : forall m n x,
    qeval (qmul (qsub (rpow zeta m) [1]) (rsum (fun k => rpow zeta (k * m)) n)) x
      = (x ^ m) ^ n - 1.
  Proof.
    intros m n x; induction n as [|n IH]; cbn [rsum].
    - rewrite qeval_mul, qeval_nil; cbn [Qcpower]; ring.
    - rewrite qeval_mul, qeval_add, qeval_rpow_zeta.
      rewrite qeval_mul in IH; rewrite qeval_zsub1 in IH |- *.
      replace (x ^ (n * m)) with ((x ^ m) ^ n)
        by (rewrite <- Qcpow_mul, Nat.mul_comm; reflexivity).
      cbn [Qcpower].
      set (P := x ^ m) in *.
      set (s := qeval (rsum (fun k => rpow zeta (k * m)) n) x) in *.
      replace ((P - 1) * (s + P ^ n)) with ((P - 1) * s + (P - 1) * P ^ n) by ring.
      rewrite IH; ring.
  Qed.

  Lemma rsum_ones : forall n x, qeval (rsum (fun _ => [1]) n) x = qnat n.
  Proof.
    intros n x; induction n as [|n IH]; cbn [rsum].
    - rewrite qeval_nil; symmetry; exact (qnat_0).
    - rewrite qeval_add, IH, qeval_one, <- qnat_succ; reflexivity.
  Qed.

  (* ================= the orthogonality ================= *)

  (* the pure req-algebra core: if s·S ≡ 0 and s is a unit, then S ≡ 0 *)
  Lemma vanish_helper : forall s S,
    R (qmul s S) [] -> (exists U, R (qmul U s) [1]) -> R S [].
  Proof.
    intros s S H1 [U HU].
    apply (req_trans S (qmul [1] S) []).
    { apply req_of_qeval; intro x; rewrite qeval_mul, qeval_one; ring. }
    apply (req_trans (qmul [1] S) (qmul (qmul U s) S) []).
    { apply req_qmul_r, req_sym; exact HU. }
    apply (req_trans (qmul (qmul U s) S) (qmul U (qmul s S)) []).
    { apply req_of_qeval; intro x; rewrite !qeval_mul; ring. }
    apply (req_trans (qmul U (qmul s S)) (qmul U []) []).
    { apply req_qmul_l; exact H1. }
    apply req_of_qeval; intro x; rewrite qeval_mul, qeval_nil; ring.
  Qed.

  Theorem cyclo_orth_vanish : forall m, (0 < m < N)%nat ->
    R (rsum (fun k => rpow zeta (k * m)) N) [].
  Proof.
    intros m Hm.
    apply (vanish_helper (qsub (rpow zeta m) [1]) (rsum (fun k => rpow zeta (k * m)) N)).
    - (* (ζ^m−1)·Σ ≡ 0 *)
      apply (req_trans _ (qsub (rpow zeta (m * N)) [1]) _).
      + apply req_of_qeval; intro x.
        rewrite qgeom_zeta, qeval_sub, qeval_rpow_zeta, qeval_one, Qcpow_mul; reflexivity.
      + apply req_sub_nil.
        apply (req_trans _ (rpow (rpow zeta N) m) _).
        * apply req_of_qeval; intro x.
          rewrite (qeval_rpow (rpow zeta N) m), !qeval_rpow_zeta.
          rewrite <- Qcpow_mul, (Nat.mul_comm m N); reflexivity.
        * apply (req_trans _ (rpow [1] m) _).
          { apply req_rpow, zeta_pow_N; exact HN1. }
          { apply req_of_qeval; intro x.
            rewrite qeval_rpow, !qeval_one, Qcpow_1_l; reflexivity. }
    - exact (zeta_pow_sub_unit N HN1 m Hm).
  Qed.

  Theorem orth_diag : R (rsum (fun _ => [1]) N) ofnatR.
  Proof.
    apply req_of_qeval; intro x; unfold ofnatR; rewrite rsum_ones, qeval_const; reflexivity.
  Qed.

  Theorem r_orthogonality : forall d, (d < N)%nat ->
    R (rsum (fun k => rpow zeta (k * d)) N) (if d =? 0 then ofnatR else []).
  Proof.
    intros d Hd; destruct (Nat.eqb_spec d 0) as [Hd0 | Hd0].
    - subst d.
      apply (req_trans _ (rsum (fun _ => [1]) N) _).
      + apply req_rsum; intro k; apply req_of_qeval; intro x.
        rewrite qeval_rpow_zeta, Nat.mul_0_r, qeval_one; cbn [Qcpower]; reflexivity.
      + apply orth_diag.
    - apply cyclo_orth_vanish; split; [ lia | exact Hd ].
  Qed.

End CycloOrth.

Print Assumptions cyclo_orth_vanish.
Print Assumptions r_orthogonality.

(* ================================================================= *)
(*  END CycloOrthogonality.v                                         *)
(*  Roots-of-unity orthogonality at the algebraic ζ, by cancelling    *)
(*  the explicit unit ζ^m−1 (no field / no irreducibility).          *)
(*  Closed under the global context (axiom-free).                    *)
(* ================================================================= *)
