(* ================================================================= *)
(*  ConstructivePi.v  —  a constructive π as an axiom-free CReal.      *)
(*                                                                    *)
(*  The Wallis / central-binomial sequence                           *)
(*      cπ₀ = 4,   cπ_{k+1} = cπ_k · (1 − 1/(2k+3)²)                  *)
(*  is the central-binomial ratio  4²ⁿ(n!)⁴/((2n)!²·n)  written as a   *)
(*  telescoping recursion — no factorials.  It is positive, DECREASING *)
(*  (each factor < 1), bounded in [π, 4], and Cauchy: the step        *)
(*  cπ_k − cπ_{k+1} = cπ_k/(2k+3)² ≤ 4/((2k+1)(2k+3)) telescopes, so   *)
(*  `CRealCv.cvQ_of_regular` gives the limit `constructive_pi : CReal`.*)
(*  This is the repo's first axiom-free π — the value classically      *)
(*  equal to π (Wallis), taken here as its constructive definition.    *)
(*                                                                    *)
(*  Purpose: the `π` side of the FEResidue value `Γ(½)²=π`, now a      *)
(*  concrete construction rather than an abstract parameter.  (The     *)
(*  identification with the circle / analytic π is Wallis's theorem,   *)
(*  classical, not formalized.)  AXIOM-FREE.                          *)
(* ================================================================= *)

From Stdlib Require Import QArith Qabs Lqa Lia List Arith ZArith.
Require Import PrimonGas CRealCv PoissonLHS.
Import ListNotations.
Open Scope Q_scope.

Lemma qeq_le : forall a b : Q, a == b -> a <= b.
Proof. intros a b H; rewrite H; apply Qle_refl. Qed.

Lemma Zn_succ_add : forall a b, Zn (a + b) == Zn a + Zn b.
Proof.
  intros a b; unfold Zn.
  assert (Z.of_nat (a + b) = Z.of_nat a + Z.of_nat b)%Z by lia.
  rewrite H, inject_Z_plus; reflexivity.
Qed.

Lemma Zn_mul : forall a b, Zn (a * b) == Zn a * Zn b.
Proof.
  intros a b; unfold Zn.
  assert (Z.of_nat (a * b) = Z.of_nat a * Z.of_nat b)%Z by lia.
  rewrite H, inject_Z_mult; reflexivity.
Qed.

(* the telescoping multiplier  1 − 1/(2k+3)² = 4(k+1)(k+2)/(2k+3)²  *)
Definition mlt (k : nat) : Q := Zn (4 * (k + 1) * (k + 2)) / Zn ((2 * k + 3) * (2 * k + 3)).

Fixpoint cpi (k : nat) : Q := match k with O => 4 | S m => cpi m * mlt m end.

Lemma den_pos : forall k, 0 < Zn ((2 * k + 3) * (2 * k + 3)).
Proof. intro k; apply Zn_pos; nia. Qed.

Lemma mlt_pos : forall k, 0 < mlt k.
Proof.
  intro k; unfold mlt; apply Qlt_shift_div_l; [ apply den_pos | ].
  rewrite Qmult_0_l; apply Zn_pos; nia.
Qed.

Lemma mlt_lt1 : forall k, mlt k < 1.
Proof.
  intro k; unfold mlt; apply Qlt_shift_div_r; [ apply den_pos | ].
  rewrite Qmult_1_l; unfold Zn; rewrite <- Zlt_Qlt; nia.
Qed.

(* 1 − mlt k = 1/(2k+3)² *)
Lemma mlt_compl : forall k, 1 - mlt k == 1 / Zn ((2 * k + 3) * (2 * k + 3)).
Proof.
  intro k; unfold mlt.
  assert (Hd : ~ Zn ((2 * k + 3) * (2 * k + 3)) == 0)
    by (apply Qnot_eq_sym, Qlt_not_eq, den_pos).
  assert (Hnum : Zn ((2 * k + 3) * (2 * k + 3)) == Zn (4 * (k + 1) * (k + 2)) + 1).
  { unfold Zn. change (1%Q) with (inject_Z 1). rewrite <- inject_Z_plus.
    assert (Z.of_nat ((2 * k + 3) * (2 * k + 3))
            = Z.of_nat (4 * (k + 1) * (k + 2)) + 1)%Z by (zify; nia).
    rewrite H; reflexivity. }
  rewrite Hnum. field. rewrite <- Hnum. exact Hd.
Qed.

Lemma cpi_pos : forall k, 0 < cpi k.
Proof.
  induction k as [| k IH]; cbn [cpi]; [ reflexivity | ].
  apply Qmult_lt_0_compat; [ exact IH | apply mlt_pos ].
Qed.

Lemma cpi_le4 : forall k, cpi k <= 4.
Proof.
  induction k as [| k IH]; cbn [cpi]; [ apply Qle_refl | ].
  apply Qle_trans with (cpi k * 1); [ | rewrite Qmult_1_r; exact IH ].
  apply Qmult_le_l; [ apply cpi_pos | apply Qlt_le_weak, mlt_lt1 ].
Qed.

(* one step, bounded by a telescoping odd-reciprocal difference *)
Lemma cpi_step : forall k, cpi k - cpi (S k) <= 2 * (/ Zn (2 * k + 1) - / Zn (2 * k + 3)).
Proof.
  intro k.
  assert (H1 : 0 < Zn (2 * k + 1)) by (apply Zn_pos; nia).
  assert (H3 : 0 < Zn (2 * k + 3)) by (apply Zn_pos; nia).
  assert (H1' : ~ Zn (2 * k + 1) == 0) by (apply Qnot_eq_sym, Qlt_not_eq; assumption).
  assert (H3' : ~ Zn (2 * k + 3) == 0) by (apply Qnot_eq_sym, Qlt_not_eq; assumption).
  assert (Hval : Zn (2 * k + 3) == Zn (2 * k + 1) + 2).
  { unfold Zn. change (2%Q) with (inject_Z 2). rewrite <- inject_Z_plus.
    assert (Z.of_nat (2 * k + 3) = Z.of_nat (2 * k + 1) + 2)%Z by lia.
    rewrite H; reflexivity. }
  (* RHS = 4 / (Zn(2k+1)·Zn(2k+3)) *)
  assert (Htel : 2 * (/ Zn (2 * k + 1) - / Zn (2 * k + 3))
                 == 4 / (Zn (2 * k + 1) * Zn (2 * k + 3))).
  { rewrite Hval; field; split; [ rewrite <- Hval; assumption | assumption ]. }
  rewrite Htel.
  (* LHS = cpi k / (Zn(2k+3))² *)
  assert (Heq : cpi k - cpi (S k) == cpi k * (1 / Zn ((2 * k + 3) * (2 * k + 3)))).
  { cbn [cpi]. rewrite <- (mlt_compl k). ring. }
  rewrite Heq, Zn_mul.
  apply Qle_trans with (4 * (1 / (Zn (2 * k + 3) * Zn (2 * k + 3)))).
  - apply Qmult_le_compat_r; [ apply cpi_le4 | ].
    apply Qlt_le_weak; unfold Qdiv; rewrite Qmult_1_l; apply Qinv_lt_0_compat.
    apply Qmult_lt_0_compat; assumption.
  - (* 4/(Zn(2k+3))² ≤ 4/(Zn(2k+1)·Zn(2k+3)) *)
    unfold Qdiv; rewrite !Qmult_1_l.
    apply Qmult_le_l; [ reflexivity | ].
    apply qinv_anti; [ apply Qmult_lt_0_compat; assumption | ].
    apply Qmult_le_compat_r; [ | apply Qlt_le_weak; assumption ].
    unfold Zn; rewrite <- Zle_Qle; nia.
Qed.

(* telescoping: the block cπ_k − cπ_{k+d} is bounded *)
Lemma cpi_tele : forall d k,
  cpi k - cpi (k + d) <= 2 * (/ Zn (2 * k + 1) - / Zn (2 * (k + d) + 1)).
Proof.
  induction d as [| d IH]; intro k.
  - rewrite Nat.add_0_r. setoid_replace (cpi k - cpi k) with 0 by ring.
    assert (0 < Zn (2 * k + 1)) by (apply Zn_pos; nia). lra.
  - replace (k + S d)%nat with (S (k + d))%nat by lia.
    apply Qle_trans with
      ((cpi k - cpi (k + d)) + (cpi (k + d) - cpi (S (k + d)))).
    + apply qeq_le; ring.
    + apply Qle_trans with
        (2 * (/ Zn (2 * k + 1) - / Zn (2 * (k + d) + 1))
         + 2 * (/ Zn (2 * (k + d) + 1) - / Zn (2 * (k + d) + 3))).
      * apply Qplus_le_compat; [ apply IH | apply cpi_step ].
      * replace (2 * S (k + d) + 1)%nat with (2 * (k + d) + 3)%nat by lia.
        set (A := / Zn (2 * k + 1)); set (B := / Zn (2 * (k + d) + 1));
          set (C := / Zn (2 * (k + d) + 3)); clearbody A B C; lra.
Qed.

Lemma cpi_regular : forall p : positive,
  { N : nat | forall i j, (N <= i)%nat -> (N <= j)%nat ->
      Qabs (cpi i - cpi j) <= 1 # p }.
Proof.
  intro p. exists (Pos.to_nat p).
  assert (key : forall a b, (Pos.to_nat p <= a)%nat -> (a <= b)%nat ->
                  Qabs (cpi a - cpi b) <= 1 # p).
  { intros a b Ha Hab.
    assert (Hpos1 : 0 < Zn (2 * a + 1)) by (apply Zn_pos; nia).
    assert (Hposj : 0 < Zn (2 * b + 1)) by (apply Zn_pos; nia).
    (* cpi decreasing: cpi a - cpi b >= 0 *)
    assert (Hge : 0 <= cpi a - cpi b).
    { replace b with (a + (b - a))%nat by lia.
      generalize (b - a)%nat as d; intro d.
      induction d as [| d IHd].
      - rewrite Nat.add_0_r; lra.
      - replace (a + S d)%nat with (S (a + d))%nat by lia.
        assert (cpi (S (a + d)) <= cpi (a + d)).
        { cbn [cpi]. apply Qle_trans with (cpi (a + d) * 1); [ | rewrite Qmult_1_r; apply Qle_refl ].
          apply Qmult_le_l; [ apply cpi_pos | apply Qlt_le_weak, mlt_lt1 ]. }
        lra. }
    rewrite Qabs_pos by exact Hge.
    apply Qle_trans with (2 * (/ Zn (2 * a + 1) - / Zn (2 * b + 1))).
    - replace b with (a + (b - a))%nat by lia. apply cpi_tele.
    - (* ≤ 2 / Zn(2a+1) ≤ 1/Zn a ≤ 1#p *)
      apply Qle_trans with (2 * / Zn (2 * a + 1)).
      + assert (0 < / Zn (2 * b + 1)) by (apply Qinv_lt_0_compat; assumption).
        assert (0 <= / Zn (2 * a + 1)) by (apply Qlt_le_weak, Qinv_lt_0_compat; assumption).
        nra.
      + (* 2/Zn(2a+1) ≤ 1#p, since 2a+1 ≥ 2·Pos.to_nat p *)
        assert (Hp0 : 0 < inject_Z (Z.pos p))
          by (change 0 with (inject_Z 0); rewrite <- Zlt_Qlt; lia).
        assert (Hp0' : ~ inject_Z (Z.pos p) == 0) by (apply Qnot_eq_sym, Qlt_not_eq; assumption).
        assert (HZ : Zn (2 * Pos.to_nat p) == 2 * inject_Z (Z.pos p)).
        { unfold Zn. change (2%Q) with (inject_Z 2). rewrite <- inject_Z_mult.
          assert (Z.of_nat (2 * Pos.to_nat p) = 2 * Z.pos p)%Z by lia.
          rewrite H; reflexivity. }
        assert (Hpi : (1 # p) == / inject_Z (Z.pos p)) by reflexivity.
        rewrite Hpi.
        apply Qle_trans with (2 * / Zn (2 * Pos.to_nat p)).
        * apply Qmult_le_l; [ reflexivity | ].
          apply qinv_anti; [ apply Zn_pos; nia | apply Zn_le; nia ].
        * rewrite HZ.
          setoid_replace (2 * / (2 * inject_Z (Z.pos p))) with (/ inject_Z (Z.pos p))
            by (field; assumption).
          apply Qle_refl. }
  intros i j Hi Hj.
  destruct (Nat.le_ge_cases i j) as [Hle | Hge].
  - apply key; assumption.
  - rewrite Qabs_Qminus. apply key; assumption.
Qed.

Definition constructive_pi := projT1 (cvQ_of_regular cpi cpi_regular).

Theorem constructive_pi_cv : cvQ cpi constructive_pi.
Proof. unfold constructive_pi; exact (projT2 (cvQ_of_regular cpi cpi_regular)). Qed.

(* Numerical certificate: the limit really is π (≈ 3.14159), not merely  *)
(* "some Cauchy limit satisfying the relations".  cπ decreases to π, so   *)
(* cπ₁₅ ∈ (π, 4); this pins it into [3.14, 3.20], catching any bug in the *)
(* recursion that the convergence proofs alone would not.                *)
Remark cpi_is_numerically_pi :
  (Qle_bool (314 # 100) (cpi 15) && Qle_bool (cpi 15) (320 # 100)) = true.
Proof. vm_compute. reflexivity. Qed.

Print Assumptions constructive_pi_cv.

(* ================================================================= *)
(*  END ConstructivePi.v                                             *)
(*  A constructive π (Wallis / central-binomial limit) as an axiom-   *)
(*  free CReal.  The π side of Γ(½)²=π, now concrete.  Closed under   *)
(*  the global context.                                              *)
(* ================================================================= *)
