(* ================================================================= *)
(*  ZetaConstructive.v                                              *)
(*                                                                    *)
(*  ζ(2) = Σ 1/n²  AS AN AXIOM-FREE CONSTRUCTIVE REAL.               *)
(*                                                                    *)
(*  The classical `ZetaConverge.zeta2_converges` puts the three       *)
(*  classical-ℝ axioms into the whole ζ arc (through `growing_cv`).   *)
(*  Here we rebuild ζ(2) as a `CReal` (Rocq's axiom-free constructive *)
(*  real): the rational partial sums `zpartQ` are shown to be a       *)
(*  regular Cauchy sequence — via the SAME telescoping estimate       *)
(*  1/(k+1)² ≤ 1/k − 1/(k+1) — and `CRealCv.cvQ_of_regular` builds    *)
(*  the limit `zeta2c` with `zeta2c_cv : cvQ zpartQ zeta2c`.          *)
(*                                                                    *)
(*  `Print Assumptions zeta2c_cv` = Closed under the global context.  *)
(*  This de-quarantines the foundational node of the ζ arc.          *)
(* ================================================================= *)

From Stdlib Require Import Reals.Cauchy.ConstructiveCauchyReals
        Reals.Cauchy.ConstructiveCauchyRealsMult
        Reals.Cauchy.ConstructiveCauchyAbs
        Reals.Cauchy.ConstructiveRcomplete.
From Stdlib Require Import ZArith QArith Qabs Qround Lqa Lia List Arith.
Import ListNotations.
Require Import PrimonGas CRealCv.
Local Open Scope Q_scope.

(* ----------------------------------------------------------------- *)
(*  ℕ ↪ ℚ and a couple of rational-arithmetic helpers                *)
(* ----------------------------------------------------------------- *)
Definition qN (k : nat) : Q := inject_Z (Z.of_nat k).

Lemma qN_pos : forall k, (1 <= k)%nat -> 0 < qN k.
Proof.
  intros k Hk; unfold qN; change 0 with (inject_Z 0); rewrite <- Zlt_Qlt; lia.
Qed.

Lemma qN_mono : forall a b, (a <= b)%nat -> qN a <= qN b.
Proof. intros a b H; unfold qN; rewrite <- Zle_Qle; lia. Qed.

Lemma qN_succ : forall k, qN (S k) == qN k + 1.
Proof.
  intro k; unfold qN; rewrite Nat2Z.inj_succ.
  replace (Z.succ (Z.of_nat k)) with (Z.of_nat k + 1)%Z by lia.
  rewrite inject_Z_plus; reflexivity.
Qed.

(* inverse is antitone on the positives *)
Lemma Qinv_le : forall a b, 0 < a -> a <= b -> / b <= / a.
Proof.
  intros a b Ha Hab.
  assert (Hb : 0 < b) by (apply Qlt_le_trans with a; assumption).
  assert (Hab0 : 0 < a * b) by (apply Qmult_lt_0_compat; assumption).
  apply (proj1 (Qmult_le_r (/ b) (/ a) (a * b) Hab0)).
  setoid_replace (/ b * (a * b)) with a by (field; intro C; rewrite C in Hb; apply (Qlt_irrefl 0); exact Hb).
  setoid_replace (/ a * (a * b)) with b by (field; intro C; rewrite C in Ha; apply (Qlt_irrefl 0); exact Ha).
  exact Hab.
Qed.

(* ----------------------------------------------------------------- *)
(*  the term 1/(k+1)² and the rational partial sums of ζ(2)          *)
(* ----------------------------------------------------------------- *)
Definition qterm (k : nat) : Q := / (qN (S k) * qN (S k)).

Lemma qterm_pos : forall k, 0 <= qterm k.
Proof.
  intro k; unfold qterm; apply Qlt_le_weak, Qinv_lt_0_compat.
  apply Qmult_lt_0_compat; apply qN_pos; lia.
Qed.

Definition zpartQ (N : nat) : Q := qsum (map qterm (seq 0 (S N))).

Lemma zpartQ_S : forall N, zpartQ (S N) == zpartQ N + qterm (S N).
Proof.
  intro N; unfold zpartQ.
  replace (seq 0 (S (S N))) with (seq 0 (S N) ++ [S N])
    by (rewrite <- seq_S; reflexivity).
  rewrite map_app, qsum_app; cbn [map qsum]; ring.
Qed.

Lemma zpartQ_mono : forall m n, (m <= n)%nat -> zpartQ m <= zpartQ n.
Proof.
  intros m n; induction n as [|n IH]; intro Hmn.
  - assert (m = 0)%nat by lia; subst; apply Qle_refl.
  - destruct (Nat.eq_dec m (S n)) as [->|Hne]; [ apply Qle_refl | ].
    rewrite zpartQ_S; apply Qle_trans with (zpartQ n);
      [ apply IH; lia | pose proof (qterm_pos (S n)); lra ].
Qed.

(* 1/(k+1) *)
Definition inv_np (k : nat) : Q := / qN (S k).

Lemma inv_np_nonneg : forall k, 0 <= inv_np k.
Proof. intro k; unfold inv_np; apply Qinv_le_0_compat, Qlt_le_weak, qN_pos; lia. Qed.

Lemma inv_np_antitone : forall a b, (a <= b)%nat -> inv_np b <= inv_np a.
Proof.
  intros a b H; unfold inv_np; apply Qinv_le; [ apply qN_pos; lia | apply qN_mono; lia ].
Qed.

(* the per-term telescoping estimate:  1/(j+2)² ≤ 1/(j+1) − 1/(j+2) *)
Lemma pterm : forall j, qterm (S j) <= inv_np j - inv_np (S j).
Proof.
  intro j; unfold qterm, inv_np.
  set (a := qN (S j)).
  assert (Ha : 0 < a) by (unfold a; apply qN_pos; lia).
  assert (Hb : qN (S (S j)) == a + 1) by (unfold a; apply qN_succ).
  rewrite Hb.
  assert (Ha1 : 0 < a + 1) by lra.
  setoid_replace (/ a - / (a + 1)) with (/ (a * (a + 1)))
    by (field; split; intro C; [ rewrite C in Ha1 | rewrite C in Ha ]; apply (Qlt_irrefl 0); assumption).
  apply Qinv_le.
  - apply Qmult_lt_0_compat; assumption.
  - apply Qmult_le_compat_nonneg; split; lra.
Qed.

(* the tail estimate over ℚ:  zpartQ n − zpartQ m ≤ 1/(m+1) − 1/(n+1) *)
Lemma zpartQ_tele : forall m n, (m <= n)%nat -> zpartQ n - zpartQ m <= inv_np m - inv_np n.
Proof.
  intros m n; induction n as [|n IH]; intro Hmn.
  - assert (m = 0)%nat by lia; subst; unfold Qminus; lra.
  - destruct (Nat.eq_dec m (S n)) as [->|Hne]; [ unfold Qminus; lra | ].
    assert (Hmn' : (m <= n)%nat) by lia.
    rewrite zpartQ_S.
    pose proof (IH Hmn') as HIH; pose proof (pterm n) as HP; lra.
Qed.

Lemma zpartQ_tail : forall m n, (m <= n)%nat -> zpartQ n - zpartQ m <= inv_np m.
Proof.
  intros m n H; pose proof (zpartQ_tele m n H); pose proof (inv_np_nonneg n); lra.
Qed.

(* symmetric closeness of two partial sums both past index i≤j *)
Lemma zpartQ_close : forall i j, (i <= j)%nat -> Qabs (zpartQ i - zpartQ j) <= inv_np i.
Proof.
  intros i j Hij; apply Qabs_Qle_condition; split.
  - pose proof (zpartQ_tail i j Hij); lra.
  - pose proof (zpartQ_mono i j Hij); pose proof (inv_np_nonneg i); lra.
Qed.

(* ----------------------------------------------------------------- *)
(*  regular Cauchy modulus, and the CReal limit ζ(2)                 *)
(* ----------------------------------------------------------------- *)
Lemma inv_np_Pos : forall p : positive, inv_np (Pos.to_nat p) <= 1 # p.
Proof.
  intro p; unfold inv_np.
  apply Qle_trans with (/ qN (Pos.to_nat p)).
  - apply Qinv_le; [ apply qN_pos; pose proof (Pos2Nat.is_pos p); lia
                   | apply qN_mono; lia ].
  - unfold qN; rewrite positive_nat_Z; apply Qle_refl.
Qed.

Lemma zpartQ_cauchymod : forall p : positive,
  {N : nat | forall i j, (N <= i)%nat -> (N <= j)%nat -> Qabs (zpartQ i - zpartQ j) <= 1 # p}.
Proof.
  intro p; exists (Pos.to_nat p); intros i j Hi Hj.
  assert (Hcl : Qabs (zpartQ i - zpartQ j) <= inv_np (Pos.to_nat p)).
  { destruct (Nat.le_ge_cases i j) as [Hle | Hge].
    - apply Qle_trans with (inv_np i); [ apply zpartQ_close; exact Hle | apply inv_np_antitone; exact Hi ].
    - rewrite Qabs_Qminus; apply Qle_trans with (inv_np j);
        [ apply zpartQ_close; exact Hge | apply inv_np_antitone; exact Hj ]. }
  apply Qle_trans with (inv_np (Pos.to_nat p)); [ exact Hcl | apply inv_np_Pos ].
Qed.

Definition zeta2c : CReal := projT1 (cvQ_of_regular zpartQ zpartQ_cauchymod).

Theorem zeta2c_cv : cvQ zpartQ zeta2c.
Proof. unfold zeta2c; exact (projT2 (cvQ_of_regular zpartQ zpartQ_cauchymod)). Qed.

Print Assumptions zeta2c_cv.

(* ================================================================= *)
(*  END ZetaConstructive.v                                          *)
(*  ζ(2) exists as an axiom-free constructive real `zeta2c`, the      *)
(*  limit of its rational partial sums.  Closed under the global      *)
(*  context.  (The ∑τ(n)/n² = ζ(2)² port is the next milestone.)     *)
(* ================================================================= *)
