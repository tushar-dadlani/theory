(* ================================================================= *)
(*  PoissonLHS.v  —  the LEFT side of a continuous Poisson summation   *)
(*  as an axiom-free CReal:  Σ_{n∈ℤ} 1/(1+n²).                        *)
(*                                                                    *)
(*  CONTEXT.  `FinitePoisson.finite_poisson_R` is the DISCRETE shadow  *)
(*  of Poisson summation, and it lives over the ALGEBRAIC cyclotomic   *)
(*  ring ℚ(ζ_N) — its roots of unity are not real numbers, so it has   *)
(*  no literal CReal limit.  The object it is the shadow OF is the     *)
(*  CONTINUOUS Poisson summation  Σ_{n∈ℤ} f(n) = Σ_{k∈ℤ} f̂(k).  Its    *)
(*  LEFT side — a lattice sum — is a genuine CReal that we CAN build   *)
(*  axiom-free, and this file does so for the archetype f(x)=1/(1+x²)  *)
(*  (whose Poisson identity is the classical Σ 1/(1+n²) = π·coth π).   *)
(*                                                                    *)
(*  The bilateral sum is 1 + 2·Σ_{n≥1} 1/(1+n²); the partial sums are  *)
(*  rational, monotone, and Cauchy with the EXPLICIT modulus N = 2p    *)
(*  coming from the telescoping tail  Σ_{n>i} 1/(1+n²) ≤ 1/i (via      *)
(*  1/(1+n²) ≤ 1/(n(n−1)) = 1/(n−1) − 1/n).  `CRealCv.cvQ_of_regular`   *)
(*  then delivers the limit `poisson_lhs : CReal`.                    *)
(*                                                                    *)
(*  HONEST BOUNDARY.  This is the SUM side only.  The RIGHT side —      *)
(*  Σ_k f̂(k) with f̂(k) = π·e^{−2π|k|} — needs the Fourier transform    *)
(*  f̂ = ∫f(x)e^{−2πikx}dx, i.e. the constructive integral (knot 1).    *)
(*  That is the next brick; here we plant the lattice-sum LHS below    *)
(*  the wall.  AXIOM-FREE (Closed under the global context).          *)
(* ================================================================= *)

From Stdlib Require Import QArith Qabs Lqa Lia List Arith.
Require Import PrimonGas CRealCv.
Import ListNotations.
Open Scope Q_scope.

(* ----------------------------------------------------------------- *)
(*  Rational / order helpers.                                         *)
(* ----------------------------------------------------------------- *)
Definition Zn (n : nat) : Q := inject_Z (Z.of_nat n).

Lemma Zn_pos : forall n, (1 <= n)%nat -> 0 < Zn n.
Proof.
  intros n Hn; unfold Zn; change 0 with (inject_Z 0); rewrite <- Zlt_Qlt; lia.
Qed.

Lemma Zn_le : forall m n, (m <= n)%nat -> Zn m <= Zn n.
Proof.
  intros m n H; unfold Zn; rewrite <- Zle_Qle; lia.
Qed.

Lemma qinv_anti : forall a b : Q, 0 < a -> a <= b -> / b <= / a.
Proof.
  intros a b Ha Hab.
  assert (Hb : 0 < b) by (apply Qlt_le_trans with a; assumption).
  assert (Ha0 : ~ a == 0) by (apply Qnot_eq_sym, Qlt_not_eq; assumption).
  assert (Hb0 : ~ b == 0) by (apply Qnot_eq_sym, Qlt_not_eq; assumption).
  apply (proj1 (Qmult_le_r (/ b) (/ a) (a * b) (Qmult_lt_0_compat _ _ Ha Hb))).
  setoid_replace (/ b * (a * b)) with a by (field; assumption).
  setoid_replace (/ a * (a * b)) with b by (field; assumption).
  exact Hab.
Qed.

(* ----------------------------------------------------------------- *)
(*  The summand  g n = 1/(1+n²)  and its telescoping bound.           *)
(* ----------------------------------------------------------------- *)
Definition g (n : nat) : Q := / (1 + Zn n * Zn n).

Lemma Zn_sq_nonneg : forall n, 0 <= Zn n * Zn n.
Proof.
  intro n; unfold Zn; rewrite <- inject_Z_mult; change 0 with (inject_Z 0);
    rewrite <- Zle_Qle; nia.
Qed.

Lemma g_pos_denom : forall n, 0 < 1 + Zn n * Zn n.
Proof.
  intro n; apply Qlt_le_trans with (1 + 0); [ lra | ].
  apply Qplus_le_r; apply Zn_sq_nonneg.
Qed.

Lemma g_nonneg : forall n, 0 <= g n.
Proof.
  intro n; unfold g; apply Qlt_le_weak, Qinv_lt_0_compat, g_pos_denom.
Qed.

(* the key telescoping step:  1/(1+(n+1)²) ≤ 1/n − 1/(n+1)  (n ≥ 1) *)
Lemma g_tele : forall n, (1 <= n)%nat -> g (S n) <= / Zn n - / Zn (S n).
Proof.
  intros n Hn.
  assert (Hn1 : 0 < Zn n) by (apply Zn_pos; assumption).
  assert (HSn : 0 < Zn (S n)) by (apply Zn_pos; lia).
  assert (Hxn : 0 <= Zn n) by (apply Qlt_le_weak; assumption).
  (* Zn (S n) = Zn n + 1 *)
  assert (HSn_val : Zn (S n) == Zn n + 1).
  { unfold Zn. change (1%Q) with (inject_Z 1). rewrite <- inject_Z_plus.
    assert (Heq : (Z.of_nat (S n) = Z.of_nat n + 1)%Z) by lia.
    rewrite Heq; reflexivity. }
  assert (Hn1' : ~ Zn n == 0) by (apply Qnot_eq_sym, Qlt_not_eq; assumption).
  assert (H1 : 0 < Zn n + 1) by lra.
  assert (HSn1 : ~ (Zn n + 1 == 0)) by (apply Qnot_eq_sym, Qlt_not_eq; assumption).
  (* / n − / (n+1) = 1/(n(n+1)) *)
  assert (Hstep : / Zn n - / Zn (S n) == / (Zn n * Zn (S n))).
  { rewrite HSn_val; field; split; assumption. }
  rewrite Hstep.
  (* g (S n) = 1/(1+(n+1)²) ≤ 1/(n(n+1))  since  n(n+1) ≤ 1+(n+1)² *)
  unfold g; apply qinv_anti.
  - apply Qmult_lt_0_compat; assumption.
  - rewrite HSn_val; nra.
Qed.

(* ----------------------------------------------------------------- *)
(*  The telescoping tail bound.                                       *)
(* ----------------------------------------------------------------- *)
Lemma tail_tele : forall d i, (1 <= i)%nat ->
  qsum (map g (seq (S i) d)) <= / Zn i - / Zn (i + d).
Proof.
  induction d as [| d IH]; intros i Hi.
  - cbn [seq map qsum]. rewrite Nat.add_0_r. lra.
  - (* seq (S i) (S d) = seq (S i) d ++ [S i + d] *)
    rewrite seq_S, map_app, qsum_app. cbn [map qsum].
    rewrite Qplus_0_r.
    (* bound the head by IH, the tail term by g_tele at (i+d) *)
    assert (Hid : (1 <= i + d)%nat) by lia.
    pose proof (IH i Hi) as Hhead.
    (* S i + d = S (i + d) *)
    replace (S i + d)%nat with (S (i + d))%nat by lia.
    pose proof (g_tele (i + d) Hid) as Htail.
    (* combine:  ≤ (/Zn i − /Zn(i+d)) + (/Zn(i+d) − /Zn(S(i+d))) *)
    apply Qle_trans with
      ((/ Zn i - / Zn (i + d)) + (/ Zn (i + d) - / Zn (S (i + d)))).
    + apply Qplus_le_compat; assumption.
    + replace (i + S d)%nat with (S (i + d))%nat by lia. lra.
Qed.

Lemma tail_bound : forall d i, (1 <= i)%nat ->
  qsum (map g (seq (S i) d)) <= / Zn i.
Proof.
  intros d i Hi. apply Qle_trans with (/ Zn i - / Zn (i + d)).
  - apply tail_tele; assumption.
  - assert (0 < Zn (i + d)) by (apply Zn_pos; lia).
    apply Qle_trans with (/ Zn i - 0); [ | lra ].
    apply Qplus_le_r. apply Qopp_le_compat. apply Qlt_le_weak, Qinv_lt_0_compat; assumption.
Qed.

(* ----------------------------------------------------------------- *)
(*  The partial sums and their regularity.                            *)
(* ----------------------------------------------------------------- *)
Definition P (N : nat) : Q := 1 + 2 * qsum (map g (seq 1 N)).

Lemma seq_1_split : forall i j, (i <= j)%nat ->
  seq 1 j = seq 1 i ++ seq (S i) (j - i).
Proof.
  intros i j Hij.
  replace j with (i + (j - i))%nat at 1 by lia.
  rewrite seq_app. replace (1 + i)%nat with (S i) by lia. reflexivity.
Qed.

Lemma P_diff : forall i j, (1 <= i)%nat -> (i <= j)%nat ->
  Qabs (P i - P j) <= 2 * / Zn i.
Proof.
  intros i j Hi Hij; unfold P.
  rewrite (seq_1_split i j Hij), map_app, qsum_app.
  (* P i − P j = −2 · (tail) ; tail ≥ 0 so |·| = 2·tail ≤ 2/Zn i *)
  set (tl := qsum (map g (seq (S i) (j - i)))).
  assert (Htl0 : 0 <= tl).
  { unfold tl. clear. generalize (seq (S i) (j - i)) as l; intro l.
    induction l as [| a l IH]; cbn [map qsum]; [ lra | ].
    pose proof (g_nonneg a); lra. }
  assert (Htlb : tl <= / Zn i) by (apply tail_bound; assumption).
  rewrite Qabs_neg.
  - (* -(P i - P j) = 2 tl *)
    ring_simplify. apply Qle_trans with (2 * tl); [ lra | ].
    apply Qmult_le_l; [ lra | assumption ].
  - (* P i - P j <= 0 *)
    assert (0 <= 2 * tl) by (apply Qmult_le_0_compat; lra). lra.
Qed.

Lemma P_regular : forall p : positive,
  { N : nat | forall i j, (N <= i)%nat -> (N <= j)%nat -> Qabs (P i - P j) <= 1 # p }.
Proof.
  intro p. exists (S (2 * Pos.to_nat p)).
  intros i j Hi Hj.
  (* WLOG i ≤ j via |P i − P j| = |P j − P i| *)
  assert (key : forall a b, (S (2 * Pos.to_nat p) <= a)%nat -> (a <= b)%nat ->
                  Qabs (P a - P b) <= 1 # p).
  { intros a b Ha Hab.
    apply Qle_trans with (2 * / Zn a); [ apply P_diff; [ lia | assumption ] | ].
    (* 2 / Zn a ≤ 1/p  since a ≥ 2p *)
    assert (Ha2 : Zn (2 * Pos.to_nat p) <= Zn a) by (apply Zn_le; lia).
    assert (Hap : 0 < Zn a) by (apply Zn_pos; lia).
    apply Qle_trans with (2 * / Zn (2 * Pos.to_nat p)).
    - apply Qmult_le_l; [ lra | apply qinv_anti; [ apply Zn_pos; lia | assumption ] ].
    - (* 2 / (2p) = 1/p = 1#p *)
      assert (HZ : Zn (2 * Pos.to_nat p) == 2 * inject_Z (Z.pos p)).
      { unfold Zn. change (2%Q) with (inject_Z 2). rewrite <- inject_Z_mult.
        assert (Heq : (Z.of_nat (2 * Pos.to_nat p) = 2 * Z.pos p)%Z) by lia.
        rewrite Heq; reflexivity. }
      rewrite HZ.
      assert (Hpp : 0 < inject_Z (Z.pos p))
        by (change 0 with (inject_Z 0); rewrite <- Zlt_Qlt; lia).
      setoid_replace (2 * / (2 * inject_Z (Z.pos p))) with (/ inject_Z (Z.pos p))
        by (field; apply Qnot_eq_sym, Qlt_not_eq; assumption).
      unfold Qle, Qinv; simpl. lia. }
  destruct (Nat.le_ge_cases i j) as [Hle | Hge].
  - apply key; assumption.
  - rewrite Qabs_Qminus. apply key; assumption.
Qed.

(* ================================================================= *)
(*  THE CReal LIMIT.                                                  *)
(* ================================================================= *)
Definition poisson_lhs := projT1 (cvQ_of_regular P P_regular).

Theorem poisson_lhs_cv : cvQ P poisson_lhs.
Proof. unfold poisson_lhs; exact (projT2 (cvQ_of_regular P P_regular)). Qed.

Print Assumptions poisson_lhs_cv.

(* ================================================================= *)
(*  END PoissonLHS.v                                                 *)
(*  The lattice-sum LEFT side of the continuous Poisson summation     *)
(*  Σ_{n∈ℤ}1/(1+n²) = π·coth π, built as an axiom-free CReal via the   *)
(*  telescoping tail modulus N=2p and cvQ_of_regular.  The Fourier    *)
(*  RIGHT side needs the constructive integral (knot 1) — the next    *)
(*  brick.  Closed under the global context.                         *)
(* ================================================================= *)
