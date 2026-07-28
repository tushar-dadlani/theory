(* ================================================================= *)
(*  CIntegral.v  —  the CONSTRUCTIVE RIEMANN INTEGRAL of a Lipschitz   *)
(*  function on [0,1], as a cvQ limit of dyadic sums.                 *)
(*                                                                    *)
(*  This is the core brick of KNOT 1 (constructive integration) — the  *)
(*  tool the continuous Fourier side of Poisson, the Gaussian integral *)
(*  ∫e^{−πx²}=√π (the FEResidue axiom), and the real Γ all wait on.    *)
(*                                                                    *)
(*  For f : ℚ→ℚ that is L-Lipschitz (integer L), the dyadic Riemann    *)
(*  sums  R_k = 2^{−k}·Σ_{j<2^k} f(j·2^{−k})  are rational and Cauchy: *)
(*  the DOUBLING estimate |R_k − R_{k+1}| ≤ B_k − B_{k+1} (each dyadic *)
(*  refinement moves the sum by ≤ the Lipschitz variation over one     *)
(*  cell) telescopes to |R_i − R_j| ≤ B_i − B_j (B_k = 2^{−k}·L/2),    *)
(*  giving the explicit modulus N = L·p.  `CRealCv.cvQ_of_regular`     *)
(*  then delivers  cintegral : CReal  with  cvQ R cintegral  — the     *)
(*  value ∫₀¹ f, axiom-free.                                          *)
(*                                                                    *)
(*  HONEST SCOPE.  Left dyadic-endpoint sums on [0,1] for a Lipschitz  *)
(*  integrand — the constructive-integral SEED.  Improper integrals    *)
(*  (∫_ℝ), higher dimension, change of variables and Fubini (what the  *)
(*  Gaussian ∫e^{−πx²} and the Mellin transform need) build ON this;   *)
(*  they are the rest of knot 1.  AXIOM-FREE (Closed under the global  *)
(*  context).                                                         *)
(* ================================================================= *)

From Stdlib Require Import QArith Qabs Lqa Lia List Arith ZArith.
Require Import PrimonGas CRealCv.
Import ListNotations.
Open Scope Q_scope.

(* ----------------------------------------------------------------- *)
(*  Order / qsum helpers.                                             *)
(* ----------------------------------------------------------------- *)
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

Lemma qabs_qsum : forall l, Qabs (qsum l) <= qsum (map Qabs l).
Proof.
  induction l as [| a l IH]; cbn [qsum map].
  - apply Qle_refl.
  - eapply Qle_trans; [ apply Qabs_triangle | apply Qplus_le_r; exact IH ].
Qed.

Lemma qsum_map_le : forall (a b : nat -> Q) l,
  (forall j, In j l -> a j <= b j) -> qsum (map a l) <= qsum (map b l).
Proof.
  intros a b l; induction l as [| x l IH]; intro H; cbn [qsum map].
  - apply Qle_refl.
  - apply Qplus_le_compat.
    + apply H; left; reflexivity.
    + apply IH; intros j Hj; apply H; right; exact Hj.
Qed.

Lemma qsum_map_ext : forall (a b : nat -> Q) l,
  (forall j, In j l -> a j == b j) -> qsum (map a l) == qsum (map b l).
Proof.
  intros a b l; induction l as [| x l IH]; intro H; cbn [qsum map].
  - reflexivity.
  - apply Qplus_comp.
    + apply H; left; reflexivity.
    + apply IH; intros j Hj; apply H; right; exact Hj.
Qed.

Lemma qsum_map_sub : forall (a b : nat -> Q) l,
  qsum (map (fun j => a j - b j) l) == qsum (map a l) - qsum (map b l).
Proof.
  intros a b l; induction l as [| x l IH]; cbn [qsum map]; [ ring | rewrite IH; ring ].
Qed.

Lemma qsum_map_scale : forall (c : Q) (a : nat -> Q) l,
  qsum (map (fun j => c * a j) l) == c * qsum (map a l).
Proof.
  intros c a l; induction l as [| x l IH]; cbn [qsum map]; [ ring | rewrite IH; ring ].
Qed.

Lemma inject_Z_S : forall n, inject_Z (Z.of_nat (S n)) == inject_Z (Z.of_nat n) + 1.
Proof.
  intro n. change (1%Q) with (inject_Z 1). rewrite <- inject_Z_plus.
  assert (Z.of_nat (S n) = Z.of_nat n + 1)%Z by lia. rewrite H; reflexivity.
Qed.

Lemma qsum_map_const_len : forall (c : Q) (l : list nat),
  qsum (map (fun _ => c) l) == inject_Z (Z.of_nat (length l)) * c.
Proof.
  intros c l; induction l as [| x l IH]; cbn [qsum map length].
  - change (Z.of_nat 0) with 0%Z. ring.
  - rewrite IH, inject_Z_S. ring.
Qed.

(* the dyadic-refinement reindex of a sum of 2n terms into n pairs *)
Lemma qsum_pair : forall (G : nat -> Q) n,
  qsum (map G (seq 0 (2 * n))) ==
  qsum (map (fun j => G (2 * j)%nat + G (2 * j + 1)%nat) (seq 0 n)).
Proof.
  intros G n; induction n as [| n IH].
  - reflexivity.
  - replace (2 * S n)%nat with (S (S (2 * n))) by lia.
    rewrite (seq_S (S (2 * n)) 0), (seq_S (2 * n) 0).
    rewrite !map_app, !qsum_app. cbn [map qsum].
    rewrite (seq_S n 0), map_app, qsum_app. cbn [map qsum].
    rewrite IH.
    replace (0 + 2 * n)%nat with (2 * n)%nat by lia.
    replace (0 + S (2 * n))%nat with (2 * n + 1)%nat by lia.
    replace (0 + n)%nat with n by lia.
    ring.
Qed.

Lemma pow2_ge : forall n, (n + 1 <= 2 ^ n)%nat.
Proof. induction n as [| n IH]; simpl; lia. Qed.

Lemma inject_Z_2 : inject_Z 2 == 2.
Proof. reflexivity. Qed.
Lemma inject_Z_1 : inject_Z 1 == 1.
Proof. reflexivity. Qed.

Lemma qeq_le : forall a b : Q, a == b -> a <= b.
Proof. intros a b H; rewrite H; apply Qle_refl. Qed.

(* ================================================================= *)
Section Integral.
  Variable f : Q -> Q.
  Variable L : nat.
  Notation Ln := (inject_Z (Z.of_nat L)).
  Hypothesis Hlip : forall x y, Qabs (f x - f y) <= Ln * Qabs (x - y).

  Lemma Ln_nonneg : 0 <= Ln.
  Proof. change 0 with (inject_Z 0); rewrite <- Zle_Qle; lia. Qed.

  Lemma f_proper : forall x y, x == y -> f x == f y.
  Proof.
    intros x y Hxy.
    assert (H0 : Qabs (f x - f y) <= 0).
    { eapply Qle_trans; [ apply Hlip | ].
      setoid_replace (x - y) with 0 by (rewrite Hxy; ring).
      change (Qabs 0) with 0. rewrite Qmult_0_r. apply Qle_refl. }
    apply Qabs_Qle_condition in H0. lra.
  Qed.

  (* ----- dyadic mesh 2^{−k} and sample points j·2^{−k} ----- *)
  Definition pow2 (k : nat) : Q := inject_Z (Z.of_nat (2 ^ k)).
  Definition mesh (k : nat) : Q := / pow2 k.
  Definition sample (k j : nat) : Q := inject_Z (Z.of_nat j) * mesh k.

  Lemma pow2_pos : forall k, 0 < pow2 k.
  Proof.
    intro k; unfold pow2; change 0 with (inject_Z 0); rewrite <- Zlt_Qlt.
    pose proof (pow2_ge k); lia.
  Qed.

  Lemma pow2_neq : forall k, ~ pow2 k == 0.
  Proof. intro k; apply Qnot_eq_sym, Qlt_not_eq, pow2_pos. Qed.

  Lemma mesh_pos : forall k, 0 < mesh k.
  Proof. intro k; unfold mesh; apply Qinv_lt_0_compat, pow2_pos. Qed.

  Lemma pow2_mesh : forall k, pow2 k * mesh k == 1.
  Proof. intro k; unfold mesh; apply Qmult_inv_r, pow2_neq. Qed.

  Lemma pow2_S : forall k, pow2 (S k) == 2 * pow2 k.
  Proof.
    intro k; unfold pow2. change (2%Q) with (inject_Z 2). rewrite <- inject_Z_mult.
    assert (Z.of_nat (2 ^ S k) = 2 * Z.of_nat (2 ^ k))%Z
      by (rewrite Nat.pow_succ_r'; lia). rewrite H; reflexivity.
  Qed.

  Lemma mesh_S : forall k, mesh (S k) == (1 # 2) * mesh k.
  Proof.
    intro k; unfold mesh. rewrite pow2_S.
    assert (Hp : ~ pow2 k == 0) by apply pow2_neq.
    field; assumption.
  Qed.

  Lemma mesh_le : forall i j, (i <= j)%nat -> mesh j <= mesh i.
  Proof.
    intros i j Hij; unfold mesh; apply qinv_anti; [ apply pow2_pos | ].
    unfold pow2; rewrite <- Zle_Qle.
    assert (2 ^ i <= 2 ^ j)%nat by (apply Nat.pow_le_mono_r; lia). lia.
  Qed.

  Lemma sample_even : forall k j, sample (S k) (2 * j)%nat == sample k j.
  Proof.
    intros k j; unfold sample. rewrite mesh_S.
    assert (H : (Z.of_nat (2 * j) = 2 * Z.of_nat j)%Z) by lia.
    rewrite H, inject_Z_mult, inject_Z_2. ring.
  Qed.

  Lemma sample_odd : forall k j,
    sample (S k) (2 * j + 1)%nat == sample k j + mesh (S k).
  Proof.
    intros k j; unfold sample. rewrite (mesh_S k).
    assert (H : (Z.of_nat (2 * j + 1) = 2 * Z.of_nat j + 1)%Z) by lia.
    rewrite H, inject_Z_plus, inject_Z_mult, inject_Z_2, inject_Z_1. ring.
  Qed.

  (* ----- the dyadic Riemann sum ----- *)
  Definition R (k : nat) : Q :=
    mesh k * qsum (map (fun j => f (sample k j)) (seq 0 (2 ^ k))).

  Lemma R_diff : forall k,
    R k - R (S k) ==
    mesh (S k) *
    qsum (map (fun j => f (sample k j) - f (sample k j + mesh (S k))) (seq 0 (2 ^ k))).
  Proof.
    intro k.
    assert (HSk : R (S k) == mesh (S k) *
      qsum (map (fun j => f (sample k j) + f (sample k j + mesh (S k))) (seq 0 (2 ^ k)))).
    { unfold R.
      replace (2 ^ S k)%nat with (2 * 2 ^ k)%nat by (rewrite Nat.pow_succ_r'; ring).
      rewrite (qsum_pair (fun i => f (sample (S k) i)) (2 ^ k)).
      f_equiv. apply qsum_map_ext; intros j Hj.
      rewrite (f_proper _ _ (sample_even k j)).
      rewrite (f_proper _ _ (sample_odd k j)). reflexivity. }
    assert (HRk : R k == mesh (S k) *
      qsum (map (fun j => 2 * f (sample k j)) (seq 0 (2 ^ k)))).
    { unfold R. rewrite (qsum_map_scale 2 (fun j => f (sample k j))).
      assert (Hm : mesh k == 2 * mesh (S k)) by (rewrite mesh_S; ring).
      rewrite Hm. ring. }
    rewrite HRk, HSk.
    setoid_replace (mesh (S k) * qsum (map (fun j => 2 * f (sample k j)) (seq 0 (2 ^ k)))
        - mesh (S k) * qsum (map (fun j => f (sample k j) + f (sample k j + mesh (S k))) (seq 0 (2 ^ k))))
      with (mesh (S k) * (qsum (map (fun j => 2 * f (sample k j)) (seq 0 (2 ^ k)))
        - qsum (map (fun j => f (sample k j) + f (sample k j + mesh (S k))) (seq 0 (2 ^ k))))) by ring.
    f_equiv. rewrite <- qsum_map_sub. apply qsum_map_ext; intros j Hj. ring.
  Qed.

  (* ----- doubling estimate ----- *)
  Definition B (k : nat) : Q := mesh k * ((1 # 2) * Ln).

  Lemma B_nonneg : forall k, 0 <= B k.
  Proof.
    intro k; unfold B; apply Qmult_le_0_compat.
    - apply Qlt_le_weak, mesh_pos.
    - apply Qmult_le_0_compat; [ apply Qlt_le_weak; reflexivity | apply Ln_nonneg ].
  Qed.

  Lemma B_le : forall i j, (i <= j)%nat -> B j <= B i.
  Proof.
    intros i j Hij; unfold B; apply Qmult_le_compat_r.
    - apply mesh_le; assumption.
    - apply Qmult_le_0_compat; [ apply Qlt_le_weak; reflexivity | apply Ln_nonneg ].
  Qed.

  Lemma doubling : forall k, Qabs (R k - R (S k)) <= B k - B (S k).
  Proof.
    intro k. rewrite R_diff, Qabs_Qmult.
    rewrite (Qabs_pos (mesh (S k))) by (apply Qlt_le_weak, mesh_pos).
    assert (Hsum :
      Qabs (qsum (map (fun j => f (sample k j) - f (sample k j + mesh (S k))) (seq 0 (2 ^ k))))
      <= pow2 k * (Ln * mesh (S k))).
    { eapply Qle_trans; [ apply qabs_qsum | ]. rewrite map_map.
      eapply Qle_trans.
      { apply qsum_map_le with (b := fun _ => Ln * mesh (S k)).
        intros j Hj. eapply Qle_trans; [ apply Hlip | ].
        setoid_replace (sample k j - (sample k j + mesh (S k))) with (- mesh (S k)) by ring.
        rewrite Qabs_opp, (Qabs_pos (mesh (S k))) by (apply Qlt_le_weak, mesh_pos).
        apply Qle_refl. }
      rewrite qsum_map_const_len, length_seq. unfold pow2. apply Qle_refl. }
    apply Qle_trans with (mesh (S k) * (pow2 k * (Ln * mesh (S k)))).
    - rewrite !(Qmult_comm (mesh (S k))).
      apply Qmult_le_compat_r; [ exact Hsum | apply Qlt_le_weak, mesh_pos ].
    - apply qeq_le.
      assert (Hpm : pow2 k * mesh (S k) == (1 # 2)).
      { rewrite mesh_S.
        setoid_replace (pow2 k * ((1 # 2) * mesh k)) with ((1 # 2) * (pow2 k * mesh k)) by ring.
        rewrite pow2_mesh; ring. }
      unfold B.
      setoid_replace (mesh (S k) * (pow2 k * (Ln * mesh (S k))))
        with (Ln * mesh (S k) * (pow2 k * mesh (S k))) by ring.
      rewrite Hpm, mesh_S. ring.
  Qed.

  (* ----- telescoping ----- *)
  Lemma tele : forall d i, Qabs (R i - R (i + d)) <= B i - B (i + d).
  Proof.
    induction d as [| d IH]; intro i.
    - rewrite Nat.add_0_r.
      setoid_replace (R i - R i) with (0 : Q) by ring.
      rewrite (Qabs_pos 0) by apply Qle_refl.
      setoid_replace (B i - B i) with (0 : Q) by ring. apply Qle_refl.
    - replace (i + S d)%nat with (S (i + d))%nat by lia.
      eapply Qle_trans.
      { setoid_replace (R i - R (S (i + d)))
          with ((R i - R (i + d)) + (R (i + d) - R (S (i + d)))) by ring.
        apply Qabs_triangle. }
      eapply Qle_trans.
      { apply Qplus_le_compat; [ apply IH | apply doubling ]. }
      apply qeq_le. ring.
  Qed.

  (* ----- the modulus and the CReal limit ----- *)
  Lemma B_modulus : forall p, B (L * Pos.to_nat p) <= 1 # p.
  Proof.
    intro p.
    assert (Hkey : Ln * inject_Z (Z.pos p) <= 2 * pow2 (L * Pos.to_nat p)).
    { unfold pow2. change (2%Q) with (inject_Z 2). rewrite <- !inject_Z_mult.
      rewrite <- Zle_Qle, <- positive_nat_Z.
      pose proof (pow2_ge (L * Pos.to_nat p)) as Hp2. nia. }
    assert (Hzp : 0 < inject_Z (Z.pos p))
      by (change 0 with (inject_Z 0); rewrite <- Zlt_Qlt; lia).
    assert (Hzp0 : ~ inject_Z (Z.pos p) == 0) by (apply Qnot_eq_sym, Qlt_not_eq; assumption).
    assert (Hpi : (1 # p) == / inject_Z (Z.pos p)) by reflexivity.
    unfold B. rewrite Hpi.
    apply (proj1 (Qmult_le_r (mesh (L * Pos.to_nat p) * ((1 # 2) * Ln))
                            (/ inject_Z (Z.pos p))
                            (pow2 (L * Pos.to_nat p) * inject_Z (Z.pos p))
                            (Qmult_lt_0_compat _ _ (pow2_pos _) Hzp))).
    setoid_replace (mesh (L * Pos.to_nat p) * ((1 # 2) * Ln)
                    * (pow2 (L * Pos.to_nat p) * inject_Z (Z.pos p)))
      with ((1 # 2) * Ln * inject_Z (Z.pos p)
            * (pow2 (L * Pos.to_nat p) * mesh (L * Pos.to_nat p))) by ring.
    rewrite pow2_mesh.
    setoid_replace (/ inject_Z (Z.pos p) * (pow2 (L * Pos.to_nat p) * inject_Z (Z.pos p)))
      with (pow2 (L * Pos.to_nat p) * (inject_Z (Z.pos p) * / inject_Z (Z.pos p))) by ring.
    rewrite Qmult_inv_r by assumption.
    setoid_replace ((1 # 2) * Ln * inject_Z (Z.pos p) * 1)
      with ((1 # 2) * (Ln * inject_Z (Z.pos p))) by ring.
    rewrite Qmult_1_r.
    apply Qle_trans with ((1 # 2) * (2 * pow2 (L * Pos.to_nat p))).
    - assert (H12 : 0 < (1 # 2)) by lra.
      apply (proj2 (Qmult_le_l (Ln * inject_Z (Z.pos p))
                               (2 * pow2 (L * Pos.to_nat p)) (1 # 2) H12)).
      exact Hkey.
    - apply qeq_le; ring.
  Qed.

  (* ----- regularity and the CReal limit ----- *)
  Lemma R_regular : forall p : positive,
    { N : nat | forall i j, (N <= i)%nat -> (N <= j)%nat -> Qabs (R i - R j) <= 1 # p }.
  Proof.
    intro p. exists (L * Pos.to_nat p)%nat.
    assert (key : forall a b, (L * Pos.to_nat p <= a)%nat -> (a <= b)%nat ->
                    Qabs (R a - R b) <= 1 # p).
    { intros a b Ha Hab.
      apply Qle_trans with (B a - B b).
      - replace b with (a + (b - a))%nat by lia. apply tele.
      - apply Qle_trans with (B a).
        + pose proof (B_nonneg b); lra.
        + apply Qle_trans with (B (L * Pos.to_nat p)); [ apply B_le; exact Ha | apply B_modulus ]. }
    intros i j Hi Hj.
    destruct (Nat.le_ge_cases i j) as [Hle | Hge].
    - apply key; assumption.
    - rewrite Qabs_Qminus. apply key; assumption.
  Qed.

  Definition cintegral := projT1 (cvQ_of_regular R R_regular).
  Theorem cintegral_cv : cvQ R cintegral.
  Proof. unfold cintegral; exact (projT2 (cvQ_of_regular R R_regular)). Qed.

End Integral.

Print Assumptions cintegral_cv.

(* ================================================================= *)
(*  END CIntegral.v                                                  *)
(*  The constructive Riemann integral of a Lipschitz function on      *)
(*  [0,1] as a cvQ limit of dyadic sums — the seed of knot 1          *)
(*  (constructive integration).  Closed under the global context.     *)
(* ================================================================= *)
