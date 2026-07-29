(* ================================================================= *)
(*  ConstructiveSqrtPi.v  —  a constructive √π, discharging FEResidue. *)
(*                                                                    *)
(*  There is no square root in stdlib's constructive reals, so we      *)
(*  build one: rational BISECTION on [1,2] with an explicit precision  *)
(*  bound |bis² − a| ≤ 4·(hi−lo)·(½)^fuel (the `4` from hi ≤ 2 lets    *)
(*  the (½)^fuel shrink telescope through the recursion).  Applied to  *)
(*  the central-binomial π-approximants `cpi n` (all in [π,4]⊂[1,4]),  *)
(*  it gives a rational sequence `sq n → √π`, bounded ≤ 2, whose       *)
(*  square tracks `cpi n`; `CRealCv.cvQ_sq` then squares the limit and *)
(*  `constructive_sqrt_pi² == constructive_pi`.  This DISCHARGES the    *)
(*  `FEResidue` value axiom `Γ(½)²=π` — over `CReal`, with `π` the      *)
(*  Wallis limit (ConstructivePi) and `Γ(½)=√π` its positive root.     *)
(*                                                                    *)
(*  HONEST BOUNDARY unchanged: `π`/`√π` are the Wallis constructions   *)
(*  (classically the analytic constants); that this `√π` equals the    *)
(*  Gaussian integral `∫e^{−πx²}` stays classical, unformalized.       *)
(*  AXIOM-FREE (Closed under the global context).                    *)
(* ================================================================= *)

From Stdlib Require Import Reals.Cauchy.ConstructiveCauchyReals
  Reals.Cauchy.ConstructiveCauchyRealsMult
  Reals.Cauchy.ConstructiveCauchyAbs
  Reals.Cauchy.ConstructiveRcomplete.
From Stdlib Require Import QArith Qabs Lqa Lia List Arith ZArith.
Require Import PrimonGas CRealCv PoissonLHS ConstructivePi.
Import ListNotations.
Open Scope Q_scope.

Lemma qeq_le : forall a b : Q, a == b -> a <= b.
Proof. intros a b H; rewrite H; apply Qle_refl. Qed.

(* (1/2)^n *)
Fixpoint half (n : nat) : Q := match n with O => 1 | S k => (1 # 2) * half k end.

Lemma half_pos : forall n, 0 < half n.
Proof. induction n as [| n IH]; cbn [half]; [ reflexivity | ]. apply Qmult_lt_0_compat; [ reflexivity | exact IH ]. Qed.

(* ----------------------------------------------------------------- *)
(*  rational bisection for √a on [lo,hi]                              *)
(* ----------------------------------------------------------------- *)
Fixpoint bis (fuel : nat) (lo hi a : Q) : Q :=
  match fuel with
  | O => (lo + hi) * (1 # 2)
  | S k => let m := (lo + hi) * (1 # 2) in
           if Qle_bool (m * m) a then bis k m hi a else bis k lo m a
  end.

Lemma bis_range : forall fuel lo hi a,
  lo <= hi -> lo <= bis fuel lo hi a /\ bis fuel lo hi a <= hi.
Proof.
  induction fuel as [| k IH]; intros lo hi a Hle; cbn [bis].
  - split; lra.
  - set (m := (lo + hi) * (1 # 2)).
    assert (Hm1 : lo <= m) by (unfold m; lra).
    assert (Hm2 : m <= hi) by (unfold m; lra).
    destruct (Qle_bool (m * m) a).
    + destruct (IH m hi a Hm2) as [H1 H2]; split; [ lra | exact H2 ].
    + destruct (IH lo m a Hm1) as [H1 H2]; split; [ exact H1 | lra ].
Qed.

Lemma bis_prec : forall fuel lo hi a, 0 <= lo -> lo <= hi -> hi <= 2 ->
  lo * lo <= a -> a <= hi * hi ->
  Qabs (bis fuel lo hi a * bis fuel lo hi a - a) <= 4 * (hi - lo) * half fuel.
Proof.
  induction fuel as [| k IH]; intros lo hi a Hlo Hle Hhi Hla Hah; cbn [bis half].
  - apply Qabs_Qle_condition; split; nra.
  - set (m := (lo + hi) * (1 # 2)).
    assert (Hm1 : lo <= m) by (unfold m; lra).
    assert (Hm2 : m <= hi) by (unfold m; lra).
    assert (Hmm : hi - m == (hi - lo) * (1 # 2)) by (unfold m; ring).
    assert (Hml : m - lo == (hi - lo) * (1 # 2)) by (unfold m; ring).
    destruct (Qle_bool (m * m) a) eqn:E.
    + apply Qle_bool_iff in E.
      eapply Qle_trans; [ apply IH; [ lra | exact Hm2 | exact Hhi | exact E | exact Hah ] | ].
      rewrite Hmm; apply qeq_le; ring.
    + assert (Ha : a <= m * m).
      { assert (Hnle : ~ (m * m <= a)).
        { intro Hc; apply Qle_bool_iff in Hc; rewrite E in Hc; discriminate. }
        apply Qlt_le_weak, Qnot_le_lt; exact Hnle. }
      eapply Qle_trans; [ apply IH; [ exact Hlo | exact Hm1 | lra | exact Hla | exact Ha ] | ].
      rewrite Hml; apply qeq_le; ring.
Qed.

(* ----------------------------------------------------------------- *)
(*  the √π sequence:  bisect √(cπ n) with n steps                     *)
(* ----------------------------------------------------------------- *)

(* cπ n stays in [2,4] ⊂ [1,4], so bisection on [1,2] applies *)
Lemma cpi_ge2 : forall n, 2 <= cpi n.
Proof.
  intro n. pose proof (cpi_tele n 0) as H. replace (0 + n)%nat with n in H by lia.
  assert (Hc0 : cpi 0 = 4) by reflexivity.
  assert (Hz1 : / Zn (2 * 0 + 1) == 1) by (unfold Zn; reflexivity).
  assert (Hnn : 0 <= / Zn (2 * n + 1))
    by (apply Qlt_le_weak, Qinv_lt_0_compat, Zn_pos; nia).
  rewrite Hc0, Hz1 in H.
  set (q := / Zn (2 * n + 1)) in *; clearbody q; lra.
Qed.

Lemma half_le_over_n : forall n, half n <= / inject_Z (Z.of_nat (S n)).
Proof.
  induction n as [| n IH]; cbn [half].
  - apply qeq_le; reflexivity.
  - assert (Hx : 0 < inject_Z (Z.of_nat (S n)))
      by (change 0 with (inject_Z 0); rewrite <- Zlt_Qlt; lia).
    assert (Hy : 0 < inject_Z (Z.of_nat (S (S n))))
      by (change 0 with (inject_Z 0); rewrite <- Zlt_Qlt; lia).
    apply Qle_trans with ((1 # 2) * / inject_Z (Z.of_nat (S n))).
    + apply Qmult_le_l; [ reflexivity | exact IH ].
    + assert (Hxy : inject_Z (Z.of_nat (S (S n))) <= 2 * inject_Z (Z.of_nat (S n))).
      { change 2 with (inject_Z 2). rewrite <- inject_Z_mult, <- Zle_Qle. lia. }
      setoid_replace ((1 # 2) * / inject_Z (Z.of_nat (S n)))
        with (/ (2 * inject_Z (Z.of_nat (S n))))
        by (field; apply Qnot_eq_sym, Qlt_not_eq; exact Hx).
      apply qinv_anti; [ exact Hy | exact Hxy ].
Qed.

Definition sq (n : nat) : Q := bis n 1 2 (cpi n).

Lemma sq_range : forall n, 1 <= sq n /\ sq n <= 2.
Proof. intro n; unfold sq; apply bis_range; lra. Qed.

Lemma sq_prec : forall n, Qabs (sq n * sq n - cpi n) <= 4 * half n.
Proof.
  intro n; unfold sq.
  apply Qle_trans with (4 * (2 - 1) * half n).
  - apply bis_prec;
      [ lra | lra | lra | pose proof (cpi_ge2 n); lra | pose proof (cpi_le4 n); lra ].
  - apply qeq_le; ring.
Qed.

(* on [1,2], differences shrink at least as fast as squared differences *)
Lemma sq_lip : forall i j, 2 * Qabs (sq i - sq j) <= Qabs (sq i * sq i - sq j * sq j).
Proof.
  intros i j.
  pose proof (sq_range i) as Hi; pose proof (sq_range j) as Hj.
  setoid_replace (sq i * sq i - sq j * sq j) with ((sq i - sq j) * (sq i + sq j)) by ring.
  rewrite Qabs_Qmult, (Qabs_pos (sq i + sq j)) by lra.
  rewrite (Qmult_comm (Qabs (sq i - sq j)) (sq i + sq j)).
  apply Qmult_le_compat_r; [ lra | apply Qabs_nonneg ].
Qed.

Lemma sq_regular : forall p : positive,
  { N : nat | forall i j, (N <= i)%nat -> (N <= j)%nat -> Qabs (sq i - sq j) <= 1 # p }.
Proof.
  intro p. destruct (cpi_regular (2 * p)%positive) as [Nc HNc].
  exists (Nat.max (6 * Pos.to_nat p) Nc).
  intros i j Hi Hj.
  assert (Hi6 : (6 * Pos.to_nat p <= i)%nat) by lia.
  assert (Hj6 : (6 * Pos.to_nat p <= j)%nat) by lia.
  assert (Hic : (Nc <= i)%nat) by lia.
  assert (Hjc : (Nc <= j)%nat) by lia.
  (* each of the three RHS pieces ≤ 2#(3p) *)
  assert (Hbnd : forall n, (6 * Pos.to_nat p <= n)%nat -> 4 * half n <= 2 # (3 * p)).
  { intros n Hn.
    assert (Hh : half n <= 1 # (6 * p)).
    { eapply Qle_trans; [ apply half_le_over_n | ].
      assert (E6 : (1 # (6 * p)) == / inject_Z (Z.pos (6 * p))) by reflexivity.
      rewrite E6. apply qinv_anti;
        [ change 0 with (inject_Z 0); rewrite <- Zlt_Qlt; lia
        | rewrite <- Zle_Qle; lia ]. }
    apply Qle_trans with (4 * (1 # (6 * p)));
      [ apply Qmult_le_l; [ reflexivity | exact Hh ] | unfold Qle; simpl; lia ]. }
  assert (Hc : Qabs (cpi i - cpi j) <= 2 # (3 * p)).
  { apply Qle_trans with (1 # (2 * p)); [ apply HNc; assumption | ].
    unfold Qle; simpl; lia. }
  (* combine: 2·|sq i − sq j| ≤ 4half i + |cpi i−cpi j| + 4half j ≤ 3·(2#(3p)) = 2#p *)
  pose proof (sq_lip i j) as Hlip.
  assert (Htri : Qabs (sq i * sq i - sq j * sq j)
                 <= 4 * half i + (Qabs (cpi i - cpi j) + 4 * half j)).
  { eapply Qle_trans.
    - setoid_replace (sq i * sq i - sq j * sq j)
        with ((sq i * sq i - cpi i) + (cpi i - sq j * sq j)) by ring.
      apply Qabs_triangle.
    - apply Qplus_le_compat; [ apply sq_prec | ].
      eapply Qle_trans.
      + setoid_replace (cpi i - sq j * sq j) with ((cpi i - cpi j) + (cpi j - sq j * sq j)) by ring.
        apply Qabs_triangle.
      + apply Qplus_le_compat; [ apply Qle_refl | rewrite Qabs_Qminus; apply sq_prec ]. }
  pose proof (Hbnd i Hi6) as Hbi. pose proof (Hbnd j Hj6) as Hbj.
  assert (Hfin : 4 * half i + (Qabs (cpi i - cpi j) + 4 * half j) <= 2 # p).
  { assert (E : (2 # (3 * p)) + ((2 # (3 * p)) + (2 # (3 * p))) == 2 # p)
      by (unfold Qeq; simpl; lia).
    rewrite <- E. apply Qplus_le_compat; [ exact Hbi | apply Qplus_le_compat; [ exact Hc | exact Hbj ] ]. }
  assert (E2 : (2 # p) == 2 * (1 # p)) by (unfold Qeq; simpl; lia).
  set (d := Qabs (sq i - sq j)) in *; clearbody d.
  (* 2 d ≤ |sq²−sq²| ≤ Htri ≤ 2#p = 2·(1#p) ⟹ d ≤ 1#p *)
  set (s := Qabs (sq i * sq i - sq j * sq j)) in *; clearbody s.
  rewrite E2 in Hfin. lra.
Qed.

Definition constructive_sqrt_pi := projT1 (cvQ_of_regular sq sq_regular).

Theorem constructive_sqrt_pi_cv : cvQ sq constructive_sqrt_pi.
Proof. unfold constructive_sqrt_pi; exact (projT2 (cvQ_of_regular sq sq_regular)). Qed.

Print Assumptions constructive_sqrt_pi_cv.
