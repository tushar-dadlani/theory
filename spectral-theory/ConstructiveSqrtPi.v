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

(* ----------------------------------------------------------------- *)
(*  discharging FEResidue:  √π² == π  and  √π > 0                     *)
(* ----------------------------------------------------------------- *)

Lemma cvQ_opp : forall a x, cvQ a x -> cvQ (fun n => (- a n)%Q) (- x)%CReal.
Proof.
  intros a x H p; destruct (H p) as [N HN]; exists N; intros n Hn.
  assert (E : (inject_Q (- a n)%Q - (- x) == - (inject_Q (a n) - x))%CReal)
    by (rewrite opp_inject_Q; ring).
  rewrite E, CReal_abs_opp. apply HN; exact Hn.
Qed.

Lemma qeq_le_creal : forall a b : CReal, (a == b)%CReal -> (a <= b)%CReal.
Proof. intros a b [_ H]; exact H. Qed.

(* a perturbed sequence shares the limit *)
Lemma cvQ_close : forall (a b : nat -> Q) x, cvQ a x ->
  (forall p, exists N, forall n, (N <= n)%nat -> Qabs (b n - a n) <= 1 # p) -> cvQ b x.
Proof.
  intros a b x Ha Hcl p.
  destruct (Ha (2 * p)%positive) as [N1 H1].
  destruct (Hcl (2 * p)%positive) as [N2 H2].
  exists (Nat.max N1 N2); intros n Hn.
  assert (E : (inject_Q (b n) - x
               == (inject_Q (b n) - inject_Q (a n)) + (inject_Q (a n) - x))%CReal) by ring.
  rewrite E. eapply CReal_le_trans; [ apply CReal_abs_triang | ].
  assert (Hba : (CReal_abs (inject_Q (b n) - inject_Q (a n)) <= inject_Q (1 # (2 * p)))%CReal).
  { setoid_replace (inject_Q (b n) - inject_Q (a n))%CReal with (inject_Q (b n - a n))
      by (rewrite inject_Q_diff; ring).
    apply inj_abs_le, H2; lia. }
  assert (Hax : (CReal_abs (inject_Q (a n) - x) <= inject_Q (1 # (2 * p)))%CReal) by (apply H1; lia).
  eapply CReal_le_trans; [ apply CReal_plus_le_compat; [ exact Hba | exact Hax ] | ].
  rewrite <- inject_Q_plus. apply inject_Q_le. unfold Qle; simpl; lia.
Qed.

(* limit uniqueness (the dense/archimedean argument) *)
Lemma cvQ_le : forall a x y, cvQ a x -> cvQ a y -> (x <= y)%CReal.
Proof.
  intros a x y Hx Hy Hlt.
  destruct (CRealQ_dense y x Hlt) as [q1 [Hyq1 Hq1x]].
  destruct (CRealQ_dense (inject_Q q1) x Hq1x) as [q2 [Hq1q2 Hq2x]].
  apply lt_inject_Q in Hq1q2.
  set (d := (q2 - q1)%Q); assert (Hd : (0 < d)%Q) by (unfold d; lra).
  set (p := Qden (d * (1 # 2))).
  assert (H2p : (2 * (1 # p) <= d)%Q).
  { assert (Hh : (1 # p <= d * (1 # 2))%Q) by (unfold p; apply Qle_1_Qden; unfold d; lra). lra. }
  destruct (Hx p) as [N1 HN1]; destruct (Hy p) as [N2 HN2].
  set (n := Nat.max N1 N2).
  pose proof (HN1 n ltac:(unfold n; lia)) as A1; apply CReal_abs_def2 in A1; destruct A1 as [A1u A1l].
  pose proof (HN2 n ltac:(unfold n; lia)) as A2; apply CReal_abs_def2 in A2; destruct A2 as [A2u A2l].
  (* x ≤ a n + 1#p  and  a n − 1#p ≤ y  ⟹  x − y ≤ 2·1#p *)
  assert (Hxa : (x <= inject_Q (a n) + inject_Q (1 # p))%CReal).
  { setoid_replace x with (inject_Q (a n) - (inject_Q (a n) - x))%CReal by ring.
    apply CReal_plus_le_compat; [ apply CRealLe_refl | ].
    (* − (a n − x) ≤ 1#p  from  A1l : −1#p ≤ a n − x *)
    rewrite <- (CReal_opp_involutive (inject_Q (1 # p))).
    apply CReal_opp_ge_le_contravar; exact A1l. }
  assert (Hay : (inject_Q (a n) - inject_Q (1 # p) <= y)%CReal).
  { setoid_replace y with (inject_Q (a n) - (inject_Q (a n) - y))%CReal by ring.
    apply CReal_plus_le_compat; [ apply CRealLe_refl | ].
    apply CReal_opp_ge_le_contravar; exact A2u. }
  assert (S1 : (x - y <= inject_Q (1 # p) + inject_Q (1 # p))%CReal).
  { apply CReal_le_trans
      with ((inject_Q (a n) + inject_Q (1 # p)) - (inject_Q (a n) - inject_Q (1 # p)))%CReal.
    - apply CReal_plus_le_compat; [ exact Hxa | apply CReal_opp_ge_le_contravar; exact Hay ].
    - apply qeq_le_creal; ring. }
  (* x − y > inject_Q d ≥ 2·1#p *)
  assert (S2 : (inject_Q (1 # p) + inject_Q (1 # p) < x - y)%CReal).
  { apply CReal_le_lt_trans with (inject_Q q2 - inject_Q q1)%CReal.
    - rewrite <- inject_Q_plus.
      setoid_replace (inject_Q q2 - inject_Q q1)%CReal with (inject_Q (q2 - q1))
        by (rewrite inject_Q_diff; ring).
      apply inject_Q_le. unfold d in H2p; lra.
    - apply CReal_lt_le_trans with (x - inject_Q q1)%CReal.
      + setoid_replace (inject_Q q2 - inject_Q q1)%CReal
          with (- inject_Q q1 + inject_Q q2)%CReal by ring.
        setoid_replace (x - inject_Q q1)%CReal with (- inject_Q q1 + x)%CReal by ring.
        apply CReal_plus_lt_compat_l; exact Hq2x.
      + apply CReal_plus_le_compat;
          [ apply CRealLe_refl | apply CReal_opp_ge_le_contravar, CRealLt_asym; exact Hyq1 ]. }
  exact (CRealLt_asym _ _ (CReal_le_lt_trans _ _ _ S1 S2) (CReal_le_lt_trans _ _ _ S1 S2)).
Qed.

Lemma cvQ_unique : forall a x y, cvQ a x -> cvQ a y -> (x == y)%CReal.
Proof. intros a x y Hx Hy; split; [ apply (cvQ_le a y x) | apply (cvQ_le a x y) ]; assumption. Qed.

(* sq² converges both to √π² and to π, so they are equal *)
Lemma sq_sq_cv_sqrt : cvQ (fun n => sq n * sq n) (constructive_sqrt_pi * constructive_sqrt_pi).
Proof.
  apply cvQ_sq; [ apply constructive_sqrt_pi_cv | ].
  intro n; pose proof (sq_range n) as Hr.
  rewrite Qabs_pos by lra; lra.
Qed.

Lemma sq_sq_cv_pi : cvQ (fun n => sq n * sq n) constructive_pi.
Proof.
  apply (cvQ_close cpi); [ apply constructive_pi_cv | ].
  intro p. exists (4 * Pos.to_nat p)%nat. intros n Hn.
  eapply Qle_trans; [ apply sq_prec | ].
  assert (Hh : half n <= 1 # (4 * p)).
  { eapply Qle_trans; [ apply half_le_over_n | ].
    assert (E4 : (1 # (4 * p)) == / inject_Z (Z.pos (4 * p))) by reflexivity.
    rewrite E4. apply qinv_anti;
      [ change 0 with (inject_Z 0); rewrite <- Zlt_Qlt; lia | rewrite <- Zle_Qle; lia ]. }
  apply Qle_trans with (4 * (1 # (4 * p)));
    [ apply Qmult_le_l; [ reflexivity | exact Hh ] | unfold Qle; simpl; lia ].
Qed.

(* ================================================================= *)
(*  THE DISCHARGE: FEResidue's value axiom, now a theorem.           *)
(* ================================================================= *)
Theorem gamma_half_sq_eq_pi :
  (constructive_sqrt_pi * constructive_sqrt_pi == constructive_pi)%CReal.
Proof. apply (cvQ_unique (fun n => sq n * sq n)); [ apply sq_sq_cv_sqrt | apply sq_sq_cv_pi ]. Qed.

Theorem gamma_half_pos : (inject_Q 1 <= constructive_sqrt_pi)%CReal.
Proof.
  assert (H : (- constructive_sqrt_pi <= - inject_Q 1)%CReal).
  { apply (cvQ_le_const _ _ _ (cvQ_opp _ _ constructive_sqrt_pi_cv)).
    intro n. rewrite opp_inject_Q.
    apply CReal_opp_ge_le_contravar, inject_Q_le. pose proof (sq_range n); lra. }
  pose proof (CReal_opp_ge_le_contravar _ _ H) as H2.
  rewrite !CReal_opp_involutive in H2. exact H2.
Qed.

(* Numerical certificate: sq₁₅ bisects √(cπ₁₅) ≈ √3.19 ≈ 1.79, en route  *)
(* to √π ≈ 1.77245; this pins it into [1.77, 1.79], certifying the        *)
(* bisection genuinely computes the square root and not something else.   *)
Remark sq_is_numerically_sqrt_pi :
  (Qle_bool (177 # 100) (sq 15) && Qle_bool (sq 15) (179 # 100)) = true.
Proof. vm_compute. reflexivity. Qed.

Print Assumptions gamma_half_sq_eq_pi.
Print Assumptions gamma_half_pos.
