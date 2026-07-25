(* ================================================================= *)
(*  QPolySqfree.v                                                    *)
(*                                                                    *)
(*  SQUAREFREENESS OF X^n − 1 in ℚ[X] (brick 5d).                   *)
(*                                                                    *)
(*    qsqfree M  :=  h²∣M → h is constant.                          *)
(*    qsqfree_Xn1 :  1 ≤ n → qsqfree (X^n − 1).                     *)
(*                                                                    *)
(*  Proof: h²∣X^n−1 ⟹ (coeff-PIT) X^n−1 = h²·k as polynomials       *)
(*  ⟹ (product rule) h ∣ (X^n−1)′ = n·X^{n−1}; also h ∣ X^n−1;       *)
(*  the Bézout X·(nX^{n−1}) − n·(X^n−1) = n then gives h ∣ [n], a     *)
(*  nonzero constant, so (degree-of-product) h is constant.  Also the *)
(*  split lemma `qsqfree_mul_copr` used for cyclotomic coprimality.   *)
(*  AXIOM-FREE.                                                       *)
(* ================================================================= *)

From Stdlib Require Import QArith Qcanon List Lia Arith.
Import ListNotations.
Require Import QPoly QPolyDiv QPolyDeg QPolyGcd QPolyCoeffPIT QPolyMul QPolyDeriv
        QPolyCoprime QPolyRoot.
Open Scope Qc_scope.

(* ----------------------------------------------------------------- *)
(*  Small helpers                                                    *)
(* ----------------------------------------------------------------- *)
Lemma qnat_pos_nz : forall n, (1 <= n)%nat -> qnat n <> 0.
Proof. intros n Hn; destruct n; [ lia | apply qnat_Sk_nz ]. Qed.

Lemma qcoeff_qconst_hi : forall c i, (1 <= i)%nat -> qcoeff (qconst c) i = 0.
Proof. intros c i Hi; unfold qcoeff, qconst; apply nth_overflow; simpl; lia. Qed.

Lemma qcoeff_qmonom_n : forall n, qcoeff (qmonom n) n = 1.
Proof.
  induction n as [|n IH]; [ reflexivity | ].
  unfold qcoeff; cbn [qmonom nth]; exact IH.
Qed.

Lemma qnorm_const_nz : forall c, c <> 0 -> qnorm (qconst c) = [c].
Proof.
  intros c Hc; unfold qconst; cbn [qnorm]; unfold qnonzero;
    destruct (Qc_eq_dec c 0); [ contradiction | reflexivity ].
Qed.

Lemma qXn1_nonzero : forall n, (1 <= n)%nat -> qnorm (qXn1 n) <> [].
Proof.
  intros n Hn Hz.
  pose proof (qnorm_all_zero _ Hz n) as H.
  unfold qXn1 in H; rewrite qcoeff_add, qcoeff_qmonom_n, qcoeff_qconst_hi in H by lia.
  apply qc_one_neq_zero; rewrite <- H; ring.
Qed.

Lemma qdivides_nonzero : forall h M, qdivides h M -> qnorm M <> [] -> qnorm h <> [].
Proof.
  intros h M [r Hr] HM Hh; apply HM; apply qeval_zero_norm; intro x.
  rewrite Hr, (qeval_qnorm_nil h Hh x); ring.
Qed.

Lemma qdivides_trans : forall a b c, qdivides a b -> qdivides b c -> qdivides a c.
Proof.
  intros a b c [rb Hb] [rc Hc]; exists (qmul rb rc); intro x.
  rewrite Hc, Hb, qeval_mul; ring.
Qed.

Lemma qmul_lead_nz : forall h r, qnorm h <> [] -> qnorm r <> [] ->
  qcoeff (qmul h r) (qdeg h + qdeg r) <> 0.
Proof.
  intros h r Hh Hr.
  rewrite (qcoeff_qmul_top h r (qdeg h) (qdeg r) (qdegle_above h) (qdegle_above r)).
  intro Hab; apply Qcmult_integral in Hab; destruct Hab as [Hz | Hz].
  - apply (qlead_nonzero h Hh); exact Hz.
  - apply (qlead_nonzero r Hr); exact Hz.
Qed.

(* a divisor of a nonzero constant is itself constant *)
Lemma divides_const_deg0 : forall h c, c <> 0 -> qdivides h (qconst c) -> qdegle h 0.
Proof.
  intros h c Hc Hdvd; assert (Hdvd' := Hdvd); destruct Hdvd as [r Hr].
  assert (Hh : qnorm h <> [])
    by (apply (qdivides_nonzero h (qconst c) Hdvd'); rewrite qnorm_const_nz; [ discriminate | exact Hc ]).
  assert (Hr0 : qnorm r <> []).
  { intro Hz; assert (Hzero : forall x, qeval (qconst c) x = 0)
      by (intro x; rewrite Hr, (qeval_qnorm_nil r Hz x); ring).
    apply Hc; rewrite <- (qeval_const c 0); apply Hzero. }
  assert (Hmuldeg : qdegle (qmul h r) 0).
  { intros i Hi.
    assert (Hmc : forall x, qeval (qmul h r) x = qeval (qconst c) x)
      by (intro x; rewrite qeval_mul; symmetry; apply Hr).
    rewrite (qeval_ext_coeff (qmul h r) (qconst c) Hmc i), qcoeff_qconst_hi by lia; reflexivity. }
  assert (Hle : (qdeg h + qdeg r <= 0)%nat).
  { destruct (le_lt_dec (qdeg h + qdeg r) 0) as [Hle | Hgt]; [ exact Hle | ].
    exfalso; apply (qmul_lead_nz h r Hh Hr0); apply Hmuldeg; lia. }
  assert (qdeg h = 0%nat) by lia.
  replace 0%nat with (qdeg h) by lia; apply qdegle_above.
Qed.

(* ----------------------------------------------------------------- *)
(*  Squarefreeness of X^n − 1                                        *)
(* ----------------------------------------------------------------- *)
Definition qsqfree (M : qpoly) : Prop :=
  forall h, qdivides (qmul h h) M -> qdegle h 0.

Theorem qsqfree_Xn1 : forall n, (1 <= n)%nat -> qsqfree (qXn1 n).
Proof.
  intros n Hn h Hdvd.
  destruct Hdvd as [k Hk].
  (* S : the cofactor showing h | (X^n-1)' *)
  set (cof := qadd (qmul (qderiv h) k) (qadd (qmul (qderiv h) k) (qmul h (qderiv k)))).
  assert (HhD : forall x, qeval (qderiv (qXn1 n)) x = qeval h x * qeval cof x).
  { intro x.
    rewrite (qderiv_resp_eval (qXn1 n) (qmul (qmul h h) k)).
    2:{ intro y; rewrite Hk, !qeval_mul; ring. }
    rewrite qderiv_mul_eval, qderiv_mul_eval.
    unfold cof; rewrite !qeval_add, !qeval_mul; ring. }
  (* h | X^n - 1 *)
  assert (HhX : qdivides h (qXn1 n)).
  { apply (qdivides_trans h (qmul h h) (qXn1 n)); [ | exists k; exact Hk ].
    exists h; intro x; rewrite qeval_mul; reflexivity. }
  destruct HhX as [kX HkX].
  (* h | [n] via Bezout *)
  assert (Hconst : qdivides h (qconst (qnat n))).
  { exists (qsub (qmul (qmonom 1) cof) (qscale (qnat n) kX)); intro x.
    rewrite qeval_const, qeval_sub, qeval_mul, qeval_monom, qeval_scale.
    assert (E1 : qeval h x * qeval cof x = qnat n * x ^ (Nat.pred n))
      by (rewrite <- (HhD x), qeval_qderiv_Xn1; reflexivity).
    assert (E2 : qeval h x * qeval kX x = x ^ n - 1)
      by (rewrite <- (HkX x), qeval_Xn1; reflexivity).
    transitivity (x ^ 1 * (qeval h x * qeval cof x) - qnat n * (qeval h x * qeval kX x)); [ | ring ].
    rewrite E1, E2.
    destruct n as [|m]; [ lia | ]; cbn [Nat.pred].
    change (x ^ 1) with (x * 1); change (x ^ S m) with (x * x ^ m); ring. }
  apply (divides_const_deg0 h (qnat n) (qnat_pos_nz n Hn) Hconst).
Qed.

(* ----------------------------------------------------------------- *)
(*  Squarefree product ⟹ its factors are coprime                    *)
(* ----------------------------------------------------------------- *)
Theorem qsqfree_mul_copr : forall A B,
  qsqfree (qmul A B) -> qnorm A <> [] -> qnorm B <> [] -> qcopr A B.
Proof.
  intros A B Hsq HA HB h HhA HhB.
  assert (Hh2 : qdivides (qmul h h) (qmul A B)).
  { destruct HhA as [a Ha]; destruct HhB as [b Hb].
    exists (qmul a b); intro x.
    rewrite qeval_mul, Ha, Hb, !qeval_mul; ring. }
  pose proof (Hsq h Hh2) as Hdeg.
  assert (Hhnz : qnorm h <> []) by (apply (qdivides_nonzero h A HhA); exact HA).
  assert (Hd0 : qdeg h = 0%nat) by (pose proof (qdegle_qdeg h 0 Hdeg); lia).
  exists (qcoeff h 0); split.
  - pose proof (qlead_nonzero h Hhnz) as Hln; unfold qlead in Hln; rewrite Hd0 in Hln; exact Hln.
  - intro x; apply (qeval_const_of_degle0 h Hdeg).
Qed.

Print Assumptions qsqfree_Xn1.

(* ================================================================= *)
(*  END QPolySqfree.v                                                *)
(*  X^n − 1 is squarefree in ℚ[X]; a squarefree product has coprime  *)
(*  factors.  Closed under the global context (axiom-free).          *)
(* ================================================================= *)
