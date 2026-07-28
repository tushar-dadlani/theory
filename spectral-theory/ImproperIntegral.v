(* ================================================================= *)
(*  ImproperIntegral.v  —  the improper integral ∫₀^∞ f as a CReal,    *)
(*  extending the [0,1] Riemann integral of CIntegral.v.             *)
(*                                                                    *)
(*  ∫₀^∞ f = Σ_{m≥0} ∫_m^{m+1} f, a series of unit-cell integrals.    *)
(*  Each cell ∫_m^{m+1} f is `cintegral` of the m-shifted integrand    *)
(*  (Lipschitz with the SAME constant, since translation preserves    *)
(*  the Lipschitz bound), so it is a CReal (CIntegral).  The partial   *)
(*  sums Σ_{m<n} form a Cauchy sequence of CReals whenever the cell    *)
(*  magnitudes are summable — `|∫_m^{m+1} f| ≤ Bd m` with Σ Bd m       *)
(*  convergent (an explicit tail modulus) — and `CRealComplete` gives  *)
(*  the limit `improper_integral : CReal`.                            *)
(*                                                                    *)
(*  The engine is an abstract SUMMABLE SERIES OF CReals (Section       *)
(*  CRealSeries): given cells with `|cell m| ≤ Bd m` and a tail        *)
(*  modulus for Bd, the partial sums converge (`series_limit`).  The   *)
(*  cell magnitudes are controlled by `CIntegral.cintegral_abs_le`     *)
(*  (the integral is ≤ its sup bound on the cell).                    *)
(*                                                                    *)
(*  ∫_ℝ f = ∫₀^∞ f + ∫₀^∞ (x ↦ f(−x)) — two applications; we build     *)
(*  the one-sided ∫₀^∞ here, the essential extension past [0,1].       *)
(*  HONEST SCOPE: the range extension (tails), for a Lipschitz         *)
(*  integrand with a summable cell bound.  2-D / change-of-variables   *)
(*  (the Gaussian ∫e^{−πx²}) is the remaining piece of knot 1.         *)
(*  AXIOM-FREE (Closed under the global context).                     *)
(* ================================================================= *)

From Stdlib Require Import Reals.Cauchy.ConstructiveCauchyReals
  Reals.Cauchy.ConstructiveCauchyRealsMult
  Reals.Cauchy.ConstructiveCauchyAbs
  Reals.Cauchy.ConstructiveRcomplete.
From Stdlib Require Import QArith Qabs Lqa Lia List Arith ZArith.
Require Import PrimonGas CRealCv CIntegral.
Import ListNotations.
Open Scope CReal_scope.

Lemma CReal_abs0_le : forall c : Q, (0 <= c)%Q ->
  (CReal_abs (inject_Q 0%Q) <= inject_Q c)%CReal.
Proof.
  intros c Hc. apply CReal_abs_le; split.
  - rewrite <- opp_inject_Q. apply inject_Q_le. lra.
  - apply inject_Q_le. exact Hc.
Qed.

(* ================================================================= *)
(*  The engine: a summable series of CReals converges.               *)
(* ================================================================= *)
Section CRealSeries.
  Variable cell : nat -> CReal.
  Variable Bd : nat -> Q.
  Hypothesis Hcell : forall m, CReal_abs (cell m) <= inject_Q (Bd m).

  Fixpoint psum (n : nat) : CReal :=
    match n with O => inject_Q 0 | S k => psum k + cell k end.

  (* a block of the series is bounded by the corresponding block of Bd *)
  Lemma psum_diff_bound : forall d i,
    CReal_abs (psum (i + d) + - psum i) <= inject_Q (qsum (map Bd (seq i d))).
  Proof.
    induction d as [| d IH]; intro i.
    - replace (i + 0)%nat with i by lia.
      setoid_replace (psum i + - psum i) with (inject_Q 0%Q) by ring.
      apply CReal_abs0_le. cbn [seq map qsum]. apply Qle_refl.
    - replace (i + S d)%nat with (S (i + d))%nat by lia. cbn [psum].
      setoid_replace (psum (i + d) + cell (i + d) + - psum i)
        with ((psum (i + d) + - psum i) + cell (i + d)) by ring.
      eapply CReal_le_trans; [ apply CReal_abs_triang | ].
      rewrite (seq_S d i), map_app, qsum_app; cbn [map qsum].
      rewrite Qplus_0_r, inject_Q_plus.
      apply CReal_plus_le_compat; [ apply IH | apply Hcell ].
  Qed.

  (* the tail-summability modulus for Bd *)
  Hypothesis Htail : forall p : positive,
    { N : nat | forall i j, (N <= i)%nat -> (i <= j)%nat ->
        (qsum (map Bd (seq i (j - i))) <= 1 # p)%Q }.

  Lemma psum_cauchy : forall p : positive,
    { n : nat | forall i j, (n <= i)%nat -> (n <= j)%nat ->
        CReal_abs (psum i + - psum j) <= inject_Q (1 # p) }.
  Proof.
    intro p. destruct (Htail p) as [N HN]. exists N. intros i j Hi Hj.
    destruct (Nat.le_ge_cases i j) as [Hle | Hge].
    - setoid_replace (psum i + - psum j) with (- (psum j + - psum i)) by ring.
      rewrite CReal_abs_opp.
      eapply CReal_le_trans with (inject_Q (qsum (map Bd (seq i (j - i))))).
      + replace j with (i + (j - i))%nat at 1 by lia. apply psum_diff_bound.
      + apply inject_Q_le. apply HN; [ exact Hi | lia ].
    - eapply CReal_le_trans with (inject_Q (qsum (map Bd (seq j (i - j))))).
      + replace i with (j + (i - j))%nat at 1 by lia. apply psum_diff_bound.
      + apply inject_Q_le. apply HN; [ exact Hj | lia ].
  Qed.

  Definition series_limit : CReal := projT1 (CRealComplete psum psum_cauchy).

  Theorem series_limit_spec : forall p : positive,
    { n : nat | forall i, (n <= i)%nat ->
        CReal_abs (psum i + - series_limit) <= inject_Q (1 # p) }.
  Proof. unfold series_limit; exact (projT2 (CRealComplete psum psum_cauchy)). Qed.

End CRealSeries.

(* ================================================================= *)
(*  The instantiation:  ∫₀^∞ f  for a decaying Lipschitz f.          *)
(* ================================================================= *)
Section Improper.
  Variable f : Q -> Q.
  Variable L : nat.
  Hypothesis Hlip : forall x y,
    (Qabs (f x - f y) <= inject_Z (Z.of_nat L) * Qabs (x - y))%Q.

  (* the m-shifted integrand: f on [m, m+1] pulled back to [0,1] *)
  Definition shift (m : nat) : Q -> Q := fun t => f (inject_Z (Z.of_nat m) + t).

  Lemma shift_lip : forall m x y,
    (Qabs (shift m x - shift m y) <= inject_Z (Z.of_nat L) * Qabs (x - y))%Q.
  Proof.
    intros m x y; unfold shift.
    eapply Qle_trans; [ apply Hlip | ].
    setoid_replace (inject_Z (Z.of_nat m) + x - (inject_Z (Z.of_nat m) + y))%Q
      with (x - y)%Q by ring.
    apply Qle_refl.
  Qed.

  (* the m-th unit-cell integral  ∫_m^{m+1} f  *)
  Definition cell (m : nat) : CReal := cintegral (shift m) L (shift_lip m).

  (* a summable decay bound on the cells *)
  Variable Bd : nat -> Q.
  Hypothesis Hbd : forall m t, (0 <= t)%Q -> (t < 1)%Q -> (Qabs (shift m t) <= Bd m)%Q.

  Lemma cell_bound : forall m, CReal_abs (cell m) <= inject_Q (Bd m).
  Proof. intro m; unfold cell; apply cintegral_abs_le; exact (Hbd m). Qed.

  Hypothesis Htail : forall p : positive,
    { N : nat | forall i j, (N <= i)%nat -> (i <= j)%nat ->
        (qsum (map Bd (seq i (j - i))) <= 1 # p)%Q }.

  (* ∫₀^∞ f, as the CReal limit of the partial sums of the cells *)
  Definition improper_integral : CReal := series_limit cell Bd cell_bound Htail.

  Theorem improper_integral_spec : forall p : positive,
    { n : nat | forall i, (n <= i)%nat ->
        CReal_abs (psum cell i + - improper_integral) <= inject_Q (1 # p) }.
  Proof. unfold improper_integral; apply series_limit_spec. Qed.

End Improper.

Print Assumptions improper_integral_spec.

(* ================================================================= *)
(*  END ImproperIntegral.v                                           *)
(*  ∫₀^∞ f as an axiom-free CReal for a Lipschitz f with a summable    *)
(*  cell bound — the range-extension of CIntegral's [0,1] integral.    *)
(*  ∫_ℝ f = ∫₀^∞ f + ∫₀^∞ (f∘neg).  The remaining piece of knot 1 is   *)
(*  the 2-D / change-of-variables step (the Gaussian ∫e^{−πx²}=√π).    *)
(*  Closed under the global context.                                 *)
(* ================================================================= *)
