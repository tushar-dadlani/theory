(* ================================================================= *)
(*  Ell2.v  —  the infinite-dimensional real Hilbert space  ℓ².       *)
(*                                                                    *)
(*  STAGE 1 — ℓ² as a genuine (infinite-dimensional) real INNER-      *)
(*  PRODUCT (pre-Hilbert) space.                                     *)
(*                                                                    *)
(*  A vector is a real sequence f : ℕ → ℝ whose squares are summable  *)
(*  (Σ f(n)² converges).  This file establishes:                     *)
(*   • ℓ² is a vector space: it contains 0 and is closed under        *)
(*     scalar multiplication and addition (Summable_scal/_plus);      *)
(*   • the inner product ⟨f,g⟩ = Σ f(n) g(n) is WELL-DEFINED — the    *)
(*     series converges (absolutely), by comparison |fg| ≤ f²+g²      *)
(*     and absolute-⇒-convergent (Ell2_ip_summable, ip);             *)
(*   • ⟨·,·⟩ is symmetric (ip_sym) and ⟨f,f⟩ ≥ 0 (ip_diag_nonneg).    *)
(*                                                                    *)
(*  The completeness axis is genuinely available: ℝ is complete       *)
(*  (Stdlib R_complete), which is what a Riesz–Fischer proof of ℓ²-   *)
(*  completeness (the Hilbert-space capstone) will run on.  That, and *)
(*  Cauchy–Schwarz / Minkowski / full bilinearity / positive-         *)
(*  definiteness, are the STAGE-2 follow-up.                          *)
(*                                                                    *)
(*  Axiom footprint: the standard classical Reals axioms only (the    *)
(*  quarantined Dedekind-reals + functional extensionality that any   *)
(*  development over ℝ uses) — same discipline as the rest of the     *)
(*  spectral-theory tree.                                            *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  Summable series and the space ℓ².                                *)
(* ----------------------------------------------------------------- *)

(* the series Σ u converges (informatively — carries the limit) *)
Definition Summable (u : nat -> R) : Type :=
  { l : R | Un_cv (fun N => sum_f_R0 u N) l }.

(* ℓ² : the square-summable real sequences *)
Definition Ell2 (f : nat -> R) : Type := Summable (fun n => (f n) ^ 2).

(* ----------------------------------------------------------------- *)
(*  Elementary series / convergence toolkit.                         *)
(* ----------------------------------------------------------------- *)

Lemma sum_f_R0_plus : forall A B N,
  sum_f_R0 (fun i => A i + B i) N = (sum_f_R0 A N + sum_f_R0 B N)%R.
Proof. intros A B N; induction N; simpl; [ ring | rewrite IHN; ring ]. Qed.

Lemma sum_f_R0_scal : forall u c N,
  sum_f_R0 (fun i => c * u i) N = (c * sum_f_R0 u N)%R.
Proof. intros u c N; induction N; simpl; [ ring | rewrite IHN; ring ]. Qed.

(* transport of convergence along a pointwise-equal sequence *)
Lemma Un_cv_eq : forall U V l,
  (forall n, U n = V n) -> Un_cv U l -> Un_cv V l.
Proof.
  intros U V l Heq H eps He; destruct (H eps He) as [N HN]; exists N.
  intros n Hn; rewrite <- Heq; apply HN; exact Hn.
Qed.

Lemma Un_cv_const : forall c, Un_cv (fun _ => c) c.
Proof.
  intros c eps He; exists O; intros n _.
  unfold R_dist; rewrite Rminus_diag_eq by reflexivity.
  rewrite Rabs_R0; exact He.
Qed.

Lemma Un_cv_scal : forall U l c, Un_cv U l -> Un_cv (fun n => c * U n) (c * l).
Proof.
  intros U l c H; apply (CV_mult (fun _ => c) U c l); [ apply Un_cv_const | exact H ].
Qed.

(* limit of a nonnegative sequence is nonnegative *)
Lemma Un_cv_nonneg : forall U l, (forall n, 0 <= U n) -> Un_cv U l -> 0 <= l.
Proof.
  intros U l Hpos Hcv; destruct (Rle_or_lt 0 l) as [Hle | Hlt]; [ exact Hle | exfalso ].
  destruct (Hcv (- l) ltac:(lra)) as [N HN].
  specialize (HN N (Nat.le_refl N)); specialize (Hpos N).
  unfold R_dist in HN; apply Rabs_def2 in HN; lra.
Qed.

(* ----------------------------------------------------------------- *)
(*  ℓ² is a vector space.                                            *)
(* ----------------------------------------------------------------- *)

Lemma Summable_scal : forall u c, Summable u -> Summable (fun i => c * u i).
Proof.
  intros u c [l Hl]; exists (c * l).
  apply (Un_cv_eq (fun N => c * sum_f_R0 u N)).
  - intro N; symmetry; apply sum_f_R0_scal.
  - apply Un_cv_scal; exact Hl.
Qed.

Lemma Summable_plus : forall u v,
  Summable u -> Summable v -> Summable (fun i => u i + v i).
Proof.
  intros u v [lu Hu] [lv Hv]; exists (lu + lv).
  apply (Un_cv_eq (fun N => sum_f_R0 u N + sum_f_R0 v N)).
  - intro N; symmetry; apply sum_f_R0_plus.
  - apply CV_plus; assumption.
Qed.

(* scalar multiples stay in ℓ² *)
Lemma Ell2_scal : forall f c, Ell2 f -> Ell2 (fun n => c * f n).
Proof.
  intros f c Hf; unfold Ell2.
  apply (fun H => Summable_scal (fun n => (f n) ^ 2) (c ^ 2) H) in Hf.
  destruct Hf as [l Hl]; exists l.
  apply (Un_cv_eq (fun N => sum_f_R0 (fun n => c ^ 2 * (f n) ^ 2) N)); [ | exact Hl ].
  intro N; apply sum_eq; intros i _; ring.
Qed.

(* sums stay in ℓ²: (f+g)² ≤ 2 f² + 2 g² *)
Lemma Ell2_plus : forall f g, Ell2 f -> Ell2 g -> Ell2 (fun n => f n + g n).
Proof.
  intros f g Hf Hg; unfold Ell2.
  (* Bn = 2 f² + 2 g² is summable *)
  assert (HB : Summable (fun n => 2 * (f n) ^ 2 + 2 * (g n) ^ 2)).
  { apply Summable_plus; apply Summable_scal; assumption. }
  apply (Rseries_CV_comp (fun n => (f n + g n) ^ 2)
                         (fun n => 2 * (f n) ^ 2 + 2 * (g n) ^ 2)).
  - intro n; split.
    + apply pow2_ge_0.
    + pose proof (pow2_ge_0 (f n - g n)); nra.
  - exact HB.
Qed.

Lemma Ell2_zero : Ell2 (fun _ => 0).
Proof.
  unfold Ell2; exists 0.
  apply (Un_cv_eq (fun _ => 0)); [ | apply Un_cv_const ].
  intro N; symmetry.
  transitivity (sum_f_R0 (fun _ : nat => 0) N).
  - apply sum_eq; intros; ring.
  - rewrite sum_cte; ring.
Qed.

(* ----------------------------------------------------------------- *)
(*  The inner product ⟨f,g⟩ = Σ f(n) g(n) is well-defined.           *)
(* ----------------------------------------------------------------- *)

(* the pointwise bound driving absolute convergence *)
Lemma ip_bound : forall x y, Rabs (x * y) <= x ^ 2 + y ^ 2.
Proof.
  intros x y.
  assert (Hx : Rabs x * Rabs x = x ^ 2) by (rewrite <- Rabs_mult, Rabs_pos_eq by nra; ring).
  assert (Hy : Rabs y * Rabs y = y ^ 2) by (rewrite <- Rabs_mult, Rabs_pos_eq by nra; ring).
  rewrite Rabs_mult, <- Hx, <- Hy.
  pose proof (Rabs_pos x); pose proof (Rabs_pos y); pose proof (pow2_ge_0 (Rabs x - Rabs y)).
  nra.
Qed.

(* the inner-product series converges (absolutely) *)
Lemma Ell2_ip_summable : forall f g,
  Ell2 f -> Ell2 g -> Summable (fun n => f n * g n).
Proof.
  intros f g Hf Hg.
  assert (HB : Summable (fun n => (f n) ^ 2 + (g n) ^ 2))
    by (apply Summable_plus; assumption).
  assert (Habs : Summable (fun n => Rabs (f n * g n))).
  { apply (Rseries_CV_comp (fun n => Rabs (f n * g n))
                           (fun n => (f n) ^ 2 + (g n) ^ 2)).
    - intro n; split; [ apply Rabs_pos | apply ip_bound ].
    - exact HB. }
  apply cv_cauchy_2, (cauchy_abs (fun n => f n * g n)), cv_cauchy_1; exact Habs.
Qed.

(* the inner product as a real number *)
Definition ip (f g : nat -> R) (Hf : Ell2 f) (Hg : Ell2 g) : R :=
  proj1_sig (Ell2_ip_summable f g Hf Hg).

(* symmetry: ⟨f,g⟩ = ⟨g,f⟩ *)
Lemma ip_sym : forall f g (Hf : Ell2 f) (Hg : Ell2 g),
  ip f g Hf Hg = ip g f Hg Hf.
Proof.
  intros f g Hf Hg; unfold ip.
  destruct (Ell2_ip_summable f g Hf Hg) as [a Ha].
  destruct (Ell2_ip_summable g f Hg Hf) as [b Hb]; simpl.
  assert (Hb' : Un_cv (fun N => sum_f_R0 (fun n => f n * g n) N) b).
  { apply (Un_cv_eq (fun N => sum_f_R0 (fun n => g n * f n) N)); [ | exact Hb ].
    intro N; apply sum_eq; intros i _; ring. }
  exact (UL_sequence _ a b Ha Hb').
Qed.

(* positive semidefinite on the diagonal: ⟨f,f⟩ ≥ 0 *)
Lemma ip_diag_nonneg : forall f (Hf : Ell2 f), 0 <= ip f f Hf Hf.
Proof.
  intros f Hf; unfold ip.
  destruct (Ell2_ip_summable f f Hf Hf) as [a Ha]; simpl.
  apply (Un_cv_nonneg (fun N => sum_f_R0 (fun n => f n * f n) N) a); [ | exact Ha ].
  intro N; apply cond_pos_sum; intro n; nra.
Qed.

Print Assumptions Ell2_ip_summable.
Print Assumptions ip_sym.

(* ================================================================= *)
(*  END Ell2.v (STAGE 1)                                             *)
(*  ℓ² is a genuine infinite-dimensional real inner-product space:   *)
(*  a vector space (0, scalar, +) with a well-defined symmetric,     *)
(*  positive-semidefinite inner product Σ f g.  Completeness         *)
(*  (Riesz–Fischer, on Stdlib's R_complete) + Cauchy–Schwarz +       *)
(*  Minkowski + positive-definiteness are STAGE 2.                   *)
(* ================================================================= *)
