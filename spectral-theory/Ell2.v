(* ================================================================= *)
(*  Ell2.v  —  the infinite-dimensional real Hilbert space  ℓ².       *)
(*                                                                    *)
(*  STAGES 1–3 — ℓ² as a genuine (infinite-dimensional) real          *)
(*  HILBERT space (complete normed inner-product space).             *)
(*                                                                    *)
(*  A vector is a real sequence f : ℕ → ℝ whose squares are summable  *)
(*  (Σ f(n)² converges).  This file establishes:                     *)
(*   STAGE 1 (vector space + well-defined inner product):            *)
(*   • ℓ² is a vector space: 0, scalar mult, addition                 *)
(*     (Ell2_zero/_scal/_plus, closure via (f+g)² ≤ 2f²+2g²);         *)
(*   • the inner product ⟨f,g⟩ = Σ f(n) g(n) is WELL-DEFINED — the    *)
(*     series converges absolutely (Ell2_ip_summable, ip), via        *)
(*     |fg| ≤ f²+g² and absolute-⇒-convergent (Stdlib cauchy_abs);    *)
(*   • ⟨·,·⟩ symmetric (ip_sym), ⟨f,f⟩ ≥ 0 (ip_diag_nonneg).          *)
(*   STAGE 2 (the full inner-product-space + normed structure):      *)
(*   • bilinearity: ip_add_r, ip_scal_r (right; left via ip_sym);     *)
(*   • positive-DEFINITENESS: ⟨f,f⟩ = 0 ⇒ f ≡ 0 (ip_diag_zero);       *)
(*   • CAUCHY–SCHWARZ: ⟨f,g⟩² ≤ ⟨f,f⟩⟨g,g⟩ (ip_CS), via finite CS on  *)
(*     partial sums (a nonnegative quadratic) + limit passage;        *)
(*   • the NORM ‖f‖ = √⟨f,f⟩ and MINKOWSKI ‖f+g‖ ≤ ‖f‖+‖g‖            *)
(*     (norm, norm_triangle).                                        *)
(*                                                                    *)
(*   STAGE 3 (the Hilbert capstone): COMPLETENESS (Riesz–Fischer,     *)
(*   Ell2_complete) — every ℓ²-Cauchy sequence converges in ℓ² to a   *)
(*   limit that is itself in ℓ².  ℝ-completeness (Stdlib R_complete)   *)
(*   yields the coordinatewise limits; a bounded-monotone argument    *)
(*   (growing_cv) with a finite-sum/limit interchange puts the        *)
(*   candidate limit in ℓ² and gives norm convergence.               *)
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

(* ================================================================= *)
(*  STAGE 2 — the genuine inner-product-space axioms, Cauchy–Schwarz, *)
(*  the norm and its triangle inequality (Minkowski).                *)
(* ================================================================= *)

(* the defining property of ip: the partial sums converge to it *)
Lemma ip_spec : forall f g (Hf : Ell2 f) (Hg : Ell2 g),
  Un_cv (fun N => sum_f_R0 (fun n => f n * g n) N) (ip f g Hf Hg).
Proof. intros f g Hf Hg; unfold ip; exact (proj2_sig (Ell2_ip_summable f g Hf Hg)). Qed.

(* the value of ip does not depend on the summability proofs *)
Lemma ip_pi : forall f g (Hf Hf' : Ell2 f) (Hg Hg' : Ell2 g),
  ip f g Hf Hg = ip f g Hf' Hg'.
Proof. intros; exact (UL_sequence _ _ _ (ip_spec f g Hf Hg) (ip_spec f g Hf' Hg')). Qed.

(* right-additivity: <f, g+h> = <f,g> + <f,h> *)
Lemma ip_add_r :
  forall f g h (Hf : Ell2 f) (Hg : Ell2 g) (Hh : Ell2 h)
         (Hgh : Ell2 (fun n => g n + h n)),
  ip f (fun n => g n + h n) Hf Hgh = (ip f g Hf Hg + ip f h Hf Hh)%R.
Proof.
  intros f g h Hf Hg Hh Hgh.
  apply (UL_sequence (fun N => sum_f_R0 (fun n => f n * (g n + h n)) N)).
  - apply ip_spec.
  - apply (Un_cv_eq (fun N => sum_f_R0 (fun n => f n * g n) N
                            + sum_f_R0 (fun n => f n * h n) N)).
    + intro N; rewrite <- sum_f_R0_plus; apply sum_eq; intros; ring.
    + apply CV_plus; apply ip_spec.
Qed.

(* right-homogeneity: <f, c*g> = c*<f,g> *)
Lemma ip_scal_r :
  forall f g c (Hf : Ell2 f) (Hg : Ell2 g) (Hcg : Ell2 (fun n => c * g n)),
  ip f (fun n => c * g n) Hf Hcg = (c * ip f g Hf Hg)%R.
Proof.
  intros f g c Hf Hg Hcg.
  apply (UL_sequence (fun N => sum_f_R0 (fun n => f n * (c * g n)) N)).
  - apply ip_spec.
  - apply (Un_cv_eq (fun N => c * sum_f_R0 (fun n => f n * g n) N)).
    + intro N; rewrite <- sum_f_R0_scal; apply sum_eq; intros; ring.
    + apply Un_cv_scal; apply ip_spec.
Qed.

(* a nonnegative term is <= the partial sum that contains it *)
Lemma term_le_sum : forall u n, (forall k, 0 <= u k) -> u n <= sum_f_R0 u n.
Proof.
  intros u n Hp; destruct n; simpl.
  - lra.
  - pose proof (cond_pos_sum u n Hp); lra.
Qed.

(* positive-DEFINITENESS: <f,f> = 0 forces f = 0 identically *)
Lemma ip_diag_zero : forall f (Hf : Ell2 f),
  ip f f Hf Hf = 0 -> forall n, f n = 0.
Proof.
  intros f Hf H0 n.
  assert (Hp : forall k, 0 <= f k * f k) by (intro k; nra).
  assert (Hle : sum_f_R0 (fun k => f k * f k) n <= 0).
  { rewrite <- H0; apply (sum_incr (fun k => f k * f k) n (ip f f Hf Hf));
      [ apply ip_spec | exact Hp ]. }
  pose proof (term_le_sum (fun k => f k * f k) n Hp).
  assert (Hz : f n * f n = 0) by nra.
  destruct (Rmult_integral _ _ Hz); assumption.
Qed.

(* ----------------------------------------------------------------- *)
(*  CAUCHY–SCHWARZ.                                                   *)
(* ----------------------------------------------------------------- *)

(* Σ (f t − g)²  expanded over a partial sum *)
Lemma sum_quad : forall f g t N,
  sum_f_R0 (fun k => (f k * t - g k) * (f k * t - g k)) N
  = (sum_f_R0 (fun k => f k * f k) N * (t * t)
     - 2 * t * sum_f_R0 (fun k => f k * g k) N
     + sum_f_R0 (fun k => g k * g k) N)%R.
Proof. intros f g t N; induction N; simpl; [ ring | rewrite IHN; ring ]. Qed.

(* any nonnegative term is <= the partial sum containing it *)
Lemma term_le_sum_any : forall u N k,
  (forall j, 0 <= u j) -> (k <= N)%nat -> u k <= sum_f_R0 u N.
Proof.
  intros u N; induction N; intros k Hp Hk; simpl.
  - assert (k = 0)%nat by lia; subst; lra.
  - destruct (Nat.eq_dec k (S N)) as [-> | Hne].
    + pose proof (cond_pos_sum u N Hp); lra.
    + assert (k <= N)%nat by lia; pose proof (IHN k Hp H); pose proof (Hp (S N)); lra.
Qed.

(* finite Cauchy–Schwarz on partial sums *)
Lemma finite_CS : forall f g N,
  (sum_f_R0 (fun k => f k * g k) N * sum_f_R0 (fun k => f k * g k) N
   <= sum_f_R0 (fun k => f k * f k) N * sum_f_R0 (fun k => g k * g k) N)%R.
Proof.
  intros f g N.
  set (A := sum_f_R0 (fun k => f k * f k) N).
  set (B := sum_f_R0 (fun k => f k * g k) N).
  set (C := sum_f_R0 (fun k => g k * g k) N).
  assert (HA : 0 <= A) by (apply cond_pos_sum; intro; nra).
  assert (Hquad : forall t, 0 <= A * (t * t) - 2 * t * B + C).
  { intro t.
    replace (A * (t * t) - 2 * t * B + C)
      with (sum_f_R0 (fun k => (f k * t - g k) * (f k * t - g k)) N)
      by (rewrite sum_quad; unfold A, B, C; ring).
    apply cond_pos_sum; intro k.
    pose proof (Rle_0_sqr (f k * t - g k)); unfold Rsqr in *; lra. }
  destruct (Rle_lt_or_eq_dec 0 A HA) as [HApos | HA0].
  - assert (Hne : A <> 0) by lra.
    pose proof (Hquad (B / A)) as H.
    replace (A * (B / A * (B / A)) - 2 * (B / A) * B + C)
      with ((A * C - B * B) * / A) in H by (field; exact Hne).
    pose proof (Rinv_0_lt_compat A HApos); nra.
  - (* A = 0: every f k (k<=N) vanishes, so B = 0 *)
    assert (HB0 : B = 0).
    { unfold B; transitivity (sum_f_R0 (fun _ : nat => 0) N).
      - apply sum_eq; intros k Hk.
        assert (Hk2 : f k * f k <= A)
          by (unfold A; apply (term_le_sum_any (fun j => f j * f j) N k);
              [ intro; nra | exact Hk ]).
        assert (f k * f k = 0) by nra.
        destruct (Rmult_integral _ _ H); rewrite H0; ring.
      - rewrite sum_cte; ring. }
    rewrite HB0, <- HA0; nra.
Qed.

(* limit comparison: pointwise <= is preserved in the limit *)
Lemma Un_cv_le : forall U V u v,
  (forall n, U n <= V n) -> Un_cv U u -> Un_cv V v -> u <= v.
Proof.
  intros U V u v Hle HU HV.
  destruct (Rle_or_lt u v) as [Hok | Hlt]; [ exact Hok | exfalso ].
  destruct (HU ((u - v) / 2) ltac:(lra)) as [N1 H1].
  destruct (HV ((u - v) / 2) ltac:(lra)) as [N2 H2].
  specialize (H1 (max N1 N2) (Nat.le_max_l _ _)).
  specialize (H2 (max N1 N2) (Nat.le_max_r _ _)).
  specialize (Hle (max N1 N2)); unfold R_dist in *.
  apply Rabs_def2 in H1; apply Rabs_def2 in H2; lra.
Qed.

(* CAUCHY–SCHWARZ for the inner product: ⟨f,g⟩² ≤ ⟨f,f⟩·⟨g,g⟩ *)
Lemma ip_CS : forall f g (Hf : Ell2 f) (Hg : Ell2 g),
  ((ip f g Hf Hg) ^ 2 <= ip f f Hf Hf * ip g g Hg Hg)%R.
Proof.
  intros f g Hf Hg.
  replace ((ip f g Hf Hg) ^ 2) with (ip f g Hf Hg * ip f g Hf Hg) by ring.
  apply (Un_cv_le
           (fun N => sum_f_R0 (fun k => f k * g k) N * sum_f_R0 (fun k => f k * g k) N)
           (fun N => sum_f_R0 (fun k => f k * f k) N * sum_f_R0 (fun k => g k * g k) N)).
  - intro N; apply finite_CS.
  - apply CV_mult; apply ip_spec.
  - apply CV_mult; apply ip_spec.
Qed.

(* ----------------------------------------------------------------- *)
(*  THE NORM and the triangle inequality (Minkowski).                *)
(* ----------------------------------------------------------------- *)

Definition norm (f : nat -> R) (Hf : Ell2 f) : R := sqrt (ip f f Hf Hf).

Lemma norm_nonneg : forall f (Hf : Ell2 f), 0 <= norm f Hf.
Proof. intros; apply sqrt_pos. Qed.

(* parallelogram expansion: <f+g,f+g> = <f,f> + 2<f,g> + <g,g> *)
Lemma ip_plus_self :
  forall f g (Hf : Ell2 f) (Hg : Ell2 g) (Hfg : Ell2 (fun n => f n + g n)),
  ip (fun n => f n + g n) (fun n => f n + g n) Hfg Hfg
  = (ip f f Hf Hf + 2 * ip f g Hf Hg + ip g g Hg Hg)%R.
Proof.
  intros f g Hf Hg Hfg.
  rewrite (ip_add_r (fun n => f n + g n) f g Hfg Hf Hg Hfg).
  rewrite (ip_sym (fun n => f n + g n) f Hfg Hf).
  rewrite (ip_sym (fun n => f n + g n) g Hfg Hg).
  rewrite (ip_add_r f f g Hf Hf Hg Hfg).
  rewrite (ip_add_r g f g Hg Hf Hg Hfg).
  rewrite (ip_sym g f Hg Hf).
  ring.
Qed.

(* Cauchy–Schwarz, square-root form: <f,g> ≤ √(<f,f>·<g,g>) *)
Lemma ip_CS_sqrt : forall f g (Hf : Ell2 f) (Hg : Ell2 g),
  ip f g Hf Hg <= sqrt (ip f f Hf Hf * ip g g Hg Hg).
Proof.
  intros f g Hf Hg.
  apply Rle_trans with (sqrt ((ip f g Hf Hg) ^ 2)).
  - rewrite <- Rsqr_pow2, sqrt_Rsqr_abs; apply Rle_abs.
  - apply sqrt_le_1_alt, ip_CS.
Qed.

(* MINKOWSKI: ‖f+g‖ ≤ ‖f‖ + ‖g‖ *)
Lemma norm_triangle :
  forall f g (Hf : Ell2 f) (Hg : Ell2 g) (Hfg : Ell2 (fun n => f n + g n)),
  norm (fun n => f n + g n) Hfg <= norm f Hf + norm g Hg.
Proof.
  intros f g Hf Hg Hfg.
  apply Rsqr_incr_0.
  - unfold norm.
    rewrite Rsqr_sqrt by apply ip_diag_nonneg.
    rewrite (ip_plus_self f g Hf Hg Hfg), Rsqr_plus.
    rewrite (Rsqr_sqrt (ip f f Hf Hf)) by apply ip_diag_nonneg.
    rewrite (Rsqr_sqrt (ip g g Hg Hg)) by apply ip_diag_nonneg.
    pose proof (sqrt_mult (ip f f Hf Hf) (ip g g Hg Hg)
                 (ip_diag_nonneg f Hf) (ip_diag_nonneg g Hg)) as Hm.
    pose proof (ip_CS_sqrt f g Hf Hg); lra.
  - apply norm_nonneg.
  - apply Rplus_le_le_0_compat; apply norm_nonneg.
Qed.

(* ================================================================= *)
(*  STAGE 3 — COMPLETENESS (Riesz–Fischer): ℓ² is a HILBERT space.   *)
(*                                                                    *)
(*  Every ℓ²-Cauchy sequence of vectors converges (in ℓ² norm) to a   *)
(*  limit vector that is itself in ℓ².  Engine: ℝ is complete         *)
(*  (Stdlib R_complete) gives the coordinatewise limits; a bounded-   *)
(*  monotone argument (growing_cv) puts the candidate limit in ℓ².    *)
(* ================================================================= *)

(* one-step unfolding of a partial sum (definitional) *)
Lemma sum_f_R0_S : forall u N, sum_f_R0 u (S N) = (sum_f_R0 u N + u (S N))%R.
Proof. reflexivity. Qed.

(* congruence for ℓ²-membership along pointwise equality *)
Lemma Ell2_ext : forall f g, (forall n, f n = g n) -> Ell2 f -> Ell2 g.
Proof.
  intros f g Heq [l Hl]; exists l.
  apply (Un_cv_eq (fun N => sum_f_R0 (fun n => (f n) ^ 2) N)); [ | exact Hl ].
  intro N; apply sum_eq; intros i _; rewrite Heq; reflexivity.
Qed.

(* ℓ² is closed under differences *)
Lemma Ell2_minus : forall f g, Ell2 f -> Ell2 g -> Ell2 (fun n => f n - g n).
Proof.
  intros f g Hf Hg.
  apply (Ell2_ext (fun n => f n + (-1) * g n)); [ intro n; ring | ].
  apply Ell2_plus; [ exact Hf | apply Ell2_scal; exact Hg ].
Qed.

(* a nonnegative series with bounded partial sums is summable *)
Lemma Summable_of_bounded : forall u B,
  (forall n, 0 <= u n) -> (forall N, sum_f_R0 u N <= B) -> Summable u.
Proof.
  intros u B Hpos Hbd; apply growing_cv.
  - intro N; rewrite sum_f_R0_S; pose proof (Hpos (S N)); lra.
  - unfold has_ub, EUn, bound, is_upper_bound.
    exists B; intros r [i ->]; apply Hbd.
Qed.

(* one coordinate is dominated by the whole squared norm *)
Lemma coord_le_ipdiag : forall f (Hf : Ell2 f) n, (f n) ^ 2 <= ip f f Hf Hf.
Proof.
  intros f Hf n; apply Rle_trans with (sum_f_R0 (fun k => f k * f k) n).
  - replace ((f n) ^ 2) with (f n * f n) by ring.
    apply (term_le_sum_any (fun k => f k * f k) n n); [ intro; nra | lia ].
  - apply (sum_incr (fun k => f k * f k) n (ip f f Hf Hf)); [ apply ip_spec | intro; nra ].
Qed.

(* every partial sum of squares is <= the squared norm *)
Lemma partial_le_ip : forall f (Hf : Ell2 f) N,
  sum_f_R0 (fun n => (f n) ^ 2) N <= ip f f Hf Hf.
Proof.
  intros f Hf N.
  rewrite (sum_eq (fun n => (f n) ^ 2) (fun n => f n * f n) N) by (intros; ring).
  apply (sum_incr (fun n => f n * f n) N (ip f f Hf Hf)); [ apply ip_spec | intro; nra ].
Qed.

(* the square of a convergent sequence converges to the square *)
Lemma Un_cv_sq : forall u l, Un_cv u l -> Un_cv (fun k => (u k) ^ 2) (l ^ 2).
Proof.
  intros u l H; apply (Un_cv_eq (fun k => u k * u k)); [ intro k; ring | ].
  replace (l ^ 2) with (l * l) by ring; apply CV_mult; exact H.
Qed.

(* a FINITE sum of squares commutes with the coordinatewise limit *)
Lemma finite_sum_sq_limit :
  forall (d : nat -> nat -> R) (e : nat -> R) N,
  (forall n, Un_cv (fun k => d k n) (e n)) ->
  Un_cv (fun k => sum_f_R0 (fun n => (d k n) ^ 2) N)
        (sum_f_R0 (fun n => (e n) ^ 2) N).
Proof.
  intros d e N Hpt; induction N; cbn [sum_f_R0].
  - apply Un_cv_sq, Hpt.
  - apply CV_plus; [ exact IHN | apply Un_cv_sq, Hpt ].
Qed.

(* a sequence eventually <= B has limit <= B *)
Lemma Un_cv_le_const : forall U l B,
  (exists K, forall k, (K <= k)%nat -> U k <= B) -> Un_cv U l -> l <= B.
Proof.
  intros U l B [K HK] Hcv; destruct (Rle_or_lt l B) as [Hok | Hlt]; [ exact Hok | exfalso ].
  destruct (Hcv (l - B) ltac:(lra)) as [N HN].
  specialize (HN (max N K) (Nat.le_max_l _ _)); specialize (HK (max N K) (Nat.le_max_r _ _)).
  unfold R_dist in HN; apply Rabs_def2 in HN; lra.
Qed.

(* |a| < e  from  a² < e²  (e > 0) *)
Lemma abs_lt_of_sq : forall a e, 0 < e -> a ^ 2 < e * e -> Rabs a < e.
Proof.
  intros a e He H.
  assert (Ha : a ^ 2 = Rabs a * Rabs a) by (rewrite <- Rabs_mult, Rabs_pos_eq by nra; ring).
  destruct (Rlt_le_dec (Rabs a) e) as [Hlt | Hge]; [ exact Hlt | exfalso ].
  pose proof (Rabs_pos a); nra.
Qed.

(* every partial sum of (x_j − f)² is <= B, when the tail is B-bounded *)
Lemma tail_partial_bound :
  forall (x : nat -> nat -> R) (Hx : forall k, Ell2 (x k)) (f : nat -> R),
    (forall n, Un_cv (fun k => x k n) (f n)) ->
    forall j K B, (K <= j)%nat ->
    (forall k, (K <= k)%nat ->
       ip (fun n => x j n - x k n) (fun n => x j n - x k n)
          (Ell2_minus (x j) (x k) (Hx j) (Hx k))
          (Ell2_minus (x j) (x k) (Hx j) (Hx k)) <= B) ->
    forall N, sum_f_R0 (fun n => (x j n - f n) ^ 2) N <= B.
Proof.
  intros x Hx f Hpt j K B Hj Hbd N.
  apply (Un_cv_le_const (fun k => sum_f_R0 (fun n => (x j n - x k n) ^ 2) N)
                        (sum_f_R0 (fun n => (x j n - f n) ^ 2) N) B).
  - exists K; intros k Hk. eapply Rle_trans.
    + apply (partial_le_ip (fun n => x j n - x k n)
                           (Ell2_minus (x j) (x k) (Hx j) (Hx k)) N).
    + apply Hbd; exact Hk.
  - apply (finite_sum_sq_limit (fun k n => x j n - x k n) (fun n => x j n - f n) N).
    intro n; apply (CV_minus (fun _ => x j n) (fun k => x k n) (x j n) (f n));
      [ apply Un_cv_const | apply Hpt ].
Qed.

(* the tail x_j − f is in ℓ² *)
Lemma Ell2_tail :
  forall (x : nat -> nat -> R) (Hx : forall k, Ell2 (x k)) (f : nat -> R),
    (forall n, Un_cv (fun k => x k n) (f n)) ->
    forall j K B, (K <= j)%nat ->
    (forall k, (K <= k)%nat ->
       ip (fun n => x j n - x k n) (fun n => x j n - x k n)
          (Ell2_minus (x j) (x k) (Hx j) (Hx k))
          (Ell2_minus (x j) (x k) (Hx j) (Hx k)) <= B) ->
    Ell2 (fun n => x j n - f n).
Proof.
  intros x Hx f Hpt j K B Hj Hbd.
  apply (Summable_of_bounded (fun n => (x j n - f n) ^ 2) B).
  - intro n; apply pow2_ge_0.
  - apply (tail_partial_bound x Hx f Hpt j K B Hj Hbd).
Qed.

(* and its squared norm is <= B *)
Lemma Ell2_tail_sqn :
  forall (x : nat -> nat -> R) (Hx : forall k, Ell2 (x k)) (f : nat -> R),
    (forall n, Un_cv (fun k => x k n) (f n)) ->
    forall j K B, (K <= j)%nat ->
    (forall k, (K <= k)%nat ->
       ip (fun n => x j n - x k n) (fun n => x j n - x k n)
          (Ell2_minus (x j) (x k) (Hx j) (Hx k))
          (Ell2_minus (x j) (x k) (Hx j) (Hx k)) <= B) ->
    forall (Hjf : Ell2 (fun n => x j n - f n)),
      ip (fun n => x j n - f n) (fun n => x j n - f n) Hjf Hjf <= B.
Proof.
  intros x Hx f Hpt j K B Hj Hbd Hjf.
  apply (Un_cv_le_const (fun N => sum_f_R0 (fun n => (x j n - f n) * (x j n - f n)) N)
                        (ip (fun n => x j n - f n) (fun n => x j n - f n) Hjf Hjf) B).
  - exists 0%nat; intros N _.
    rewrite (sum_eq (fun n => (x j n - f n) * (x j n - f n))
                    (fun n => (x j n - f n) ^ 2) N) by (intros; ring).
    apply (tail_partial_bound x Hx f Hpt j K B Hj Hbd).
  - apply ip_spec.
Qed.

(* RIESZ–FISCHER: ℓ² is complete.                                     *)
(*  Cauchy and convergence are stated in squared-norm form            *)
(*  (⟨u,u⟩ = ‖u‖²), which is equivalent to the norm form.             *)
Theorem Ell2_complete :
  forall (x : nat -> nat -> R) (Hx : forall k, Ell2 (x k)),
    (forall eps, eps > 0 -> exists K, forall j k, (K <= j)%nat -> (K <= k)%nat ->
       ip (fun n => x j n - x k n) (fun n => x j n - x k n)
          (Ell2_minus (x j) (x k) (Hx j) (Hx k))
          (Ell2_minus (x j) (x k) (Hx j) (Hx k)) < eps) ->
    exists (f : nat -> R) (Hf : Ell2 f),
      forall eps, eps > 0 -> exists K, forall k, (K <= k)%nat ->
        ip (fun n => x k n - f n) (fun n => x k n - f n)
           (Ell2_minus (x k) f (Hx k) Hf) (Ell2_minus (x k) f (Hx k) Hf) < eps.
Proof.
  intros x Hx Hcauchy.
  (* Step A — coordinatewise Cauchy, hence a coordinatewise limit f *)
  assert (Hcc : forall n, Cauchy_crit (fun k => x k n)).
  { intros n eps Heps.
    destruct (Hcauchy (eps * eps) ltac:(nra)) as [K HK].
    exists K; intros p q Hp Hq; unfold R_dist.
    apply abs_lt_of_sq; [ exact Heps | ].
    eapply Rle_lt_trans.
    - apply (coord_le_ipdiag (fun m => x p m - x q m)
                             (Ell2_minus (x p) (x q) (Hx p) (Hx q)) n).
    - apply (HK p q Hp Hq). }
  set (f := fun n => proj1_sig (R_complete (fun k => x k n) (Hcc n))).
  assert (Hpt : forall n, Un_cv (fun k => x k n) (f n))
    by (intro n; exact (proj2_sig (R_complete (fun k => x k n) (Hcc n)))).
  (* Step B — f ∈ ℓ² (subtract the tail x_{K0} − f from x_{K0}) *)
  destruct (Hcauchy 1 Rlt_0_1) as [K0 HK0].
  assert (HxK0f : Ell2 (fun n => x K0 n - f n)).
  { apply (Ell2_tail x Hx f Hpt K0 K0 1); [ lia | ].
    intros k Hk; left; apply HK0; [ lia | exact Hk ]. }
  assert (Hf : Ell2 f).
  { apply (Ell2_ext (fun n => x K0 n - (x K0 n - f n))); [ intro n; ring | ].
    apply Ell2_minus; [ apply Hx | exact HxK0f ]. }
  exists f, Hf.
  (* Step C — norm convergence *)
  intros eps Heps.
  destruct (Hcauchy (eps / 2) ltac:(lra)) as [K HK].
  exists K; intros k Hk.
  pose proof (Ell2_tail_sqn x Hx f Hpt k K (eps / 2) Hk
                (fun k' Hk' => Rlt_le _ _ (HK k k' Hk Hk'))
                (Ell2_minus (x k) f (Hx k) Hf)) as Hb.
  lra.
Qed.

Print Assumptions Ell2_ip_summable.
Print Assumptions ip_CS.
Print Assumptions norm_triangle.
Print Assumptions Ell2_complete.

(* ================================================================= *)
(*  END Ell2.v (STAGES 1–3)                                          *)
(*  ℓ² is a genuine infinite-dimensional real HILBERT space: a vector *)
(*  space (0, scalar, +) with a symmetric, bilinear, positive-        *)
(*  DEFINITE inner product Σ f g satisfying Cauchy–Schwarz, a norm    *)
(*  ‖f‖ = √⟨f,f⟩ obeying the triangle inequality, and COMPLETENESS    *)
(*  (Riesz–Fischer, Ell2_complete).  Axiom footprint: the standard    *)
(*  classical-Reals + functional-extensionality axioms only.         *)
(* ================================================================= *)
