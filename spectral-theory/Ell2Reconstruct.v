(* ================================================================= *)
(*  Ell2Reconstruct.v  —  reconstruction of f from its Fourier         *)
(*  coefficients:  f = Σ_i ⟨f,e i⟩ · e i   (as an ℓ²-norm limit).      *)
(*                                                                    *)
(*  The N-th partial sum  recon f N = Σ_{i≤N} ⟨f,e i⟩·e i  is (since   *)
(*  ⟨f,e i⟩ = f(i)) the truncation of f to coordinates ≤ N.  We split  *)
(*      f = recon f N + tail f N,                                     *)
(*  show the two summands are ORTHOGONAL (disjoint support), whence    *)
(*  Pythagoras gives ‖f‖² = ‖recon‖² + ‖tail‖², with ‖recon‖² the      *)
(*  finite head Σ_{n≤N} f(n)².  Therefore                            *)
(*      ‖f − recon f N‖² = ‖f‖² − Σ_{n≤N} f(n)²  →  0,                 *)
(*  i.e. the Fourier series converges to f in ℓ²  (reconstruction).    *)
(*                                                                    *)
(*  Axiom footprint: inherited from Ell2 — the standard classical-    *)
(*  Reals + functional-extensionality axioms only.                   *)
(* ================================================================= *)

Require Import Ell2 Ell2Basis Ell2Parseval.
From Stdlib Require Import Reals Lra Lia.
Open Scope R_scope.

Lemma e_sym : forall i j, e i j = e j i.
Proof. intros i j; unfold e; rewrite (Nat.eqb_sym j i); reflexivity. Qed.

(* the N-th Fourier partial sum, at coordinate n *)
Definition recon (f : nat -> R) (N : nat) : nat -> R :=
  fun n => sum_f_R0 (fun i => f i * e i n) N.

Definition tail (f : nat -> R) (N : nat) : nat -> R :=
  fun n => f n - recon f N n.

(* recon is the truncation of f to coordinates ≤ N *)
Lemma recon_closed : forall f N n,
  recon f N n = (if Nat.leb n N then f n else 0)%R.
Proof.
  intros f N n; unfold recon.
  rewrite (sum_eq (fun i => f i * e i n) (fun i => f i * e n i) N)
    by (intros i _; rewrite (e_sym i n); reflexivity).
  apply sum_fe_closed.
Qed.

Lemma tail_closed : forall f N n,
  tail f N n = (if Nat.leb n N then 0 else f n)%R.
Proof.
  intros f N n; unfold tail; rewrite (recon_closed f N n); destruct (Nat.leb n N); ring.
Qed.

(* both summands stay in ℓ² (dominated by f²) *)
Lemma Ell2_recon : forall f N, Ell2 f -> Ell2 (recon f N).
Proof.
  intros f N Hf.
  apply (Rseries_CV_comp (fun n => (recon f N n) ^ 2) (fun n => (f n) ^ 2)); [ | exact Hf ].
  intro n; rewrite (recon_closed f N n); destruct (Nat.leb n N);
    split; [ apply pow2_ge_0 | pose proof (pow2_ge_0 (f n)); nra
           | apply pow2_ge_0 | pose proof (pow2_ge_0 (f n)); nra ].
Qed.

Lemma Ell2_tailvec : forall f N, Ell2 f -> Ell2 (tail f N).
Proof.
  intros f N Hf.
  apply (Rseries_CV_comp (fun n => (tail f N n) ^ 2) (fun n => (f n) ^ 2)); [ | exact Hf ].
  intro n; rewrite (tail_closed f N n); destruct (Nat.leb n N);
    split; [ apply pow2_ge_0 | pose proof (pow2_ge_0 (f n)); nra
           | apply pow2_ge_0 | pose proof (pow2_ge_0 (f n)); nra ].
Qed.

(* two sequences agreeing from some point on share their limit *)
Lemma Un_cv_eventually : forall U V l,
  (exists K, forall M, (K <= M)%nat -> U M = V M) -> Un_cv V l -> Un_cv U l.
Proof.
  intros U V l [K HK] Hv eps Heps.
  destruct (Hv eps Heps) as [N HN]; exists (max K N); intros M HM.
  rewrite HK by lia; apply HN; lia.
Qed.

(* ‖recon‖² stabilises at the finite head Σ_{n≤N} f² *)
Lemma recon_sq_stab : forall f N d,
  sum_f_R0 (fun n => recon f N n * recon f N n) (N + d)
  = sum_f_R0 (fun n => f n * f n) N.
Proof.
  intros f N d; induction d.
  - rewrite Nat.add_0_r; apply sum_eq; intros n Hn.
    rewrite (recon_closed f N n).
    assert (Nat.leb n N = true) as -> by (apply Nat.leb_le; exact Hn); reflexivity.
  - replace (N + S d)%nat with (S (N + d)) by lia.
    rewrite sum_f_R0_S, IHd, (recon_closed f N (S (N + d))).
    assert (Nat.leb (S (N + d)) N = false) as -> by (apply Nat.leb_gt; lia); ring.
Qed.

Lemma ip_recon_eq : forall f N (Hr : Ell2 (recon f N)),
  ip (recon f N) (recon f N) Hr Hr = sum_f_R0 (fun n => (f n) ^ 2) N.
Proof.
  intros f N Hr.
  apply (UL_sequence (fun M => sum_f_R0 (fun n => recon f N n * recon f N n) M)
                     (ip (recon f N) (recon f N) Hr Hr)
                     (sum_f_R0 (fun n => (f n) ^ 2) N)).
  - apply ip_spec.
  - apply (Un_cv_eventually
             (fun M => sum_f_R0 (fun n => recon f N n * recon f N n) M)
             (fun _ => sum_f_R0 (fun n => (f n) ^ 2) N)
             (sum_f_R0 (fun n => (f n) ^ 2) N)); [ | apply Un_cv_const ].
    exists N; intros M HM.
    replace M with (N + (M - N))%nat by lia.
    rewrite recon_sq_stab; apply sum_eq; intros n _; ring.
Qed.

(* ip is insensitive to a pointwise-equal argument *)
Lemma ip_ext : forall f g (Hf : Ell2 f) (Hg : Ell2 g),
  (forall n, f n = g n) -> ip f f Hf Hf = ip g g Hg Hg.
Proof.
  intros f g Hf Hg Heq.
  apply (UL_sequence (fun N => sum_f_R0 (fun n => f n * f n) N)
                     (ip f f Hf Hf) (ip g g Hg Hg)); [ apply ip_spec | ].
  apply (Un_cv_eq (fun N => sum_f_R0 (fun n => g n * g n) N)); [ | apply ip_spec ].
  intro N; apply sum_eq; intros n _; rewrite !Heq; reflexivity.
Qed.

(* ORTHOGONALITY of the truncation and the tail (disjoint supports) *)
Lemma ip_ortho : forall f N (Hr : Ell2 (recon f N)) (Ht : Ell2 (tail f N)),
  ip (recon f N) (tail f N) Hr Ht = 0.
Proof.
  intros f N Hr Ht.
  apply (UL_sequence (fun M => sum_f_R0 (fun n => recon f N n * tail f N n) M)
                     (ip (recon f N) (tail f N) Hr Ht) 0); [ apply ip_spec | ].
  apply (Un_cv_eq (fun _ => 0)); [ | apply Un_cv_const ].
  intro M; symmetry; transitivity (sum_f_R0 (fun _ : nat => 0) M).
  - apply sum_eq; intros n _.
    rewrite (recon_closed f N n), (tail_closed f N n); destruct (Nat.leb n N); ring.
  - rewrite sum_cte; ring.
Qed.

(* PYTHAGORAS ⇒ the reconstruction error:  ‖tail‖² = ‖f‖² − Σ_{n≤N} f² *)
Lemma ip_tail_eq : forall f N (Hf : Ell2 f),
  ip (tail f N) (tail f N) (Ell2_tailvec f N Hf) (Ell2_tailvec f N Hf)
  = ip f f Hf Hf - sum_f_R0 (fun n => (f n) ^ 2) N.
Proof.
  intros f N Hf.
  set (Hr := Ell2_recon f N Hf).
  set (Ht := Ell2_tailvec f N Hf).
  set (Hrt := Ell2_plus (recon f N) (tail f N) Hr Ht).
  assert (Hsum : ip f f Hf Hf
                 = ip (recon f N) (recon f N) Hr Hr + ip (tail f N) (tail f N) Ht Ht).
  { rewrite (ip_ext f (fun n => recon f N n + tail f N n) Hf Hrt
              ltac:(intro n; unfold tail; ring)).
    rewrite (ip_plus_self (recon f N) (tail f N) Hr Ht Hrt), (ip_ortho f N Hr Ht); ring. }
  rewrite (ip_recon_eq f N Hr) in Hsum; lra.
Qed.

(* RECONSTRUCTION:  ‖f − Σ_{i≤N} ⟨f,e i⟩·e i‖² → 0. *)
Theorem reconstruction : forall f (Hf : Ell2 f),
  Un_cv (fun N => ip (tail f N) (tail f N)
                     (Ell2_tailvec f N Hf) (Ell2_tailvec f N Hf)) 0.
Proof.
  intros f Hf.
  apply (Un_cv_eq (fun N => ip f f Hf Hf - sum_f_R0 (fun n => (f n) ^ 2) N)).
  - intro N; symmetry; apply ip_tail_eq.
  - replace 0 with (ip f f Hf Hf - ip f f Hf Hf) by ring.
    apply CV_minus; [ apply Un_cv_const | ].
    apply (Un_cv_eq (fun N => sum_f_R0 (fun n => f n * f n) N)); [ | apply ip_spec ].
    intro N; apply sum_eq; intros n _; ring.
Qed.

Print Assumptions ip_tail_eq.
Print Assumptions reconstruction.

(* ================================================================= *)
(*  END Ell2Reconstruct.v                                            *)
(*  Every f ∈ ℓ² is the ℓ²-limit of its Fourier partial sums          *)
(*  Σ_{i≤N} ⟨f,e i⟩·e i (= recon f N): ‖f − recon f N‖² → 0.  With     *)
(*  Parseval, this completes {e i} as a genuine orthonormal basis.   *)
(* ================================================================= *)
