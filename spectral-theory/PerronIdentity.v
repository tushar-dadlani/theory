(* ================================================================= *)
(*  PerronIdentity.v  —  Perron A2: the Dirichlet-series ↔ Perron         *)
(*  identity.  For x>0 and c>1,                                          *)
(*                                                                    *)
(*    (1/2π) ∫_{−T}^{T} Φ(c+it)·x^{c+it}/(c+it) dt                        *)
(*        =  Σ_{n≥1} Λ(n)·Vperron(x/n, c, T).                             *)
(*                                                                    *)
(*  Route: apply Cintf_series (PerronSeriesInt) to the termwise            *)
(*  integrand  f n t = Λ(n+1)·(x/(n+1))^{c+it}/(c+it).  The pointwise      *)
(*  sum is Φ(c+it)·x^{c+it}/(c+it) (pterm_Gint + Cseries_scal_r on          *)
(*  Phi_spec); the Weierstrass majorant is M n = (x^c/c)·blam(c) n         *)
(*  (blam_sum_cv gives Σ M).  The continuity of the sum Φ(c+it) along the   *)
(*  line — absent in the repo — is DISCHARGED by unif_limit_cont, the      *)
(*  uniform-limit-of-continuous theorem proved here from the same M-test.  *)
(*  Axiom-clean.                                                          *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia FunctionalExtensionality.
Require Import ComplexField Cmodulus CDeriv CSeries CIntegral2 CSegInt CLeibniz
        CexpFull CPowMul CZetaTerm CDirichlet VonMangoldtGlobal Chebyshev CVonMangoldtSeries
        PerronVertical PerronSeriesInt PerronRemovable.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  0.  small generic helpers on convergence / series scaling          *)
(* ----------------------------------------------------------------- *)

Lemma Un_cv_ext : forall u v l, (forall n, u n = v n) -> Un_cv u l -> Un_cv v l.
Proof.
  intros u v l Heq Hu eps Heps; destruct (Hu eps Heps) as [N HN].
  exists N; intros n Hn; rewrite <- (Heq n); apply HN; exact Hn.
Qed.

Lemma Un_cv_scal : forall u l a, Un_cv u l -> Un_cv (fun n => a * u n) (a * l).
Proof.
  intros u l a Hu eps Heps.
  set (K := Rabs a + 1); assert (HK : 0 < K) by (unfold K; pose proof (Rabs_pos a); lra).
  destruct (Hu (eps / K) ltac:(apply Rdiv_lt_0_compat; [ exact Heps | exact HK ])) as [N HN].
  exists N; intros n Hn; unfold R_dist.
  replace (a * u n - a * l) with (a * (u n - l)) by ring.
  rewrite Rabs_mult; specialize (HN n Hn); unfold R_dist in HN.
  apply Rle_lt_trans with (Rabs a * (eps / K)).
  - apply Rmult_le_compat_l; [ apply Rabs_pos | left; exact HN ].
  - apply Rlt_le_trans with (K * (eps / K)).
    + apply Rmult_lt_compat_r; [ apply Rdiv_lt_0_compat; [ exact Heps | exact HK ] | unfold K; lra ].
    + right; field; lra.
Qed.

Lemma Cseries_cv_ext : forall a a' S, (forall n, a n = a' n) ->
  Cseries_cv a S -> Cseries_cv a' S.
Proof.
  intros a a' S Heq Ha.
  assert (Hfe : a = a') by (apply functional_extensionality; exact Heq).
  rewrite <- Hfe; exact Ha.
Qed.

Lemma Cpsum_scal_r : forall (a : nat -> C) (k : C) N,
  Cpsum (fun n => Cmul (a n) k) N = Cmul (Cpsum a N) k.
Proof. induction N as [|N IH]; simpl; [ reflexivity | rewrite IH; ring ]. Qed.

Lemma Cpsum_scal_l : forall (a : nat -> C) (k : C) N,
  Cpsum (fun n => Cmul k (a n)) N = Cmul k (Cpsum a N).
Proof. induction N as [|N IH]; simpl; [ reflexivity | rewrite IH; ring ]. Qed.

Lemma Cseries_scal_r : forall a P k, Cseries_cv a P ->
  Cseries_cv (fun n => Cmul (a n) k) (Cmul P k).
Proof.
  intros a P k Ha eps Heps.
  set (K := Cmod k + 1); assert (HK : 0 < K) by (unfold K; pose proof (Cmod_nonneg k); lra).
  destruct (Ha (eps / K) ltac:(apply Rdiv_lt_0_compat; [ exact Heps | exact HK ])) as [N HN].
  exists N; intros n Hn; rewrite Cpsum_scal_r.
  replace (Cminus (Cmul (Cpsum a n) k) (Cmul P k))
    with (Cmul (Cminus (Cpsum a n) P) k) by ring.
  rewrite Cmod_mul; specialize (HN n Hn).
  apply Rle_lt_trans with (Cmod (Cminus (Cpsum a n) P) * K).
  - apply Rmult_le_compat_l; [ apply Cmod_nonneg | unfold K; lra ].
  - apply Rlt_le_trans with (eps / K * K).
    + apply Rmult_lt_compat_r; [ exact HK | exact HN ].
    + right; field; lra.
Qed.

Lemma Cseries_scal_l : forall a P k, Cseries_cv a P ->
  Cseries_cv (fun n => Cmul k (a n)) (Cmul k P).
Proof.
  intros a P k Ha eps Heps.
  set (K := Cmod k + 1); assert (HK : 0 < K) by (unfold K; pose proof (Cmod_nonneg k); lra).
  destruct (Ha (eps / K) ltac:(apply Rdiv_lt_0_compat; [ exact Heps | exact HK ])) as [N HN].
  exists N; intros n Hn; rewrite Cpsum_scal_l.
  replace (Cminus (Cmul k (Cpsum a n)) (Cmul k P))
    with (Cmul k (Cminus (Cpsum a n) P)) by ring.
  rewrite Cmod_mul; specialize (HN n Hn).
  apply Rle_lt_trans with (K * Cmod (Cminus (Cpsum a n) P)).
  - apply Rmult_le_compat_r; [ apply Cmod_nonneg | unfold K; lra ].
  - apply Rlt_le_trans with (K * (eps / K)).
    + apply Rmult_lt_compat_l; [ exact HK | exact HN ].
    + right; field; lra.
Qed.

(* ----------------------------------------------------------------- *)
(*  1.  R->C continuity <-> Cmod-δ bound                               *)
(* ----------------------------------------------------------------- *)

Lemma Ccont_from_Cmod : forall (F : R -> C),
  (forall x eps, 0 < eps -> exists del, 0 < del /\
     forall u, Rabs (u - x) < del -> Cmod (Cminus (F u) (F x)) < eps) ->
  Ccont F.
Proof.
  intros F HF; split; intro x; apply continuity_pt_from_bound; intros eps Heps;
    destruct (HF x eps Heps) as [del [Hdel Hb]]; exists del; split; try exact Hdel;
    intros u Hu; specialize (Hb u Hu).
  - replace (Re (F u) - Re (F x)) with (Re (Cminus (F u) (F x)))
      by (unfold Cminus, Cadd, Copp; cbn; ring).
    eapply Rle_lt_trans; [ apply Rabs_Re_le_Cmod | exact Hb ].
  - replace (Im (F u) - Im (F x)) with (Im (Cminus (F u) (F x)))
      by (unfold Cminus, Cadd, Copp; cbn; ring).
    eapply Rle_lt_trans; [ apply Rabs_Im_le_Cmod | exact Hb ].
Qed.

Lemma Ccont_to_Cmod : forall (F : R -> C) x eps, 0 < eps -> Ccont F ->
  exists del, 0 < del /\
    forall u, Rabs (u - x) < del -> Cmod (Cminus (F u) (F x)) < eps.
Proof.
  intros F x eps Heps [HR HI].
  destruct (continuity_pt_bound _ x (HR x) (eps / 2) ltac:(lra)) as [d1 [Hd1 Hc1]].
  destruct (continuity_pt_bound _ x (HI x) (eps / 2) ltac:(lra)) as [d2 [Hd2 Hc2]].
  exists (Rmin d1 d2); split; [ apply Rmin_pos; lra | ]; intros u Hu.
  assert (H1 : Rabs (Re (F u) - Re (F x)) < eps / 2)
    by (apply Hc1; eapply Rlt_le_trans; [ exact Hu | apply Rmin_l ]).
  assert (H2 : Rabs (Im (F u) - Im (F x)) < eps / 2)
    by (apply Hc2; eapply Rlt_le_trans; [ exact Hu | apply Rmin_r ]).
  eapply Rle_lt_trans; [ apply Cmod_le_sum | ].
  unfold Cminus, Cadd, Copp; cbn [Re Im]; lra.
Qed.

(* ----------------------------------------------------------------- *)
(*  2.  uniform (Weierstrass-M) limit of continuous C-functions is       *)
(*      continuous — discharges the sum-function continuity.            *)
(* ----------------------------------------------------------------- *)

Section UnifLimit.
Variables (f : nat -> R -> C) (Sf : R -> C) (M : nat -> R) (SM : R).
Hypothesis Hfc : forall n, Ccont (f n).
Hypothesis Hbd : forall n t, Cmod (f n t) <= M n.
Hypothesis HMcv : Un_cv (sum_f_R0 M) SM.
Hypothesis Hptw : forall t, Cseries_cv (fun n => f n t) (Sf t).

Lemma ul_Mnn : forall n, 0 <= M n.
Proof. intro n; eapply Rle_trans; [ apply Cmod_nonneg | apply (Hbd n 0) ]. Qed.

Lemma ul_sumle : forall N, sum_f_R0 M N <= SM.
Proof. intro N; apply growing_ineq; [ intro n; simpl; pose proof (ul_Mnn (S n)); lra | exact HMcv ]. Qed.

Lemma ul_pcont : forall N, Ccont (fun t => Cpsum (fun n => f n t) N).
Proof.
  induction N as [|N IH]; [ apply Hfc | simpl; apply Ccont_add; [ exact IH | apply Hfc ] ].
Qed.

Lemma ul_tail : forall N t,
  Cmod (Cminus (Sf t) (Cpsum (fun n => f n t) N)) <= SM - sum_f_R0 M N.
Proof.
  intros N t.
  apply Rle_cv_lim with
    (Un := fun k => Cmod (Cminus (Cpsum (fun n => f n t) (N + k)) (Cpsum (fun n => f n t) N)))
    (Vn := fun k => sum_f_R0 M (N + k) - sum_f_R0 M N).
  - intro k; apply (Cpsum_shift_bound (fun n => f n t) M (fun n => Hbd n t) N k).
  - intros eps Heps; destruct (Hptw t eps Heps) as [n0 Hn0].
    exists n0; intros k Hk; unfold R_dist.
    eapply Rle_lt_trans; [ apply Cmod_diff_le | ].
    replace (Cminus (Cminus (Cpsum (fun n => f n t) (N + k)) (Cpsum (fun n => f n t) N))
                    (Cminus (Sf t) (Cpsum (fun n => f n t) N)))
      with (Cminus (Cpsum (fun n => f n t) (N + k)) (Sf t)) by ring.
    apply Hn0; lia.
  - apply (CV_minus (fun k => sum_f_R0 M (N + k)) (fun _ => sum_f_R0 M N) SM (sum_f_R0 M N));
      [ apply Un_cv_shift; exact HMcv | apply Un_cv_const ].
Qed.

Theorem unif_limit_cont : Ccont Sf.
Proof.
  apply Ccont_from_Cmod; intros x eps Heps.
  destruct (HMcv (eps / 3) ltac:(lra)) as [N0 HN0].
  pose proof (HN0 N0 (Nat.le_refl N0)) as HcvN; unfold R_dist in HcvN.
  pose proof (ul_sumle N0) as Hsle.
  assert (Htail3 : SM - sum_f_R0 M N0 < eps / 3)
    by (rewrite Rabs_minus_sym, Rabs_pos_eq in HcvN by lra; lra).
  destruct (Ccont_to_Cmod (fun t => Cpsum (fun n => f n t) N0) x (eps / 3)
              ltac:(lra) (ul_pcont N0)) as [del [Hdel Hpc]].
  exists del; split; [ exact Hdel | ]; intros u Hu.
  set (P := fun t => Cpsum (fun n => f n t) N0).
  replace (Cminus (Sf u) (Sf x))
    with (Cadd (Cadd (Cminus (Sf u) (P u)) (Cminus (P u) (P x))) (Cminus (P x) (Sf x)))
    by (unfold P; ring).
  eapply Rle_lt_trans; [ apply Cmod_triangle | ].
  eapply Rle_lt_trans; [ apply Rplus_le_compat_r; apply Cmod_triangle | ].
  assert (HA : Cmod (Cminus (Sf u) (P u)) < eps / 3)
    by (eapply Rle_lt_trans; [ apply (ul_tail N0 u) | exact Htail3 ]).
  assert (HC : Cmod (Cminus (P x) (Sf x)) < eps / 3)
    by (rewrite Cmod_Cminus_sym; eapply Rle_lt_trans; [ apply (ul_tail N0 x) | exact Htail3 ]).
  pose proof (Hpc u Hu) as HB; unfold P in *; lra.
Qed.

End UnifLimit.

(* ----------------------------------------------------------------- *)
(*  3.  the base/exponent algebra                                      *)
(* ----------------------------------------------------------------- *)

Lemma Rpower_div_base : forall x m c, 0 < x -> 0 < m ->
  Rpower (x / m) c = Rpower x c * Rpower m (- c).
Proof.
  intros x m c Hx Hm; unfold Rpower, Rdiv.
  rewrite ln_mult by (try lra; apply Rinv_0_lt_compat; lra).
  rewrite ln_Rinv by lra.
  rewrite Rmult_plus_distr_l, exp_plus.
  f_equal; f_equal; ring.
Qed.

(* cterm(s) n · x^s  =  (x/(n+1))^s :  the key multiplicative collapse *)
Lemma pterm_Gint : forall x c t n, 0 < x ->
  Cmul (pterm (mkC c t) n) (Gint x c t)
  = Cmul (RtoC (Lam (S n))) (Gint (x / INR (S n)) c t).
Proof.
  intros x c t n Hx.
  assert (HSn : 0 < INR (S n)) by (apply lt_0_INR; lia).
  unfold pterm, Gint, cterm, gC.
  (* reduce to:  (n+1)^{-s} · x^s = (x/(n+1))^s  *)
  assert (Hbase : Cmul (Cpw (INR (S n)) (Copp (mkC c t))) (Cpw x (mkC c t))
                  = Cpw (x / INR (S n)) (mkC c t)).
  { unfold Cpw.
    replace (x / INR (S n)) with (x * / INR (S n)) by (unfold Rdiv; reflexivity).
    rewrite ln_mult by (try lra; apply Rinv_0_lt_compat; lra).
    rewrite ln_Rinv by exact HSn.
    rewrite RtoC_add, <- Cexpf_add.
    f_equal.
    unfold Copp, Cmul, RtoC; apply Ceq; cbn; ring. }
  (* now stitch through the scalar Λ and the common 1/(c+it) *)
  rewrite <- Hbase; ring.
Qed.

(* ----------------------------------------------------------------- *)
(*  4.  the identity                                                   *)
(* ----------------------------------------------------------------- *)

Section Identity.
Variables (x c T : R).
Hypothesis Hx : 0 < x.
Hypothesis Hc1 : 1 < c.
Hypothesis HT : 0 < T.

Definition Hc : c <> 0 := Rgt_not_eq c 0 (Rlt_trans 0 1 c Rlt_0_1 Hc1).
Definition Hphi (t : R) : 1 < Re (mkC c t) := Hc1.

Definition Sfun (t : R) : C := Cmul (Phi (mkC c t) (Hphi t)) (Gint x c t).
Definition fterm (n : nat) (t : R) : C := Cmul (RtoC (Lam (S n))) (Gint (x / INR (S n)) c t).
Definition Mm (n : nat) : R := Rpower x c / c * blam (mkC c 0) n.

Let Hab : - T <= T. Proof. lra. Qed.
Let Hcpos : 0 < c := Rlt_trans 0 1 c Rlt_0_1 Hc1.

Lemma fterm_cont : forall n, Ccont (fterm n).
Proof. intro n; unfold fterm; apply Ccont_scal; apply Gint_cont; exact Hc. Qed.

Lemma fterm_bd : forall n t, Cmod (fterm n t) <= Mm n.
Proof.
  intros n t; unfold fterm.
  assert (HSn : 0 < INR (S n)) by (apply lt_0_INR; lia).
  rewrite Cmod_mul, Cmod_RtoC, (Rabs_pos_eq (Lam (S n))) by apply Lam_nonneg.
  assert (HGint : Cmod (Gint (x / INR (S n)) c t) <= Rpower (x / INR (S n)) c / c).
  { unfold Gint; rewrite Cmod_mul, (Cpw_mod (x / INR (S n)) (mkC c t)).
    rewrite (Cmod_inv (mkC c t) (mkC_c_ne0 c t Hc)); cbn [Re].
    assert (Hge : c <= Cmod (mkC c t))
      by (pose proof (Rabs_Re_le_Cmod (mkC c t)) as H; cbn in H;
          rewrite Rabs_pos_eq in H by lra; exact H).
    assert (Hrp : 0 <= Rpower (x / INR (S n)) c) by (left; unfold Rpower; apply exp_pos).
    unfold Rdiv; apply Rmult_le_compat_l; [ exact Hrp | ].
    apply Rinv_le_contravar; [ exact Hcpos | exact Hge ]. }
  eapply Rle_trans; [ apply Rmult_le_compat_l; [ apply Lam_nonneg | exact HGint ] | ].
  unfold Mm, blam; cbn [Re].
  rewrite (Rpower_div_base x (INR (S n)) c Hx HSn).
  assert (HA : 0 <= Rpower x c * Rpower (INR (S n)) (- c) / c).
  { unfold Rdiv; repeat apply Rmult_le_pos; try (left; unfold Rpower; apply exp_pos).
    left; apply Rinv_0_lt_compat; exact Hcpos. }
  assert (Hll : Lam (S n) <= ln (INR (S n))) by (apply Lam_le_ln; lia).
  replace (Rpower x c / c * (ln (INR (S n)) * Rpower (INR (S n)) (- c)))
    with (ln (INR (S n)) * (Rpower x c * Rpower (INR (S n)) (- c) / c))
    by (field; lra).
  apply Rmult_le_compat_r; [ exact HA | exact Hll ].
Qed.

Lemma Mm_cv : { SM | Un_cv (sum_f_R0 Mm) SM }.
Proof.
  destruct (blam_sum_cv (mkC c 0) Hc1) as [Tb HTb].
  exists (Rpower x c / c * Tb).
  assert (Hsum : forall N, sum_f_R0 Mm N = Rpower x c / c * sum_f_R0 (blam (mkC c 0)) N).
  { induction N as [|N IH]; [ unfold Mm; reflexivity | rewrite !tech5, IH; unfold Mm; ring ]. }
  apply (Un_cv_ext (fun N => Rpower x c / c * sum_f_R0 (blam (mkC c 0)) N));
    [ intro n; symmetry; apply Hsum | apply Un_cv_scal; exact HTb ].
Qed.

Lemma Sfun_ptw : forall t, Cseries_cv (fun n => fterm n t) (Sfun t).
Proof.
  intro t.
  apply (Cseries_cv_ext (fun n => Cmul (pterm (mkC c t) n) (Gint x c t)));
    [ intro n; apply pterm_Gint; exact Hx | ].
  unfold Sfun; apply Cseries_scal_r; apply Phi_spec.
Qed.

Lemma Sfun_cont : Ccont Sfun.
Proof.
  destruct Mm_cv as [SM HSM].
  exact (unif_limit_cont fterm Sfun Mm SM fterm_cont fterm_bd HSM Sfun_ptw).
Qed.

(*  the raw (un-normalised) identity:  Σ Λ(n)·Vraw(x/n) = ∫ Φ·x^s/s        *)
Lemma perron_identity_raw :
  Cseries_cv (fun n => Cmul (RtoC (Lam (S n))) (Vraw (x / INR (S n)) c T Hc))
             (Cintf Sfun Sfun_cont (- T) T).
Proof.
  destruct Mm_cv as [SM HSM].
  apply (Cseries_cv_ext (fun n => Cintf (fterm n) (fterm_cont n) (- T) T)).
  - intro n; unfold fterm.
    apply (Cintf_cmul_l (RtoC (Lam (S n))) (Gint (x / INR (S n)) c)
             (Gint_cont (x / INR (S n)) c Hc) (fterm_cont n) (- T) T Hab).
  - (* the interchange *)
    exact (Cintf_series fterm Sfun (- T) T Mm SM Hab fterm_cont Sfun_cont
             (fun n t _ => fterm_bd n t) HSM (fun t _ => Sfun_ptw t)).
Qed.

(*  normalised form:  Σ Λ(n)·Vperron(x/n) = (1/2π)·∫ Φ·x^s/s               *)
Theorem perron_identity :
  Cseries_cv (fun n => Cmul (RtoC (Lam (S n))) (Vperron (x / INR (S n)) c T Hc))
             (Cmul (RtoC (/ (2 * PI))) (Cintf Sfun Sfun_cont (- T) T)).
Proof.
  apply (Cseries_cv_ext
           (fun n => Cmul (RtoC (/ (2 * PI)))
                       (Cmul (RtoC (Lam (S n))) (Vraw (x / INR (S n)) c T Hc)))).
  - intro n; unfold Vperron; ring.
  - apply Cseries_scal_l; apply perron_identity_raw.
Qed.

End Identity.

Print Assumptions perron_identity.

(* ================================================================= *)
(*  END PerronIdentity.v — Σ Λ(n)·Vperron(x/n) = (1/2π)∫ Φ(c+it)x^{c+it}/(c+it).*)
(* ================================================================= *)
