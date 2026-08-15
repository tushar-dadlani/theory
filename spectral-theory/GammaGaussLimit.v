(* ================================================================= *)
(*  GammaGaussLimit.v   (the Gauss-limit representation of Gamma)       *)
(*                                                                    *)
(*  Content A: the Beta integral  betaI s N = int_0^1 u^{s-1}(1-u)^N du  *)
(*  and its closed form  betaI s N = N! / (s(s+1)...(s+N))  via IBP.     *)
(*                                                                    *)
(*  Mirrors GammaReal.gnear (ImproperCv0 near 0) and GammaRecur.v       *)
(*  (integration by parts on an improper integral via FTC_antideriv).   *)
(*                                                                    *)
(*  Axioms: standard classical-Reals only.                            *)
(* ================================================================= *)

From Stdlib Require Import Reals Rpower Lra Lia Factorial.
Require Import GammaReal MellinElem ImproperCv0 ImproperCv1 RpowerZero ZetaContinuation
        GammaFunction ContinuousCoV GammaExtend GammaRecur GammaGaussBounds.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  the Beta integrand  u^{s-1} (1-u)^N  and its integral over (0,1]  *)
(* ----------------------------------------------------------------- *)
Definition bnk (s : R) (N : nat) (u : R) : R := Rpower u (s - 1) * (1 - u) ^ N.

Lemma cont_bnk : forall s N u, 0 < u -> continuity_pt (bnk s N) u.
Proof.
  intros s N u Hu. unfold bnk. apply continuity_pt_mult.
  - apply cont_Rpower_pos; exact Hu.
  - apply (continuity_pt_comp (fun u => 1 - u) (fun x => x ^ N) u).
    + apply continuity_pt_minus;
        [ apply continuity_pt_const; unfold constant; reflexivity
        | apply derivable_continuous_pt; exists 1; apply derivable_pt_lim_id ].
    + apply derivable_continuous_pt; apply derivable_pt_pow.
Qed.

Lemma Hf_bnk : forall s N, forall x y, 0 < x -> x <= y ->
  Riemann_integrable (bnk s N) x y.
Proof.
  intros s N x y Hx Hxy. apply continuity_implies_RiemannInt;
    [ exact Hxy | intros t Ht; apply cont_bnk; lra ].
Qed.

Lemma bnk_nonneg : forall s N u, 0 < u -> u <= 1 -> 0 <= bnk s N u.
Proof.
  intros s N u Hu Hu1. unfold bnk. apply Rmult_le_pos.
  - left; unfold Rpower; apply exp_pos.
  - apply pow_le; lra.
Qed.

(* betaI's partial integral over [x,1] is bounded by 1/s *)
Lemma bnk_bound : forall s N x (Hx : 0 < x) (Hx1 : x <= 1), 0 < s ->
  rint01 (bnk s N) (Hf_bnk s N) x <= / s.
Proof.
  intros s N x Hx Hx1 Hs.
  rewrite (rint01_val (bnk s N) (Hf_bnk s N) x Hx Hx1).
  apply Rle_trans with (RiemannInt (rpow_ri s x 1 Hx Hx1)).
  - apply RiemannInt_P19; [ exact Hx1 | intros t [Ht1 HtA]; unfold bnk ].
    rewrite <- (Rmult_1_r (Rpower t (s - 1))) at 2.
    apply Rmult_le_compat_l; [ left; unfold Rpower; apply exp_pos | ].
    apply Rle_trans with (1 ^ N); [ apply pow_incr; lra | rewrite pow1; apply Rle_refl ].
  - rewrite (rpow_pint s x Hx Hx1 (Rgt_not_eq _ _ Hs)), Rpower_base1.
    assert (0 <= Rpower x s) by (left; unfold Rpower; apply exp_pos).
    assert (0 < / s) by (apply Rinv_0_lt_compat; exact Hs).
    nra.
Qed.

Definition betaI_sig (s : R) (N : nat) (Hs : 0 < s) :
  { I : R | ImproperCv0 (bnk s N) (Hf_bnk s N) I }.
Proof.
  apply (improper_bounded_cv0 (bnk s N) (Hf_bnk s N)
           (fun x Hx Hx1 => bnk_nonneg s N x Hx Hx1)).
  exists (/ s); intros x Hx Hx1; apply bnk_bound; assumption.
Defined.

Definition betaI (s : R) (N : nat) (Hs : 0 < s) : R := proj1_sig (betaI_sig s N Hs).

Lemma betaI_spec : forall s N (Hs : 0 < s),
  ImproperCv0 (bnk s N) (Hf_bnk s N) (betaI s N Hs).
Proof. intros s N Hs. exact (proj2_sig (betaI_sig s N Hs)). Qed.

(* ----------------------------------------------------------------- *)
(*  the IBP antiderivative  F(u) = (1/s) u^s (1-u)^{S N}               *)
(*  with  F'(u) = bnk s (S N) u - (S N/s) bnk (s+1) N u                *)
(* ----------------------------------------------------------------- *)
Lemma Fanti_deriv : forall s N u, 0 < s -> 0 < u ->
  derivable_pt_lim (fun w => / s * (Rpower w s * (1 - w) ^ (S N))) u
    (bnk s (S N) u - INR (S N) / s * bnk (s + 1) N u).
Proof.
  intros s N u Hs Hu.
  assert (HA : derivable_pt_lim (fun w => Rpower w s) u (s * Rpower u (s - 1)))
    by (apply Rpower_deriv; exact Hu).
  assert (Hin : derivable_pt_lim (fun w => 1 - w) u (-1)).
  { replace (-1) with (0 - 1) by ring.
    apply (derivable_pt_lim_minus (fun _ => 1) (fun w => w) u 0 1);
      [ apply derivable_pt_lim_const | apply derivable_pt_lim_id ]. }
  assert (HB : derivable_pt_lim (fun w => (1 - w) ^ (S N)) u (INR (S N) * (1 - u) ^ N * (-1))).
  { apply (derivable_pt_lim_comp (fun w => 1 - w) (fun x => x ^ (S N)) u
             (-1) (INR (S N) * (1 - u) ^ N)).
    - exact Hin.
    - pose proof (derivable_pt_lim_pow (1 - u) (S N)) as Hp.
      simpl Init.Nat.pred in Hp. exact Hp. }
  assert (HAB : derivable_pt_lim (fun w => Rpower w s * (1 - w) ^ (S N)) u
                  (s * Rpower u (s - 1) * (1 - u) ^ (S N)
                   + Rpower u s * (INR (S N) * (1 - u) ^ N * (-1))))
    by (apply (derivable_pt_lim_mult (fun w => Rpower w s) (fun w => (1 - w) ^ (S N)) u
                 (s * Rpower u (s - 1)) (INR (S N) * (1 - u) ^ N * (-1))); [ exact HA | exact HB ]).
  pose proof (derivable_pt_lim_scal (fun w => Rpower w s * (1 - w) ^ (S N)) (/ s) u _ HAB) as HF.
  apply (derivable_pt_lim_ext (mult_real_fct (/ s) (fun w => Rpower w s * (1 - w) ^ (S N)))
           (fun w => / s * (Rpower w s * (1 - w) ^ (S N)))).
  - intro w; unfold mult_real_fct; reflexivity.
  - replace (bnk s (S N) u - INR (S N) / s * bnk (s + 1) N u)
      with (/ s * (s * Rpower u (s - 1) * (1 - u) ^ (S N)
                   + Rpower u s * (INR (S N) * (1 - u) ^ N * (-1)))).
    + exact HF.
    + unfold bnk. replace (s + 1 - 1) with s by ring. field. lra.
Qed.

(* ----------------------------------------------------------------- *)
(*  the IBP recursion  betaI s (S N) = (S N / s) * betaI (s+1) N       *)
(* ----------------------------------------------------------------- *)
Lemma betaI_recur : forall s N (Hs : 0 < s) (Hs1 : 0 < s + 1),
  betaI s (S N) Hs = INR (S N) / s * betaI (s + 1) N Hs1.
Proof.
  intros s N Hs Hs1.
  assert (Hsne : s <> 0) by lra.
  set (ek := fun k => / (1 + INR k)).
  assert (Hp : forall k, 0 < 1 + INR k) by (intro k; pose proof (pos_INR k); lra).
  assert (Hek0 : forall k, 0 < ek k) by (intro k; unfold ek; apply Rinv_0_lt_compat; apply Hp).
  assert (Hek1 : forall k, ek k <= 1)
    by (intro k; unfold ek; apply inv_le_1; pose proof (pos_INR k); lra).
  assert (Hek_cv : Un_cv ek 0)
    by (unfold ek; apply Un_cv_recip_0; [ intro k; apply Hp | apply cv_infty_1_INR ]).
  set (Mint := fun k => rint01 (bnk s (S N)) (Hf_bnk s (S N)) (ek k)).
  set (Nint := fun k => rint01 (bnk (s + 1) N) (Hf_bnk (s + 1) N) (ek k)).
  assert (HMcv : Un_cv Mint (betaI s (S N) Hs))
    by exact (betaI_spec s (S N) Hs ek Hek0 Hek1 Hek_cv).
  assert (HNcv : Un_cv Nint (betaI (s + 1) N Hs1))
    by exact (betaI_spec (s + 1) N Hs1 ek Hek0 Hek1 Hek_cv).
  set (l := - (INR (S N) / s)).
  assert (Hibp : forall k, Mint k + l * Nint k
                 = - (/ s * (Rpower (ek k) s * (1 - ek k) ^ (S N)))).
  { intro k.
    set (g := fun u => bnk s (S N) u + l * bnk (s + 1) N u).
    set (F := fun u => / s * (Rpower u s * (1 - u) ^ (S N))).
    assert (Hgc : forall u, ek k <= u <= 1 -> continuity_pt g u).
    { intros u [Hu1 Hu2]. assert (0 < u) by (pose proof (Hek0 k); lra). unfold g.
      apply continuity_pt_plus;
        [ apply cont_bnk; assumption
        | apply continuity_pt_scal; apply cont_bnk; assumption ]. }
    assert (Hint : Riemann_integrable g (ek k) 1)
      by (apply continuity_implies_RiemannInt; [ apply Hek1 | exact Hgc ]).
    assert (Hanti : antiderivative g F (ek k) 1).
    { split; [ | apply Hek1 ]. intros u [Hu1 Hu2].
      assert (Hupos : 0 < u) by (pose proof (Hek0 k); lra).
      assert (Hd : derivable_pt_lim F u (g u)).
      { unfold F, g, l. pose proof (Fanti_deriv s N u Hs Hupos) as HFa.
        replace (bnk s (S N) u + - (INR (S N) / s) * bnk (s + 1) N u)
          with (bnk s (S N) u - INR (S N) / s * bnk (s + 1) N u) by ring.
        exact HFa. }
      exists (exist (fun m => derivable_pt_lim F u m) (g u) Hd); reflexivity. }
    assert (HFTC : RiemannInt Hint = F 1 - F (ek k))
      by (apply (FTC_antideriv g F (ek k) 1 (Hek1 k) Hgc Hint Hanti)).
    assert (Hlin : RiemannInt Hint = Mint k + l * Nint k).
    { unfold Mint, Nint.
      rewrite (rint01_val (bnk s (S N)) (Hf_bnk s (S N)) (ek k) (Hek0 k) (Hek1 k)).
      rewrite (rint01_val (bnk (s + 1) N) (Hf_bnk (s + 1) N) (ek k) (Hek0 k) (Hek1 k)).
      exact (RiemannInt_P13 (Hf_bnk s (S N) (ek k) 1 (Hek0 k) (Hek1 k))
               (Hf_bnk (s + 1) N (ek k) 1 (Hek0 k) (Hek1 k)) Hint). }
    assert (HF1 : F 1 = 0).
    { unfold F. replace (1 - 1) with 0 by ring.
      assert (H0N : (0:R) ^ (S N) = 0) by (simpl; ring). rewrite H0N. ring. }
    rewrite Hlin in HFTC. rewrite HF1 in HFTC. rewrite HFTC. unfold F. ring. }
  assert (Hbnd : Un_cv (fun k => Mint k + l * Nint k) 0).
  { apply (Un_cv_ext (fun k => - (/ s * (Rpower (ek k) s * (1 - ek k) ^ (S N)))));
      [ intro k; symmetry; apply Hibp | ].
    replace 0 with (- 0) by ring. apply CV_opp.
    replace 0 with (/ s * 0) by ring.
    apply (CV_mult (fun _ => / s) (fun k => Rpower (ek k) s * (1 - ek k) ^ (S N))
                   (/ s) 0); [ apply Un_cv_const | ].
    (* Rpower ek s * (1-ek)^{S N} -> 0 : dominated by Rpower ek s -> 0 *)
    apply (Un_cv_squeeze0 (fun k => Rpower (ek k) s * (1 - ek k) ^ (S N))
                          (fun k => Rpower (ek k) s)).
    - exists 0%nat; intros p _; split.
      + apply Rmult_le_pos; [ left; unfold Rpower; apply exp_pos | apply pow_le;
          pose proof (Hek1 p); lra ].
      + rewrite <- (Rmult_1_r (Rpower (ek p) s)) at 2.
        apply Rmult_le_compat_l; [ left; unfold Rpower; apply exp_pos | ].
        apply Rle_trans with (1 ^ (S N));
          [ apply pow_incr; pose proof (Hek0 p); pose proof (Hek1 p); lra
          | rewrite pow1; apply Rle_refl ].
    - apply Rpower_pos_cv0; [ exact Hs | exact Hek0 | exact Hek_cv ]. }
  assert (Hlim : Un_cv (fun k => Mint k + l * Nint k)
                   (betaI s (S N) Hs + l * betaI (s + 1) N Hs1)).
  { apply CV_plus; [ exact HMcv | ].
    apply (CV_mult (fun _ => l) Nint l (betaI (s + 1) N Hs1));
      [ apply Un_cv_const | exact HNcv ]. }
  assert (Heq0 : betaI s (S N) Hs + l * betaI (s + 1) N Hs1 = 0)
    by (apply (UL_sequence (fun k => Mint k + l * Nint k)); [ exact Hlim | exact Hbnd ]).
  apply (Rplus_eq_reg_r (l * betaI (s + 1) N Hs1)).
  rewrite Heq0. unfold l. ring.
Qed.

Lemma prodshift_pos : forall s N, 0 < s -> 0 < prodshift s N.
Proof.
  intros s N Hs. induction N as [| N IH]; simpl.
  - lra.
  - apply Rmult_lt_0_compat; [ pose proof (pos_INR N); lra | exact IH ].
Qed.

(* ----------------------------------------------------------------- *)
(*  the closed form  betaI s N = N! / (s(s+1)...(s+N))                *)
(* ----------------------------------------------------------------- *)
Lemma betaI_eq : forall N s (Hs : 0 < s),
  betaI s N Hs = INR (fact N) / prodshift s (S N).
Proof.
  induction N as [| N IH]; intros s Hs.
  - (* base: betaI s 0 = 1/s *)
    assert (Hb : betaI s 0 Hs = / s).
    { set (ek := fun k => / (1 + INR k)).
      assert (Hp : forall k, 0 < 1 + INR k) by (intro k; pose proof (pos_INR k); lra).
      assert (Hek0 : forall k, 0 < ek k)
        by (intro k; unfold ek; apply Rinv_0_lt_compat; apply Hp).
      assert (Hek1 : forall k, ek k <= 1)
        by (intro k; unfold ek; apply inv_le_1; pose proof (pos_INR k); lra).
      assert (Hek_cv : Un_cv ek 0)
        by (unfold ek; apply Un_cv_recip_0; [ intro k; apply Hp | apply cv_infty_1_INR ]).
      apply (UL_sequence (fun k => rint01 (bnk s 0) (Hf_bnk s 0) (ek k))).
      - exact (betaI_spec s 0 Hs ek Hek0 Hek1 Hek_cv).
      - apply (Un_cv_ext (fun k => / s - / s * Rpower (ek k) s)).
        + intro k. rewrite (rint01_val (bnk s 0) (Hf_bnk s 0) (ek k) (Hek0 k) (Hek1 k)).
          rewrite (RiemannInt_P18 (Hf_bnk s 0 (ek k) 1 (Hek0 k) (Hek1 k))
                     (rpow_ri s (ek k) 1 (Hek0 k) (Hek1 k)) (Hek1 k)).
          * rewrite (rpow_pint s (ek k) (Hek0 k) (Hek1 k) (Rgt_not_eq _ _ Hs)), Rpower_base1.
            ring.
          * intros x [Hx1 Hx2]. unfold bnk. simpl. ring.
        + assert (Hz : Un_cv (fun k => / s * Rpower (ek k) s) 0).
          { replace 0 with (/ s * 0) by ring.
            apply (CV_mult (fun _ => / s) (fun k => Rpower (ek k) s) (/ s) 0);
              [ apply Un_cv_const | apply Rpower_pos_cv0; [ exact Hs | exact Hek0 | exact Hek_cv ] ]. }
          intros eps Heps. destruct (Hz eps Heps) as [Nn HN]. exists Nn. intros n Hn.
          specialize (HN n Hn). unfold R_dist in *.
          replace (/ s - / s * Rpower (ek n) s - / s)
            with (- (/ s * Rpower (ek n) s - 0)) by ring.
          rewrite Rabs_Ropp. exact HN. }
    rewrite Hb. simpl. field. lra.
  - assert (Hs1 : 0 < s + 1) by lra.
    rewrite (betaI_recur s N Hs Hs1), (IH (s + 1) Hs1).
    assert (Hfact : INR (fact (S N)) = INR (S N) * INR (fact N))
      by (rewrite <- mult_INR; reflexivity).
    assert (Hps : prodshift s (S (S N)) = s * prodshift (s + 1) (S N))
      by (symmetry; apply prodshift_shift).
    rewrite Hfact, Hps.
    assert (Hpp : 0 < prodshift (s + 1) (S N)) by (apply prodshift_pos; lra).
    field. split; apply Rgt_not_eq; lra.
Qed.

Print Assumptions betaI_eq.

(* ================================================================= *)
(*  Content A2: the truncated Gauss integral and the change of vars    *)
(*    int_x^N (1-t/N)^N t^{s-1} dt = N^s int_{x/N}^1 (1-u)^N u^{s-1} du  *)
(* ================================================================= *)
Require Import LocalCoV.

Definition tnk (s : R) (N : nat) (t : R) : R :=
  (1 - t / INR N) ^ N * Rpower t (s - 1).

Lemma cont_tnk : forall s N t, 0 < t -> continuity_pt (tnk s N) t.
Proof.
  intros s N t Ht. unfold tnk. apply continuity_pt_mult.
  - apply (continuity_pt_comp (fun t => 1 - t / INR N) (fun x => x ^ N) t).
    + apply continuity_pt_minus;
        [ apply continuity_pt_const; unfold constant; reflexivity
        | apply (continuity_pt_mult (fun t => t) (fun _ => / INR N));
            [ apply derivable_continuous_pt; exists 1; apply derivable_pt_lim_id
            | apply continuity_pt_const; unfold constant; reflexivity ] ].
    + apply derivable_continuous_pt; apply derivable_pt_pow.
  - apply cont_Rpower_pos; exact Ht.
Qed.

Lemma Hf_tnk : forall s N x y, 0 < x -> x <= y ->
  Riemann_integrable (tnk s N) x y.
Proof.
  intros s N x y Hx Hxy. apply continuity_implies_RiemannInt;
    [ exact Hxy | intros t Ht; apply cont_tnk; lra ].
Qed.

(* the pointwise rescaling identity *)
Lemma rpow_rescale : forall s NN t, 0 < NN -> 0 < t ->
  Rpower NN s * Rpower (t / NN) (s - 1) * / NN = Rpower t (s - 1).
Proof.
  intros s NN t HNN Ht. unfold Rpower.
  assert (HinvN : / NN = exp (- ln NN))
    by (rewrite exp_Ropp, (exp_ln NN HNN); reflexivity).
  rewrite HinvN, <- !exp_plus. f_equal.
  assert (Hln : ln (t / NN) = ln t - ln NN).
  { unfold Rdiv. rewrite ln_mult by (try exact Ht; apply Rinv_0_lt_compat; exact HNN).
    rewrite ln_Rinv by exact HNN. ring. }
  rewrite Hln. ring.
Qed.

Print Assumptions rpow_rescale.

(* RiemannInt is proof-irrelevant in the endpoint value *)
Lemma RiemannInt_endpoint : forall f a b b'
    (pr : Riemann_integrable f a b) (pr' : Riemann_integrable f a b'),
  b = b' -> RiemannInt pr = RiemannInt pr'.
Proof. intros f a b b' pr pr' Heq. subst b'. apply RiemannInt_P5. Qed.

(* pulling a constant out of a Riemann integral (continuous integrand) *)
Lemma RiemannInt_scal_cont : forall (f : R -> R) (c a b : R) (Hab : a <= b)
    (Hc : forall x, a <= x <= b -> continuity_pt f x)
    (pr : Riemann_integrable f a b)
    (prc : Riemann_integrable (fun x => c * f x) a b),
  RiemannInt prc = c * RiemannInt pr.
Proof.
  intros f c a b Hab Hc pr prc.
  assert (pr3 : Riemann_integrable (fun x => fct_cte 0 x + c * f x) a b)
    by (apply continuity_implies_RiemannInt;
        [ exact Hab | intros x Hx; apply continuity_pt_plus;
          [ apply continuity_pt_const; unfold constant, fct_cte; reflexivity
          | apply (continuity_pt_scal f c); apply Hc; exact Hx ] ]).
  assert (Hpc : RiemannInt prc = RiemannInt pr3)
    by (apply RiemannInt_P18; [ exact Hab | intros x Hx; unfold fct_cte; ring ]).
  rewrite Hpc, (RiemannInt_P13 (RiemannInt_P14 a b 0) pr pr3).
  rewrite (@RiemannInt_P15 a b 0 (RiemannInt_P14 a b 0)). ring.
Qed.

(* ----------------------------------------------------------------- *)
(*  the change of variables  t = N u                                 *)
(* ----------------------------------------------------------------- *)
Lemma cov_partial : forall s N x (Hs : 0 < s) (HN : (1 <= N)%nat) (Hx : 0 < x)
    (HxN : x <= INR N) (HxN0 : 0 < x / INR N) (HxN1 : x / INR N <= 1),
  RiemannInt (Hf_tnk s N x (INR N) Hx HxN)
  = Rpower (INR N) s * RiemannInt (Hf_bnk s N (x / INR N) 1 HxN0 HxN1).
Proof.
  intros s N x Hs HN Hx HxN HxN0 HxN1.
  assert (HNN : 0 < INR N) by (apply lt_0_INR; lia).
  set (g := fun t => t / INR N).
  set (g' := fun _ : R => / INR N).
  set (f := fun u => Rpower (INR N) s * bnk s N u).
  assert (Hgd : forall t, x <= t <= INR N -> derivable_pt_lim g t (g' t)).
  { intros t0 _. unfold g, g'. replace (/ INR N) with (1 * / INR N + t0 * 0) by ring.
    apply (derivable_pt_lim_mult (fun t => t) (fun _ => / INR N) t0);
      [ apply derivable_pt_lim_id | apply derivable_pt_lim_const ]. }
  assert (Hg'c : forall t, x <= t <= INR N -> continuity_pt g' t)
    by (intros; unfold g'; apply continuity_pt_const; unfold constant; reflexivity).
  assert (Hgx : g x = x / INR N) by reflexivity.
  assert (Hgb : g (INR N) = 1) by (unfold g; field; apply Rgt_not_eq; exact HNN).
  assert (Hmap : forall t, x <= t <= INR N -> g x <= g t <= g (INR N)).
  { intros t [Ht1 Ht2]. unfold g. split; apply Rmult_le_compat_r;
      solve [ left; apply Rinv_0_lt_compat; exact HNN | lra ]. }
  assert (Hfc : forall u, g x <= u <= g (INR N) -> continuity_pt f u).
  { intros u Hu. rewrite Hgx, Hgb in Hu. unfold f. apply continuity_pt_mult;
      [ apply continuity_pt_const; unfold constant; reflexivity | apply cont_bnk; lra ]. }
  assert (HfL : forall t, x <= t <= INR N -> f (g t) * g' t = tnk s N t).
  { intros t [Ht1 Ht2]. unfold f, g, g', bnk, tnk.
    rewrite <- (rpow_rescale s (INR N) t HNN ltac:(lra)). ring. }
  assert (prL : Riemann_integrable (fun t => f (g t) * g' t) x (INR N)).
  { apply continuity_implies_RiemannInt; [ exact HxN | ].
    intros t Ht. apply continuity_pt_mult.
    - apply (continuity_pt_comp g f t).
      + apply derivable_continuous_pt; exists (g' t); apply Hgd; exact Ht.
      + apply Hfc; apply Hmap; exact Ht.
    - apply Hg'c; exact Ht. }
  assert (prR : Riemann_integrable f (g x) (g (INR N)))
    by (apply continuity_implies_RiemannInt; [ rewrite Hgx, Hgb; exact HxN1 | exact Hfc ]).
  assert (prR1 : Riemann_integrable f (x / INR N) 1).
  { unfold f. apply continuity_implies_RiemannInt; [ exact HxN1 | ].
    intros u Hu. apply continuity_pt_mult;
      [ apply continuity_pt_const; unfold constant; reflexivity | apply cont_bnk; lra ]. }
  (* chain the equalities *)
  transitivity (RiemannInt prL).
  { apply (RiemannInt_P18 (Hf_tnk s N x (INR N) Hx HxN) prL HxN
             (fun t Ht => eq_sym (HfL t (conj (Rlt_le _ _ (proj1 Ht)) (Rlt_le _ _ (proj2 Ht)))))). }
  transitivity (RiemannInt prR).
  { exact (cov_local g g' f x (INR N) HxN Hgd Hg'c Hmap Hfc prL prR). }
  transitivity (RiemannInt prR1).
  { exact (RiemannInt_endpoint f (g x) (g (INR N)) 1 prR prR1 Hgb). }
  exact (RiemannInt_scal_cont (bnk s N) (Rpower (INR N) s) (x / INR N) 1 HxN1
           (fun u Hu => cont_bnk s N u ltac:(lra)) (Hf_bnk s N (x / INR N) 1 HxN0 HxN1) prR1).
Qed.

Print Assumptions cov_partial.

(* ================================================================= *)
(*  Content B, sub-lemma: the pointwise limit  (1-t/N)^N -> e^{-t}      *)
(* ================================================================= *)
Lemma ln_le_x1 : forall x, 0 < x -> ln x <= x - 1.
Proof.
  intros x Hx. pose proof (exp_ineq1_le (ln x)) as H.
  rewrite exp_ln in H by exact Hx. lra.
Qed.

(* N * ln(1 - t/N) -> -t *)
Lemma Nln_cv : forall t, 0 < t -> Un_cv (fun N => INR N * ln (1 - t / INR N)) (- t).
Proof.
  intros t Ht eps Heps.
  destruct (INR_unbounded (t + t * t / eps)) as [N0 HN0].
  assert (Haux : 0 <= t * t / eps) by (apply Rle_mult_inv_pos; [ nra | exact Heps ]).
  exists (S N0). intros N HN.
  assert (HNbig : t + t * t / eps < INR N).
  { apply Rlt_le_trans with (INR N0); [ exact HN0 | apply le_INR; lia ]. }
  assert (HNt : t < INR N) by lra.
  assert (HNNpos : 0 < INR N) by lra.
  set (x := t / INR N).
  assert (Hxpos : 0 < x) by (unfold x; apply Rdiv_lt_0_compat; lra).
  assert (HNx : INR N * x = t) by (unfold x; field; lra).
  assert (Hx1 : x < 1).
  { apply (Rmult_lt_reg_r (INR N)); [ exact HNNpos | ].
    rewrite Rmult_1_l, (Rmult_comm x (INR N)), HNx; exact HNt. }
  assert (H1x : 0 < 1 - x) by lra.
  (* ln bounds *)
  assert (Hub : ln (1 - x) <= - x) by (pose proof (ln_le_x1 (1 - x) H1x); lra).
  assert (Hlb : - (x / (1 - x)) <= ln (1 - x)).
  { pose proof (ln_le_x1 (/ (1 - x)) (Rinv_0_lt_compat _ H1x)) as H.
    rewrite ln_Rinv in H by exact H1x.
    assert (Heq : / (1 - x) - 1 = x / (1 - x)) by (field; lra). lra. }
  (* N ln(1-x) in [-t/(1-x), -t] ; distance to -t bounded by t^2/(N-t) *)
  assert (Hupper : INR N * ln (1 - x) <= - t).
  { apply Rle_trans with (INR N * (- x));
      [ apply Rmult_le_compat_l; [ lra | exact Hub ] | rewrite <- HNx; lra ]. }
  assert (Hlower : - (t / (1 - x)) <= INR N * ln (1 - x)).
  { apply Rle_trans with (INR N * (- (x / (1 - x)))).
    - assert (INR N * (x / (1 - x)) = t / (1 - x))
        by (unfold Rdiv; rewrite <- Rmult_assoc, HNx; reflexivity).
      lra.
    - apply Rmult_le_compat_l; [ lra | exact Hlb ]. }
  unfold R_dist.
  assert (Hdist : Rabs (INR N * ln (1 - x) - - t) <= t * t / (INR N - t)).
  { rewrite Rabs_left1; [ | lra ].
    (* -(N ln(1-x) + t) <= t^2/(N-t) ; i.e. -t/(1-x) - (-t) = -t^2/(N-t)-ish *)
    assert (Hval : - (t / (1 - x)) - - t = - (t * t / (INR N - t))).
    { assert (1 - x = (INR N - t) / INR N)
        by (unfold x; field; lra).
      rewrite H. field; lra. }
    lra. }
  apply Rle_lt_trans with (t * t / (INR N - t)); [ exact Hdist | ].
  apply (Rmult_lt_reg_r (INR N - t)); [ lra | ].
  replace (t * t / (INR N - t) * (INR N - t)) with (t * t) by (field; lra).
  assert (Hrw : t * t = eps * (t * t / eps)) by (field; lra).
  rewrite Hrw. apply Rmult_lt_compat_l; [ exact Heps | lra ].
Qed.

Lemma one_minus_pow_cv : forall t, 0 <= t ->
  Un_cv (fun N => (1 - t / INR N) ^ N) (exp (- t)).
Proof.
  intros t Ht. destruct (Rle_lt_or_eq_dec 0 t Ht) as [Htpos | Ht0].
  - assert (Hexp : Un_cv (fun N => exp (INR N * ln (1 - t / INR N))) (exp (- t)))
      by (apply (continuity_seq exp (fun N => INR N * ln (1 - t / INR N)) (- t));
          [ apply derivable_continuous; apply derivable_exp | apply Nln_cv; exact Htpos ]).
    intros eps Heps. destruct (Hexp eps Heps) as [N1 HN1].
    destruct (INR_unbounded t) as [N2 HN2].
    exists (max N1 (S N2)). intros N HN.
    assert (HNt : t < INR N)
      by (apply Rlt_le_trans with (INR (S N2));
          [ apply Rlt_le_trans with (INR N2); [ exact HN2 | apply le_INR; lia ]
          | apply le_INR; pose proof (Nat.le_max_r N1 (S N2)); lia ]).
    assert (HNNpos : 0 < INR N) by lra.
    assert (H1x : 0 < 1 - t / INR N).
    { assert (t / INR N < 1).
      { apply (Rmult_lt_reg_r (INR N)); [ exact HNNpos | ].
        replace (t / INR N * INR N) with t by (field; lra). lra. }
      lra. }
    assert (Heq : (1 - t / INR N) ^ N = exp (INR N * ln (1 - t / INR N))).
    { rewrite <- (exp_ln (1 - t / INR N) H1x) at 1.
      rewrite exp_pow_nat. f_equal. ring. }
    rewrite Heq. apply HN1. pose proof (Nat.le_max_l N1 (S N2)); lia.
  - subst t. intros eps Heps. exists 0%nat. intros N _.
    replace (1 - 0 / INR N) with 1 by (unfold Rdiv; rewrite Rmult_0_l; lra).
    rewrite pow1. replace (- 0) with 0 by ring. rewrite exp_0.
    unfold R_dist. replace (1 - 1) with 0 by ring. rewrite Rabs_R0. exact Heps.
Qed.

Print Assumptions one_minus_pow_cv.

(* ================================================================= *)
(*  Content B: the convergence interchange   N^s betaI s N -> Gam s     *)
(* ================================================================= *)

(* general change of variables on a compact [a,b] subset (0,N] *)
Lemma cov_general : forall s N a b (Hs : 0 < s) (HN : (1 <= N)%nat)
    (Ha : 0 < a) (Hab : a <= b) (HbN : b <= INR N)
    (Ha' : 0 < a / INR N) (Hab' : a / INR N <= b / INR N),
  RiemannInt (Hf_tnk s N a b Ha Hab)
  = Rpower (INR N) s * RiemannInt (Hf_bnk s N (a / INR N) (b / INR N) Ha' Hab').
Proof.
  intros s N a b Hs HN Ha Hab HbN Ha' Hab'.
  assert (HNN : 0 < INR N) by (apply lt_0_INR; lia).
  set (g := fun t => t / INR N).
  set (g' := fun _ : R => / INR N).
  set (f := fun u => Rpower (INR N) s * bnk s N u).
  assert (Hgd : forall t, a <= t <= b -> derivable_pt_lim g t (g' t)).
  { intros t0 _. unfold g, g'. replace (/ INR N) with (1 * / INR N + t0 * 0) by ring.
    apply (derivable_pt_lim_mult (fun t => t) (fun _ => / INR N) t0);
      [ apply derivable_pt_lim_id | apply derivable_pt_lim_const ]. }
  assert (Hg'c : forall t, a <= t <= b -> continuity_pt g' t)
    by (intros; unfold g'; apply continuity_pt_const; unfold constant; reflexivity).
  assert (Hga : g a = a / INR N) by reflexivity.
  assert (Hgb : g b = b / INR N) by reflexivity.
  assert (Hmap : forall t, a <= t <= b -> g a <= g t <= g b).
  { intros t [Ht1 Ht2]. unfold g. split; apply Rmult_le_compat_r;
      solve [ left; apply Rinv_0_lt_compat; exact HNN | lra ]. }
  assert (Hfc : forall u, g a <= u <= g b -> continuity_pt f u).
  { intros u Hu. rewrite Hga, Hgb in Hu. unfold f. apply continuity_pt_mult;
      [ apply continuity_pt_const; unfold constant; reflexivity
      | apply cont_bnk;
        assert (0 < a / INR N) by exact Ha'; lra ]. }
  assert (HfL : forall t, a <= t <= b -> f (g t) * g' t = tnk s N t).
  { intros t [Ht1 Ht2]. unfold f, g, g', bnk, tnk.
    rewrite <- (rpow_rescale s (INR N) t HNN ltac:(lra)). ring. }
  assert (prL : Riemann_integrable (fun t => f (g t) * g' t) a b).
  { apply continuity_implies_RiemannInt; [ exact Hab | ].
    intros t Ht. apply continuity_pt_mult.
    - apply (continuity_pt_comp g f t).
      + apply derivable_continuous_pt; exists (g' t); apply Hgd; exact Ht.
      + apply Hfc; apply Hmap; exact Ht.
    - apply Hg'c; exact Ht. }
  assert (prR : Riemann_integrable f (g a) (g b))
    by (apply continuity_implies_RiemannInt; [ rewrite Hga, Hgb; exact Hab' | exact Hfc ]).
  assert (prR1 : Riemann_integrable f (a / INR N) (b / INR N)).
  { unfold f. apply continuity_implies_RiemannInt; [ exact Hab' | ].
    intros u Hu. apply continuity_pt_mult;
      [ apply continuity_pt_const; unfold constant; reflexivity | apply cont_bnk; lra ]. }
  transitivity (RiemannInt prL).
  { apply (RiemannInt_P18 (Hf_tnk s N a b Ha Hab) prL Hab
             (fun t Ht => eq_sym (HfL t (conj (Rlt_le _ _ (proj1 Ht)) (Rlt_le _ _ (proj2 Ht)))))). }
  transitivity (RiemannInt prR).
  { exact (cov_local g g' f a b Hab Hgd Hg'c Hmap Hfc prL prR). }
  transitivity (RiemannInt prR1).
  { apply (RiemannInt_P5 prR prR1). }
  exact (RiemannInt_scal_cont (bnk s N) (Rpower (INR N) s) (a / INR N) (b / INR N) Hab'
           (fun u Hu => cont_bnk s N u ltac:(lra)) (Hf_bnk s N (a / INR N) (b / INR N) Ha' Hab') prR1).
Qed.

Print Assumptions cov_general.

Lemma exp_le : forall x y, x <= y -> exp x <= exp y.
Proof.
  intros x y H. destruct (Rle_lt_or_eq_dec x y H) as [Hlt | Heq];
    [ left; apply exp_increasing; exact Hlt | rewrite Heq; apply Rle_refl ].
Qed.

(* uniform bound:  0 <= e^{-t} - (1-t/N)^N <= t^2/(N-t)  *)
Lemma exp_sub_pow_bound : forall t N, 0 < t -> t < INR N ->
  exp (- t) - (1 - t / INR N) ^ N <= t * t / (INR N - t).
Proof.
  intros t N Ht HtN.
  assert (HNN : 0 < INR N) by lra.
  assert (Hx1 : t / INR N < 1).
  { apply (Rmult_lt_reg_r (INR N)); [ lra | ].
    replace (t / INR N * INR N) with t by (field; lra). lra. }
  assert (H1x : 0 < 1 - t / INR N) by lra.
  assert (Hpow : (1 - t / INR N) ^ N = exp (INR N * ln (1 - t / INR N))).
  { rewrite <- (exp_ln (1 - t / INR N) H1x) at 1. rewrite exp_pow_nat. f_equal. ring. }
  rewrite Hpow.
  set (x := t / INR N).
  assert (HNx : INR N * x = t) by (unfold x; field; lra).
  assert (Hxne : 1 - x <> 0) by (unfold x; apply Rgt_not_eq; lra).
  assert (HNne : INR N <> 0) by (apply Rgt_not_eq; lra).
  assert (Htne : INR N - t <> 0) by (apply Rgt_not_eq; lra).
  assert (Hlb : - t - t * t / (INR N - t) <= INR N * ln (1 - x)).
  { assert (H1x' : 0 < 1 - x) by (unfold x; lra).
    assert (Hln : - (x / (1 - x)) <= ln (1 - x)).
    { pose proof (ln_le_x1 (/ (1 - x)) (Rinv_0_lt_compat _ H1x')) as H.
      rewrite ln_Rinv in H by exact H1x'.
      assert (Heq2 : / (1 - x) - 1 = x / (1 - x)) by (field; exact Hxne).
      rewrite Heq2 in H. lra. }
    apply Rle_trans with (INR N * (- (x / (1 - x)))).
    - assert (Heq : INR N * (- (x / (1 - x))) = - (t / (1 - x)))
        by (rewrite <- HNx; field; exact Hxne).
      assert (Ht1x : t / (1 - x) = t + t * t / (INR N - t)).
      { assert (H1xe : 1 - x = (INR N - t) / INR N) by (unfold x; field; exact HNne).
        rewrite H1xe. field; split; assumption. }
      rewrite Heq, Ht1x. lra.
    - apply Rmult_le_compat_l; [ lra | exact Hln ]. }
  assert (Hge : exp (- t) * exp (- (t * t / (INR N - t))) <= exp (INR N * ln (1 - x)))
    by (rewrite <- exp_plus; apply exp_le; lra).
  assert (Hexp1 : exp (- t) <= 1) by (rewrite <- exp_0; apply exp_le; lra).
  assert (H1e : 1 - exp (- (t * t / (INR N - t))) <= t * t / (INR N - t))
    by (pose proof (exp_ineq1_le (- (t * t / (INR N - t)))); lra).
  assert (He2 : 0 <= 1 - exp (- (t * t / (INR N - t)))).
  { assert (exp (- (t * t / (INR N - t))) <= 1)
      by (rewrite <- exp_0; apply exp_le; apply Ropp_le_cancel; rewrite Ropp_involutive, Ropp_0;
          apply Rle_mult_inv_pos; [ nra | lra ]). lra. }
  apply Rle_trans with (exp (- t) - exp (- t) * exp (- (t * t / (INR N - t)))).
  - apply Rplus_le_compat_l, Ropp_le_contravar. exact Hge.
  - replace (exp (- t) - exp (- t) * exp (- (t * t / (INR N - t))))
      with (exp (- t) * (1 - exp (- (t * t / (INR N - t))))) by ring.
    apply Rle_trans with (1 * (t * t / (INR N - t))); [ | lra ].
    apply Rmult_le_compat; [ left; apply exp_pos | exact He2 | exact Hexp1 | exact H1e ].
Qed.

Print Assumptions exp_sub_pow_bound.

(* ----------------------------------------------------------------- *)
(*  compact convergence :  int_a^b tnk s N  ->  int_a^b (gnk s 1)      *)
(* ----------------------------------------------------------------- *)

Lemma ln_le : forall x y, 0 < x -> x <= y -> ln x <= ln y.
Proof.
  intros x y Hx Hxy. destruct (Rle_lt_or_eq_dec x y Hxy) as [Hlt | Heq];
    [ left; apply ln_increasing; [ exact Hx | exact Hlt ] | rewrite Heq; apply Rle_refl ].
Qed.

Lemma Rpower_pos : forall x y, 0 < Rpower x y.
Proof. intros x y; unfold Rpower; apply exp_pos. Qed.

(* Rpower t p (t in [a,b], a>0) is bounded by the sum of the endpoint values *)
Lemma Rpower_bound_compact : forall a b t p, 0 < a -> a <= t -> t <= b ->
  Rpower t p <= Rpower a p + Rpower b p.
Proof.
  intros a b t p Ha Hat Htb.
  assert (Ht : 0 < t) by lra.
  assert (Hlna : ln a <= ln t) by (apply ln_le; [ exact Ha | exact Hat ]).
  assert (Hlnb : ln t <= ln b) by (apply ln_le; [ exact Ht | exact Htb ]).
  pose proof (Rpower_pos a p) as Hpa. pose proof (Rpower_pos b p) as Hpb.
  destruct (Rle_lt_dec 0 p) as [Hp | Hp].
  - assert (Rpower t p <= Rpower b p).
    { unfold Rpower; apply exp_le; apply Rmult_le_compat_l; [ exact Hp | exact Hlnb ]. }
    lra.
  - assert (Rpower t p <= Rpower a p).
    { unfold Rpower; apply exp_le.
      apply Rmult_le_compat_neg_l with (r := p); [ lra | exact Hlna ]. }
    lra.
Qed.

(* C / (INR N - b)  ->  0  as N -> infinity  *)
Lemma recip_lin_cv0 : forall C b, Un_cv (fun N => C * / (INR N - b)) 0.
Proof.
  intros C b eps Heps.
  destruct (INR_unbounded (b + Rabs C * / eps + 1)) as [N0 HN0].
  exists N0. intros n Hn.
  assert (Hle : INR N0 <= INR n) by (apply le_INR; exact Hn).
  assert (Hinv : 0 < / eps) by (apply Rinv_0_lt_compat; exact Heps).
  assert (Hq : 0 <= Rabs C * / eps)
    by (apply Rmult_le_pos; [ apply Rabs_pos | left; exact Hinv ]).
  assert (Hpos : 0 < INR n - b) by lra.
  unfold R_dist. rewrite Rminus_0_r, Rabs_mult.
  rewrite (Rabs_right (/ (INR n - b)));
    [ | apply Rle_ge; left; apply Rinv_0_lt_compat; exact Hpos ].
  apply (Rmult_lt_reg_r (INR n - b)); [ exact Hpos | ].
  rewrite Rmult_assoc, Rinv_l; [ | apply Rgt_not_eq; exact Hpos ].
  rewrite Rmult_1_r.
  apply Rlt_le_trans with (eps * (Rabs C * / eps + 1)).
  - replace (eps * (Rabs C * / eps + 1)) with (Rabs C + eps)
      by (field; apply Rgt_not_eq; exact Heps).
    lra.
  - apply Rmult_le_compat_l; [ left; exact Heps | lra ].
Qed.

Lemma Un_cv_const_minus : forall (w : nat -> R) (c : R),
  Un_cv w 0 -> Un_cv (fun N => c - w N) c.
Proof.
  intros w c Hw eps Heps.
  destruct (Hw eps Heps) as [N HN]. exists N. intros n Hn.
  specialize (HN n Hn). unfold R_dist in *.
  replace (c - w n - c) with (- (w n - 0)) by ring.
  rewrite Rabs_Ropp. exact HN.
Qed.

(* pointwise:  0 <= gnk s 1 t - tnk s N t <= M * (b^2/(N-b))  on [a,b], b<N *)
Lemma gnk_sub_tnk_bounds : forall s a b N t,
  0 < a -> a <= t -> t <= b -> b < INR N ->
  0 <= gnk s 1 t - tnk s N t /\
  gnk s 1 t - tnk s N t <=
    (Rpower a (s - 1) + Rpower b (s - 1)) * (b * b / (INR N - b)).
Proof.
  intros s a b N t Ha Hat Htb HbN.
  assert (Ht : 0 < t) by lra.
  assert (Hb0 : 0 < b) by lra.
  assert (HtN : t < INR N) by lra.
  assert (HNb : 0 < INR N - b) by lra.
  assert (HNt : 0 < INR N - t) by lra.
  unfold gnk, tnk.
  replace (exp (- (1 * t))) with (exp (- t)) by (f_equal; ring).
  set (R := Rpower t (s - 1)).
  assert (HR0 : 0 <= R) by (unfold R; left; apply Rpower_pos).
  set (E := exp (- t) - (1 - t / INR N) ^ N).
  replace (R * exp (- t) - (1 - t / INR N) ^ N * R) with (R * E)
    by (unfold E; ring).
  assert (HE0 : 0 <= E).
  { unfold E. pose proof (one_minus_pow_le_exp t N (Rlt_le _ _ Ht) (Rlt_le _ _ HtN)). lra. }
  assert (HEb : E <= t * t / (INR N - t))
    by (unfold E; apply exp_sub_pow_bound; [ exact Ht | exact HtN ]).
  assert (Hstep : t * t / (INR N - t) <= b * b / (INR N - b)).
  { apply Rmult_le_compat.
    - apply Rmult_le_pos; lra.
    - left; apply Rinv_0_lt_compat; exact HNt.
    - apply Rmult_le_compat; lra.
    - apply Rinv_le_contravar; [ exact HNb | lra ]. }
  assert (Hbb0 : 0 <= b * b / (INR N - b)).
  { apply Rmult_le_pos; [ apply Rmult_le_pos; lra | left; apply Rinv_0_lt_compat; exact HNb ]. }
  split.
  - apply Rmult_le_pos; [ exact HR0 | exact HE0 ].
  - apply Rle_trans with (R * (b * b / (INR N - b))).
    + apply Rmult_le_compat_l; [ exact HR0 | lra ].
    + apply Rmult_le_compat_r; [ exact Hbb0 | ].
      unfold R; apply Rpower_bound_compact; [ exact Ha | exact Hat | exact Htb ].
Qed.

(* the integral gap is nonnegative and O(1/(N-b)) *)
Lemma int_diff_bound : forall s a b N (Ha : 0 < a) (Hab : a <= b), b < INR N ->
  0 <= RiemannInt (Hf_near s 1 a b Ha Hab) - RiemannInt (Hf_tnk s N a b Ha Hab) /\
  RiemannInt (Hf_near s 1 a b Ha Hab) - RiemannInt (Hf_tnk s N a b Ha Hab)
    <= (b - a) * (Rpower a (s - 1) + Rpower b (s - 1)) * (b * b) * / (INR N - b).
Proof.
  intros s a b N Ha Hab HbN.
  set (Hfe := Hf_near s 1 a b Ha Hab).
  set (Hge := Hf_tnk s N a b Ha Hab).
  set (M := Rpower a (s - 1) + Rpower b (s - 1)).
  set (K := M * (b * b / (INR N - b))).
  pose proof (@RiemannInt_P10 (gnk s 1) (tnk s N) a b (-1) Hfe Hge) as prd.
  pose proof (RiemannInt_P13 Hfe Hge prd) as Hval.
  assert (Heq : RiemannInt prd = RiemannInt Hfe - RiemannInt Hge)
    by (rewrite Hval; ring).
  assert (Hlo : 0 <= RiemannInt prd).
  { pose proof (@RiemannInt_P15 a b 0 (RiemannInt_P14 a b 0)) as H0.
    apply Rle_trans with (RiemannInt (RiemannInt_P14 a b 0)).
    - rewrite H0; ring_simplify; apply Rle_refl.
    - apply RiemannInt_P19; [ lra | ].
      intros x Hx. unfold fct_cte.
      destruct (gnk_sub_tnk_bounds s a b N x Ha (Rlt_le _ _ (proj1 Hx))
                  (Rlt_le _ _ (proj2 Hx)) HbN) as [Hlo2 _]. lra. }
  assert (Hup : RiemannInt prd <= K * (b - a)).
  { pose proof (@RiemannInt_P15 a b K (RiemannInt_P14 a b K)) as H0.
    apply Rle_trans with (RiemannInt (RiemannInt_P14 a b K)).
    - apply RiemannInt_P19; [ lra | ].
      intros x Hx. unfold fct_cte.
      destruct (gnk_sub_tnk_bounds s a b N x Ha (Rlt_le _ _ (proj1 Hx))
                  (Rlt_le _ _ (proj2 Hx)) HbN) as [_ Hub2].
      unfold K, M. lra.
    - rewrite H0; apply Rle_refl. }
  rewrite Heq in Hlo, Hup.
  split.
  - exact Hlo.
  - eapply Rle_trans; [ exact Hup | ].
    unfold K, M. apply Req_le. field. apply Rgt_not_eq; lra.
Qed.

Lemma compact_cv : forall s a b (Ha : 0 < a) (Hab : a <= b),
  Un_cv (fun N => RiemannInt (Hf_tnk s N a b Ha Hab))
        (RiemannInt (Hf_near s 1 a b Ha Hab)).
Proof.
  intros s a b Ha Hab.
  set (L := RiemannInt (Hf_near s 1 a b Ha Hab)).
  set (C := (b - a) * (Rpower a (s - 1) + Rpower b (s - 1)) * (b * b)).
  assert (He : Un_cv (fun N => L - RiemannInt (Hf_tnk s N a b Ha Hab)) 0).
  { apply (Un_cv_squeeze0 (fun N => L - RiemannInt (Hf_tnk s N a b Ha Hab))
                          (fun N => C * / (INR N - b))).
    - destruct (INR_unbounded b) as [N0 HN0].
      exists (S N0). intros n Hn.
      assert (HbN : b < INR n)
        by (apply Rlt_le_trans with (INR N0); [ exact HN0 | apply le_INR; lia ]).
      destruct (int_diff_bound s a b n Ha Hab HbN) as [Hlo Hup].
      split; [ exact Hlo | ].
      eapply Rle_trans; [ exact Hup | unfold C; apply Req_le; ring ].
    - apply recip_lin_cv0. }
  apply (Un_cv_ext (fun N => L - (L - RiemannInt (Hf_tnk s N a b Ha Hab)))).
  - intro N; ring.
  - apply Un_cv_const_minus; exact He.
Qed.

Print Assumptions compact_cv.

