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
        GammaFunction ContinuousCoV GammaExtend GammaRecur.
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

