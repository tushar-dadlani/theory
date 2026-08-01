(* ================================================================= *)
(*  GammaRecur.v  —  the Gamma recurrence  Γ(s+1) = s·Γ(s)  (s>0).    *)
(*                                                                    *)
(*  Integration by parts of  ∫₀^∞ t^s e^{−t} dt  with antiderivative   *)
(*  −t^s e^{−t}: on [ε,A],                                             *)
(*     ∫_ε^A (t^s − s·t^{s−1}) e^{−t} = [−t^s e^{−t}]_ε^A             *)
(*                                    = ε^s e^{−ε} − A^s e^{−A}.       *)
(*  As ε→0⁺, A→∞ the boundary terms vanish (s>0), the left side       *)
(*  tends to Γ(s+1) − s·Γ(s), giving the recurrence.  Structure       *)
(*  mirrors MellinKernel.mellin_scale (Chasles at 1, UL_sequence).    *)
(*  A first step toward continuing Γ to negative arguments.          *)
(*  No new axioms (classical Reals only).                            *)
(* ================================================================= *)

From Stdlib Require Import Reals Rpower Lra Lia.
Require Import GammaReal MellinElem MellinTail ImproperCv0 ImproperCv1
        RpowerZero ZetaContinuation GammaFunction ContinuousCoV JacobiTheta.
Open Scope R_scope.

(* --- the IBP antiderivative's derivative --- *)

Lemma Gs_deriv : forall s t, 0 < t ->
  derivable_pt_lim (fun t => - (Rpower t s * exp (- t))) t
    (Rpower t s * exp (- t) - s * (Rpower t (s - 1) * exp (- t))).
Proof.
  intros s t Ht.
  assert (Hprod : derivable_pt_lim (fun t => Rpower t s * exp (- t)) t
                    (s * Rpower t (s - 1) * exp (- t) + Rpower t s * (- exp (- t))))
    by (apply (derivable_pt_lim_mult (fun t => Rpower t s) (fun t => exp (- t)) t
                 (s * Rpower t (s - 1)) (- exp (- t)));
        [ apply Rpower_deriv; exact Ht | apply exp_neg_deriv ]).
  pose proof (derivable_pt_lim_opp (fun t => Rpower t s * exp (- t)) t
                (s * Rpower t (s - 1) * exp (- t) + Rpower t s * (- exp (- t))) Hprod) as Hopp.
  apply (derivable_pt_lim_ext (opp_fct (fun t => Rpower t s * exp (- t)))
           (fun t => - (Rpower t s * exp (- t)))).
  - intro z; unfold opp_fct; reflexivity.
  - replace (Rpower t s * exp (- t) - s * (Rpower t (s - 1) * exp (- t)))
      with (- (s * Rpower t (s - 1) * exp (- t) + Rpower t s * (- exp (- t)))) by ring.
    exact Hopp.
Qed.

(* the integrand t^s e^{−t} − s·t^{s−1}e^{−t} = gnk(s+1) − s·gnk s on (0,∞) *)
Lemma gnk_Sp : forall s t, 0 < t -> gnk (s + 1) 1 t = Rpower t s * exp (- t).
Proof.
  intros s t Ht; unfold gnk; replace (s + 1 - 1) with s by ring;
    replace (1 * t) with t by ring; reflexivity.
Qed.

Lemma gnk_id : forall s t, gnk s 1 t = Rpower t (s - 1) * exp (- t).
Proof. intros s t; unfold gnk; replace (1 * t) with t by ring; reflexivity. Qed.

(* --- boundary terms vanish --- *)

Lemma boundary_zero : forall s, 0 < s ->
  forall e, (forall k, 0 < e k) -> Un_cv e 0 ->
  Un_cv (fun k => Rpower (e k) s * exp (- e k)) 0.
Proof.
  intros s Hs e He Hcv eps Heps.
  destruct (Rpower_pos_cv0 s Hs e He Hcv eps Heps) as [N HN]; exists N; intros k Hk.
  specialize (HN k Hk); unfold R_dist in HN |- *; rewrite Rminus_0_r in HN |- *.
  rewrite Rabs_right in HN by (apply Rle_ge; left; unfold Rpower; apply exp_pos).
  rewrite Rabs_right by (apply Rle_ge; apply Rmult_le_pos; left; apply exp_pos).
  apply Rle_lt_trans with (Rpower (e k) s); [ | exact HN ].
  rewrite <- (Rmult_1_r (Rpower (e k) s)) at 2; apply Rmult_le_compat_l;
    [ left; unfold Rpower; apply exp_pos | ].
  rewrite <- exp_0; apply Rlt_le; apply exp_increasing; pose proof (He k); lra.
Qed.

Lemma boundary_infty : forall s, 0 < s -> forall A, (forall k, 1 <= A k) -> cv_infty A ->
  Un_cv (fun k => Rpower (A k) s * exp (- A k)) 0.
Proof.
  intros s Hs A HA Hinf.
  destruct (nat_gt s) as [n Hn].
  set (m := S n).
  set (C := INR (S m) ^ (S m)).
  assert (Hbound : forall k, Rpower (A k) s * exp (- A k) <= C * / A k).
  { intro k; pose proof (HA k) as Hk1; assert (Hkpos : 0 < A k) by lra.
    (* Rpower (A k) s <= A k ^ m *)
    assert (Hp : Rpower (A k) s <= A k ^ m).
    { rewrite <- (Rpower_pow m (A k) Hkpos); apply Rle_Rpower;
        [ exact Hk1 | unfold m; lra ]. }
    (* exp(-A k) <= (S m)^(S m) / A k ^ (S m) *)
    assert (Hct : 0 <= A k) by lra.
    pose proof (exp_lb2 m (A k) Hct) as Hlb.
    assert (Hexp : exp (- A k) <= C / A k ^ (S m)).
    { unfold C; rewrite exp_Ropp; apply Rle_trans with (/ (A k ^ (S m) / INR (S m) ^ (S m))).
      - apply Rinv_le_contravar;
          [ apply Rdiv_lt_0_compat; [ apply pow_lt; exact Hkpos | apply pow_lt; apply lt_0_INR; lia ]
          | exact Hlb ].
      - unfold Rdiv; rewrite Rinv_mult, Rinv_inv; apply Req_le; ring. }
    apply Rle_trans with (A k ^ m * (C / A k ^ (S m))).
    - apply Rmult_le_compat; [ left; unfold Rpower; apply exp_pos | left; apply exp_pos | exact Hp | exact Hexp ].
    - apply Req_le; replace (S m) with (m + 1)%nat by lia; rewrite pow_add, pow_1.
      field; repeat split;
        (apply Rgt_not_eq; solve [ apply pow_lt; exact Hkpos | exact Hkpos ]). }
  apply (Un_cv_squeeze0 (fun k => Rpower (A k) s * exp (- A k)) (fun k => C * / A k)).
  - exists 0%nat; intros p _; split;
      [ apply Rmult_le_pos; [ left; unfold Rpower; apply exp_pos | left; apply exp_pos ] | apply Hbound ].
  - replace 0 with (C * 0) by ring; apply (CV_mult (fun _ => C) (fun k => / A k) C 0);
      [ apply Un_cv_const | apply Un_cv_recip_0; [ intro k; pose proof (HA k); lra | exact Hinf ] ].
Qed.

(* ================================================================= *)
(*  The recurrence.                                                  *)
(* ================================================================= *)

Theorem Gam_recur : forall s (Hs : 0 < s) (Hs1 : 0 < s + 1),
  Gam (s + 1) Hs1 = s * Gam s Hs.
Proof.
  intros s Hs Hs1.
  set (ek := fun k => / (1 + INR k)).
  set (Ak := fun k => 1 + INR k).
  assert (Hp : forall k, 0 < 1 + INR k) by (intro k; pose proof (pos_INR k); lra).
  assert (Hek0 : forall k, 0 < ek k) by (intro k; unfold ek; apply Rinv_0_lt_compat; apply Hp).
  assert (Hek1 : forall k, ek k <= 1) by (intro k; unfold ek; apply inv_le_1; pose proof (pos_INR k); lra).
  assert (HAk1 : forall k, 1 <= Ak k) by (intro k; unfold Ak; pose proof (pos_INR k); lra).
  assert (HekAk : forall k, ek k <= Ak k) by (intro k; pose proof (Hek1 k); pose proof (HAk1 k); lra).
  assert (Hek_cv : Un_cv ek 0)
    by (unfold ek; apply Un_cv_recip_0; [ intro k; apply Hp | apply cv_infty_1_INR ]).
  assert (HAk_cv : cv_infty Ak) by (unfold Ak; apply cv_infty_1_INR).
  (* the two finite integrals *)
  set (Mint := fun k => RiemannInt (Hf_near (s + 1) 1 (ek k) (Ak k) (Hek0 k) (HekAk k))).
  set (Nint := fun k => RiemannInt (Hf_near s 1 (ek k) (Ak k) (Hek0 k) (HekAk k))).
  (* Mint → Gam(s+1) via Chasles at 1 *)
  assert (HMcv : Un_cv Mint (Gam (s + 1) Hs1)).
  { apply (Un_cv_ext (fun k => rint01 (gnk (s + 1) 1) (Hf_near (s + 1) 1) (ek k)
                             + pint1 (gtk (s + 1) 1) (gtk_int (s + 1) 1) (Ak k))).
    - intro k; unfold Mint.
      pose proof (RiemannInt_P26 (Hf_near (s + 1) 1 (ek k) 1 (Hek0 k) (Hek1 k))
                    (Hf_near (s + 1) 1 1 (Ak k) Rlt_0_1 (HAk1 k))
                    (Hf_near (s + 1) 1 (ek k) (Ak k) (Hek0 k) (HekAk k))) as Hadd.
      rewrite <- Hadd, (rint01_val (gnk (s + 1) 1) (Hf_near (s + 1) 1) (ek k) (Hek0 k) (Hek1 k)).
      f_equal; unfold pint1; apply RiemannInt_P18; [ apply HAk1 | intros t Ht;
        unfold gnk, gtk; rewrite (clamp_id t); [ reflexivity | lra ] ].
    - unfold Gam, mellin; apply CV_plus.
      + unfold gnear; exact (proj2_sig (gnear_sig (s + 1) 1 Hs1 Rlt_0_1) ek Hek0 Hek1 Hek_cv).
      + unfold gtail; exact (proj2_sig (gtail_sig (s + 1) 1 Rlt_0_1) Ak HAk1 HAk_cv). }
  assert (HNcv : Un_cv Nint (Gam s Hs)).
  { apply (Un_cv_ext (fun k => rint01 (gnk s 1) (Hf_near s 1) (ek k)
                             + pint1 (gtk s 1) (gtk_int s 1) (Ak k))).
    - intro k; unfold Nint.
      pose proof (RiemannInt_P26 (Hf_near s 1 (ek k) 1 (Hek0 k) (Hek1 k))
                    (Hf_near s 1 1 (Ak k) Rlt_0_1 (HAk1 k))
                    (Hf_near s 1 (ek k) (Ak k) (Hek0 k) (HekAk k))) as Hadd.
      rewrite <- Hadd, (rint01_val (gnk s 1) (Hf_near s 1) (ek k) (Hek0 k) (Hek1 k)).
      f_equal; unfold pint1; apply RiemannInt_P18; [ apply HAk1 | intros t Ht;
        unfold gnk, gtk; rewrite (clamp_id t); [ reflexivity | lra ] ].
    - unfold Gam, mellin; apply CV_plus.
      + unfold gnear; exact (proj2_sig (gnear_sig s 1 Hs Rlt_0_1) ek Hek0 Hek1 Hek_cv).
      + unfold gtail; exact (proj2_sig (gtail_sig s 1 Rlt_0_1) Ak HAk1 HAk_cv). }
  (* IBP: Mint k - s*Nint k = boundary *)
  assert (Hibp : forall k, Mint k - s * Nint k
                 = Rpower (ek k) s * exp (- ek k) - Rpower (Ak k) s * exp (- Ak k)).
  { intro k.
    set (F := fun t => - (Rpower t s * exp (- t))).
    set (g := fun t => gnk (s + 1) 1 t + - s * gnk s 1 t).
    assert (Hgc : forall t, ek k <= t <= Ak k -> continuity_pt g t).
    { intros t [Ht1 Ht2]; assert (0 < t) by (pose proof (Hek0 k); lra); unfold g;
        apply continuity_pt_plus;
        [ apply cont_gnk; assumption | apply continuity_pt_scal; apply cont_gnk; assumption ]. }
    assert (Hint : Riemann_integrable g (ek k) (Ak k))
      by (apply continuity_implies_RiemannInt; [ apply HekAk | exact Hgc ]).
    assert (Hanti : antiderivative g F (ek k) (Ak k)).
    { split; [ | apply HekAk ]. intros t [Ht1 Ht2].
      assert (Htpos : 0 < t) by (pose proof (Hek0 k); lra).
      assert (Hd : derivable_pt_lim F t (g t)).
      { unfold F, g; pose proof (Gs_deriv s t Htpos) as Hg.
        rewrite (gnk_Sp s t Htpos), (gnk_id s t).
        replace (Rpower t s * exp (- t) + - s * (Rpower t (s - 1) * exp (- t)))
          with (Rpower t s * exp (- t) - s * (Rpower t (s - 1) * exp (- t))) by ring.
        exact Hg. }
      exists (exist (fun l => derivable_pt_lim F t l) (g t) Hd); reflexivity. }
    assert (HFTC : RiemannInt Hint = F (Ak k) - F (ek k))
      by (apply (FTC_antideriv g F (ek k) (Ak k) (HekAk k) Hgc Hint Hanti)).
    assert (Hlin : RiemannInt Hint = Mint k + - s * Nint k)
      by (unfold Mint, Nint;
          exact (RiemannInt_P13 (Hf_near (s + 1) 1 (ek k) (Ak k) (Hek0 k) (HekAk k))
                   (Hf_near s 1 (ek k) (Ak k) (Hek0 k) (HekAk k)) Hint)).
    unfold F in HFTC; rewrite Hlin in HFTC; lra. }
  (* boundary → 0, and left side → Gam(s+1) - s*Gam s *)
  assert (Hbnd : Un_cv (fun k => Mint k - s * Nint k) 0).
  { apply (Un_cv_ext (fun k => Rpower (ek k) s * exp (- ek k)
                             - Rpower (Ak k) s * exp (- Ak k)));
      [ intro k; symmetry; apply Hibp | ].
    replace 0 with (0 - 0) by ring; apply CV_minus;
      [ apply boundary_zero; [ exact Hs | exact Hek0 | exact Hek_cv ]
      | apply boundary_infty; [ exact Hs | exact HAk1 | exact HAk_cv ] ]. }
  assert (Hlim : Un_cv (fun k => Mint k - s * Nint k) (Gam (s + 1) Hs1 - s * Gam s Hs)).
  { apply CV_minus; [ exact HMcv | ].
    apply (CV_mult (fun _ => s) Nint s (Gam s Hs)); [ apply Un_cv_const | exact HNcv ]. }
  assert (Gam (s + 1) Hs1 - s * Gam s Hs = 0)
    by (apply (UL_sequence (fun k => Mint k - s * Nint k)); [ exact Hlim | exact Hbnd ]).
  lra.
Qed.

Print Assumptions Gam_recur.

(* ================================================================= *)
(*  END GammaRecur.v.  Γ(s+1) = s·Γ(s)  (s>0).                        *)
(* ================================================================= *)
