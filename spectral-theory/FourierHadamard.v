(* ================================================================= *)
(*  FourierHadamard.v  —  the smooth Hadamard factor of the localiser. *)
(*                                                                    *)
(*  For the 2π-periodic C² representative ftil, the removable-          *)
(*  singularity factor of the localiser is                            *)
(*     had y = ∫₀¹ ftil'(s·y) ds   (= (ftil y − ftil 0)/y for y≠0),    *)
(*  which is globally C¹:                                             *)
(*    • had_id : had y · y = ftil y − ftil 0   (FTC);                  *)
(*    • had' y = ∫₀¹ s·ftil''(s·y) ds, via the LOCAL bounded-interval  *)
(*      Leibniz rule, whose second-order remainder is the Taylor       *)
(*      bound |ftil'(a+k)−ftil'(a)−k ftil''(a)| ≤ L k² coming from      *)
(*      ftil'' Lipschitz (ftil2_lip) through one MVT;                  *)
(*    • had' is continuous (Lipschitz under the integral).            *)
(*  Packaged as hadC1 : C1_fun.  No new axioms (classical Reals only). *)
(* ================================================================= *)

From Stdlib Require Import Reals Ranalysis5 FunctionalExtensionality Lra Lia.
Require Import JacobiTheta GaussPeriodDeriv2 GaussPeriodLip
        GaussFull GaussPiValue ContinuousCoV LeibnizInterval.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  Generic helpers.                                                 *)
(* ----------------------------------------------------------------- *)

Lemma abs_le_interval : forall a b, Rabs a <= b -> - b <= a <= b.
Proof.
  intros a b H; pose proof (Rle_abs a); pose proof (Rle_abs (- a));
    rewrite Rabs_Ropp in *; lra.
Qed.

Lemma loclip_cont : forall (f : R -> R) (u L d : R), 0 <= L -> 0 < d ->
  (forall x, Rabs (x - u) < d -> Rabs (f x - f u) <= L * Rabs (x - u)) ->
  continuity_pt f u.
Proof.
  intros f u L d HL Hd Hlip eps He.
  exists (Rmin d (eps / (L + 1))); split.
  - apply Rmin_pos; [ exact Hd | apply Rdiv_lt_0_compat; lra ].
  - intros x [_ Hdist]; simpl in Hdist; unfold R_dist in *.
    assert (Hxd : Rabs (x - u) < d) by (eapply Rlt_le_trans; [ exact Hdist | apply Rmin_l ]).
    assert (Hxe : Rabs (x - u) < eps / (L + 1)) by (eapply Rlt_le_trans; [ exact Hdist | apply Rmin_r ]).
    eapply Rle_lt_trans; [ apply Hlip; exact Hxd | ].
    apply Rle_lt_trans with ((L + 1) * Rabs (x - u));
      [ apply Rmult_le_compat_r; [ apply Rabs_pos | lra ] | ].
    pose proof (Rmult_lt_compat_l (L + 1) (Rabs (x - u)) (eps / (L + 1)) ltac:(lra) Hxe) as Hm.
    replace ((L + 1) * (eps / (L + 1))) with eps in Hm by (field; lra); exact Hm.
Qed.

Section Had.

Variable t : R.
Hypothesis Ht : 0 < t.

(* d/ds (s·y) = y *)
Lemma dlin : forall y s, derivable_pt_lim (fun s => s * y) s y.
Proof.
  intros y s.
  pose proof (derivable_pt_lim_mult (fun s0 => s0) (fun _ => y) s 1 0
                (derivable_pt_lim_id s) (derivable_pt_lim_const y s)) as Hm.
  cbv beta in Hm; replace (1 * y + s * 0) with y in Hm by ring.
  unfold mult_fct in Hm; exact Hm.
Qed.

Lemma ftil2_cont : continuity (ftil2 t Ht).
Proof.
  intro u.
  destruct (ftil2_lip t Ht (Rabs u + 1) ltac:(pose proof (Rabs_pos u); lra)) as [L [HL0 HLip]].
  apply (loclip_cont (ftil2 t Ht) u L 1 HL0 Rlt_0_1).
  intros x Hx; apply HLip.
  - apply abs_le_interval.
    replace x with ((x - u) + u) by ring; eapply Rle_trans; [ apply Rabs_triang | lra ].
  - apply abs_le_interval; lra.
Qed.

(* --- continuity of the integrands --- *)

Lemma cont_ftil1_lin : forall y, continuity (fun s => ftil1 t Ht (s * y)).
Proof.
  intros y s; apply (continuity_pt_comp (fun s => s * y) (ftil1 t Ht) s).
  - apply continuity_pt_mult;
      [ apply derivable_continuous_pt; exists 1; apply derivable_pt_lim_id
      | apply continuity_pt_const; intros a b; reflexivity ].
  - apply ftil1_cont.
Qed.

Lemma cont_ftil2_lin : forall y, continuity (fun s => ftil2 t Ht (s * y)).
Proof.
  intros y s; apply (continuity_pt_comp (fun s => s * y) (ftil2 t Ht) s).
  - apply continuity_pt_mult;
      [ apply derivable_continuous_pt; exists 1; apply derivable_pt_lim_id
      | apply continuity_pt_const; intros a b; reflexivity ].
  - apply ftil2_cont.
Qed.

Lemma cont_hd : forall y, continuity (fun s => s * ftil2 t Ht (s * y)).
Proof.
  intros y s; apply continuity_pt_mult;
    [ apply derivable_continuous_pt; exists 1; apply derivable_pt_lim_id | apply cont_ftil2_lin ].
Qed.

Lemma cont_scal : forall y, continuity (fun s => y * ftil1 t Ht (s * y)).
Proof.
  intros y s; apply (continuity_pt_scal (fun s => ftil1 t Ht (s * y)) y s); apply cont_ftil1_lin.
Qed.

Lemma cont_sq2 : continuity (fun s : R => s ^ 2).
Proof.
  intros s; apply (continuity_pt_mult (fun z => z) (fun z => z * 1) s);
    [ apply derivable_continuous_pt; exists 1; apply derivable_pt_lim_id | ].
  apply continuity_pt_mult;
    [ apply derivable_continuous_pt; exists 1; apply derivable_pt_lim_id
    | apply continuity_pt_const; intros a b; reflexivity ].
Qed.

Lemma pr_had : forall y, Riemann_integrable (fun s => ftil1 t Ht (s * y)) 0 1.
Proof. intro y; apply continuity_implies_RiemannInt; [ apply Rle_0_1 | intros x _; apply cont_ftil1_lin ]. Qed.
Lemma pr_hd : forall y, Riemann_integrable (fun s => s * ftil2 t Ht (s * y)) 0 1.
Proof. intro y; apply continuity_implies_RiemannInt; [ apply Rle_0_1 | intros x _; apply cont_hd ]. Qed.
Lemma pr_scal : forall y, Riemann_integrable (fun s => y * ftil1 t Ht (s * y)) 0 1.
Proof. intro y; apply continuity_implies_RiemannInt; [ apply Rle_0_1 | intros x _; apply cont_scal ]. Qed.

Definition had (y : R) : R := RiemannInt (pr_had y).
Definition had' (y : R) : R := RiemannInt (pr_hd y).

(* --- had y · y = ftil y − ftil 0  (FTC) --- *)

Lemma had_id : forall y, had y * y = ftil t Ht y - ftil t Ht 0.
Proof.
  intro y.
  assert (Hanti : antiderivative (fun s => y * ftil1 t Ht (s * y)) (fun s => ftil t Ht (s * y)) 0 1).
  { split; [ | apply Rle_0_1 ]. intros s Hs.
    pose proof (derivable_pt_lim_comp (fun s0 => s0 * y) (ftil t Ht) s y (ftil1 t Ht (s * y))
                  (dlin y s) (ftil_C1 t Ht (s * y))) as Hc.
    replace (ftil1 t Ht (s * y) * y) with (y * ftil1 t Ht (s * y)) in Hc by ring.
    exists (exist _ (y * ftil1 t Ht (s * y)) Hc); reflexivity. }
  assert (Hftc : RiemannInt (pr_scal y) = ftil t Ht y - ftil t Ht 0).
  { rewrite (FTC_antideriv (fun s => y * ftil1 t Ht (s * y)) (fun s => ftil t Ht (s * y)) 0 1 Rle_0_1
               (fun x _ => cont_scal y x) (pr_scal y) Hanti).
    replace (1 * y) with y by ring; replace (0 * y) with 0 by ring; reflexivity. }
  assert (Hscal : RiemannInt (pr_scal y) = y * had y)
    by (unfold had; apply (RInt_scal_cont (fun s => ftil1 t Ht (s * y)) y 0 1 Rle_0_1
          (cont_ftil1_lin y) (pr_had y) (pr_scal y))).
  rewrite <- Hftc, Hscal; ring.
Qed.

(* --- the Taylor bound from ftil'' Lipschitz (one MVT) --- *)

Lemma taylor2 : forall (L a k lo hi : R), 0 <= L ->
  lo <= a <= hi -> lo <= a + k <= hi ->
  (forall p q, lo <= p <= hi -> lo <= q <= hi ->
     Rabs (ftil2 t Ht p - ftil2 t Ht q) <= L * Rabs (p - q)) ->
  Rabs (ftil1 t Ht (a + k) - ftil1 t Ht a - k * ftil2 t Ht a) <= L * k ^ 2.
Proof.
  intros L a k lo hi HL0 Ha Hak HLip.
  set (pr := fun x => exist (fun l => derivable_pt_lim (ftil1 t Ht) x l)
                        (ftil2 t Ht x) (ftil_C2 t Ht x) : derivable_pt (ftil1 t Ht) x).
  destruct (Req_dec k 0) as [-> | Hk].
  - replace (a + 0) with a by ring;
      replace (ftil1 t Ht a - ftil1 t Ht a - 0 * ftil2 t Ht a) with 0 by ring;
      rewrite Rabs_R0; replace (0 ^ 2) with 0 by ring; rewrite Rmult_0_r; apply Rle_refl.
  - assert (Hc : exists c, ftil1 t Ht (a + k) - ftil1 t Ht a = ftil2 t Ht c * k
                           /\ lo <= c <= hi /\ Rabs (c - a) <= Rabs k).
    { destruct (Rdichotomy k 0 Hk) as [Hneg | Hpos].
      - assert (Hlt : a + k < a) by lra.
        destruct (MVT_cor1 (ftil1 t Ht) (a + k) a pr Hlt) as [c [Hc [Hc1 Hc2]]].
        assert (Hd : derive_pt (ftil1 t Ht) c (pr c) = ftil2 t Ht c) by reflexivity.
        rewrite Hd in Hc; exists c; repeat split;
          [ replace (a - (a + k)) with (- k) in Hc by ring; lra
          | lra | lra | rewrite Rabs_left1 by lra; rewrite (Rabs_left k) by lra; lra ].
      - assert (Hlt : a < a + k) by lra.
        destruct (MVT_cor1 (ftil1 t Ht) a (a + k) pr Hlt) as [c [Hc [Hc1 Hc2]]].
        assert (Hd : derive_pt (ftil1 t Ht) c (pr c) = ftil2 t Ht c) by reflexivity.
        rewrite Hd in Hc; exists c; repeat split;
          [ replace (a + k - a) with k in Hc by ring; lra
          | lra | lra | rewrite Rabs_right by lra; rewrite (Rabs_right k) by lra; lra ]. }
    destruct Hc as [c [Heq [Hcin Hcd]]].
    replace (ftil1 t Ht (a + k) - ftil1 t Ht a - k * ftil2 t Ht a)
      with (k * (ftil2 t Ht c - ftil2 t Ht a)) by (rewrite Heq; ring).
    rewrite Rabs_mult.
    apply Rle_trans with (Rabs k * (L * Rabs (c - a))).
    + apply Rmult_le_compat_l; [ apply Rabs_pos | apply HLip; [ exact Hcin | exact Ha ] ].
    + apply Rle_trans with (Rabs k * (L * Rabs k)).
      * apply Rmult_le_compat_l; [ apply Rabs_pos | apply Rmult_le_compat_l; [ exact HL0 | exact Hcd ] ].
      * apply Req_le; rewrite <- Rsqr_pow2, Rsqr_abs; unfold Rsqr; ring.
Qed.

(* --- had' y is the derivative of had (local Leibniz) --- *)

Lemma had_deriv : forall y, derivable_pt_lim had y (had' y).
Proof.
  intro y.
  destruct (ftil2_lip t Ht (Rabs y + 1) ltac:(pose proof (Rabs_pos y); lra)) as [L [HL0 HLip]].
  apply (leibniz_interval_local (fun v s => ftil1 t Ht (s * v)) (fun w s => s * ftil2 t Ht (s * w))
           (fun s => L * s ^ 2) 0 1 y (mkposreal 1 Rlt_0_1) Rle_0_1).
  - intro v; apply cont_ftil1_lin.
  - apply cont_hd.
  - intro s; apply (continuity_pt_scal (fun s => s ^ 2) L s); apply cont_sq2.
  - intros x _; apply Rmult_le_pos; [ exact HL0 | rewrite <- Rsqr_pow2; apply Rle_0_sqr ].
  - intros h s Hh [Hs0 Hs1]; simpl in Hh.
    replace (s * (y + h)) with (s * y + s * h) by ring.
    replace (h * (s * ftil2 t Ht (s * y))) with (s * h * ftil2 t Ht (s * y)) by ring.
    assert (Habsy : Rabs (s * y) <= Rabs y + 1)
      by (rewrite Rabs_mult, (Rabs_right s) by lra; pose proof (Rabs_pos y);
          apply Rle_trans with (1 * Rabs y); [ apply Rmult_le_compat_r; [ apply Rabs_pos | lra ] | lra ]).
    assert (Habsyh : Rabs (s * y + s * h) <= Rabs y + 1).
    { replace (s * y + s * h) with (s * (y + h)) by ring.
      rewrite Rabs_mult, (Rabs_right s) by lra.
      apply Rle_trans with (1 * Rabs (y + h)); [ apply Rmult_le_compat_r; [ apply Rabs_pos | lra ] | ].
      rewrite Rmult_1_l; eapply Rle_trans; [ apply Rabs_triang | pose proof (Rabs_pos y); lra ]. }
    eapply Rle_trans;
      [ apply (taylor2 L (s * y) (s * h) (- (Rabs y + 1)) (Rabs y + 1) HL0
                 (abs_le_interval _ _ Habsy) (abs_le_interval _ _ Habsyh) HLip) | ].
    apply Req_le; ring.
Qed.

Lemma had_cont : continuity had.
Proof. intro y; apply derivable_continuous_pt; exists (had' y); apply had_deriv. Qed.

(* --- had' is continuous (Lipschitz under the integral) --- *)

Lemma had'_cont : continuity had'.
Proof.
  intro y0.
  destruct (ftil2_lip t Ht (Rabs y0 + 1) ltac:(pose proof (Rabs_pos y0); lra)) as [L [HL0 HLip]].
  assert (Hsq : Riemann_integrable (fun s => s ^ 2) 0 1)
    by (apply continuity_implies_RiemannInt; [ apply Rle_0_1 | intros x _; apply cont_sq2 ]).
  apply (loclip_cont had' y0 (L * RiemannInt Hsq) 1);
    [ apply Rmult_le_pos;
        [ exact HL0 | apply (nonneg_int (fun s => s ^ 2) 0 1 Hsq); [ apply Rle_0_1 | intros x _;
          rewrite <- Rsqr_pow2; apply Rle_0_sqr ] ]
    | apply Rlt_0_1 | ].
  intros y Hy; unfold had'.
  set (dd := fun s => s * ftil2 t Ht (s * y) - s * ftil2 t Ht (s * y0)).
  assert (prdd : Riemann_integrable dd 0 1)
    by (apply continuity_implies_RiemannInt; [ apply Rle_0_1 | intros x _; unfold dd;
        apply continuity_pt_minus; apply cont_hd ]).
  assert (Hlin : RiemannInt (pr_hd y) - RiemannInt (pr_hd y0) = RiemannInt prdd).
  { assert (prg : Riemann_integrable
                    (fun s => s * ftil2 t Ht (s * y) + (-1) * (s * ftil2 t Ht (s * y0))) 0 1)
      by (apply continuity_implies_RiemannInt; [ apply Rle_0_1 | intros x _;
          apply continuity_pt_plus; [ apply cont_hd
          | apply (continuity_pt_scal (fun s => s * ftil2 t Ht (s * y0)) (-1) x); apply cont_hd ] ]).
    pose proof (RiemannInt_P13 (pr_hd y) (pr_hd y0) prg) as HP.
    assert (Hdg : RiemannInt prdd = RiemannInt prg)
      by (apply RiemannInt_P18; [ apply Rle_0_1 | intros x _; unfold dd; ring ]).
    rewrite Hdg, HP; ring. }
  assert (prTM : Riemann_integrable (fun s => Rabs (y - y0) * (L * s ^ 2)) 0 1)
    by (apply continuity_implies_RiemannInt; [ apply Rle_0_1 | intros x _;
        apply (continuity_pt_scal (fun s => L * s ^ 2) (Rabs (y - y0)) x);
        apply (continuity_pt_scal (fun s => s ^ 2) L x); apply cont_sq2 ]).
  rewrite Hlin.
  apply Rle_trans with (RiemannInt (RiemannInt_P16 prdd)); [ apply RiemannInt_P17; apply Rle_0_1 | ].
  apply Rle_trans with (RiemannInt prTM).
  - apply RiemannInt_P19; [ apply Rle_0_1 | intros s [Hs0 Hs1]; unfold dd ].
    replace (s * ftil2 t Ht (s * y) - s * ftil2 t Ht (s * y0))
      with (s * (ftil2 t Ht (s * y) - ftil2 t Ht (s * y0))) by ring.
    rewrite Rabs_mult, (Rabs_right s) by lra.
    apply Rle_trans with (s * (L * Rabs (s * y - s * y0))).
    + apply Rmult_le_compat_l; [ lra | apply HLip ].
      * apply abs_le_interval; rewrite Rabs_mult, (Rabs_right s) by lra.
        apply Rle_trans with (1 * Rabs y); [ apply Rmult_le_compat_r; [ apply Rabs_pos | lra ] | ].
        replace y with ((y - y0) + y0) by ring; eapply Rle_trans; [ rewrite Rmult_1_l; apply Rabs_triang | lra ].
      * apply abs_le_interval; rewrite Rabs_mult, (Rabs_right s) by lra.
        apply Rle_trans with (1 * Rabs y0); [ apply Rmult_le_compat_r; [ apply Rabs_pos | lra ] | lra ].
    + replace (Rabs (y - y0) * (L * s ^ 2)) with (s * (L * (s * Rabs (y - y0)))) by (unfold Rdiv; ring).
      apply Rmult_le_compat_l; [ lra | ].
      apply Rmult_le_compat_l; [ exact HL0 | ].
      replace (s * y - s * y0) with (s * (y - y0)) by ring.
      rewrite Rabs_mult, (Rabs_right s) by lra; apply Rle_refl.
  - assert (prLsq : Riemann_integrable (fun s => L * s ^ 2) 0 1)
      by (apply continuity_implies_RiemannInt; [ apply Rle_0_1 | intros x _;
          apply (continuity_pt_scal (fun s => s ^ 2) L x); apply cont_sq2 ]).
    rewrite (RInt_scal_cont (fun s => L * s ^ 2) (Rabs (y - y0)) 0 1 Rle_0_1
              (fun s => continuity_pt_scal (fun z => z ^ 2) L s (cont_sq2 s)) prLsq prTM).
    rewrite (RInt_scal_cont (fun s => s ^ 2) L 0 1 Rle_0_1 cont_sq2 Hsq prLsq).
    apply Req_le; ring.
Qed.

Definition hadC1 : C1_fun :=
  mkC1 (c1 := had) (diff0 := fun y => exist _ (had' y) (had_deriv y)) had'_cont.

Lemma hadC1_val : forall y, hadC1 y = had y.
Proof. reflexivity. Qed.

End Had.

Print Assumptions had_id.
Print Assumptions had_deriv.

(* ================================================================= *)
(*  END FourierHadamard.v                                            *)
(*  had (=hadC1) is a global C1_fun with had·y = ftil y − ftil 0 and   *)
(*  had' y = ∫₀¹ s ftil''(s y) ds.  The removable-singularity numerator *)
(*  factor of the localiser is in place.                             *)
(* ================================================================= *)
