(* ================================================================= *)
(*  IntegrandLip.v  --  midpoint_single, DISCHARGED for the integrand. *)
(*                                                                    *)
(*    gint t x  =  Psi(e^x) . e^{x/4} . cos(t x / 2)                   *)
(*                                                                    *)
(*    gint_midpoint : 0 <= r -> 0 <= c - r -> c + r <= L ->            *)
(*      |int_{c-r}^{c+r} gint t - 2 r . gint t c| <= Mfin r^3 / 3      *)
(*                                                                    *)
(*  Stage 4b/4c join.  MidpointQuad.midpoint_single has been proved    *)
(*  since the quadrature brick; this is the first time its hypotheses  *)
(*  are actually met by the object the sign change needs.  Three       *)
(*  things had to exist first: Psi differentiable (ThetaDeriv, via     *)
(*  CVU), Psi' Lipschitz (ThetaDeriv2, via MVT on the partials), and   *)
(*  those transported into x-space WITHOUT going through the chain     *)
(*  rule on the constants (PsiXDeriv).                                 *)
(*                                                                    *)
(*  Everything here is bookkeeping over LipCalc.  The derivative is a  *)
(*  sum of two products of two factors each, and each factor needs a   *)
(*  bound AND a Lipschitz constant, so the raw obligation is twelve    *)
(*  facts; lip_mult / lip_plus / lip_of_deriv supply the closure and   *)
(*  the only genuinely analytic inputs are DG_bound and DG_lipschitz.  *)
(*                                                                    *)
(*  Mfin is left as an explicit expression in Kg1, Kg2, e^{L/4} and    *)
(*  |t| rather than a numeral, so the node count can be re-derived     *)
(*  when L and t are fixed.  At t = 16, L = ln 5 it is about 190,      *)
(*  against a true max|g''| of 2.5 -- a factor 76, i.e. ~8000          *)
(*  quadrature nodes for a total error of 1e-6.  Axiom-clean.          *)
(* ================================================================= *)

From Stdlib Require Import Reals Ranalysis5 Lra Lia.
Require Import JacobiTheta RiemannPsi ThetaTailSharp PsiXSpace CertifiedPi
        ThetaDerivMajorant ThetaDeriv ThetaDeriv2 PsiXDeriv
        LipCalc MidpointQuad.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  A.  the pieces                                                    *)
(* ----------------------------------------------------------------- *)
Definition Qe   (x : R) : R := exp (/ 4 * x).
Definition Qe'  (x : R) : R := / 4 * Qe x.
Definition Qe'' (x : R) : R := / 4 * Qe' x.

Definition Ct   (t x : R) : R := cos (t / 2 * x).
Definition Ct'  (t x : R) : R := - (t / 2 * sin (t / 2 * x)).
Definition Ct'' (t x : R) : R := - (t / 2 * (t / 2 * cos (t / 2 * x))).

Definition gint  (t x : R) : R := GPsi x * Qe x * Ct t x.
Definition dgint (t x : R) : R :=
  (DG x * Qe x + GPsi x * Qe' x) * Ct t x + GPsi x * Qe x * Ct' t x.

(* --- elementary chain rules --- *)
Lemma dexp_scal : forall a x, derivable_pt_lim (fun s => exp (a * s)) x (a * exp (a * x)).
Proof.
  intros a x.
  assert (H1 : derivable_pt_lim (fun s => a * s) x (a * 1))
    by (apply derivable_pt_lim_scal; apply derivable_pt_lim_id).
  pose proof (derivable_pt_lim_comp (fun s => a * s) exp x (a * 1) (exp (a * x))
                H1 (derivable_pt_lim_exp _)) as Hc.
  replace (a * exp (a * x)) with (exp (a * x) * (a * 1)) by ring. exact Hc.
Qed.

Lemma dsin_scal : forall a x,
  derivable_pt_lim (fun s => sin (a * s)) x (a * cos (a * x)).
Proof.
  intros a x.
  assert (H1 : derivable_pt_lim (fun s => a * s) x (a * 1))
    by (apply derivable_pt_lim_scal; apply derivable_pt_lim_id).
  pose proof (derivable_pt_lim_comp (fun s => a * s) sin x (a * 1) (cos (a * x))
                H1 (derivable_pt_lim_sin _)) as Hc.
  replace (a * cos (a * x)) with (cos (a * x) * (a * 1)) by ring. exact Hc.
Qed.

Lemma dcos_scal : forall a x,
  derivable_pt_lim (fun s => cos (a * s)) x (- (a * sin (a * x))).
Proof.
  intros a x.
  assert (H1 : derivable_pt_lim (fun s => a * s) x (a * 1))
    by (apply derivable_pt_lim_scal; apply derivable_pt_lim_id).
  pose proof (derivable_pt_lim_comp (fun s => a * s) cos x (a * 1) (- sin (a * x))
                H1 (derivable_pt_lim_cos _)) as Hc.
  replace (- (a * sin (a * x))) with (- sin (a * x) * (a * 1)) by ring. exact Hc.
Qed.

Lemma Qe_deriv  : forall x, derivable_pt_lim Qe x (Qe' x).
Proof. intro x. unfold Qe', Qe. apply dexp_scal. Qed.

Lemma Qe'_deriv : forall x, derivable_pt_lim Qe' x (Qe'' x).
Proof.
  intro x. unfold Qe''. apply derivable_pt_lim_scal. apply Qe_deriv.
Qed.

Lemma Ct_deriv  : forall t x, derivable_pt_lim (Ct t) x (Ct' t x).
Proof. intros t x. unfold Ct, Ct'. apply dcos_scal. Qed.

Lemma Ct'_deriv : forall t x, derivable_pt_lim (Ct' t) x (Ct'' t x).
Proof.
  intros t x. unfold Ct'', Ct'.
  apply derivable_pt_lim_opp. apply derivable_pt_lim_scal. apply dsin_scal.
Qed.

(* ----------------------------------------------------------------- *)
(*  B.  bounds on [0, L]                                              *)
(* ----------------------------------------------------------------- *)
(* Psi(e^x) at ITS maximum, x = 0, rather than the crude 1/2.          *)
(* MP = 0.0432 against 0.5 -- another factor 12, and it multiplies the *)
(* (t/2)^2 term of Mfin, which is the dominant one at t = 16.          *)
Definition MP : R := exp (- PI) + exp (- (4 * PI)) + 2 * exp (- (9 * PI)).

Lemma MP_nonneg : 0 <= MP.
Proof.
  unfold MP. pose proof (exp_pos (- PI)). pose proof (exp_pos (- (4 * PI))).
  pose proof (exp_pos (- (9 * PI))). lra.
Qed.

Lemma GPsi_bdd : forall L, BddOn GPsi 0 L MP.
Proof.
  intros L x Hx. destruct Hx as [Hx0 HxL].
  assert (Hu : 1 <= exp x) by (apply exp_ge_1; exact Hx0).
  pose proof PI_RGT_0.
  destruct (Psi_simple (exp x) Hu) as [Hlo Hhi].
  pose proof (Psi_nonneg (exp x)) as Hnn.
  (* each exponential is largest at u = 1 *)
  assert (H1 : exp (- (PI * exp x)) <= exp (- PI))
    by (apply exp_le_compat; nra).
  assert (H2 : exp (- (PI * 4 * exp x)) <= exp (- (4 * PI)))
    by (apply exp_le_compat; nra).
  assert (H3 : exp (- (9 * (PI * exp x))) <= exp (- (9 * PI)))
    by (apply exp_le_compat; nra).
  unfold GPsi, MP. rewrite Rabs_pos_eq by exact Hnn. lra.
Qed.

Lemma DG_bdd : forall L, BddOn DG 0 L Kg1.
Proof. intros L x Hx. apply DG_bound. apply Hx. Qed.

(* ----------------------------------------------------------------- *)
(*  JOINT bounds.  Both products below have their two factors peaking  *)
(*  at OPPOSITE ends of [0, L] -- Psi(e^x) and |DG x| at x = 0, e^{x/4} *)
(*  at x = L -- so bounding them separately pays a spurious factor      *)
(*  e^{L/4} = 1.5 each.  Bounding the product directly costs one line   *)
(*  in each case, because the e^{x/4} growth is dominated many times    *)
(*  over by the e^{-pi e^x} decay: the requirement is only              *)
(*  5x/4 <= pi (e^x - 1), and e^x - 1 >= x already gives 3x.            *)
(* ----------------------------------------------------------------- *)
Lemma DGQe_bdd : forall L, BddOn (fun x => DG x * Qe x) 0 L Kg1.
Proof.
  intros L x Hx. unfold Qe. apply DG_Qe_bound. apply Hx.
Qed.

Lemma GPsi_lip : forall L, LipOn GPsi 0 L Kg1.
Proof.
  intro L. apply (lip_of_deriv GPsi DG 0 L Kg1).
  - intros x Hx. apply GPsi_deriv. apply Hx.
  - apply DG_bdd.
Qed.

Lemma DG_lip : forall L, LipOn DG 0 L Kg2.
Proof.
  intros L x y Hx Hy. apply DG_lipschitz; [ apply Hx | apply Hy ].
Qed.

Lemma Qe_pos : forall x, 0 < Qe x. Proof. intro x. apply exp_pos. Qed.

Lemma GPsiQe_bdd : forall L, BddOn (fun x => GPsi x * Qe x) 0 L MP.
Proof.
  intros L x Hx. destruct Hx as [Hx0 HxL].
  assert (Hu : 1 <= exp x) by (apply exp_ge_1; exact Hx0).
  pose proof PI_lower as HP3.
  destruct (Psi_simple (exp x) Hu) as [_ Hhi].
  pose proof (Psi_nonneg (exp x)) as Hnn.
  assert (Hex : 1 + x <= exp x) by apply exp_ineq1_le.
  (* each exponential absorbs the e^{x/4} and is left at its x = 0 value *)
  assert (Habs : forall d, PI <= d ->
            exp (- (d * exp x)) * exp (/ 4 * x) <= exp (- d)).
  { intros d Hd.
    rewrite <- exp_plus. apply exp_le_compat.
    assert (Hgap : x / 4 <= d * (exp x - 1)).
    { apply Rle_trans with (d * x); [ nra | apply Rmult_le_compat_l; lra ]. }
    lra. }
  assert (A1 : exp (- (PI * exp x)) * exp (/ 4 * x) <= exp (- PI))
    by (apply Habs; lra).
  assert (A2 : exp (- (PI * 4 * exp x)) * exp (/ 4 * x) <= exp (- (4 * PI))).
  { replace (PI * 4) with (4 * PI) by ring. apply Habs; lra. }
  assert (A3 : exp (- (9 * (PI * exp x))) * exp (/ 4 * x) <= exp (- (9 * PI))).
  { replace (9 * (PI * exp x)) with (9 * PI * exp x) by ring.
    apply Habs; lra. }
  assert (Hq : 0 < exp (/ 4 * x)) by apply exp_pos.
  unfold GPsi, Qe, MP.
  rewrite Rabs_pos_eq
    by (apply Rmult_le_pos; [ exact Hnn | lra ]).
  assert (Hmul : Psi (exp x) * exp (/ 4 * x)
              <= (exp (- (PI * exp x)) + exp (- (PI * 4 * exp x))
                  + 2 * exp (- (9 * (PI * exp x)))) * exp (/ 4 * x))
    by (apply Rmult_le_compat_r; lra).
  nra.
Qed.

(* Qe' = (1/4) Qe, so the same joint bound divides through *)
Lemma GPsiQe'_bdd : forall L, BddOn (fun x => GPsi x * Qe' x) 0 L (/ 4 * MP).
Proof.
  intros L x Hx.
  assert (E : GPsi x * Qe' x = / 4 * (GPsi x * Qe x)) by (unfold Qe'; ring).
  rewrite E, Rabs_mult, (Rabs_pos_eq (/ 4)) by lra.
  apply Rmult_le_compat_l; [ lra | exact (GPsiQe_bdd L x Hx) ].
Qed.

Lemma Qe_bdd : forall L, BddOn Qe 0 L (exp (/ 4 * L)).
Proof.
  intros L x Hx. unfold Qe. rewrite Rabs_pos_eq by (left; apply exp_pos).
  apply exp_le_compat. destruct Hx. lra.
Qed.

Lemma Qe'_bdd : forall L, BddOn Qe' 0 L (/ 4 * exp (/ 4 * L)).
Proof.
  intros L x Hx. unfold Qe'.
  rewrite Rabs_pos_eq by (left; apply Rmult_lt_0_compat; [ lra | apply Qe_pos ]).
  apply Rmult_le_compat_l; [ lra | ].
  pose proof (Qe_bdd L x Hx) as H. rewrite Rabs_pos_eq in H by (left; apply Qe_pos).
  exact H.
Qed.

Lemma Qe''_bdd : forall L, BddOn Qe'' 0 L (/ 16 * exp (/ 4 * L)).
Proof.
  intros L x Hx. unfold Qe''.
  assert (H := Qe'_bdd L x Hx).
  rewrite Rabs_mult, Rabs_pos_eq in * by lra.
  replace (/ 16 * exp (/ 4 * L)) with (/ 4 * (/ 4 * exp (/ 4 * L))) by field.
  apply Rmult_le_compat_l; [ lra | exact H ].
Qed.

Lemma Qe_lip : forall L, LipOn Qe 0 L (/ 4 * exp (/ 4 * L)).
Proof.
  intro L. apply (lip_of_deriv Qe Qe' 0 L).
  - intros x _. apply Qe_deriv.
  - apply Qe'_bdd.
Qed.

Lemma Qe'_lip : forall L, LipOn Qe' 0 L (/ 16 * exp (/ 4 * L)).
Proof.
  intro L. apply (lip_of_deriv Qe' Qe'' 0 L).
  - intros x _. apply Qe'_deriv.
  - apply Qe''_bdd.
Qed.

Lemma Rabs_half : forall t, Rabs (t / 2) = Rabs t / 2.
Proof.
  intro t. unfold Rdiv. rewrite Rabs_mult, (Rabs_pos_eq (/ 2)) by lra. reflexivity.
Qed.

Lemma abs_cos_le1 : forall x, Rabs (cos x) <= 1.
Proof. intro x. apply Rabs_le. pose proof (COS_bound x). lra. Qed.

Lemma abs_sin_le1 : forall x, Rabs (sin x) <= 1.
Proof. intro x. apply Rabs_le. pose proof (SIN_bound x). lra. Qed.

Lemma Ct_bdd : forall t L, BddOn (Ct t) 0 L 1.
Proof. intros t L x _. unfold Ct. apply abs_cos_le1. Qed.

Lemma Ct'_bdd : forall t L, BddOn (Ct' t) 0 L (Rabs t / 2).
Proof.
  intros t L x _. unfold Ct'. rewrite Rabs_Ropp, Rabs_mult, Rabs_half.
  pose proof (abs_sin_le1 (t / 2 * x)) as Hs.
  pose proof (Rabs_pos t).
  assert (0 <= Rabs t / 2) by lra. nra.
Qed.

Lemma Ct''_bdd : forall t L, BddOn (Ct'' t) 0 L (Rabs t / 2 * (Rabs t / 2)).
Proof.
  intros t L x _. unfold Ct''.
  rewrite Rabs_Ropp, Rabs_mult, Rabs_mult, Rabs_half.
  pose proof (abs_cos_le1 (t / 2 * x)) as Hc.
  pose proof (Rabs_pos t). pose proof (Rabs_pos (cos (t / 2 * x))).
  assert (0 <= Rabs t / 2) by lra. nra.
Qed.

Lemma Ct_lip : forall t L, LipOn (Ct t) 0 L (Rabs t / 2).
Proof.
  intros t L. apply (lip_of_deriv (Ct t) (Ct' t) 0 L).
  - intros x _. apply Ct_deriv.
  - apply Ct'_bdd.
Qed.

Lemma Ct'_lip : forall t L, LipOn (Ct' t) 0 L (Rabs t / 2 * (Rabs t / 2)).
Proof.
  intros t L. apply (lip_of_deriv (Ct' t) (Ct'' t) 0 L).
  - intros x _. apply Ct'_deriv.
  - apply Ct''_bdd.
Qed.

(* ----------------------------------------------------------------- *)
(*  C.  the derivative of the integrand                               *)
(* ----------------------------------------------------------------- *)
Lemma gint_deriv : forall t x, 0 <= x -> derivable_pt_lim (gint t) x (dgint t x).
Proof.
  intros t x Hx.
  assert (HP : derivable_pt_lim (fun s => GPsi s * Qe s) x
                 (DG x * Qe x + GPsi x * Qe' x))
    by (apply derivable_pt_lim_mult;
        [ apply GPsi_deriv; exact Hx | apply Qe_deriv ]).
  pose proof (derivable_pt_lim_mult (fun s => GPsi s * Qe s) (Ct t) x
                (DG x * Qe x + GPsi x * Qe' x) (Ct' t x)
                HP (Ct_deriv t x)) as Hm.
  unfold gint, dgint. exact Hm.
Qed.

Lemma gint_cont : forall t x, 0 <= x -> continuity_pt (gint t) x.
Proof.
  intros t x Hx. apply derivable_continuous_pt.
  exists (dgint t x). apply gint_deriv; exact Hx.
Qed.

Theorem gint_RI : forall t a b, 0 <= a -> a <= b -> Riemann_integrable (gint t) a b.
Proof.
  intros t a b Ha Hab. apply continuity_implies_RiemannInt; [ exact Hab | ].
  intros x Hx. apply gint_cont. lra.
Qed.

(* ----------------------------------------------------------------- *)
(*  D.  the Lipschitz constant of the derivative                      *)
(* ----------------------------------------------------------------- *)
Definition EL (L : R) : R := exp (/ 4 * L).
Definition Tt (t : R) : R := Rabs t / 2.

(* SB bounds the integrand's first derivative-factor (GPsi.Qe)', and   *)
(* doubles as the Lipschitz constant of GPsi.Qe -- via lip_of_deriv    *)
(* rather than the product rule, which is both sharper and shorter.    *)
Definition SB (L : R) : R := Kg1 + / 4 * MP.
Definition SL (L : R) : R :=
  (Kg1 * (/ 4 * EL L) + EL L * Kg2) + / 4 * SB L.

Definition Mfin (t L : R) : R :=
  (SB L * Tt t + 1 * SL L) + (MP * (Tt t * Tt t) + Tt t * SB L).

Lemma EL_pos : forall L, 0 < EL L. Proof. intro L. apply exp_pos. Qed.
Lemma Tt_nonneg : forall t, 0 <= Tt t.
Proof. intro t. unfold Tt. pose proof (Rabs_pos t). lra. Qed.

Lemma SB_nonneg : forall L, 0 <= SB L.
Proof. intro L. unfold SB. pose proof Kg1_nonneg. pose proof MP_nonneg. lra. Qed.

Lemma SL_nonneg : forall L, 0 <= SL L.
Proof.
  intro L. unfold SL. pose proof Kg1_nonneg. pose proof Kg2_nonneg.
  pose proof (EL_pos L). pose proof (SB_nonneg L).
  assert (0 <= Kg1 * (/ 4 * EL L)) by (apply Rmult_le_pos; lra).
  assert (0 <= EL L * Kg2) by (apply Rmult_le_pos; lra).
  lra.
Qed.

Lemma Mfin_nonneg : forall t L, 0 <= Mfin t L.
Proof.
  intros t L. unfold Mfin.
  pose proof (Tt_nonneg t). pose proof MP_nonneg.
  pose proof (SB_nonneg L). pose proof (SL_nonneg L).
  assert (0 <= SB L * Tt t) by (apply Rmult_le_pos; lra).
  assert (0 <= MP * (Tt t * Tt t))
    by (apply Rmult_le_pos; [ lra | apply Rmult_le_pos; lra ]).
  assert (0 <= Tt t * SB L) by (apply Rmult_le_pos; lra).
  lra.
Qed.

Theorem dgint_lip : forall t L, LipOn (dgint t) 0 L (Mfin t L).
Proof.
  intros t L.
  pose proof (EL_pos L) as HE. pose proof (Tt_nonneg t) as HT.
  pose proof Kg1_nonneg as HK1. pose proof Kg2_nonneg as HK2.
  pose proof MP_nonneg as HMP.
  pose proof (SB_nonneg L) as HSB. pose proof (SL_nonneg L) as HSL.
  assert (HQ  : 0 <= EL L) by lra.
  assert (HQ' : 0 <= / 4 * EL L) by lra.
  (* DG * Qe : JOINTLY bounded by Kg1, no e^{L/4} factor *)
  assert (HA_b : BddOn (fun x => DG x * Qe x) 0 L Kg1) by apply DGQe_bdd.
  assert (HA_l : LipOn (fun x => DG x * Qe x) 0 L
                   (Kg1 * (/ 4 * EL L) + EL L * Kg2)).
  { apply lip_mult; try assumption; try lra.
    - apply DG_bdd.
    - apply Qe_bdd.
    - apply DG_lip.
    - apply Qe_lip. }
  (* GPsi * Qe' : jointly bounded by MP/4 *)
  assert (HB_b : BddOn (fun x => GPsi x * Qe' x) 0 L (/ 4 * MP))
    by apply GPsiQe'_bdd.
  (* GPsi * Qe : jointly bounded by MP *)
  assert (HP_b : BddOn (fun x => GPsi x * Qe x) 0 L MP) by apply GPsiQe_bdd.
  (* (GPsi.Qe)' = DG.Qe + GPsi.Qe', bounded by SB *)
  assert (HS_b : BddOn (fun x => DG x * Qe x + GPsi x * Qe' x) 0 L (SB L)).
  { unfold SB. apply bdd_plus; assumption. }
  (* hence GPsi.Qe is Lipschitz with constant SB -- via the DERIVATIVE, *)
  (* not the product rule: sharper, and it reuses HS_b for free.        *)
  assert (HP_l : LipOn (fun x => GPsi x * Qe x) 0 L (SB L)).
  { apply (lip_of_deriv _ (fun x => DG x * Qe x + GPsi x * Qe' x) 0 L).
    - intros y Hy. apply derivable_pt_lim_mult;
        [ apply GPsi_deriv; apply Hy | apply Qe_deriv ].
    - exact HS_b. }
  (* GPsi * Qe' = (1/4) (GPsi * Qe), so its Lipschitz constant divides *)
  assert (HB_l : LipOn (fun x => GPsi x * Qe' x) 0 L (/ 4 * SB L)).
  { intros y z Hy Hz.
    assert (Ey : GPsi y * Qe' y = / 4 * (GPsi y * Qe y)) by (unfold Qe'; ring).
    assert (Ez : GPsi z * Qe' z = / 4 * (GPsi z * Qe z)) by (unfold Qe'; ring).
    rewrite Ey, Ez.
    replace (/ 4 * (GPsi y * Qe y) - / 4 * (GPsi z * Qe z))
      with (/ 4 * (GPsi y * Qe y - GPsi z * Qe z)) by ring.
    rewrite Rabs_mult, (Rabs_pos_eq (/ 4)) by lra.
    assert (H := HP_l y z Hy Hz).
    replace (/ 4 * SB L * Rabs (y - z)) with (/ 4 * (SB L * Rabs (y - z)))
      by ring.
    apply Rmult_le_compat_l; lra. }
  assert (HS_l : LipOn (fun x => DG x * Qe x + GPsi x * Qe' x) 0 L (SL L)).
  { unfold SL. apply lip_plus; assumption. }
  (* assemble *)
  unfold dgint, Mfin.
  apply lip_plus.
  - apply lip_mult with (M1 := SB L) (M2 := 1); try assumption; try nra.
    + apply Ct_bdd.
    + apply Ct_lip.
  - apply lip_mult with (M1 := MP) (M2 := Tt t); try assumption; try nra.
    + apply Ct'_bdd.
    + apply Ct'_lip.
Qed.

(* ----------------------------------------------------------------- *)
(*  E.  midpoint_single, DISCHARGED                                   *)
(* ----------------------------------------------------------------- *)
Theorem gint_midpoint : forall t L c r
  (prf : Riemann_integrable (gint t) (c - r) (c + r)),
  0 <= r -> 0 <= c - r -> c + r <= L ->
  Rabs (RiemannInt prf - 2 * r * gint t c) <= Mfin t L * r ^ 3 / 3.
Proof.
  intros t L c r prf Hr Hlo Hhi.
  apply (midpoint_single (gint t) (dgint t) c (Mfin t L) r prf).
  - exact Hr.
  - apply Mfin_nonneg.
  - intros y Hy. apply gint_deriv. lra.
  - intros y z Hy Hz. apply (dgint_lip t L); split; lra.
Qed.

Print Assumptions dgint_lip.
Print Assumptions gint_RI.
Print Assumptions gint_midpoint.
