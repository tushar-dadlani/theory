(* ================================================================= *)
(*  CLeibniz.v  —  Milestone C, brick C2d Block 4: differentiation      *)
(*  under the finite C-integral (Leibniz rule).                         *)
(*                                                                    *)
(*  Given a uniform-in-θ first-order estimate on φ(r,θ), the parametric  *)
(*  integral r ↦ ∫_a^b φ(r,θ)dθ is (componentwise) differentiable with   *)
(*  derivative ∫_a^b ∂_r φ(r0,θ)dθ.  Pure Cintf linearity + the ML       *)
(*  bound — no topology.  The uniform estimate is supplied by C2d's      *)
(*  caller (CCauchyFormula, via seg-FTC + arc_Fp_unifcont).             *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import ComplexField Cmodulus CImproperIntegral CSeries CIntegral2
        CSegInt CGoursatLin.
Open Scope R_scope.

(* ---- RiemannInt scaling and subtraction (mirroring RInt_plus) ---- *)
Lemma RInt_scal : forall (u : R -> R) (c a b : R)
  (pu : Riemann_integrable u a b)
  (pcu : Riemann_integrable (fun x => c * u x) a b),
  a <= b -> RiemannInt pcu = c * RiemannInt pu.
Proof.
  intros u c a b pu pcu Hab.
  pose (p0 := RiemannInt_P14 a b 0).
  rewrite (RiemannInt_P18 pcu (RiemannInt_P10 c p0 pu) Hab
             ltac:(intros x _; unfold fct_cte; cbv beta; ring)).
  rewrite (RiemannInt_P13 p0 pu (RiemannInt_P10 c p0 pu)).
  rewrite (RiemannInt_P15 p0); ring.
Qed.

Lemma RInt_sub : forall (g1 g2 : R -> R) (a b : R)
  (pr1 : Riemann_integrable g1 a b) (pr2 : Riemann_integrable g2 a b)
  (pr : Riemann_integrable (fun x => g1 x - g2 x) a b),
  a <= b -> RiemannInt pr = RiemannInt pr1 - RiemannInt pr2.
Proof.
  intros g1 g2 a b pr1 pr2 pr Hab.
  rewrite (RiemannInt_P18 pr (RiemannInt_P10 (-1) pr1 pr2) Hab
             ltac:(intros x _; cbv beta; ring)).
  rewrite (RiemannInt_P13 pr1 pr2 (RiemannInt_P10 (-1) pr1 pr2)); ring.
Qed.

(* ---- Cintf: pull out a complex constant, and subtract ---- *)
Lemma Cintf_cmul_l : forall k g (Hg : Ccont g)
  (Hkg : Ccont (fun u => Cmul k (g u))) a b, a <= b ->
  Cintf (fun u => Cmul k (g u)) Hkg a b = Cmul k (Cintf g Hg a b).
Proof.
  intros k g Hg Hkg a b Hab; apply Ceq; unfold Cintf; cbn [Re Im].
  - etransitivity.
    { apply (RInt_sub (fun x => Re k * Re (g x)) (fun x => Im k * Im (g x)) a b
               (Riemann_integrable_scal (Re k) (cont_RI _ (proj1 Hg) a b))
               (Riemann_integrable_scal (Im k) (cont_RI _ (proj2 Hg) a b))
               (cont_RI _ (proj1 Hkg) a b) Hab). }
    rewrite (RInt_scal (fun u => Re (g u)) (Re k) a b (cont_RI _ (proj1 Hg) a b)
               (Riemann_integrable_scal (Re k) (cont_RI _ (proj1 Hg) a b)) Hab).
    rewrite (RInt_scal (fun u => Im (g u)) (Im k) a b (cont_RI _ (proj2 Hg) a b)
               (Riemann_integrable_scal (Im k) (cont_RI _ (proj2 Hg) a b)) Hab).
    unfold Cmul; cbn [Re Im]; ring.
  - etransitivity.
    { apply (RInt_plus (fun x => Re k * Im (g x)) (fun x => Im k * Re (g x)) a b
               (Riemann_integrable_scal (Re k) (cont_RI _ (proj2 Hg) a b))
               (Riemann_integrable_scal (Im k) (cont_RI _ (proj1 Hg) a b))
               (cont_RI _ (proj2 Hkg) a b) Hab). }
    rewrite (RInt_scal (fun u => Im (g u)) (Re k) a b (cont_RI _ (proj2 Hg) a b)
               (Riemann_integrable_scal (Re k) (cont_RI _ (proj2 Hg) a b)) Hab).
    rewrite (RInt_scal (fun u => Re (g u)) (Im k) a b (cont_RI _ (proj1 Hg) a b)
               (Riemann_integrable_scal (Im k) (cont_RI _ (proj1 Hg) a b)) Hab).
    unfold Cmul; cbn [Re Im]; ring.
Qed.

Lemma Cintf_sub : forall f g (Hf : Ccont f) (Hg : Ccont g)
  (Hfg : Ccont (fun u => Cminus (f u) (g u))) a b, a <= b ->
  Cintf (fun u => Cminus (f u) (g u)) Hfg a b
  = Cminus (Cintf f Hf a b) (Cintf g Hg a b).
Proof.
  intros f g Hf Hg Hfg a b Hab; apply Ceq; unfold Cminus; cbn [Re Im].
  - exact (RInt_sub (fun u => Re (f u)) (fun u => Re (g u)) a b
             (cont_RI _ (proj1 Hf) a b) (cont_RI _ (proj1 Hg) a b)
             (cont_RI _ (proj1 Hfg) a b) Hab).
  - exact (RInt_sub (fun u => Im (f u)) (fun u => Im (g u)) a b
             (cont_RI _ (proj2 Hf) a b) (cont_RI _ (proj2 Hg) a b)
             (cont_RI _ (proj2 Hfg) a b) Hab).
Qed.

Lemma Ccont_sub : forall f g, Ccont f -> Ccont g ->
  Ccont (fun u => Cminus (f u) (g u)).
Proof.
  intros f g Hf Hg; exact (Ccont_add f (fun u => Copp (g u)) Hf (Ccont_opp g Hg)).
Qed.

(* ================================================================= *)
(*  Leibniz rule.                                                      *)
(* ================================================================= *)

Section Leibniz.
Variables (phi dphi : R -> R -> C) (a b r0 : R).
Hypothesis Hab : a <= b.
(* per-r continuity of the integrand and of the derivative-integrand *)
Hypothesis Hphi  : forall r, Ccont (fun t => phi r t).
Hypothesis Hdphi : Ccont (fun t => dphi r0 t).
(* the uniform first-order estimate *)
Hypothesis Hunif : forall eps, 0 < eps -> exists del, 0 < del /\
  forall r t, a <= t <= b -> Rabs (r - r0) < del ->
    Cmod (Cminus (Cminus (phi r t) (phi r0 t))
                 (Cmul (dphi r0 t) (RtoC (r - r0)))) <= eps * Rabs (r - r0).

Definition Ig (r : R) : C := Cintf (fun t => phi r t) (Hphi r) a b.
Definition Jg : C := Cintf (fun t => dphi r0 t) Hdphi a b.

(* the increment I(r) − I(r0) − J·(r−r0) is one integral of the o-term, ML-bounded *)
Lemma leibniz_bound : forall eps, 0 < eps -> exists del, 0 < del /\
  forall r, Rabs (r - r0) < del ->
    Cmod (Cminus (Cminus (Ig r) (Ig r0)) (Cmul Jg (RtoC (r - r0))))
    <= 2 * (eps * Rabs (r - r0)) * (b - a).
Proof.
  intros eps Heps; destruct (Hunif eps Heps) as [del [Hdel Hu]].
  exists del; split; [ exact Hdel | ]; intros r Hr.
  assert (Hoc : Ccont (fun t => Cminus (Cminus (phi r t) (phi r0 t))
                                 (Cmul (RtoC (r - r0)) (dphi r0 t)))) by
    (apply Ccont_sub; [ apply Ccont_sub; [ apply Hphi | apply Hphi ]
                      | apply Ccont_scal, Hdphi ]).
  replace (Cminus (Cminus (Ig r) (Ig r0)) (Cmul Jg (RtoC (r - r0))))
     with (Cintf (fun t => Cminus (Cminus (phi r t) (phi r0 t))
                            (Cmul (RtoC (r - r0)) (dphi r0 t))) Hoc a b).
  - apply (Cintf_ML _ Hoc a b (eps * Rabs (r - r0)) Hab).
    intros t Ht.
    replace (Cmul (RtoC (r - r0)) (dphi r0 t))
       with (Cmul (dphi r0 t) (RtoC (r - r0))) by ring.
    apply Hu; [ exact Ht | exact Hr ].
  - rewrite (Cintf_sub (fun t => Cminus (phi r t) (phi r0 t))
              (fun t => Cmul (RtoC (r - r0)) (dphi r0 t))
              (Ccont_sub _ _ (Hphi r) (Hphi r0)) (Ccont_scal _ _ Hdphi)
              Hoc a b Hab).
    rewrite (Cintf_sub (fun t => phi r t) (fun t => phi r0 t)
              (Hphi r) (Hphi r0) (Ccont_sub _ _ (Hphi r) (Hphi r0)) a b Hab).
    rewrite (Cintf_cmul_l (RtoC (r - r0)) (fun t => dphi r0 t) Hdphi
              (Ccont_scal _ _ Hdphi) a b Hab).
    unfold Ig, Jg; ring.
Qed.

(* one component (Re or Im), factored via a projection `pick` *)
Lemma leibniz_comp : forall (pick : C -> R),
  (forall c, Rabs (pick c) <= Cmod c) ->
  (forall h, pick (Cmul Jg (RtoC h)) = pick Jg * h) ->
  (forall a' b', pick (Cminus a' b') = pick a' - pick b') ->
  derivable_pt_lim (fun r => pick (Ig r)) r0 (pick Jg).
Proof.
  intros pick Hmod Hscal Hsub eps' Heps'.
  assert (Hba : 0 <= b - a) by lra.
  destruct (leibniz_bound (eps' / (2 * (b - a) + 1))
             ltac:(apply Rdiv_lt_0_compat; lra)) as [del [Hdel Hb]].
  exists (mkposreal del Hdel); intros h Hh0 Hh; cbn.
  assert (Hh' : 0 < Rabs h) by (apply Rabs_pos_lt; exact Hh0).
  assert (Hbnd := Hb (r0 + h) ltac:(replace (r0 + h - r0) with h by ring; exact Hh)).
  replace (r0 + h - r0) with h in Hbnd by ring.
  assert (HX : Rabs (pick (Ig (r0 + h)) - pick (Ig r0) - pick Jg * h)
               <= 2 * (eps' / (2 * (b - a) + 1) * Rabs h) * (b - a)).
  { replace (pick (Ig (r0 + h)) - pick (Ig r0) - pick Jg * h)
       with (pick (Cminus (Cminus (Ig (r0 + h)) (Ig r0)) (Cmul Jg (RtoC h))))
       by (rewrite !Hsub, Hscal; ring).
    eapply Rle_trans; [ apply Hmod | exact Hbnd ]. }
  replace ((pick (Ig (r0 + h)) - pick (Ig r0)) / h - pick Jg)
     with ((pick (Ig (r0 + h)) - pick (Ig r0) - pick Jg * h) / h)
     by (field; exact Hh0).
  unfold Rdiv; rewrite Rabs_mult, (Rabs_inv h).
  apply Rle_lt_trans with (2 * (eps' / (2 * (b - a) + 1)) * (b - a)).
  - apply Rle_trans with
      (2 * (eps' / (2 * (b - a) + 1) * Rabs h) * (b - a) * / Rabs h).
    + apply Rmult_le_compat_r; [ left; apply Rinv_0_lt_compat; exact Hh' | exact HX ].
    + apply Req_le; field; lra.
  - apply (Rmult_lt_reg_r (2 * (b - a) + 1)); [ lra | ].
    replace (2 * (eps' / (2 * (b - a) + 1)) * (b - a) * (2 * (b - a) + 1))
       with (2 * eps' * (b - a)) by (field; lra).
    lra.
Qed.

Theorem leibniz_deriv :
  derivable_pt_lim (fun r => Re (Ig r)) r0 (Re Jg)
  /\ derivable_pt_lim (fun r => Im (Ig r)) r0 (Im Jg).
Proof.
  split.
  - apply (leibniz_comp Re Cmod_Re);
      intros; unfold Cmul, Cminus, RtoC; cbn; ring.
  - apply (leibniz_comp Im Cmod_Im);
      intros; unfold Cmul, Cminus, RtoC; cbn; ring.
Qed.

End Leibniz.

(* ================================================================= *)
(*  END CLeibniz.v                                                     *)
(* ================================================================= *)
