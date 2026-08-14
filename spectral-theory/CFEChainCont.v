(* ================================================================= *)
(*  CFEChainCont.v  (identity-theorem plan, FE chain brick 2 — ML)     *)
(*                                                                    *)
(*  The Cauchy power integral is Lipschitz in the pole:  for poles     *)
(*  p1, p2 in the closed disk |p| <= rho < R,                          *)
(*    | oint g/(z-p1)^n - oint g/(z-p2)^n | <= C . |p1 - p2|,           *)
(*  via Cintf_sub + the kernel Lipschitz bound (CCauchyCont.            *)
(*  Cinv_pow_diff_bound) + Cintf_ML.  This is the integral-continuous-  *)
(*  in-the-pole half of the clamped-integral continuity.               *)
(*                                                                    *)
(*  Axioms: standard classical-Reals only.                            *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import ComplexField Cmodulus CIntegral2 CSegInt CPathIntegral CLeibniz
        RootsOfUnity CWindingOffCenter CCauchyAnalytic CCauchyCont.
Open Scope R_scope.

(* factor g and z' out of the kernel difference (fresh-var lemma: ring
   rejects Cpow/Cinv atoms directly) *)
Lemma kdiff : forall (gg A B ap : C),
  Cminus (Cmul (Cmul gg A) ap) (Cmul (Cmul gg B) ap)
  = Cmul (Cmul gg (Cminus A B)) ap.
Proof. intros; ring. Qed.

Lemma rmul3 : forall x y w z : R, x * (y * w) * z = x * y * z * w.
Proof. intros; ring. Qed.

Section PoleLip.
Variable g : C -> C.
Variable Rr rho : R.
Hypothesis HR : 0 < Rr.
Hypothesis Hrho : 0 <= rho.
Hypothesis HrhoR : rho < Rr.
Hypothesis Hg : CcontC g.
Variable Mg : R.
Hypothesis HMg : 0 <= Mg.
Hypothesis Hgb : forall u, Cmod (g (arc Rr u)) <= Mg.

Lemma arc_p_lb : forall p u, Cmod p <= rho -> Rr - rho <= Cmod (Cminus (arc Rr u) p).
Proof.
  intros p u Hp. eapply Rle_trans; [ | apply Cmod_rev_triangle ].
  rewrite (Cmod_arc Rr u) by lra. lra.
Qed.

Lemma arc_p_ub : forall p u, Cmod p <= rho -> Cmod (Cminus (arc Rr u) p) <= Rr + rho.
Proof.
  intros p u Hp. replace (Cminus (arc Rr u) p) with (Cadd (arc Rr u) (Copp p)) by ring.
  eapply Rle_trans; [ apply Cmod_triangle | ]. rewrite Cmod_opp, (Cmod_arc Rr u) by lra. lra.
Qed.

Theorem pole_lipschitz : forall (m : nat) (p1 p2 : C)
  (H1 : Ccont (Kwn g Rr (S m) p1)) (H2 : Ccont (Kwn g Rr (S m) p2)),
  Cmod p1 <= rho -> Cmod p2 <= rho ->
  Cmod (Cminus (Cintf (Kwn g Rr (S m) p1) H1 0 (2 * PI))
               (Cintf (Kwn g Rr (S m) p2) H2 0 (2 * PI)))
  <= 2 * (Mg * (INR (S m) * (Rr + rho) ^ m
                / ((Rr - rho) ^ S m * (Rr - rho) ^ S m)) * Rr)
       * (2 * PI) * Cmod (Cminus p1 p2).
Proof.
  intros m p1 p2 H1 H2 Hp1 Hp2.
  set (L := INR (S m) * (Rr + rho) ^ m / ((Rr - rho) ^ S m * (Rr - rho) ^ S m)).
  assert (Hpi : 0 <= 2 * PI) by (generalize PI_RGT_0; lra).
  assert (Hsub : Ccont (fun u => Cminus (Kwn g Rr (S m) p1 u) (Kwn g Rr (S m) p2 u)))
    by (apply Ccont_sub; assumption).
  rewrite <- (Cintf_sub (Kwn g Rr (S m) p1) (Kwn g Rr (S m) p2) H1 H2 Hsub 0 (2 * PI) Hpi).
  set (M := Mg * L * Rr * Cmod (Cminus p1 p2)).
  (* pointwise bound *)
  assert (Hpb : forall u, 0 <= u <= 2 * PI ->
    Cmod (Cminus (Kwn g Rr (S m) p1 u) (Kwn g Rr (S m) p2 u)) <= M).
  { intros u _. unfold Kwn.
    rewrite (kdiff (g (arc Rr u)) (Cinv (Cpow (Cminus (arc Rr u) p1) (S m)))
               (Cinv (Cpow (Cminus (arc Rr u) p2) (S m))) (arc' Rr u)).
    rewrite Cmod_mul, Cmod_mul, (Cmod_arc' Rr u ltac:(lra)).
    assert (Hab : Cmod (Cminus (Cminus (arc Rr u) p1) (Cminus (arc Rr u) p2))
                  = Cmod (Cminus p1 p2)).
    { replace (Cminus (Cminus (arc Rr u) p1) (Cminus (arc Rr u) p2))
        with (Copp (Cminus p1 p2)) by ring. apply Cmod_opp. }
    unfold M.
    apply Rle_trans with (Mg * (L * Cmod (Cminus p1 p2)) * Rr).
    - apply Rmult_le_compat_r; [ lra | ].
      apply Rmult_le_compat; [ apply Cmod_nonneg | apply Cmod_nonneg | apply Hgb | ].
      unfold L. rewrite <- Hab.
      apply (Cinv_pow_diff_bound (Cminus (arc Rr u) p1) (Cminus (arc Rr u) p2)
               (Rr - rho) (Rr + rho) m).
      + lra.
      + apply arc_p_lb; exact Hp1.
      + apply arc_p_lb; exact Hp2.
      + apply arc_p_ub; exact Hp1.
      + apply arc_p_ub; exact Hp2.
    - apply Req_le. apply rmul3. }
  clearbody L.
  eapply Rle_trans;
    [ apply (Cintf_ML (fun u => Cminus (Kwn g Rr (S m) p1 u) (Kwn g Rr (S m) p2 u))
               Hsub 0 (2 * PI) M Hpi Hpb) | ].
  unfold M. apply Req_le.
  generalize (Cmod (Cminus p1 p2)); generalize (2 * PI); intros T C. ring.
Qed.

End PoleLip.

(* ================================================================= *)
(*  PhiN continuity from clampw continuity + pole_lipschitz            *)
(* ================================================================= *)
Theorem PhiN_ptcont : forall (g : C -> C) (Rr : R) (w0 : C) (m : nat)
  (HR : 0 < Rr) (Hw0 : Cmod w0 < Rr) (Hg : CcontC g) (Mg : R),
  (forall u, Cmod (g (arc Rr u)) <= Mg) ->
  (forall w2 e, 0 < e -> exists del, 0 < del /\ forall w, Cmod (Cminus w w2) < del ->
     Cmod (Cminus (clampw Rr w0 w) (clampw Rr w0 w2)) < e) ->
  forall w2 eps, 0 < eps -> exists del, 0 < del /\
    forall w, Cmod (Cminus w w2) < del ->
      Cmod (Cminus (PhiN g Rr w0 (S m) HR Hw0 Hg w)
                   (PhiN g Rr w0 (S m) HR Hw0 Hg w2)) < eps.
Proof.
  intros g Rr w0 m HR Hw0 Hg Mg Hgb Hclampcont w2 eps Heps.
  assert (HMg : 0 <= Mg)
    by (pose proof (Hgb 0); pose proof (Cmod_nonneg (g (arc Rr 0))); lra).
  assert (HrR : rho Rr w0 < Rr) by (unfold rho; lra).
  assert (Hrho0 : 0 <= rho Rr w0)
    by (unfold rho; pose proof (Cmod_nonneg w0); lra).
  remember (2 * (Mg * (INR (S m) * (Rr + rho Rr w0) ^ m
              / ((Rr - rho Rr w0) ^ S m * (Rr - rho Rr w0) ^ S m)) * Rr) * (2 * PI))
    as C eqn:HCeq.
  assert (HC0 : 0 <= C).
  { rewrite HCeq. apply Rmult_le_pos; [ | generalize PI_RGT_0; lra ].
    apply Rmult_le_pos; [ lra | ].
    apply Rmult_le_pos; [ apply Rmult_le_pos; [ exact HMg | ] | lra ].
    apply Rle_mult_inv_pos;
      [ apply Rmult_le_pos; [ apply pos_INR | apply pow_le; lra ]
      | apply Rmult_lt_0_compat; apply pow_lt; lra ]. }
  destruct (Hclampcont w2 (eps / (C + 1)) ltac:(apply Rdiv_lt_0_compat; lra))
    as [del [Hdel Hcl]].
  exists del; split; [ exact Hdel | ].
  intros w Hw.
  assert (Hpl : Cmod (Cminus (PhiN g Rr w0 (S m) HR Hw0 Hg w)
                             (PhiN g Rr w0 (S m) HR Hw0 Hg w2))
                <= C * Cmod (Cminus (clampw Rr w0 w) (clampw Rr w0 w2))).
  { rewrite HCeq.
    exact (pole_lipschitz g Rr (rho Rr w0) HR HrR Mg Hgb m
             (clampw Rr w0 w) (clampw Rr w0 w2)
             (Kwn_cont g Rr (S m) Hg (clampw Rr w0 w) (clamp_ne Rr w0 HR Hw0 w))
             (Kwn_cont g Rr (S m) Hg (clampw Rr w0 w2) (clamp_ne Rr w0 HR Hw0 w2))
             (clampw_mod Rr w0 HR w) (clampw_mod Rr w0 HR w2)). }
  eapply Rle_lt_trans; [ exact Hpl | ].
  set (X := Cmod (Cminus (clampw Rr w0 w) (clampw Rr w0 w2))).
  assert (HX : X < eps / (C + 1)) by (apply Hcl; exact Hw).
  assert (HX0 : 0 <= X) by (unfold X; apply Cmod_nonneg).
  clearbody X.
  assert (Hlt : X * (C + 1) < eps).
  { apply (Rmult_lt_reg_r (/ (C + 1))); [ apply Rinv_0_lt_compat; lra | ].
    rewrite Rmult_assoc. rewrite Rinv_r by lra. rewrite Rmult_1_r.
    unfold Rdiv in HX. exact HX. }
  apply Rle_lt_trans with (X * (C + 1)); [ | exact Hlt ].
  rewrite Rmult_comm. apply Rmult_le_compat_l; [ exact HX0 | lra ].
Qed.

Print Assumptions pole_lipschitz.
Print Assumptions PhiN_ptcont.
