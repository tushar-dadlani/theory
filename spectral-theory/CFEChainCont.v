(* ================================================================= *)
(*  CFEChainCont.v  (identity-theorem plan, FE chain brick 2 — ML)     *)
(*                                                                    *)
(*  The Cauchy power integral is Lipschitz in the pole:  for poles     *)
(*  p1, p2 in the closed disk |p| <= rho < R,                          *)
(*    | oint g/(z-p1)^n - oint g/(z-p2)^n | <= C . |p1 - p2|,           *)
(*  via Cintf_sub + the kernel Lipschitz bound (CCauchyCont.            *)
(*  Cinv_pow_diff_bound) + Cintf_ML.  This is the "integral continuous  *)
(*  in the pole" half of the clamped-integral continuity.              *)
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

Print Assumptions pole_lipschitz.
