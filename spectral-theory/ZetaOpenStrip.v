(* ================================================================= *)
(*  ZetaOpenStrip.v  --  the OPEN critical strip.                      *)
(*                                                                    *)
(*    XiC_zeros_in_open_strip : XiC z = 0  ==>  0 < Re z < 1           *)
(*                                                                    *)
(*  ZetaStripConfinement gives the CLOSED strip from the Euler product *)
(*  alone (zetaC <> 0 for Re > 1).  Pushing to the open strip costs a  *)
(*  strictly stronger input: the boundary line Re = 1 needs            *)
(*  ZetaLineNonzero.zetaC_line_nonzero, i.e. the full Mertens 3-4-1    *)
(*  chain.  That is why this lives in its own file rather than in      *)
(*  ZetaStripConfinement -- otherwise every consumer of the closed     *)
(*  strip would pay for the 3-4-1 tower transitively.                  *)
(*                                                                    *)
(*  The argument runs on CZetaStripId.XiC_completed_strip, which is    *)
(*  the completion identity on the WHOLE half-plane Re > 0 -- boundary *)
(*  line and the point z = 1 included.  That matters: LambdaC has a    *)
(*  pole at z = 1, so the LambdaC-shaped identity of                   *)
(*  ZetaStripConfinement cannot reach the boundary.  RHSc is built on  *)
(*  the REGULARISED BfnT = (z-1) zeta(z), which is holomorphic there   *)
(*  and satisfies BfnT C1 = C1 -- so z = 1 needs no special pleading.  *)
(*                                                                    *)
(*  Re z <= 0 folds over by XiC_symmetric, exactly as the closed-strip *)
(*  proof does.  Axiom-clean.                                          *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra.
Require Import ComplexField Cmodulus CexpFull CDeriv CZeta CEulerProductZeta
        GammaC RiemannXiEntire ZetaFn CZetaXiComplex CZetaRegular6
        CZetaStripId GammaCNe0 ZetaLineNonzero.
Open Scope R_scope.

Lemma C1_ne_C0 : C1 <> C0.
Proof. intro H; apply (f_equal Re) in H; unfold C1, C0 in H; cbn [Re] in H; lra. Qed.

(* ----------------------------------------------------------------- *)
(*  the regularised zeta is nonzero on the closed half-plane Re >= 1  *)
(* ----------------------------------------------------------------- *)
Lemma BfnT_nonzero_ge1 : forall w, 1 <= Re w -> BfnT w <> C0.
Proof.
  intros w Hw.
  assert (H0 : 0 < Re w) by lra.
  destruct (Ceq_dec2 w C1) as [Hc | Hc]; [ subst w; rewrite BfnT_at1; exact C1_ne_C0 | ].
  assert (H1 : Cminus C1 w <> C0).
  { intro Ha. apply Hc. apply Ceq; unfold C1; cbn [Re Im];
    [ apply (f_equal Re) in Ha | apply (f_equal Im) in Ha ];
    unfold Cminus, C1, C0 in Ha; cbn [Re Im] in Ha; lra. }
  rewrite (BfnT_eq w H0 H1). apply Cmul_ne0.
  - intro He; apply Hc; replace w with (Cadd (Cminus w C1) C1) by ring; rewrite He; ring.
  - rewrite (zF_eq w H0 H1). destruct (Rle_lt_or_eq_dec 1 (Re w) Hw) as [Hgt | Heq].
    + exact (zetaC_nonzero w Hgt H0 H1).
    + (* the boundary line Re w = 1 : this is where 3-4-1 is spent *)
      assert (Hwm : w = mkC 1 (Im w)) by (apply Ceq; cbn [Re Im]; [ lra | reflexivity ]).
      assert (Ht : Im w <> 0)
        by (intro Hb; apply Hc; apply Ceq; unfold C1; cbn [Re Im]; lra).
      assert (K0 : 0 < Re (mkC 1 (Im w))) by (cbn [Re]; lra).
      assert (K1 : Cminus C1 (mkC 1 (Im w)) <> C0)
        by (intro Hd; apply Ht; apply (f_equal Im) in Hd;
            unfold Cminus, C1, C0 in Hd; cbn [Im] in Hd; lra).
      rewrite (zetaC_congr w (mkC 1 (Im w)) H0 H1 K0 K1 Hwm).
      exact (zetaC_line_nonzero (Im w) Ht K0 K1).
Qed.

(* ----------------------------------------------------------------- *)
(*  hence XiC has no zero with Re >= 1                                *)
(* ----------------------------------------------------------------- *)
Theorem XiC_nonzero_ge1 : forall w, 1 <= Re w -> XiC w <> C0.
Proof.
  intros w Hw. assert (H0 : 0 < Re w) by lra.
  rewrite (XiC_completed_strip w H0). unfold RHSc.
  apply Cmul_ne0; [ apply Cmul_ne0 | apply BfnT_nonzero_ge1; exact Hw ].
  - apply Cmul_ne0.
    + intro He; apply (f_equal Re) in He; unfold RtoC, C0 in He; cbn [Re] in He; lra.
    + intro He; apply (f_equal Re) in He; unfold C0 in He; cbn [Re] in He; lra.
  - apply Cmul_ne0.
    + unfold archexp, Cpw; apply Cexpf_ne0.
    + apply GammaC_ne0_final. unfold halfz, Cadd, Cmul, RtoC, C0; cbn [Re Im]; lra.
Qed.

(* ----------------------------------------------------------------- *)
(*  THE OPEN STRIP                                                     *)
(* ----------------------------------------------------------------- *)
Theorem XiC_zeros_in_open_strip : forall z, XiC z = C0 -> 0 < Re z < 1.
Proof.
  intros z Hz; split.
  - (* 0 < Re z : else Re(1-z) >= 1 and XiC(1-z) = XiC z <> 0 *)
    destruct (Rlt_le_dec 0 (Re z)) as [H | H]; [ exact H | exfalso ].
    apply (XiC_nonzero_ge1 (Cminus C1 z)); [ unfold Cminus, C1; cbn [Re]; lra | ].
    rewrite <- (XiC_symmetric z); exact Hz.
  - destruct (Rlt_le_dec (Re z) 1) as [H | H]; [ exact H | exfalso ].
    apply (XiC_nonzero_ge1 z H); exact Hz.
Qed.

Print Assumptions BfnT_nonzero_ge1.
Print Assumptions XiC_nonzero_ge1.
Print Assumptions XiC_zeros_in_open_strip.
