(* ================================================================= *)
(*  FusionIntegral.v  —  Newman A3: the integral-level fusion bridge.     *)
(*                                                                    *)
(*  CgderivInt_Laplace : the u-space cell integral of gderivC equals the  *)
(*  Newman Laplace-kernel cell integral (t-space, cexpzt), scaled by -s:  *)
(*                                                                    *)
(*    int_a^b gderivC s  =  -s * int_{ln a}^{ln b} e^{-st} dt.            *)
(*                                                                    *)
(*  This crosses the "global continuity" wall: gderivC is continuous only *)
(*  on (0,oo) (so CgderivInt is interval-specific, not a Cintf), but the  *)
(*  RIGHT side is a Cintf of the globally-continuous cexpzt.  The CoV      *)
(*  u = e^t is run at the RiemannInt component level (cov_local on Re/Im), *)
(*  with a dependent-endpoint rewrite (exp(ln a)=a) via RiemannInt_bound_  *)
(*  eq, the integrand matching supplied by FusionKernel (gderivC_Fpow +    *)
(*  Fpow_exp), and the -s scalar factored out by Cintf_cmul_l.            *)
(*                                                                    *)
(*  Combined with phi_cellint_rep this turns the Phi cell representation   *)
(*  into the Newman Laplace form.  Axiom-clean.                          *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import ComplexField Cmodulus CIntegral2 CSegInt CLeibniz
        ContinuousCoV LocalCoV CExpKernel CZetaTerm CFTC FusionKernel ExpBridge.
Open Scope R_scope.

(*  RiemannInt is insensitive to the (equal) endpoints and the proof       *)
Lemma RiemannInt_bound_eq : forall (f : R -> R) a a' b b'
  (pr : Riemann_integrable f a b) (pr' : Riemann_integrable f a' b'),
  a = a' -> b = b' -> RiemannInt pr = RiemannInt pr'.
Proof.
  intros f a a' b b' pr pr' Ha Hb; revert pr; rewrite Ha, Hb; intro pr; apply RiemannInt_P5.
Qed.

Lemma CgderivInt_Laplace : forall s a b (Ha : 0 < a) (Hab : a <= b),
  CgderivInt s a b Ha Hab
  = Cmul (Copp s) (Cintf (fun t => cexpzt (Copp s) t) (Ccont_cexpzt (Copp s)) (ln a) (ln b)).
Proof.
  intros s a b Ha Hab; assert (Hb : 0 < b) by lra.
  assert (Hlab : ln a <= ln b)
    by (destruct (Rle_lt_or_eq_dec a b Hab) as [H | H];
        [ apply Rlt_le, ln_increasing; assumption | subst; apply Rle_refl ]).
  set (Hc := Ccont_scal (Copp s) (fun t => cexpzt (Copp s) t) (Ccont_cexpzt (Copp s))).
  transitivity (Cintf (fun t => Cmul (Copp s) (cexpzt (Copp s) t)) Hc (ln a) (ln b)).
  - apply Ceq.
    + (* Re component *)
      unfold CgderivInt; cbn [Re]; rewrite Re_Cintf.
      assert (prR : Riemann_integrable (fun u => Re (gderivC s u)) (exp (ln a)) (exp (ln b))).
      { apply continuity_implies_RiemannInt; [ apply exp_mono_le; exact Hlab | intros u Hu;
          apply Re_gderivC_cont; apply Rlt_le_trans with (exp (ln a));
            [ apply exp_pos | apply (proj1 Hu) ] ]. }
      assert (prL : Riemann_integrable (fun t => Re (gderivC s (exp t)) * exp t) (ln a) (ln b)).
      { apply continuity_implies_RiemannInt; [ exact Hlab | intros t _; apply continuity_pt_mult;
          [ apply (continuity_pt_comp exp (fun u => Re (gderivC s u)));
              [ apply cont_exp | apply Re_gderivC_cont; apply exp_pos ]
          | apply cont_exp ] ]. }
      transitivity (RiemannInt prR).
      * apply RiemannInt_bound_eq; symmetry; apply exp_ln; assumption.
      * transitivity (RiemannInt prL).
        -- symmetry; apply (cov_local exp exp (fun u => Re (gderivC s u)) (ln a) (ln b) Hlab
             (fun t _ => derivable_pt_lim_exp t) (fun t _ => cont_exp t)
             (fun t Ht => conj (exp_mono_le (ln a) t (proj1 Ht)) (exp_mono_le t (ln b) (proj2 Ht)))
             (fun u Hu => Re_gderivC_cont s u
                (Rlt_le_trans _ _ _ (exp_pos (ln a)) (proj1 Hu)))).
        -- apply RiemannInt_P18; [ exact Hlab | intros t _;
             rewrite gderivC_Fpow, <- Fpow_exp; unfold Cmul, RtoC; cbn [Re Im]; ring ].
    + (* Im component *)
      unfold CgderivInt; cbn [Im]; rewrite Im_Cintf.
      assert (prR : Riemann_integrable (fun u => Im (gderivC s u)) (exp (ln a)) (exp (ln b))).
      { apply continuity_implies_RiemannInt; [ apply exp_mono_le; exact Hlab | intros u Hu;
          apply Im_gderivC_cont; apply Rlt_le_trans with (exp (ln a));
            [ apply exp_pos | apply (proj1 Hu) ] ]. }
      assert (prL : Riemann_integrable (fun t => Im (gderivC s (exp t)) * exp t) (ln a) (ln b)).
      { apply continuity_implies_RiemannInt; [ exact Hlab | intros t _; apply continuity_pt_mult;
          [ apply (continuity_pt_comp exp (fun u => Im (gderivC s u)));
              [ apply cont_exp | apply Im_gderivC_cont; apply exp_pos ]
          | apply cont_exp ] ]. }
      transitivity (RiemannInt prR).
      * apply RiemannInt_bound_eq; symmetry; apply exp_ln; assumption.
      * transitivity (RiemannInt prL).
        -- symmetry; apply (cov_local exp exp (fun u => Im (gderivC s u)) (ln a) (ln b) Hlab
             (fun t _ => derivable_pt_lim_exp t) (fun t _ => cont_exp t)
             (fun t Ht => conj (exp_mono_le (ln a) t (proj1 Ht)) (exp_mono_le t (ln b) (proj2 Ht)))
             (fun u Hu => Im_gderivC_cont s u
                (Rlt_le_trans _ _ _ (exp_pos (ln a)) (proj1 Hu)))).
        -- apply RiemannInt_P18; [ exact Hlab | intros t _;
             rewrite gderivC_Fpow, <- Fpow_exp; unfold Cmul, RtoC; cbn [Re Im]; ring ].
  - apply (Cintf_cmul_l (Copp s) (fun t => cexpzt (Copp s) t)
             (Ccont_cexpzt (Copp s)) Hc (ln a) (ln b) Hlab).
Qed.

Print Assumptions CgderivInt_Laplace.

(* ================================================================= *)
(*  END FusionIntegral.v — int_a^b gderivC s = -s int_{ln a}^{ln b} e^{-st}.*)
(*  With s = z+1 the RHS Laplace integral is exactly the Newman kernel     *)
(*  cell integral; feeding this cell-by-cell into phi_cellint_rep turns     *)
(*  the Phi cell representation into the Laplace form, and with laplace_one *)
(*  (the 1/z term) assembles g(z) = Phi(z+1)/(z+1) - 1/z.                   *)
(* ================================================================= *)
