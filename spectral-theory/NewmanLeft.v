(* ================================================================= *)
(*  NewmanLeft.v  —  Newman A3: the left-half-plane g_T contour piece.    *)
(*                                                                    *)
(*  The mirror of right_arc_bound, for the truncated transform g_T on the *)
(*  LEFT semicircle (Re z < 0), where g_T is entire:                     *)
(*                                                                    *)
(*    LT_left_bound : |g_T(z)| <= 2B e^{-(Re z)T}/(-(Re z))   (Re z < 0),  *)
(*    left_arc_bound: |g_T(z) e^{zT} K_R(z)| <= 4B/R^2  on |z|=R,          *)
(*                                                                    *)
(*  the same 4B/R^2 as the right piece (right_arc_bound), so via           *)
(*  newman_arc_ML the left g_T contribution is also O(B/R).  Axiom-clean. *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import ComplexField Cmodulus CIntegral2 CSegInt CExpKernel CNewmanKernel
        ContinuousCoV PerronBound PerronEdge LaplaceFull.
Open Scope R_scope.

(*  the exponential integral for a <> 0 (not just a > 0)  *)
Lemma exp_int_AB_ne : forall Bc a A B0 (Ha : a <> 0) (Hab : A <= B0)
  (pr : Riemann_integrable (fun t => Bc * exp (- (a * t))) A B0),
  RiemannInt pr = Bc * (exp (- (a * A)) - exp (- (a * B0))) / a.
Proof.
  intros Bc a A B0 Ha Hab pr.
  assert (Hanti : antiderivative (fun t => Bc * exp (- (a * t)))
                    (fun x => Bc * (- / a * exp (- (a * x)))) A B0).
  { split; [ | exact Hab ]; intros x _.
    exists (exist (fun l => derivable_pt_lim (fun t => Bc * (- / a * exp (- (a * t)))) x l)
              (Bc * exp (- (a * x)))
              (derivable_pt_lim_scal (fun t => - / a * exp (- (a * t))) Bc x
                 (exp (- (a * x))) (exp_scaled_deriv a x Ha))).
    unfold derive_pt; simpl; reflexivity. }
  rewrite (FTC_antideriv (fun t => Bc * exp (- (a * t)))
             (fun x => Bc * (- / a * exp (- (a * x)))) A B0 Hab
             (fun x _ => Bexp_cont Bc a x) pr Hanti).
  field; exact Ha.
Qed.

(*  the truncated transform on the left half-plane  *)
Lemma LT_left_bound : forall f (Hfc : Ccont f) B (Hfb : forall t, Cmod (f t) <= B)
  z (HzL : Re z < 0) T (HT : 0 <= T),
  Cmod (LT f Hfc z T) <= 2 * (B * exp (- (Re z * T)) / (- Re z)).
Proof.
  intros f Hfc B Hfb z HzL T HT.
  assert (Hzne : Re z <> 0) by lra.
  assert (Hnz : 0 < - Re z) by lra.
  assert (Hcm : Riemann_integrable (fun u => Cmod (lint f z u)) 0 T)
    by (apply continuity_implies_RiemannInt;
        [ exact HT | intros u _; apply (Ccont_Cmod (lint f z) (lint_cont f Hfc z)) ]).
  assert (Hbexp : Riemann_integrable (fun t => B * exp (- (Re z * t))) 0 T)
    by (apply continuity_implies_RiemannInt; [ exact HT | intros u _; apply Bexp_cont ]).
  unfold LT.
  eapply Rle_trans; [ apply (Cintf_mod_le2 (lint f z) (lint_cont f Hfc z) 0 T Hcm HT) | ].
  apply Rmult_le_compat_l; [ lra | ].
  eapply Rle_trans.
  - apply (RiemannInt_P19 Hcm Hbexp HT); intros u Hu.
    unfold lint; rewrite Cmod_mul, (Cmod_cexpzt (Copp z) u).
    replace (Re (Copp z) * u) with (- (Re z * u)) by (unfold Copp; cbn [Re]; ring).
    apply Rmult_le_compat_r; [ left; apply exp_pos | apply Hfb ].
  - rewrite (exp_int_AB_ne B (Re z) 0 T Hzne HT Hbexp).
    rewrite Rmult_0_r, Ropp_0, exp_0.
    apply Rmult_le_reg_r with (- Re z); [ exact Hnz | ].
    replace (B * (1 - exp (- (Re z * T))) / Re z * (- Re z))
      with (B * (exp (- (Re z * T)) - 1)) by (field; exact Hzne).
    replace (B * exp (- (Re z * T)) / (- Re z) * (- Re z))
      with (B * exp (- (Re z * T))) by (field; intro Hc; lra).
    pose proof (B_nonneg f B Hfb); pose proof (exp_pos (- (Re z * T))); nra.
Qed.

(*  the left-semicircle integrand bound (mirror of right_arc_bound)  *)
Theorem left_arc_bound :
  forall (f : R -> C) (Hfc : Ccont f) (B : R) (Hfb : forall t, Cmod (f t) <= B)
         z (HzL : Re z < 0) (T : R) (HT : 0 <= T) (R : R) (HR : 0 < R)
         (Hcirc : Cnorm2 z = R * R),
  Cmod (Cmul (LT f Hfc z T) (Cmul (cexpzt z T) (newman_kernel R z)))
  <= 4 * B / (R * R).
Proof.
  intros f Hfc B Hfb z HzL T HT R HR Hcirc.
  assert (HRne : R <> 0) by (apply Rgt_not_eq; exact HR).
  assert (HRR : R * R <> 0) by (intro Hc; nra).
  assert (Hzne : Re z <> 0) by lra.
  assert (Hnz : - Re z <> 0) by (apply Rgt_not_eq; lra).
  assert (Hex : exp (Re z * T) <> 0) by (apply Rgt_not_eq; apply exp_pos).
  rewrite !Cmod_mul, (Cmod_cexpzt z T), (Cmod_newman_kernel R z HR Hcirc).
  eapply Rle_trans.
  - apply Rmult_le_compat_r; [ | apply (LT_left_bound f Hfc B Hfb z HzL T HT) ].
    apply Rmult_le_pos; [ left; apply exp_pos | ].
    unfold Rdiv; apply Rmult_le_pos;
      [ apply Rmult_le_pos; [ lra | apply Rabs_pos ]
      | left; apply Rinv_0_lt_compat; nra ].
  - rewrite (Rabs_left (Re z)) by exact HzL.
    rewrite exp_Ropp.
    apply Req_le; field; repeat split;
      solve [ assumption | (intro Hc; lra) | (intro Hc; nra)
            | (intro Hc; pose proof (exp_pos (Re z * T)); lra) ].
Qed.

Print Assumptions LT_left_bound.
Print Assumptions left_arc_bound.

(* ================================================================= *)
(*  END NewmanLeft.v — the left g_T piece, same 4B/R^2 bound.             *)
(*  With right_arc_bound (right, g-g_T) and newman_arc_ML, both semicircle *)
(*  g_T contributions are O(B/R).  Remaining: the left g piece (analytic   *)
(*  continuation, e^{zT}->0), Cauchy's formula on the contour, and the      *)
(*  T->oo, R->oo limits.                                                   *)
(* ================================================================= *)
