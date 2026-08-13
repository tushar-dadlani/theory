(* ================================================================= *)
(*  GammaCRealAxis.v  (Block B of docs/complex_gamma_plan.md)          *)
(*                                                                    *)
(*  The complex Gamma function GammaC is REAL and STRICTLY POSITIVE    *)
(*  on the positive real axis, hence nonvanishing there.  This is the  *)
(*  real-axis ANCHOR for the Riemann-Siegel phase route: on R+ the      *)
(*  continuous argument of GammaC is exactly 0 (GammaC sits on the      *)
(*  positive real ray), so the accumulated argument                    *)
(*     ArgGamma(t) = Im (Clog (GammaC (1/4 + i t/2)))                   *)
(*  can be based at a real point where it is 0.                        *)
(*                                                                    *)
(*  PROVED (axiom-clean, standard classical-Reals only):               *)
(*   - Gam_ne0: the real Gamma is nonzero on (0,oo) (from Gam_pos);    *)
(*   - GammaC_real_Re / _Im: GammaC(RtoC s) = Gam s (real, Im = 0);    *)
(*   - GammaC_real_pos: 0 < Re (GammaC (RtoC s));                       *)
(*   - GammaC_ne0_real: GammaC(RtoC s) <> 0;                            *)
(*   - GammaC_real_axis_anchor: Im = 0 AND Re > 0 on R+ -- the arg-0    *)
(*     anchor.                                                          *)
(*                                                                    *)
(*  SCOPE / remaining gap: full nonvanishing GammaC z <> 0 for all      *)
(*  Re z > 0 (i.e. "Gamma has no zeros") needs the reflection formula   *)
(*  Gamma(z)Gamma(1-z) = pi/sin(pi z) or the Weierstrass product --     *)
(*  neither is in the repo.  This module establishes the real-axis      *)
(*  base case + anchor that the continuous-argument route starts from;  *)
(*  the off-axis nonvanishing stays the standing gap.                   *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra.
Require Import ComplexField GammaReal GammaC XiReflection.
Open Scope R_scope.

(* the real Gamma is nonzero on (0,oo) *)
Lemma Gam_ne0 : forall a (Ha : 0 < a), Gam a Ha <> 0.
Proof. intros a Ha; apply Rgt_not_eq, Gam_pos. Qed.

(* GammaC on the real axis is exactly the real Gamma (real part) ... *)
Lemma GammaC_real_Re : forall s (Hs : 0 < s), Re (GammaC (RtoC s)) = Gam s Hs.
Proof. intros s Hs; rewrite (GammaC_agree s Hs); unfold RtoC; reflexivity. Qed.

(* ... with vanishing imaginary part. *)
Lemma GammaC_real_Im : forall s (Hs : 0 < s), Im (GammaC (RtoC s)) = 0.
Proof. intros s Hs; rewrite (GammaC_agree s Hs); unfold RtoC; reflexivity. Qed.

(* strictly positive real part on the positive real axis *)
Lemma GammaC_real_pos : forall s (Hs : 0 < s), 0 < Re (GammaC (RtoC s)).
Proof. intros s Hs; rewrite (GammaC_real_Re s Hs); apply Gam_pos. Qed.

(* hence nonvanishing on the positive real axis *)
Theorem GammaC_ne0_real : forall s (Hs : 0 < s), GammaC (RtoC s) <> C0.
Proof.
  intros s Hs H. pose proof (GammaC_real_pos s Hs) as Hp.
  rewrite H in Hp. unfold C0 in Hp; simpl in Hp; lra.
Qed.

(* THE ANCHOR: on R+, GammaC lies on the positive real ray -- Im = 0    *)
(* and Re > 0 -- so its continuous argument there is 0.                 *)
Theorem GammaC_real_axis_anchor : forall s (Hs : 0 < s),
  Im (GammaC (RtoC s)) = 0 /\ 0 < Re (GammaC (RtoC s)).
Proof.
  intros s Hs; split; [ exact (GammaC_real_Im s Hs) | exact (GammaC_real_pos s Hs) ].
Qed.

Print Assumptions GammaC_ne0_real.
Print Assumptions GammaC_real_axis_anchor.
