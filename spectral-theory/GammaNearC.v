(* ================================================================= *)
(*  GammaNearC.v  —  the complex Gamma near-0 piece  gnearC z =         *)
(*  ∫_(0,1] t^{z-1} e^{-t} dt, defined for Re z > 0 (the t^{z-1}         *)
(*  singularity at 0), agreeing with the real gnear.                   *)
(*                                                                    *)
(*  Kernel gnkC z u = Cpw u (z-1) · exp(-u)  (RAW u, no clamp: the      *)
(*  clamp is unusable at 0).  Components are continuous on (0,∞) only   *)
(*  (via Re/Im_Cpw_deriv), so integrability is positivity-gated         *)
(*  (cont_pos_RI).  Built through CImp0_abs.  Axiom-clean.             *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia FunctionalExtensionality.
Require Import ComplexField Cmodulus CexpFull CPowBase GammaReal
        ImproperCv0 ImproperCv1 CImpZero.
Open Scope R_scope.

(* a zero-integral near-0 improper integral (fct_cte 0 to match P14/P15) *)
Lemma improper_zero0 : forall Hf, ImproperCv0 (fct_cte 0) Hf 0.
Proof.
  intros Hf e He0 He1 Hecv.
  assert (Hz : forall k, rint01 (fct_cte 0) Hf (e k) = 0).
  { intro k; rewrite (rint01_val (fct_cte 0) Hf (e k) (He0 k) (He1 k)).
    rewrite (RiemannInt_P5 (Hf (e k) 1 (He0 k) (He1 k)) (RiemannInt_P14 (e k) 1 0)).
    rewrite RiemannInt_P15; ring. }
  apply (Un_cv_ext (fun _ => 0) (fun k => rint01 (fct_cte 0) Hf (e k)) 0);
    [ intro k; symmetry; apply Hz | apply Un_cv_const ].
Qed.

Definition gnkC (z : C) (u : R) : C := Cmul (Cpw u (Cminus z C1)) (RtoC (exp (- u))).

Lemma Re_gnkC_eq : forall z u, Re (gnkC z u) = Re (Cpw u (Cminus z C1)) * exp (- u).
Proof. intros z u; unfold gnkC, Cmul, RtoC; cbn; ring. Qed.
Lemma Im_gnkC_eq : forall z u, Im (gnkC z u) = Im (Cpw u (Cminus z C1)) * exp (- u).
Proof. intros z u; unfold gnkC, Cmul, RtoC; cbn; ring. Qed.

Lemma cont_exp_neg : forall t, continuity_pt (fun u => exp (- u)) t.
Proof.
  intro t; apply derivable_continuous_pt.
  exists (exp (- t) * (-1)).
  apply (derivable_pt_lim_comp (fun u => - u) exp t (-1) (exp (- t))).
  - apply (derivable_pt_lim_opp (fun u => u) t 1); apply derivable_pt_lim_id.
  - apply derivable_pt_lim_exp.
Qed.

Lemma cont_Re_gnkC : forall z t, 0 < t -> continuity_pt (fun u => Re (gnkC z u)) t.
Proof.
  intros z t Ht.
  assert (Heq : (fun u => Re (gnkC z u)) = (fun u => Re (Cpw u (Cminus z C1)) * exp (- u)))
    by (apply functional_extensionality; apply Re_gnkC_eq).
  rewrite Heq; apply continuity_pt_mult; [ | apply cont_exp_neg ].
  apply derivable_continuous_pt; eexists; apply Re_Cpw_deriv; exact Ht.
Qed.

Lemma cont_Im_gnkC : forall z t, 0 < t -> continuity_pt (fun u => Im (gnkC z u)) t.
Proof.
  intros z t Ht.
  assert (Heq : (fun u => Im (gnkC z u)) = (fun u => Im (Cpw u (Cminus z C1)) * exp (- u)))
    by (apply functional_extensionality; apply Im_gnkC_eq).
  rewrite Heq; apply continuity_pt_mult; [ | apply cont_exp_neg ].
  apply derivable_continuous_pt; eexists; apply Im_Cpw_deriv; exact Ht.
Qed.

Definition Hre_gnkC (z : C) := cont_pos_RI (fun u => Re (gnkC z u)) (cont_Re_gnkC z).
Definition Him_gnkC (z : C) := cont_pos_RI (fun u => Im (gnkC z u)) (cont_Im_gnkC z).

Lemma Cmod_gnkC : forall z u, Cmod (gnkC z u) = gnk (Re z) 1 u.
Proof.
  intros z u; unfold gnkC, gnk.
  rewrite Cmod_mul, Cpw_mod, Cmod_RtoC.
  rewrite (Rabs_right (exp (- u))) by (apply Rle_ge; apply Rlt_le; apply exp_pos).
  assert (HRe : Re (Cminus z C1) = Re z - 1) by (unfold Cminus, Cadd, Copp, C1; simpl; ring).
  rewrite HRe; replace (1 * u) with u by ring; reflexivity.
Qed.

Lemma gnkC_real : forall s u, gnkC (RtoC s) u = RtoC (gnk s 1 u).
Proof.
  intros s u; unfold gnkC, gnk.
  assert (HW : Cminus (RtoC s) C1 = RtoC (s - 1))
    by (unfold Cminus, Cadd, Copp, RtoC, C1; apply Ceq; simpl; lra).
  rewrite HW, Cpw_RtoC, <- RtoC_mul.
  f_equal; replace (1 * u) with u by ring; reflexivity.
Qed.

Definition gnearC_sig (z : C) (Hz : 0 < Re z) :
  { I : C | CImp0 (gnkC z) (Hre_gnkC z) (Him_gnkC z) I } :=
  CImp0_abs (gnkC z) (gnk (Re z) 1) (Hf_near (Re z) 1) (gnear (Re z) 1 Hz Rlt_0_1)
    (Hre_gnkC z) (Him_gnkC z)
    (fun x _ _ => Req_le _ _ (Cmod_gnkC z x)) (proj2_sig (gnear_sig (Re z) 1 Hz Rlt_0_1)).

Definition gnearC (z : C) (Hz : 0 < Re z) : C := proj1_sig (gnearC_sig z Hz).

Lemma gnearC_spec : forall z (Hz : 0 < Re z),
  CImp0 (gnkC z) (Hre_gnkC z) (Him_gnkC z) (gnearC z Hz).
Proof. intros z Hz; exact (proj2_sig (gnearC_sig z Hz)). Qed.

Lemma gnearC_agree : forall s (Hs : 0 < s) (Hz : 0 < Re (RtoC s)),
  gnearC (RtoC s) Hz = RtoC (gnear s 1 Hs Rlt_0_1).
Proof.
  intros s Hs Hz; destruct (gnearC_spec (RtoC s) Hz) as [HRe HIm]; apply Ceq; simpl.
  - apply (improper_unique0 (fun u => Re (gnkC (RtoC s) u)) (Hre_gnkC (RtoC s))
             (gnk s 1) (Hf_near s 1) (Re (gnearC (RtoC s) Hz)) (gnear s 1 Hs Rlt_0_1));
      [ intros x _ _; rewrite gnkC_real; reflexivity | exact HRe
      | exact (proj2_sig (gnear_sig s 1 Hs Rlt_0_1)) ].
  - apply (improper_unique0 (fun u => Im (gnkC (RtoC s) u)) (Him_gnkC (RtoC s))
             (fct_cte 0) (fun x y _ _ => RiemannInt_P14 x y 0) (Im (gnearC (RtoC s) Hz)) 0);
      [ intros x _ _; rewrite gnkC_real; reflexivity | exact HIm | apply improper_zero0 ].
Qed.

Print Assumptions gnearC_agree.

(* ================================================================= *)
(*  END GammaNearC.v (near-0 kernel, value, agreement).               *)
(* ================================================================= *)
