(* ================================================================= *)
(*  PerronPower.v  —  Perron milestone A1a: the kernel y^s/s and the     *)
(*  residue-on-a-circle  ∮_{|z|=R} y^z/z dz = 2πi.                        *)
(*                                                                    *)
(*  y^s is the complex power `Cpw y s = Cexpf(s·ln y)` (CexpFull); it is  *)
(*  entire with d/ds y^s = ln y·y^s (CPower.Cpw_deriv), and y^0 = 1.      *)
(*  So the Cauchy integral formula (CUnifCont.cauchy_formula_full, the    *)
(*  Harc_uc-discharged wrapper of CCauchyFormula) applied to F := Cpw y   *)
(*  gives ∮ y^z/z = 2πi·y^0 = 2πi — the residue value every downstream    *)
(*  Perron brick cites.  Axiom-clean.                                    *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import ComplexField Cmodulus CIntegral2 CPathIntegral
        CexpFull CPower CDeriv Holomorphic CHoloCalculus CSegInt
        EulerFormula CUnifCont.
Require ThetaTailEntire.
Open Scope R_scope.

(* the Perron kernel y^s / s *)
Definition Kperron (y : R) (s : C) : C := Cmul (Cpw y s) (Cinv s).

(* ----------------------------------------------------------------- *)
(*  y^0 = 1                                                           *)
(* ----------------------------------------------------------------- *)

Lemma Cpw_exp0 : forall y, Cpw y C0 = C1.
Proof.
  intro y; unfold Cpw.
  replace (Cmul C0 (RtoC (ln y))) with C0 by ring.
  unfold Cexpf, C0; cbn [Re Im].
  rewrite exp_0, Cexp_0.
  unfold RtoC, C1, Cmul; apply Ceq; cbn; ring.
Qed.

(* ----------------------------------------------------------------- *)
(*  continuity of y^s and of its derivative (along all paths)        *)
(* ----------------------------------------------------------------- *)

Lemma CcontC_Cpw : forall y, CcontC (Cpw y).
Proof.
  intros y g Hg; unfold Cpw.
  apply ThetaTailEntire.Ccont_Cexpf.
  apply Ccont_mul; [ exact Hg | apply Ccont_const ].
Qed.

Lemma CcontC_Fp : forall y, CcontC (fun z => Cmul (RtoC (ln y)) (Cpw y z)).
Proof.
  intros y g Hg; apply Ccont_scal, (CcontC_Cpw y g Hg).
Qed.

(* the derivative of y^s is itself complex-differentiable (needed for    *)
(* the pointwise-continuity hypothesis of cauchy_formula_full)           *)
Lemma Fp_deriv : forall y, 0 < y -> forall z,
  is_Cderiv (fun z => Cmul (RtoC (ln y)) (Cpw y z)) z
            (Cmul (RtoC (ln y)) (Cmul (RtoC (ln y)) (Cpw y z))).
Proof.
  intros y Hy z; apply Cderiv_cscal, Cpw_deriv; exact Hy.
Qed.

Lemma Fp_pcont : forall y, 0 < y ->
  forall w eps, 0 < eps -> exists del, 0 < del /\
    forall w', Cmod (Cminus w' w) < del ->
      Cmod (Cminus (Cmul (RtoC (ln y)) (Cpw y w')) (Cmul (RtoC (ln y)) (Cpw y w))) < eps.
Proof.
  intros y Hy w eps Heps.
  destruct (is_Cderiv_cont _ w _ (Fp_deriv y Hy w) eps Heps) as [del [Hd Hc]].
  exists del; split; [ exact Hd | ].
  intros w' Hw'.
  assert (Hwe : w' = Cadd w (Cminus w' w)) by ring.
  rewrite Hwe; apply Hc; exact Hw'.
Qed.

(* ----------------------------------------------------------------- *)
(*  the residue on a circle                                           *)
(* ----------------------------------------------------------------- *)

Theorem perron_residue_circle : forall (y : R) (Hy : 0 < y) (R : R) (HR : 0 < R)
  (Hpf : Ccont (fun u => Cmul (Cmul (Cpw y (arc R u)) (Cinv (arc R u))) (arc' R u))),
  pathint (arc R) (arc' R) (fun z => Cmul (Cpw y z) (Cinv z)) Hpf 0 (2 * PI)
  = mkC 0 (2 * PI).
Proof.
  intros y Hy R HR Hpf.
  rewrite (cauchy_formula_full (Cpw y) (fun z => Cmul (RtoC (ln y)) (Cpw y z))
             (CcontC_Cpw y) (CcontC_Fp y) (fun z => Cpw_deriv y z Hy)
             (Fp_pcont y Hy) R HR Hpf).
  rewrite Cpw_exp0.
  unfold C1, Cmul; apply Ceq; cbn; ring.
Qed.

Print Assumptions perron_residue_circle.

(* ================================================================= *)
(*  END PerronPower.v  —  y^s entire, y^0=1, and ∮_{|z|=R} y^z/z = 2πi.  *)
(*  The residue value + entireness feed every downstream Perron brick.   *)
(* ================================================================= *)
