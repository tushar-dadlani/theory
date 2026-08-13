(* ================================================================= *)
(*  CCauchyAnalytic.v  (identity-theorem plan, analyticity master key) *)
(*                                                                    *)
(*  The complex differentiation-under-the-integral for the Cauchy      *)
(*  kernel (n = 1): w |-> oint_{|z|=R} g(z)/(z-w) dz is holomorphic in  *)
(*  w (|w| < R) with derivative oint g(z)/(z-w)^2 dz.                   *)
(*                                                                    *)
(*  This file: the reusable ALGEBRAIC + MODULUS core of the first-order *)
(*  remainder estimate,                                                *)
(*    1/(zeta-h) - 1/zeta - h/zeta^2 = h^2 / ((zeta-h) zeta^2),         *)
(*  and its modulus, plus the pointwise integrand bound feeding the ML  *)
(*  estimate.  (The is_Cderiv packaging, with a clamp to totalise the   *)
(*  parametrised integral, is the next installment.)                   *)
(*                                                                    *)
(*  Axioms: standard classical-Reals only.                            *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import ComplexField Cmodulus CDeriv CWindingOffCenter.
Open Scope R_scope.

(* ---- the first-order Cauchy-kernel remainder, as pure C-field algebra ---- *)
Lemma cauchy_bracket : forall (zeta h : C),
  zeta <> C0 -> Cminus zeta h <> C0 ->
  Cminus (Cminus (Cinv (Cminus zeta h)) (Cinv zeta)) (Cmul h (Cinv (Cmul zeta zeta)))
  = Cmul (Cmul h h) (Cinv (Cmul (Cminus zeta h) (Cmul zeta zeta))).
Proof.
  intros zeta h Hz Hzh. field. split; assumption.
Qed.

(* ---- its modulus ---- *)
Lemma cauchy_bracket_mod : forall (zeta h : C),
  zeta <> C0 -> Cminus zeta h <> C0 ->
  Cmod (Cmul (Cmul h h) (Cinv (Cmul (Cminus zeta h) (Cmul zeta zeta))))
  = Cmod h * Cmod h * / (Cmod (Cminus zeta h) * (Cmod zeta * Cmod zeta)).
Proof.
  intros zeta h Hz Hzh.
  assert (HY : Cmul (Cminus zeta h) (Cmul zeta zeta) <> C0)
    by (apply Cmul_ne0; [ exact Hzh | apply Cmul_ne0; exact Hz ]).
  rewrite Cmod_mul, Cmod_mul, (Cmod_inv _ HY), Cmod_mul, Cmod_mul.
  reflexivity.
Qed.

(* ---- the remainder modulus is bounded by  |h|^2 / (m' * m^2) ---- *)
Lemma cauchy_bracket_bound : forall (zeta h : C) (m mp : R),
  zeta <> C0 -> Cminus zeta h <> C0 ->
  0 < mp -> mp <= Cmod (Cminus zeta h) ->
  0 < m -> m <= Cmod zeta ->
  Cmod (Cmul (Cmul h h) (Cinv (Cmul (Cminus zeta h) (Cmul zeta zeta))))
  <= Cmod h * Cmod h * / (mp * (m * m)).
Proof.
  intros zeta h m mp Hz Hzh Hmp Hmpb Hm Hmb.
  rewrite cauchy_bracket_mod by assumption.
  assert (Hhh : 0 <= Cmod h * Cmod h)
    by (apply Rmult_le_pos; apply Cmod_nonneg).
  apply Rmult_le_compat_l; [ exact Hhh | ].
  apply Rinv_le_contravar.
  - apply Rmult_lt_0_compat; [ exact Hmp | apply Rmult_lt_0_compat; exact Hm ].
  - apply Rmult_le_compat; try lra.
    + apply Rmult_le_pos; lra.
    + apply Rmult_le_compat; lra.
Qed.

Print Assumptions cauchy_bracket.
Print Assumptions cauchy_bracket_bound.
