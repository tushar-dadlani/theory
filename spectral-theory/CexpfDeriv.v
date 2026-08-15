(* ================================================================= *)
(*  CexpfDeriv.v   (the complex exponential is its own derivative)       *)
(*                                                                    *)
(*  is_Cderiv Cexpf w (Cexpf w),  proven directly from the Taylor        *)
(*  remainder bound  |Cexpf h - 1 - h| <= 3|h|^2 e^{|h|}                 *)
(*  (CexpRemainder.Cexpf_remainder) and the addition formula             *)
(*  Cexpf(w+h) = Cexpf w . Cexpf h.  With the chain rule this gives       *)
(*  the derivative of  Cexpf o g  for any holomorphic g.                 *)
(*                                                                    *)
(*  Axioms: standard classical-Reals only.                            *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import ComplexField Cmodulus CexpFull CexpRemainder Holomorphic CDeriv.
Open Scope R_scope.

Lemma Cexpf_deriv : forall w, is_Cderiv Cexpf w (Cexpf w).
Proof.
  intros w eps Heps.
  set (C := 3 * exp (Re w) * exp 1).
  assert (Hew : 0 < exp (Re w)) by apply exp_pos.
  assert (He1 : 0 < exp 1) by apply exp_pos.
  assert (HC0 : 0 <= C) by (unfold C; repeat apply Rmult_le_pos; lra).
  exists (Rmin 1 (eps / (C + 1))).
  split.
  - apply Rmin_glb_lt; [ lra | apply Rdiv_lt_0_compat; lra ].
  - intros h Hh.
    assert (Hh1 : Cmod h < 1) by (eapply Rlt_le_trans; [ exact Hh | apply Rmin_l ]).
    assert (Hh2 : Cmod h < eps / (C + 1)) by (eapply Rlt_le_trans; [ exact Hh | apply Rmin_r ]).
    pose proof (Cmod_nonneg h) as Hmh.
    replace (Cminus (Cminus (Cexpf (Cadd w h)) (Cexpf w)) (Cmul (Cexpf w) h))
       with (Cmul (Cexpf w) (Cminus (Cminus (Cexpf h) C1) h)) by (rewrite Cexpf_add; ring).
    rewrite Cmod_mul, Cmod_Cexpf.
    assert (Hsq : 0 <= Cmod h * Cmod h) by (apply Rmult_le_pos; exact Hmh).
    assert (Hstep1 : exp (Re w) * Cmod (Cminus (Cminus (Cexpf h) C1) h)
                     <= C * (Cmod h * Cmod h)).
    { apply Rle_trans with (exp (Re w) * (3 * Cmod h ^ 2 * exp (Cmod h))).
      - apply Rmult_le_compat_l; [ lra | apply Cexpf_remainder ].
      - assert (Hexp : exp (Cmod h) <= exp 1) by (apply Rlt_le, exp_increasing; exact Hh1).
        unfold C. replace (Cmod h ^ 2) with (Cmod h * Cmod h) by ring.
        replace (exp (Re w) * (3 * (Cmod h * Cmod h) * exp (Cmod h)))
          with ((3 * exp (Re w) * (Cmod h * Cmod h)) * exp (Cmod h)) by ring.
        replace (3 * exp (Re w) * exp 1 * (Cmod h * Cmod h))
          with ((3 * exp (Re w) * (Cmod h * Cmod h)) * exp 1) by ring.
        apply Rmult_le_compat_l; [ | exact Hexp ].
        apply Rmult_le_pos; [ apply Rmult_le_pos; lra | exact Hsq ]. }
    apply Rle_trans with (C * (Cmod h * Cmod h)); [ exact Hstep1 | ].
    assert (HCC : C / (C + 1) <= 1).
    { apply Rmult_le_reg_r with (C + 1); [ lra | ].
      rewrite Rmult_1_l. unfold Rdiv. rewrite Rmult_assoc, Rinv_l by lra. lra. }
    apply Rle_trans with (C * (Cmod h * (eps / (C + 1)))).
    + apply Rmult_le_compat_l; [ exact HC0 | ].
      apply Rmult_le_compat_l; [ exact Hmh | left; exact Hh2 ].
    + replace (C * (Cmod h * (eps / (C + 1)))) with ((C / (C + 1)) * (eps * Cmod h))
        by (field; lra).
      rewrite <- (Rmult_1_l (eps * Cmod h)) at 2.
      apply Rmult_le_compat_r; [ apply Rmult_le_pos; lra | exact HCC ].
Qed.

(* chain rule for  Cexpf o g *)
Lemma Cexpf_comp_deriv : forall (g : C -> C) z dg,
  is_Cderiv g z dg -> is_Cderiv (fun w => Cexpf (g w)) z (Cmul (Cexpf (g z)) dg).
Proof.
  intros g z dg Hg.
  apply (Cderiv_comp Cexpf g z (Cexpf (g z)) dg); [ apply Cexpf_deriv | exact Hg ].
Qed.

Print Assumptions Cexpf_comp_deriv.
