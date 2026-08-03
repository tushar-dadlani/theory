(* ================================================================= *)
(*  CPower.v  —  holomorphy of the complex power c^v (real base c>0)   *)
(*  in its exponent v.                                                 *)
(*                                                                    *)
(*  Cpw_deriv : d/dv (c^v) = ln c · c^v, proved by the same shift +    *)
(*  Cexpf_remainder estimate used for TC_entire (Cpw c (v+h) =         *)
(*  Cpw c v · Cexpf(h·ln c), quadratic remainder).  This is the core  *)
(*  building block for a complex Dirichlet/Euler-Maclaurin zeta on the *)
(*  critical strip.  Axiom-clean.                                      *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra.
Require Import ComplexField Cmodulus CexpFull CexpRemainder Holomorphic.
Open Scope R_scope.

Lemma Cpw_deriv : forall c w0, 0 < c ->
  is_Cderiv (fun v => Cpw c v) w0 (Cmul (RtoC (ln c)) (Cpw c w0)).
Proof.
  intros c w0 Hc eps Heps.
  set (P := Cmod (Cpw c w0)).
  set (L := Rabs (ln c)).
  set (K := 3 * P * L ^ 2 * exp L).
  assert (HP : 0 <= P) by apply Cmod_nonneg.
  assert (HL : 0 <= L) by apply Rabs_pos.
  assert (HK : 0 <= K).
  { unfold K.
    apply Rmult_le_pos; [ | left; apply exp_pos ].
    apply Rmult_le_pos; [ | apply pow_le; exact HL ].
    apply Rmult_le_pos; lra. }
  assert (Hd : 0 < eps / (K + 1)) by (apply Rdiv_lt_0_compat; lra).
  exists (Rmin 1 (eps / (K + 1))); split.
  - unfold Rmin; destruct (Rle_dec 1 (eps / (K + 1))); lra.
  - intros h Hh.
    assert (Hh1 : Cmod h <= 1) by (pose proof (Rmin_l 1 (eps / (K + 1))); lra).
    assert (Hh2 : Cmod h < eps / (K + 1)) by (pose proof (Rmin_r 1 (eps / (K + 1))); lra).
    set (w := Cmul h (RtoC (ln c))).
    assert (Hrem : Cminus (Cminus (Cpw c (Cadd w0 h)) (Cpw c w0))
                     (Cmul (Cmul (RtoC (ln c)) (Cpw c w0)) h)
                 = Cmul (Cpw c w0) (Cminus (Cminus (Cexpf w) C1) w)).
    { rewrite Cpw_split; unfold w, Cpw; ring. }
    rewrite Hrem, Cmod_mul.
    assert (Hwmod : Cmod w = Cmod h * L)
      by (unfold w, L; rewrite Cmod_mul, Cmod_RtoC; ring).
    apply Rle_trans with (P * (3 * (Cmod w) ^ 2 * exp (Cmod w))).
    + apply Rmult_le_compat_l; [ exact HP | apply Cexpf_remainder ].
    + rewrite Hwmod.
      assert (HmL : Cmod h * L <= L) by nra.
      assert (Hexp : exp (Cmod h * L) <= exp L).
      { destruct (Rle_lt_or_eq_dec _ _ HmL) as [Hlt | Heq];
          [ left; apply exp_increasing; exact Hlt | rewrite Heq; apply Rle_refl ]. }
      apply Rle_trans with (K * Cmod h ^ 2).
      * replace (P * (3 * (Cmod h * L) ^ 2 * exp (Cmod h * L)))
          with ((3 * P * L ^ 2 * Cmod h ^ 2) * exp (Cmod h * L)) by ring.
        unfold K; replace (3 * P * L ^ 2 * exp L * Cmod h ^ 2)
          with ((3 * P * L ^ 2 * Cmod h ^ 2) * exp L) by ring.
        apply Rmult_le_compat_l; [ | exact Hexp ].
        apply Rmult_le_pos; [ | apply pow_le; apply Cmod_nonneg ].
        apply Rmult_le_pos; [ | apply pow_le; exact HL ].
        apply Rmult_le_pos; lra.
      * assert (HcK : Cmod h * (K + 1) < eps).
        { apply Rlt_le_trans with (eps / (K + 1) * (K + 1));
            [ apply Rmult_lt_compat_r; [ lra | exact Hh2 ] | right; field; lra ]. }
        pose proof (Cmod_nonneg h) as Hcm.
        assert (Hsq : 0 <= Cmod h ^ 2) by (apply pow_le; apply Cmod_nonneg).
        nra.
Qed.

Print Assumptions Cpw_deriv.

(* ================================================================= *)
(*  END CPower.v.                                                     *)
(* ================================================================= *)
