(* ================================================================= *)
(*  CBaseDeriv.v  —  base (t) derivatives of the s-derivative kernels   *)
(*  of the complex power, toward the (ln)^2 double-MVT bound on the     *)
(*  second s-derivative of gtermC.                                     *)
(*                                                                    *)
(*  d2k w t = (ln t)^2 · t^w  is the second s-derivative kernel of      *)
(*  gC (at exponent w = -s).  Its t-derivative dd2k and the modulus     *)
(*  bound |dd2k| <= (2 ln t + (ln t)^2 |w|) t^{Re w-1} feed the base     *)
(*  double-MVT.  Axiom-clean.                                          *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra FunctionalExtensionality.
Require Import ComplexField Cmodulus CexpFull CPowBase.
Open Scope R_scope.

Lemma dln_sq : forall t, 0 < t -> derivable_pt_lim (fun u => ln u * ln u) t (2 * ln t * / t).
Proof.
  intros t Ht.
  replace (2 * ln t * / t) with (/ t * ln t + ln t * / t) by (field; lra).
  apply (derivable_pt_lim_mult ln ln t (/ t) (/ t)); apply derivable_pt_lim_ln; exact Ht.
Qed.

Definition d2k (w : C) (t : R) : C := Cmul (RtoC (ln t * ln t)) (Cpw t w).

Definition dd2k (w : C) (t : R) : C :=
  Cadd (Cmul (RtoC (2 * ln t * / t)) (Cpw t w))
       (Cmul (RtoC (ln t * ln t)) (Cmul w (Cpw t (Cminus w C1)))).

Lemma Re_d2k_deriv : forall w t, 0 < t ->
  derivable_pt_lim (fun u => Re (d2k w u)) t (Re (dd2k w t)).
Proof.
  intros w t Ht.
  assert (Heq : (fun u => Re (d2k w u)) = (fun u => (ln u * ln u) * Re (Cpw u w)))
    by (apply functional_extensionality; intro u; unfold d2k, Cmul, RtoC; cbn; ring).
  rewrite Heq.
  replace (Re (dd2k w t))
    with (2 * ln t * / t * Re (Cpw t w)
          + ln t * ln t * Re (Cmul w (Cpw t (Cminus w C1))))
    by (unfold dd2k, Cadd, Cmul, RtoC; cbn; ring).
  apply (derivable_pt_lim_mult (fun u => ln u * ln u) (fun u => Re (Cpw u w)) t
           (2 * ln t * / t) (Re (Cmul w (Cpw t (Cminus w C1))))).
  - apply dln_sq; exact Ht.
  - apply Re_Cpw_deriv; exact Ht.
Qed.

Lemma Im_d2k_deriv : forall w t, 0 < t ->
  derivable_pt_lim (fun u => Im (d2k w u)) t (Im (dd2k w t)).
Proof.
  intros w t Ht.
  assert (Heq : (fun u => Im (d2k w u)) = (fun u => (ln u * ln u) * Im (Cpw u w)))
    by (apply functional_extensionality; intro u; unfold d2k, Cmul, RtoC; cbn; ring).
  rewrite Heq.
  replace (Im (dd2k w t))
    with (2 * ln t * / t * Im (Cpw t w)
          + ln t * ln t * Im (Cmul w (Cpw t (Cminus w C1))))
    by (unfold dd2k, Cadd, Cmul, RtoC; cbn; ring).
  apply (derivable_pt_lim_mult (fun u => ln u * ln u) (fun u => Im (Cpw u w)) t
           (2 * ln t * / t) (Im (Cmul w (Cpw t (Cminus w C1))))).
  - apply dln_sq; exact Ht.
  - apply Im_Cpw_deriv; exact Ht.
Qed.

Lemma Cmod_dd2k : forall w t, 1 <= t ->
  Cmod (dd2k w t) <= (2 * ln t + ln t * ln t * Cmod w) * Rpower t (Re w - 1).
Proof.
  intros w t Ht.
  assert (Htp : 0 < t) by lra.
  assert (Hln : 0 <= ln t) by (rewrite <- ln_1; destruct (Rle_lt_or_eq_dec 1 t Ht) as [H|H];
    [ left; apply ln_increasing; lra | rewrite <- H; apply Rle_refl ]).
  assert (Hpred : Rpower t (Re w) * / t = Rpower t (Re w - 1)) by (apply Rpower_pred; exact Htp).
  unfold dd2k.
  eapply Rle_trans; [ apply Cmod_triangle | ].
  rewrite !Cmod_mul, !Cmod_RtoC, !Cpw_mod.
  replace (Re (Cminus w C1)) with (Re w - 1) by (unfold Cminus, Cadd, Copp, C1; cbn; ring).
  rewrite (Rabs_right (2 * ln t * / t)) by (apply Rle_ge; apply Rmult_le_pos;
    [ apply Rmult_le_pos; lra | apply Rlt_le; apply Rinv_0_lt_compat; exact Htp ]).
  rewrite (Rabs_right (ln t * ln t)) by (apply Rle_ge; apply Rmult_le_pos; exact Hln).
  replace (2 * ln t * / t * Rpower t (Re w))
    with (2 * ln t * (Rpower t (Re w) * / t)) by ring.
  rewrite Hpred.
  apply Req_le; ring.
Qed.

Print Assumptions Re_d2k_deriv.
Print Assumptions Cmod_dd2k.

(* ================================================================= *)
(*  END CBaseDeriv.v (part 1: the second-s-derivative kernel of gC).   *)
(* ================================================================= *)
