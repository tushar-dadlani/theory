(* ================================================================= *)
(*  CBaseDeriv3.v  —  Milestone B, brick B6a: base (t) derivatives of   *)
(*  the THIRD s-derivative kernel, one order up from CBaseDeriv.        *)
(*                                                                    *)
(*  d3kb w t = -(ln t)^3 · t^w  is the pole-free third s-derivative      *)
(*  kernel of gC (at exponent w = -s); d3k s t = d3kb (Copp s) t.        *)
(*  Its t-derivative dd3kb and the modulus bound                        *)
(*    |dd3kb w t| <= (3 (ln t)^2 + (ln t)^3 |w|) t^{Re w-1}              *)
(*  feed the base double-MVT for the third-derivative term bound.       *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra FunctionalExtensionality.
Require Import ComplexField Cmodulus CexpFull CPowBase CBaseDeriv.
Open Scope R_scope.

Lemma dln_cube : forall t, 0 < t ->
  derivable_pt_lim (fun u => ln u * ln u * ln u) t (3 * (ln t * ln t) * / t).
Proof.
  intros t Ht.
  replace (3 * (ln t * ln t) * / t)
    with ((2 * ln t * / t) * ln t + (ln t * ln t) * / t) by (field; lra).
  apply (derivable_pt_lim_mult (fun u => ln u * ln u) ln t (2 * ln t * / t) (/ t)).
  - apply dln_sq; exact Ht.
  - apply derivable_pt_lim_ln; exact Ht.
Qed.

Definition d3kb (w : C) (t : R) : C := Cmul (RtoC (- (ln t * ln t * ln t))) (Cpw t w).

Definition dd3kb (w : C) (t : R) : C :=
  Cadd (Cmul (RtoC (- (3 * (ln t * ln t) * / t))) (Cpw t w))
       (Cmul (RtoC (- (ln t * ln t * ln t))) (Cmul w (Cpw t (Cminus w C1)))).

Lemma Re_d3kb_deriv : forall w t, 0 < t ->
  derivable_pt_lim (fun u => Re (d3kb w u)) t (Re (dd3kb w t)).
Proof.
  intros w t Ht.
  assert (Heq : (fun u => Re (d3kb w u))
                = (fun u => (- (ln u * ln u * ln u)) * Re (Cpw u w)))
    by (apply functional_extensionality; intro u; unfold d3kb, Cmul, RtoC; cbn; ring).
  rewrite Heq.
  replace (Re (dd3kb w t))
    with ((- (3 * (ln t * ln t) * / t)) * Re (Cpw t w)
          + (- (ln t * ln t * ln t)) * Re (Cmul w (Cpw t (Cminus w C1))))
    by (unfold dd3kb, Cadd, Cmul, RtoC; cbn; ring).
  apply (derivable_pt_lim_mult (fun u => - (ln u * ln u * ln u)) (fun u => Re (Cpw u w)) t
           (- (3 * (ln t * ln t) * / t)) (Re (Cmul w (Cpw t (Cminus w C1))))).
  - apply (derivable_pt_lim_opp (fun u => ln u * ln u * ln u) t (3 * (ln t * ln t) * / t));
      apply dln_cube; exact Ht.
  - apply Re_Cpw_deriv; exact Ht.
Qed.

Lemma Im_d3kb_deriv : forall w t, 0 < t ->
  derivable_pt_lim (fun u => Im (d3kb w u)) t (Im (dd3kb w t)).
Proof.
  intros w t Ht.
  assert (Heq : (fun u => Im (d3kb w u))
                = (fun u => (- (ln u * ln u * ln u)) * Im (Cpw u w)))
    by (apply functional_extensionality; intro u; unfold d3kb, Cmul, RtoC; cbn; ring).
  rewrite Heq.
  replace (Im (dd3kb w t))
    with ((- (3 * (ln t * ln t) * / t)) * Im (Cpw t w)
          + (- (ln t * ln t * ln t)) * Im (Cmul w (Cpw t (Cminus w C1))))
    by (unfold dd3kb, Cadd, Cmul, RtoC; cbn; ring).
  apply (derivable_pt_lim_mult (fun u => - (ln u * ln u * ln u)) (fun u => Im (Cpw u w)) t
           (- (3 * (ln t * ln t) * / t)) (Im (Cmul w (Cpw t (Cminus w C1))))).
  - apply (derivable_pt_lim_opp (fun u => ln u * ln u * ln u) t (3 * (ln t * ln t) * / t));
      apply dln_cube; exact Ht.
  - apply Im_Cpw_deriv; exact Ht.
Qed.

Lemma Cmod_dd3kb : forall w t, 1 <= t ->
  Cmod (dd3kb w t) <= (3 * (ln t * ln t) + ln t * ln t * ln t * Cmod w) * Rpower t (Re w - 1).
Proof.
  intros w t Ht.
  assert (Htp : 0 < t) by lra.
  assert (Hln : 0 <= ln t) by (rewrite <- ln_1; destruct (Rle_lt_or_eq_dec 1 t Ht) as [H|H];
    [ left; apply ln_increasing; lra | rewrite <- H; apply Rle_refl ]).
  assert (Hpred : Rpower t (Re w) * / t = Rpower t (Re w - 1)) by (apply Rpower_pred; exact Htp).
  unfold dd3kb.
  eapply Rle_trans; [ apply Cmod_triangle | ].
  rewrite !Cmod_mul, !Cmod_RtoC, !Cpw_mod.
  replace (Re (Cminus w C1)) with (Re w - 1) by (unfold Cminus, Cadd, Copp, C1; cbn; ring).
  rewrite (Rabs_left1 (- (3 * (ln t * ln t) * / t))).
  2:{ apply Ropp_le_cancel; rewrite Ropp_involutive, Ropp_0.
      apply Rmult_le_pos; [ apply Rmult_le_pos; [ lra | apply Rmult_le_pos; exact Hln ]
        | apply Rlt_le; apply Rinv_0_lt_compat; exact Htp ]. }
  rewrite (Rabs_left1 (- (ln t * ln t * ln t))).
  2:{ apply Ropp_le_cancel; rewrite Ropp_involutive, Ropp_0.
      apply Rmult_le_pos; [ apply Rmult_le_pos; exact Hln | exact Hln ]. }
  rewrite !Ropp_involutive.
  replace (3 * (ln t * ln t) * / t * Rpower t (Re w))
    with (3 * (ln t * ln t) * (Rpower t (Re w) * / t)) by ring.
  rewrite Hpred; apply Req_le; ring.
Qed.

Print Assumptions Re_d3kb_deriv.
Print Assumptions Cmod_dd3kb.

(* ================================================================= *)
(*  END CBaseDeriv3.v  —  base derivatives of the third-deriv kernel.   *)
(* ================================================================= *)
