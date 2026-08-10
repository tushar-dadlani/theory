(* ================================================================= *)
(*  PerronRemovable.v  —  Perron milestone A1c: the removable extension  *)
(*  of  (y^s − 1)/s  and the rectangle loop  ∮_rect (y^s−1)/s = 0.        *)
(*                                                                    *)
(*  y^s/s = (y^s−1)/s + 1/s.  The first summand qy(s) := (y^s−1)/s has a  *)
(*  REMOVABLE singularity at 0 (value ln y).  Its globally-continuous     *)
(*  extension phi_ext discharges the exceptional-point interface of       *)
(*  CGoursatExcept.PrimE (holo off 0, bounded near 0, globally cont —     *)
(*  the "extension concern" CTruncCauchy left open), so its rectangle     *)
(*  loop telescopes to 0.  Global continuity through 0 rests on the       *)
(*  2nd-order bound Cexpf_remainder:  |e^w − 1 − w| ≤ 3|w|²e^{|w|}.        *)
(*                                                                    *)
(*  THIS FILE (checkpoint 1): the analytic core — extension, off-0/at-0,  *)
(*  holomorphy off 0, the removability estimate, and boundedness.        *)
(*  Axiom-clean.                                                         *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import ComplexField Cmodulus Holomorphic CHoloCalculus CDeriv
        CexpFull CPower CexpRemainder PerronPower.
Open Scope R_scope.

Definition Ceq0_dec (w : C) : {w = C0} + {w <> C0}.
Proof.
  destruct (Req_dec_T (Re w) 0) as [Hr | Hr];
    [ destruct (Req_dec_T (Im w) 0) as [Hi | Hi] | ].
  - left; apply Ceq; cbn; assumption.
  - right; intro H; apply Hi; rewrite H; reflexivity.
  - right; intro H; apply Hr; rewrite H; reflexivity.
Defined.

Lemma exp_le_compat : forall a b, a <= b -> exp a <= exp b.
Proof.
  intros a b Hab; destruct (Rle_lt_or_eq_dec a b Hab) as [Hlt | Heq];
    [ left; apply exp_increasing; exact Hlt | subst; apply Rle_refl ].
Qed.

Lemma Cmod_C0 : Cmod C0 = 0.
Proof. apply (proj2 (Cmod0 C0)); reflexivity. Qed.

(* the raw quotient (y^s − 1)/s *)
Definition qy (y : R) (s : C) : C := Cmul (Cminus (Cpw y s) C1) (Cinv s).

(* the removable extension: value ln y at 0, the quotient elsewhere *)
Definition phi_ext (y : R) (s : C) : C :=
  match Req_dec_T (Re s) 0 with
  | left _ => match Req_dec_T (Im s) 0 with
              | left _ => RtoC (ln y)
              | right _ => qy y s
              end
  | right _ => qy y s
  end.

Lemma phi_ext_at0 : forall y, phi_ext y C0 = RtoC (ln y).
Proof.
  intro y; unfold phi_ext, C0; cbn [Re Im].
  destruct (Req_dec_T 0 0) as [_ | Hn]; [ | lra ].
  destruct (Req_dec_T 0 0) as [_ | Hn]; [ reflexivity | lra ].
Qed.

Lemma phi_ext_off0 : forall y s, s <> C0 -> phi_ext y s = qy y s.
Proof.
  intros y s Hs; unfold phi_ext.
  destruct (Req_dec_T (Re s) 0) as [Hr | Hr]; [ | reflexivity ].
  destruct (Req_dec_T (Im s) 0) as [Hi | Hi]; [ | reflexivity ].
  exfalso; apply Hs; apply Ceq; cbn; [ exact Hr | exact Hi ].
Qed.

(* ----------------------------------------------------------------- *)
(*  local-agreement transfer of the derivative                        *)
(* ----------------------------------------------------------------- *)

Lemma is_Cderiv_congr : forall F G z d r, 0 < r ->
  (forall w, Cmod (Cminus w z) < r -> F w = G w) ->
  is_Cderiv G z d -> is_Cderiv F z d.
Proof.
  intros F G z d r Hr Hag HG eps Heps.
  destruct (HG eps Heps) as [del [Hdel Hd]].
  exists (Rmin del r); split; [ apply Rmin_pos; lra | ].
  intros h Hh.
  assert (Hhd : Cmod h < del) by (eapply Rlt_le_trans; [ exact Hh | apply Rmin_l ]).
  assert (Hhr : Cmod h < r) by (eapply Rlt_le_trans; [ exact Hh | apply Rmin_r ]).
  assert (Hz : F z = G z)
    by (apply Hag; replace (Cminus z z) with C0 by ring; rewrite Cmod_C0; lra).
  assert (Hzh : F (Cadd z h) = G (Cadd z h))
    by (apply Hag; replace (Cminus (Cadd z h) z) with h by ring; exact Hhr).
  rewrite Hz, Hzh; apply Hd; exact Hhd.
Qed.

(* ----------------------------------------------------------------- *)
(*  holomorphy off 0                                                  *)
(* ----------------------------------------------------------------- *)

Lemma qy_holo : forall y s, 0 < y -> s <> C0 -> exists d, is_Cderiv (qy y) s d.
Proof.
  intros y s Hy Hs; unfold qy.
  eexists.
  apply (Cderiv_div (fun w => Cminus (Cpw y w) C1) (fun w => w) s
           (Cminus (Cmul (RtoC (ln y)) (Cpw y s)) C0) C1).
  - apply Cderiv_minus; [ apply Cpw_deriv; exact Hy | apply Cderiv_const ].
  - apply Cderiv_id.
  - exact Hs.
Qed.

Lemma phi_ext_holo_off0 : forall y s, 0 < y -> s <> C0 ->
  exists d, is_Cderiv (phi_ext y) s d.
Proof.
  intros y s Hy Hs; destruct (qy_holo y s Hy Hs) as [d Hd]; exists d.
  apply (is_Cderiv_congr (phi_ext y) (qy y) s d (Cmod s)).
  - apply Cmod_pos_ne0; exact Hs.
  - intros w Hw; apply phi_ext_off0.
    intro Hw0; subst w.
    assert (Cmod (Cminus C0 s) = Cmod s)
      by (replace (Cminus C0 s) with (Copp s) by ring; apply Cmod_opp).
    lra.
  - exact Hd.
Qed.

(* ----------------------------------------------------------------- *)
(*  the removability estimate (heart):  |qy(w) − ln y| ≤ 3|w|(ln y)²e^…   *)
(* ----------------------------------------------------------------- *)

Lemma qy_remainder : forall y w, 0 < y -> w <> C0 ->
  Cmod (Cminus (qy y w) (RtoC (ln y)))
  <= 3 * Cmod w * (Rabs (ln y)) ^ 2 * exp (Cmod w * Rabs (ln y)).
Proof.
  intros y w Hy Hw.
  set (w' := Cmul w (RtoC (ln y))).
  assert (Hwi : Cmul w (Cinv w) = C1)
    by (replace (Cmul w (Cinv w)) with (Cmul (Cinv w) w) by ring; apply Cinv_l; exact Hw).
  assert (Hlny : Cmul w' (Cinv w) = RtoC (ln y)).
  { unfold w'; replace (Cmul (Cmul w (RtoC (ln y))) (Cinv w))
      with (Cmul (RtoC (ln y)) (Cmul w (Cinv w))) by ring.
    rewrite Hwi; ring. }
  (* algebraic identity:  qy − ln y = (e^{w'} − 1 − w')·(1/w) *)
  assert (Hid : Cminus (qy y w) (RtoC (ln y))
                = Cmul (Cminus (Cminus (Cexpf w') C1) w') (Cinv w)).
  { unfold qy, Cpw; fold w'; rewrite <- Hlny; ring. }
  rewrite Hid, Cmod_mul, (Cmod_inv w Hw).
  (* |w'| = |w|·|ln y| *)
  assert (Hmw' : Cmod w' = Cmod w * Rabs (ln y))
    by (unfold w'; rewrite Cmod_mul, Cmod_RtoC; reflexivity).
  assert (Hr : 0 < Cmod w) by (apply Cmod_pos_ne0; exact Hw).
  pose proof (Cexpf_remainder w') as Hrem.
  apply Rle_trans with (3 * (Cmod w') ^ 2 * exp (Cmod w') * / Cmod w).
  - apply Rmult_le_compat_r; [ left; apply Rinv_0_lt_compat; exact Hr | exact Hrem ].
  - rewrite Hmw'; apply Req_le; field; lra.
Qed.

(* ----------------------------------------------------------------- *)
(*  boundedness near 0                                                *)
(* ----------------------------------------------------------------- *)

Lemma phi_ext_bd : forall y, 0 < y -> exists M eta, 0 < eta /\
  forall w, Cmod (Cminus w C0) < eta -> Cmod (phi_ext y w) <= M.
Proof.
  intros y Hy.
  set (L := Rabs (ln y)).
  exists (Rabs (ln y) + 3 * 1 * L ^ 2 * exp (1 * L)), 1.
  split; [ lra | ].
  intros w Hw. replace (Cminus w C0) with w in Hw by ring.
  assert (HLpos : 0 <= 3 * 1 * L ^ 2 * exp (1 * L)).
  { pose proof (pow2_ge_0 L); pose proof (exp_pos (1 * L)); nra. }
  destruct (Ceq0_dec w) as [Hw0 | Hw0].
  - (* w = 0 *)
    subst w; rewrite phi_ext_at0, Cmod_RtoC. unfold L in *; lra.
  - (* w ≠ 0 *)
    rewrite phi_ext_off0 by exact Hw0.
    pose proof (qy_remainder y w Hy Hw0) as Hrem.
    assert (Htri : Cmod (qy y w) <= Cmod (Cminus (qy y w) (RtoC (ln y))) + Cmod (RtoC (ln y))).
    { replace (Cmod (qy y w))
        with (Cmod (Cadd (Cminus (qy y w) (RtoC (ln y))) (RtoC (ln y))))
        by (f_equal; ring).
      apply Cmod_triangle. }
    rewrite Cmod_RtoC in Htri.
    assert (Hw1 : Cmod w <= 1) by lra.
    assert (Hmono : 3 * Cmod w * L ^ 2 * exp (Cmod w * L) <= 3 * 1 * L ^ 2 * exp (1 * L)).
    { apply Rmult_le_compat.
      - pose proof (pow2_ge_0 L); pose proof (Cmod_nonneg w); nra.
      - left; apply exp_pos.
      - apply Rmult_le_compat_r; [ apply pow2_ge_0 | ].
        apply Rmult_le_compat_l; [ lra | exact Hw1 ].
      - apply exp_le_compat, Rmult_le_compat_r; [ unfold L; apply Rabs_pos | exact Hw1 ]. }
    unfold L in *; lra.
Qed.

(* ================================================================= *)
(*  END PerronRemovable.v (checkpoint 1) — removable extension core.     *)
(* ================================================================= *)
