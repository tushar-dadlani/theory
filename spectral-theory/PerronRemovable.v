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
        CIntegral2 CSegInt CexpFull CPower CexpRemainder PerronPower
        CPrimConv CPathIntegral CPathFTC CGoursatExcept CTruncCauchy.
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

(* ----------------------------------------------------------------- *)
(*  continuity bridge:  ε-δ (Cmod)  ⇄  continuity_pt, and CcontC          *)
(* ----------------------------------------------------------------- *)

Lemma Rabs_Re_le_Cmod : forall c, Rabs (Re c) <= Cmod c.
Proof.
  intro c; unfold Cmod, Cnorm2; rewrite <- (sqrt_Rsqr_abs (Re c)).
  apply sqrt_le_1_alt; unfold Rsqr; pose proof (Rle_0_sqr (Im c)); unfold Rsqr in *; nra.
Qed.

Lemma Rabs_Im_le_Cmod : forall c, Rabs (Im c) <= Cmod c.
Proof.
  intro c; unfold Cmod, Cnorm2; rewrite <- (sqrt_Rsqr_abs (Im c)).
  apply sqrt_le_1_alt; unfold Rsqr; pose proof (Rle_0_sqr (Re c)); unfold Rsqr in *; nra.
Qed.

Lemma Cmod_le_sum : forall c, Cmod c <= Rabs (Re c) + Rabs (Im c).
Proof.
  intro c; unfold Cmod, Cnorm2.
  rewrite <- (sqrt_Rsqr (Rabs (Re c) + Rabs (Im c)))
    by (apply Rplus_le_le_0_compat; apply Rabs_pos).
  apply sqrt_le_1_alt; unfold Rsqr.
  pose proof (Rabs_pos (Re c)); pose proof (Rabs_pos (Im c)).
  pose proof (Rsqr_abs (Re c)); pose proof (Rsqr_abs (Im c)); unfold Rsqr in *; nra.
Qed.

Lemma continuity_pt_from_bound : forall (f : R -> R) x,
  (forall eps, 0 < eps -> exists del, 0 < del /\
     forall u, Rabs (u - x) < del -> Rabs (f u - f x) < eps) ->
  continuity_pt f x.
Proof.
  intros f x Hb; unfold continuity_pt, continue_in, limit1_in, limit_in; intros eps Heps.
  destruct (Hb eps Heps) as [del [Hdel Hc]].
  exists del; split; [ exact Hdel | ].
  intros u [_ Hdist]; unfold R_dist in *; apply Hc; exact Hdist.
Qed.

Lemma continuity_pt_bound : forall (f : R -> R) x, continuity_pt f x ->
  forall eps, 0 < eps -> exists del, 0 < del /\
    forall u, Rabs (u - x) < del -> Rabs (f u - f x) < eps.
Proof.
  intros f x Hf eps Heps;
    unfold continuity_pt, continue_in, limit1_in, limit_in in Hf.
  destruct (Hf eps Heps) as [del [Hdel Hc]].
  exists del; split; [ exact Hdel | ].
  intros u Hu; destruct (Req_dec u x) as [Heq | Hne].
  - subst u; rewrite Rminus_diag, Rabs_R0; exact Heps.
  - apply (Hc u); split; [ split; [ exact I | apply not_eq_sym; exact Hne ] | exact Hu ].
Qed.

(* pointwise Cmod-continuity everywhere ⇒ CcontC *)
Lemma ptcont_CcontC : forall F,
  (forall z eps, 0 < eps -> exists del, 0 < del /\
     forall w, Cmod (Cminus w z) < del -> Cmod (Cminus (F w) (F z)) < eps) ->
  CcontC F.
Proof.
  intros F HF g [HgR HgI]; split; intro x; apply continuity_pt_from_bound; intros eps Heps.
  all: destruct (HF (g x) eps Heps) as [del [Hdel Hb]];
       destruct (continuity_pt_bound _ x (HgR x) (del / 2) ltac:(lra)) as [d1 [Hd1 Hc1]];
       destruct (continuity_pt_bound _ x (HgI x) (del / 2) ltac:(lra)) as [d2 [Hd2 Hc2]];
       exists (Rmin d1 d2); split; [ apply Rmin_pos; lra | ];
       intros u Hu;
       assert (Hu1 : Rabs (Re (g u) - Re (g x)) < del / 2)
         by (apply Hc1; eapply Rlt_le_trans; [ exact Hu | apply Rmin_l ]);
       assert (Hu2 : Rabs (Im (g u) - Im (g x)) < del / 2)
         by (apply Hc2; eapply Rlt_le_trans; [ exact Hu | apply Rmin_r ]);
       assert (Hgd : Cmod (Cminus (g u) (g x)) < del);
       [ eapply Rle_lt_trans; [ apply Cmod_le_sum | ];
         unfold Cminus, Cadd, Copp; cbn [Re Im]; lra
       | pose proof (Hb (g u) Hgd) as Hfb ].
  - replace (Re (F (g u)) - Re (F (g x)))
      with (Re (Cminus (F (g u)) (F (g x)))) by (unfold Cminus, Cadd, Copp; cbn; ring).
    eapply Rle_lt_trans; [ apply Rabs_Re_le_Cmod | exact Hfb ].
  - replace (Im (F (g u)) - Im (F (g x)))
      with (Im (Cminus (F (g u)) (F (g x)))) by (unfold Cminus, Cadd, Copp; cbn; ring).
    eapply Rle_lt_trans; [ apply Rabs_Im_le_Cmod | exact Hfb ].
Qed.

(* ----------------------------------------------------------------- *)
(*  pointwise continuity of phi_ext everywhere, and hence CcontC        *)
(* ----------------------------------------------------------------- *)

Lemma phi_ext_ptcont : forall y, 0 < y -> forall z eps, 0 < eps ->
  exists del, 0 < del /\ forall w, Cmod (Cminus w z) < del ->
    Cmod (Cminus (phi_ext y w) (phi_ext y z)) < eps.
Proof.
  intros y Hy z eps Heps; destruct (Ceq0_dec z) as [Hz0 | Hz0].
  - (* z = 0: removability *)
    subst z; rewrite phi_ext_at0.
    set (L := Rabs (ln y)); set (K := 3 * L ^ 2 * exp L + 1).
    assert (HK : 0 < K) by (unfold K; pose proof (pow2_ge_0 L); pose proof (exp_pos L); nra).
    exists (Rmin 1 (eps / K)); split;
      [ apply Rmin_pos; [ lra | apply Rdiv_lt_0_compat; [ exact Heps | exact HK ] ] | ].
    intros w Hw; replace (Cminus w C0) with w in Hw by ring.
    destruct (Ceq0_dec w) as [Hw0 | Hw0].
    + subst w; rewrite phi_ext_at0.
      replace (Cminus (RtoC (ln y)) (RtoC (ln y))) with C0 by ring; rewrite Cmod_C0; exact Heps.
    + rewrite (phi_ext_off0 y w Hw0).
      pose proof (qy_remainder y w Hy Hw0) as Hrem.
      assert (Hw1 : Cmod w <= 1) by (eapply Rle_trans; [ left; eapply Rlt_le_trans; [ exact Hw | apply Rmin_l ] | apply Rle_refl ]).
      assert (Hwk : Cmod w * K < eps).
      { apply Rlt_le_trans with (eps / K * K);
          [ apply Rmult_lt_compat_r; [ exact HK | eapply Rlt_le_trans; [ exact Hw | apply Rmin_r ] ]
          | apply Req_le; field; lra ]. }
      eapply Rle_lt_trans; [ exact Hrem | ].
      assert (Hmono : 3 * Cmod w * L ^ 2 * exp (Cmod w * L) <= 3 * Cmod w * L ^ 2 * exp L).
      { apply Rmult_le_compat_l;
          [ pose proof (pow2_ge_0 L); pose proof (Cmod_nonneg w); nra
          | apply exp_le_compat; rewrite <- (Rmult_1_l L) at 2;
            apply Rmult_le_compat_r; [ unfold L; apply Rabs_pos | exact Hw1 ] ]. }
      eapply Rle_lt_trans; [ exact Hmono | ].
      unfold K in Hwk; pose proof (Cmod_nonneg w); pose proof (pow2_ge_0 L);
        pose proof (exp_pos L); nra.
  - (* z ≠ 0: phi_ext = qy near z, use is_Cderiv_cont *)
    destruct (qy_holo y z Hy Hz0) as [d Hd].
    destruct (is_Cderiv_cont (qy y) z d Hd eps Heps) as [del0 [Hdel0 Hc]].
    exists (Rmin del0 (Cmod z)); split;
      [ apply Rmin_pos; [ exact Hdel0 | apply Cmod_pos_ne0; exact Hz0 ] | ].
    intros w Hw.
    assert (Hwz : Cmod (Cminus w z) < Cmod z) by (eapply Rlt_le_trans; [ exact Hw | apply Rmin_r ]).
    assert (Hw0 : w <> C0).
    { intro Hc0; subst w.
      assert (Cmod (Cminus C0 z) = Cmod z)
        by (replace (Cminus C0 z) with (Copp z) by ring; apply Cmod_opp).
      lra. }
    rewrite (phi_ext_off0 y w Hw0), (phi_ext_off0 y z Hz0).
    set (h := Cminus w z); assert (Hweq : w = Cadd z h) by (unfold h; ring).
    rewrite Hweq; apply Hc.
    eapply Rlt_le_trans; [ | apply Rmin_l ]; unfold h; exact Hw.
Qed.

Lemma phi_ext_cont : forall y, 0 < y -> CcontC (phi_ext y).
Proof. intros y Hy; apply ptcont_CcontC, phi_ext_ptcont; exact Hy. Qed.

(* ----------------------------------------------------------------- *)
(*  the rectangle loop of phi_ext = 0  (exceptional-point primitive)    *)
(* ----------------------------------------------------------------- *)

Definition Uall : C -> Prop := fun _ => True.

Lemma Uall_conv : Convex Uall.
Proof. intros a b _ _ s _; exact I. Qed.

Lemma Uall_open : Open Uall.
Proof. intros z _; exists 1; split; [ lra | intros; exact I ]. Qed.

Section RectLoop.
Variable y : R.
Hypothesis Hy : 0 < y.

Definition PE : C -> C := PrimE (phi_ext y) (phi_ext_cont y Hy) C1.

(* PE is a primitive of phi_ext everywhere (the exceptional point 0 is absorbed) *)
Lemma HH_all : forall z, is_Cderiv PE z (phi_ext y z).
Proof.
  intro z; unfold PE.
  apply (PrimE_deriv Uall Uall_conv Uall_open (phi_ext y) (phi_ext_cont y Hy) C0 I
           (fun z _ Hz => phi_ext_holo_off0 y z Hy Hz)
           (phi_ext_bd y Hy)
           (fun z _ eps Heps => phi_ext_ptcont y Hy z eps Heps)
           C1 I z I).
Qed.

(* each edge integral telescopes to PE(end) − PE(start) *)
Lemma Iedge : forall P Q
  (Hf : Ccont (fun u => Cmul (phi_ext y (seg P Q u)) (seg' P Q u))),
  pathint (seg P Q) (seg' P Q) (phi_ext y) Hf 0 1 = Cminus (PE Q) (PE P).
Proof.
  intros P Q Hf.
  rewrite (pathint_FTC PE (phi_ext y) (seg P Q) (seg' P Q) Hf 0 1 Rle_0_1
             (fun s _ => HH_all (seg P Q s))
             (fun s _ => chord_Re_deriv P Q s)
             (fun s _ => chord_Im_deriv P Q s)).
  rewrite seg_at1, seg_at0; reflexivity.
Qed.

Theorem phi_ext_rect_loop : forall (c Uu T : R), 0 < c -> 0 < Uu -> 0 < T ->
  forall (Hf1 : Ccont (fun u => Cmul (phi_ext y (seg (mkC c (- T)) (mkC c T) u))
                                     (seg' (mkC c (- T)) (mkC c T) u)))
         (Hf2 : Ccont (fun u => Cmul (phi_ext y (seg (mkC c T) (mkC (- Uu) T) u))
                                     (seg' (mkC c T) (mkC (- Uu) T) u)))
         (Hf3 : Ccont (fun u => Cmul (phi_ext y (seg (mkC (- Uu) T) (mkC (- Uu) (- T)) u))
                                     (seg' (mkC (- Uu) T) (mkC (- Uu) (- T)) u)))
         (Hf4 : Ccont (fun u => Cmul (phi_ext y (seg (mkC (- Uu) (- T)) (mkC c (- T)) u))
                                     (seg' (mkC (- Uu) (- T)) (mkC c (- T)) u))),
  Cadd (pathint (seg (mkC c (- T)) (mkC c T))
                (seg' (mkC c (- T)) (mkC c T)) (phi_ext y) Hf1 0 1)
  (Cadd (pathint (seg (mkC c T) (mkC (- Uu) T))
                 (seg' (mkC c T) (mkC (- Uu) T)) (phi_ext y) Hf2 0 1)
  (Cadd (pathint (seg (mkC (- Uu) T) (mkC (- Uu) (- T)))
                 (seg' (mkC (- Uu) T) (mkC (- Uu) (- T))) (phi_ext y) Hf3 0 1)
        (pathint (seg (mkC (- Uu) (- T)) (mkC c (- T)))
                 (seg' (mkC (- Uu) (- T)) (mkC c (- T))) (phi_ext y) Hf4 0 1)))
  = C0.
Proof.
  intros c Uu T Hc HU HT Hf1 Hf2 Hf3 Hf4.
  rewrite (Iedge (mkC c (- T)) (mkC c T) Hf1).
  rewrite (Iedge (mkC c T) (mkC (- Uu) T) Hf2).
  rewrite (Iedge (mkC (- Uu) T) (mkC (- Uu) (- T)) Hf3).
  rewrite (Iedge (mkC (- Uu) (- T)) (mkC c (- T)) Hf4).
  ring.
Qed.

End RectLoop.

Print Assumptions phi_ext_rect_loop.

(* ================================================================= *)
(*  END PerronRemovable.v — A1c complete:  ∮_rect (y^s−1)/s = 0, the      *)
(*  removable half of the Perron contour, with the extension concern      *)
(*  (globally-continuous removable extension through the pole) fully       *)
(*  discharged for a concrete function.  Axiom-clean.                    *)
(* ================================================================= *)
