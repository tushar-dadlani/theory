(* ================================================================= *)
(*  FourierLocalizeGauss.v  —  the concrete C¹ localiser at x = 0.     *)
(*                                                                    *)
(*  Assembles the localiser g with  g y·sin((0−y)/2) = ftil y − ftil 0 *)
(*  on [−π,π], as a global C1_fun, from                               *)
(*    • the Hadamard numerator factor hadC1 (had·y = ftil y − ftil 0); *)
(*    • the reciprocal recsinc = 1/sinc_mod, where sinc_mod is a        *)
(*      globally-POSITIVE C¹ modification of sinc (equal to sinc on     *)
(*      [−π/2,π/2]) — so recsinc is globally C¹, no poles, no lattice   *)
(*      gluing.  sinc_mod = sinc·χ + (1−χ) uses ONE C¹ cutoff χ.        *)
(*  Then  g = −2·had·recsinc(·/2),  and on [−π,π] (where χ=1, sinc>0)   *)
(*  sinc_mod = sinc and sinc_id closes the identity.                  *)
(*  No new axioms (classical Reals only).                            *)
(* ================================================================= *)

From Stdlib Require Import Reals Ranalysis5 FunctionalExtensionality Lra Lia.
Require Import FourierSincCore FourierSincC1 GaussTaylor GaussSubst ChangeOfVariables
        GaussPeriodDeriv2 GaussPeriodLip FourierHadamard.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  Two glue helpers.                                                *)
(* ----------------------------------------------------------------- *)

Lemma derivable_pt_lim_loceq : forall (f g : R -> R) (x l : R) (d : posreal),
  (forall y, Rabs (y - x) < d -> f y = g y) -> derivable_pt_lim g x l -> derivable_pt_lim f x l.
Proof.
  intros f g x l d Heq Hg eps He.
  destruct (Hg eps He) as [d2 Hd2].
  exists (mkposreal (Rmin d d2) (Rmin_pos _ _ (cond_pos d) (cond_pos d2))).
  intros h Hh Hhd; simpl in Hhd.
  assert (Hhd2 : Rabs h < d2) by (eapply Rlt_le_trans; [ exact Hhd | apply Rmin_r ]).
  assert (Hhd1 : Rabs h < d) by (eapply Rlt_le_trans; [ exact Hhd | apply Rmin_l ]).
  assert (Hfx : f x = g x) by (apply Heq; replace (x - x) with 0 by ring; rewrite Rabs_R0; apply cond_pos).
  assert (Hfxh : f (x + h) = g (x + h)) by (apply Heq; replace (x + h - x) with h by ring; exact Hhd1).
  rewrite Hfxh, Hfx; apply Hd2; [ exact Hh | exact Hhd2 ].
Qed.

Lemma deriv_0_of_quad : forall (f : R -> R) (a C : R) (d : posreal), 0 <= C ->
  (forall h, Rabs h < d -> Rabs (f (a + h) - f a) <= C * h ^ 2) -> derivable_pt_lim f a 0.
Proof.
  intros f a C d HC Hb eps He.
  exists (mkposreal (Rmin d (eps / (C + 1))) (Rmin_pos _ _ (cond_pos d)
            (Rdiv_lt_0_compat eps (C + 1) He ltac:(lra)))).
  intros h Hh Hhd; simpl in Hhd; unfold R_dist; rewrite Rminus_0_r.
  assert (Hhd1 : Rabs h < d) by (eapply Rlt_le_trans; [ exact Hhd | apply Rmin_l ]).
  assert (Hhe : Rabs h < eps / (C + 1)) by (eapply Rlt_le_trans; [ exact Hhd | apply Rmin_r ]).
  assert (Hpos : 0 < Rabs h) by (apply Rabs_pos_lt; exact Hh).
  replace ((f (a + h) - f a) / h) with ((f (a + h) - f a) * / h) by (unfold Rdiv; ring).
  rewrite Rabs_mult, Rabs_inv.
  apply Rmult_lt_reg_r with (Rabs h); [ exact Hpos | ].
  rewrite Rmult_assoc, Rinv_l by (apply Rabs_no_R0; exact Hh); rewrite Rmult_1_r.
  eapply Rle_lt_trans; [ apply Hb; exact Hhd1 | ].
  replace (h ^ 2) with (Rabs h * Rabs h)
    by (rewrite <- Rsqr_pow2, Rsqr_abs; unfold Rsqr; ring).
  assert (Hlt : (C + 1) * Rabs h < eps)
    by (apply Rlt_le_trans with ((C + 1) * (eps / (C + 1)));
        [ apply Rmult_lt_compat_l; [ lra | exact Hhe ] | apply Req_le; field; lra ]).
  nra.
Qed.

Lemma abs_cos1 : forall u, Rabs (cos u - 1) <= u ^ 2.
Proof.
  intro u; pose proof (cos_taylor_bound 0 u) as H;
    rewrite Rplus_0_l, cos_0, sin_0 in H;
    replace (cos u - 1 + u * 0) with (cos u - 1) in H by ring; exact H.
Qed.

(* ----------------------------------------------------------------- *)
(*  The one-sided C¹ ramp q: 1 on (−∞,π/2], 0 on [3π/4,∞).            *)
(* ----------------------------------------------------------------- *)

Definition q (w : R) : R :=
  if Rle_dec w (PI / 2) then 1
  else if Rle_dec (3 * PI / 4) w then 0
  else (1 + cos (4 * (w - PI / 2))) / 2.
Definition q' (w : R) : R :=
  if Rle_dec w (PI / 2) then 0
  else if Rle_dec (3 * PI / 4) w then 0
  else - 2 * sin (4 * (w - PI / 2)).

Lemma PI4 : 0 < PI / 4. Proof. pose proof PI_RGT_0; lra. Qed.

Lemma q_lo : forall w, w <= PI / 2 -> q w = 1.
Proof. intros w H; unfold q; destruct (Rle_dec w (PI / 2)); [ reflexivity | lra ]. Qed.
Lemma q_hi : forall w, 3 * PI / 4 <= w -> q w = 0.
Proof.
  intros w H; unfold q; destruct (Rle_dec w (PI / 2)) as [Hle | _];
    [ pose proof PI_RGT_0; lra | destruct (Rle_dec (3 * PI / 4) w); [ reflexivity | lra ] ].
Qed.
Lemma q_mid : forall w, PI / 2 < w -> w < 3 * PI / 4 -> q w = (1 + cos (4 * (w - PI / 2))) / 2.
Proof.
  intros w H1 H2; unfold q; destruct (Rle_dec w (PI / 2)) as [Hle | _]; [ lra | ].
  destruct (Rle_dec (3 * PI / 4) w); [ lra | reflexivity ].
Qed.

Lemma q_deriv : forall w, derivable_pt_lim q w (q' w).
Proof.
  intro w; pose proof PI_RGT_0 as HPI.
  destruct (total_order_T w (PI / 2)) as [[Hlt | Heq] | Hgt].
  - assert (Hq' : q' w = 0) by (unfold q'; destruct (Rle_dec w (PI / 2)); [ reflexivity | lra ]).
    rewrite Hq'.
    apply (derivable_pt_lim_loceq q (fun _ => 1) w 0 (mkposreal (PI / 2 - w) ltac:(simpl; lra))).
    + intros y Hy; simpl in Hy; apply q_lo; apply Rabs_def2 in Hy; lra.
    + apply derivable_pt_lim_const.
  - subst w. assert (Hq' : q' (PI / 2) = 0)
      by (unfold q'; destruct (Rle_dec (PI / 2) (PI / 2)); [ reflexivity | lra ]).
    rewrite Hq'.
    apply (deriv_0_of_quad q (PI / 2) 8 (mkposreal (PI / 4) PI4)); [ lra | ].
    intros h Hh; simpl in Hh.
    destruct (Rle_dec h 0) as [Hh0 | Hh0].
    * rewrite (q_lo (PI / 2 + h)) by lra; rewrite (q_lo (PI / 2)) by lra.
      replace (1 - 1) with 0 by ring; rewrite Rabs_R0;
        apply Rmult_le_pos; [ lra | rewrite <- Rsqr_pow2; apply Rle_0_sqr ].
    * rewrite (q_mid (PI / 2 + h)) by (apply Rabs_def2 in Hh; lra); rewrite (q_lo (PI / 2)) by lra.
      replace (4 * (PI / 2 + h - PI / 2)) with (4 * h) by ring.
      replace ((1 + cos (4 * h)) / 2 - 1) with (- ((1 - cos (4 * h)) / 2)) by field.
      rewrite Rabs_Ropp, Rabs_pos_eq by (pose proof (COS_bound (4 * h)); lra).
      pose proof (abs_cos1 (4 * h)) as Hc; rewrite Rabs_left1 in Hc
        by (pose proof (COS_bound (4 * h)); lra).
      replace ((4 * h) ^ 2) with (16 * h ^ 2) in Hc by ring; lra.
  - assert (Hgt2 := Hgt).
    destruct (total_order_T w (3 * PI / 4)) as [[Hlt2 | Heq2] | Hgt3].
    + assert (Hq' : q' w = - 2 * sin (4 * (w - PI / 2)))
        by (unfold q'; destruct (Rle_dec w (PI / 2)); [ lra | ];
            destruct (Rle_dec (3 * PI / 4) w); [ lra | reflexivity ]).
      rewrite Hq'.
      apply (derivable_pt_lim_loceq q (fun w => (1 + cos (4 * (w - PI / 2))) / 2) w
               (- 2 * sin (4 * (w - PI / 2)))
               (mkposreal (Rmin (w - PI / 2) (3 * PI / 4 - w)) ltac:(simpl; apply Rmin_pos; lra))).
      * intros y Hy; simpl in Hy; apply Rabs_def2 in Hy; destruct Hy as [Hya Hyb];
          pose proof (Rmin_l (w - PI / 2) (3 * PI / 4 - w));
          pose proof (Rmin_r (w - PI / 2) (3 * PI / 4 - w));
          apply q_mid; lra.
      * (* derivative of (1+cos(4(w-π/2)))/2 *)
        assert (Hin : derivable_pt_lim (fun w => 4 * (w - PI / 2)) w 4).
        { pose proof (derivable_pt_lim_minus (fun w => w) (fun _ => PI / 2) w 1 0
              (derivable_pt_lim_id w) (derivable_pt_lim_const (PI / 2) w)) as Hmn.
          pose proof (derivable_pt_lim_scal (fun w => w - PI / 2) 4 w (1 - 0) Hmn) as Hs.
          replace (4 * (1 - 0)) with 4 in Hs by ring; exact Hs. }
        assert (Hcos : derivable_pt_lim (fun w => cos (4 * (w - PI / 2))) w
                         (- sin (4 * (w - PI / 2)) * 4))
          by (apply (derivable_pt_lim_comp (fun w => 4 * (w - PI / 2)) cos w 4
                       (- sin (4 * (w - PI / 2))) Hin (derivable_pt_lim_cos _))).
        pose proof (derivable_pt_lim_scal (fun w => 1 + cos (4 * (w - PI / 2))) (/ 2) w
                      (0 + - sin (4 * (w - PI / 2)) * 4)
                      (derivable_pt_lim_plus (fun _ => 1) (fun w => cos (4 * (w - PI / 2))) w 0
                         (- sin (4 * (w - PI / 2)) * 4) (derivable_pt_lim_const 1 w) Hcos)) as Hfull.
        replace (fun w0 => (1 + cos (4 * (w0 - PI / 2))) / 2)
          with (fun w0 => / 2 * (1 + cos (4 * (w0 - PI / 2))))
          by (apply functional_extensionality; intro; field).
        replace (- 2 * sin (4 * (w - PI / 2))) with (/ 2 * (0 + - sin (4 * (w - PI / 2)) * 4)) by field.
        exact Hfull.
    + subst w. assert (Hq' : q' (3 * PI / 4) = 0)
        by (unfold q'; destruct (Rle_dec (3 * PI / 4) (PI / 2)); [ lra | ];
            destruct (Rle_dec (3 * PI / 4) (3 * PI / 4)); [ reflexivity | lra ]).
      rewrite Hq'.
      apply (deriv_0_of_quad q (3 * PI / 4) 8 (mkposreal (PI / 4) PI4)); [ lra | ].
      intros h Hh; simpl in Hh.
      destruct (Rle_dec 0 h) as [Hh0 | Hh0].
      * rewrite (q_hi (3 * PI / 4 + h)) by lra; rewrite (q_hi (3 * PI / 4)) by lra.
        replace (0 - 0) with 0 by ring; rewrite Rabs_R0;
          apply Rmult_le_pos; [ lra | rewrite <- Rsqr_pow2; apply Rle_0_sqr ].
      * rewrite (q_mid (3 * PI / 4 + h)) by (apply Rabs_def2 in Hh; lra); rewrite (q_hi (3 * PI / 4)) by lra.
        replace (4 * (3 * PI / 4 + h - PI / 2)) with (4 * h + PI) by field.
        replace ((1 + cos (4 * h + PI)) / 2 - 0) with ((1 + cos (4 * h + PI)) / 2) by field.
        rewrite neg_cos.
        replace ((1 + - cos (4 * h)) / 2) with ((1 - cos (4 * h)) / 2) by field.
        rewrite Rabs_pos_eq by (pose proof (COS_bound (4 * h)); lra).
        pose proof (abs_cos1 (4 * h)) as Hc; rewrite Rabs_left1 in Hc
          by (pose proof (COS_bound (4 * h)); lra).
        replace ((4 * h) ^ 2) with (16 * h ^ 2) in Hc by ring; lra.
    + assert (Hq' : q' w = 0) by (unfold q'; destruct (Rle_dec w (PI / 2)); [ lra | ];
            destruct (Rle_dec (3 * PI / 4) w); [ reflexivity | lra ]).
      rewrite Hq'.
      apply (derivable_pt_lim_loceq q (fun _ => 0) w 0 (mkposreal (w - 3 * PI / 4) ltac:(simpl; lra))).
      * intros y Hy; simpl in Hy; apply q_hi; apply Rabs_def2 in Hy; lra.
      * apply derivable_pt_lim_const.
Qed.

(* ----------------------------------------------------------------- *)
(*  C1_fun combinators.                                              *)
(* ----------------------------------------------------------------- *)

Definition C1d (F : C1_fun) (t : R) : R := derive (c1 F) (diff0 F) t.
Lemma C1dl : forall (F : C1_fun) t, derivable_pt_lim (c1 F) t (C1d F t).
Proof. intros F t; exact (proj2_sig (diff0 F t)). Qed.
Lemma C1c : forall (F : C1_fun), continuity (c1 F).
Proof. intros F t; apply derivable_continuous_pt; exists (C1d F t); apply C1dl. Qed.

Definition const_C1 (c : R) : C1_fun :=
  mkC1 (c1 := fun _ => c) (diff0 := fun t => exist _ 0 (derivable_pt_lim_const c t))
       (fun t => continuity_pt_const (fun _ => 0) t (fun a b => eq_refl)).

Definition scal_C1 (c : R) (F : C1_fun) : C1_fun :=
  mkC1 (c1 := fun t => c * c1 F t)
       (diff0 := fun t => exist _ (c * C1d F t) (derivable_pt_lim_scal (c1 F) c t (C1d F t) (C1dl F t)))
       (fun t => continuity_pt_scal (C1d F) c t (cont1 F t)).

Definition plus_C1 (F G : C1_fun) : C1_fun :=
  mkC1 (c1 := fun t => c1 F t + c1 G t)
       (diff0 := fun t => exist _ (C1d F t + C1d G t)
                    (derivable_pt_lim_plus (c1 F) (c1 G) t (C1d F t) (C1d G t) (C1dl F t) (C1dl G t)))
       (fun t => continuity_pt_plus (C1d F) (C1d G) t (cont1 F t) (cont1 G t)).

Definition minus_C1 (F G : C1_fun) : C1_fun :=
  mkC1 (c1 := fun t => c1 F t - c1 G t)
       (diff0 := fun t => exist _ (C1d F t - C1d G t)
                    (derivable_pt_lim_minus (c1 F) (c1 G) t (C1d F t) (C1d G t) (C1dl F t) (C1dl G t)))
       (fun t => continuity_pt_minus (C1d F) (C1d G) t (cont1 F t) (cont1 G t)).

Definition mult_C1 (F G : C1_fun) : C1_fun :=
  mkC1 (c1 := fun t => c1 F t * c1 G t)
       (diff0 := fun t => exist _ (C1d F t * c1 G t + c1 F t * C1d G t)
                    (derivable_pt_lim_mult (c1 F) (c1 G) t (C1d F t) (C1d G t) (C1dl F t) (C1dl G t)))
       (fun t => continuity_pt_plus _ _ t
                   (continuity_pt_mult (C1d F) (c1 G) t (cont1 F t) (C1c G t))
                   (continuity_pt_mult (c1 F) (C1d G) t (C1c F t) (cont1 G t))).

Lemma const_C1_val : forall c t, const_C1 c t = c. Proof. reflexivity. Qed.
Lemma scal_C1_val : forall c F t, scal_C1 c F t = c * c1 F t. Proof. reflexivity. Qed.
Lemma plus_C1_val : forall F G t, plus_C1 F G t = c1 F t + c1 G t. Proof. reflexivity. Qed.
Lemma minus_C1_val : forall F G t, minus_C1 F G t = c1 F t - c1 G t. Proof. reflexivity. Qed.
Lemma mult_C1_val : forall F G t, mult_C1 F G t = c1 F t * c1 G t. Proof. reflexivity. Qed.

Lemma recip_dl : forall (F : C1_fun) (Hpos : forall t, 0 < c1 F t) t,
  derivable_pt_lim (fun t => 1 / c1 F t) t ((0 * c1 F t - C1d F t * 1) / Rsqr (c1 F t)).
Proof.
  intros F Hpos t.
  exact (derivable_pt_lim_div (fun _ => 1) (c1 F) t 0 (C1d F t)
           (derivable_pt_lim_const 1 t) (C1dl F t) (Rgt_not_eq _ _ (Hpos t))).
Qed.

Lemma recip_ct : forall (F : C1_fun) (Hpos : forall t, 0 < c1 F t),
  continuity (fun t => (0 * c1 F t - C1d F t * 1) / Rsqr (c1 F t)).
Proof.
  intros F Hpos t.
  apply (continuity_pt_div (fun t => 0 * c1 F t - C1d F t * 1) (fun t => Rsqr (c1 F t)) t).
  - apply continuity_pt_minus.
    + apply continuity_pt_mult; [ apply continuity_pt_const; intros a b; reflexivity | apply C1c ].
    + apply continuity_pt_mult; [ exact (cont1 F t) | apply continuity_pt_const; intros a b; reflexivity ].
  - apply (continuity_pt_mult (c1 F) (c1 F) t (C1c F t) (C1c F t)).
  - unfold Rsqr; apply Rgt_not_eq; apply Rmult_lt_0_compat; apply Hpos.
Qed.

Definition recip_C1 (F : C1_fun) (Hpos : forall t, 0 < c1 F t) : C1_fun :=
  mkC1 (c1 := fun t => 1 / c1 F t)
       (diff0 := fun t => exist _ ((0 * c1 F t - C1d F t * 1) / Rsqr (c1 F t)) (recip_dl F Hpos t))
       (recip_ct F Hpos).

Lemma recip_C1_val : forall F Hpos t, recip_C1 F Hpos t = 1 / c1 F t. Proof. reflexivity. Qed.

Definition idC1 : C1_fun :=
  mkC1 (c1 := fun t => t) (diff0 := fun t => exist _ 1 (derivable_pt_lim_id t))
       (fun t => continuity_pt_const (fun _ => 1) t (fun a b => eq_refl)).
Definition negC1 : C1_fun :=
  mkC1 (c1 := fun t => - t)
       (diff0 := fun t => exist _ (-1) (derivable_pt_lim_opp (fun t => t) t 1 (derivable_pt_lim_id t)))
       (fun t => continuity_pt_const (fun _ => -1) t (fun a b => eq_refl)).
Lemma negC1_val : forall t, negC1 t = - t. Proof. reflexivity. Qed.
Definition halfC1 : C1_fun := scal_C1 (/ 2) idC1.
Lemma halfC1_val : forall t, halfC1 t = / 2 * t. Proof. reflexivity. Qed.

(* ----------------------------------------------------------------- *)
(*  q' continuous and q ∈ [0,1] ⇒ q is a C1_fun.                     *)
(* ----------------------------------------------------------------- *)

Lemma q_cont : continuity q'.
Proof.
  intro w; pose proof PI_RGT_0 as HPI.
  destruct (total_order_T w (PI / 2)) as [[Hlt | Heq] | Hgt].
  - apply (continuity_pt_loceq q' (fun _ => 0) w (mkposreal (PI / 2 - w) ltac:(simpl; lra))).
    + intros y Hy; unfold q'; destruct (Rle_dec y (PI / 2)); [ reflexivity | ];
        simpl in Hy; apply Rabs_def2 in Hy; lra.
    + apply continuity_pt_const; intros a b; reflexivity.
  - subst w.
    assert (Hq0 : q' (PI / 2) = 0)
      by (unfold q'; destruct (Rle_dec (PI / 2) (PI / 2)); [ reflexivity | lra ]).
    apply (loclip_cont q' (PI / 2) 8 (PI / 4)); [ lra | pose proof PI4; lra | ].
    intros x Hx; rewrite Hq0, Rminus_0_r.
    destruct (Rle_dec x (PI / 2)) as [Hle | Hgt'].
    + assert (Hqx : q' x = 0) by (unfold q'; destruct (Rle_dec x (PI / 2)); [ reflexivity | lra ]).
      rewrite Hqx, Rabs_R0; apply Rmult_le_pos; [ lra | apply Rabs_pos ].
    + assert (Hlt2 : x < 3 * PI / 4) by (apply Rabs_def2 in Hx; lra).
      assert (Hqx : q' x = - 2 * sin (4 * (x - PI / 2)))
        by (unfold q'; destruct (Rle_dec x (PI / 2)); [ lra | ];
            destruct (Rle_dec (3 * PI / 4) x); [ lra | reflexivity ]).
      rewrite Hqx.
      replace (- 2 * sin (4 * (x - PI / 2))) with (- (2 * sin (4 * (x - PI / 2)))) by ring.
      rewrite Rabs_Ropp, Rabs_mult, (Rabs_pos_eq 2) by lra.
      apply Rle_trans with (2 * (4 * Rabs (x - PI / 2))).
      * apply Rmult_le_compat_l; [ lra | ].
        pose proof (sin_lipschitz (4 * (x - PI / 2)) 0) as Hsl;
          rewrite sin_0, !Rminus_0_r in Hsl.
        eapply Rle_trans; [ exact Hsl | ].
        rewrite Rabs_mult, (Rabs_pos_eq 4) by lra; apply Rle_refl.
      * apply Req_le; ring.
  - destruct (total_order_T w (3 * PI / 4)) as [[Hlt2 | Heq2] | Hgt3].
    + apply (continuity_pt_loceq q' (fun w => - 2 * sin (4 * (w - PI / 2))) w
               (mkposreal (Rmin (w - PI / 2) (3 * PI / 4 - w)) ltac:(simpl; apply Rmin_pos; lra))).
      * intros y Hy; simpl in Hy; apply Rabs_def2 in Hy; destruct Hy as [Hya Hyb];
          pose proof (Rmin_l (w - PI / 2) (3 * PI / 4 - w));
          pose proof (Rmin_r (w - PI / 2) (3 * PI / 4 - w));
          unfold q'; destruct (Rle_dec y (PI / 2)); [ lra | ];
          destruct (Rle_dec (3 * PI / 4) y); [ lra | reflexivity ].
      * apply (continuity_pt_scal (fun w => sin (4 * (w - PI / 2))) (-2) w).
        apply (continuity_pt_comp (fun w => 4 * (w - PI / 2)) sin w).
        -- apply (continuity_pt_scal (fun w => w - PI / 2) 4 w).
           apply continuity_pt_minus;
             [ apply derivable_continuous_pt; exists 1; apply derivable_pt_lim_id
             | apply continuity_pt_const; intros a b; reflexivity ].
        -- apply continuity_sin.
    + subst w.
      assert (Hq0 : q' (3 * PI / 4) = 0)
        by (unfold q'; destruct (Rle_dec (3 * PI / 4) (PI / 2)); [ lra | ];
            destruct (Rle_dec (3 * PI / 4) (3 * PI / 4)); [ reflexivity | lra ]).
      apply (loclip_cont q' (3 * PI / 4) 8 (PI / 4)); [ lra | pose proof PI4; lra | ].
      intros x Hx; rewrite Hq0, Rminus_0_r.
      destruct (Rle_dec (3 * PI / 4) x) as [Hge | Hlt'].
      * assert (Hqx : q' x = 0) by (unfold q'; destruct (Rle_dec x (PI / 2)); [ lra | ];
              destruct (Rle_dec (3 * PI / 4) x); [ reflexivity | lra ]).
        rewrite Hqx, Rabs_R0; apply Rmult_le_pos; [ lra | apply Rabs_pos ].
      * assert (Hgt' : PI / 2 < x) by (apply Rabs_def2 in Hx; lra).
        assert (Hqx : q' x = - 2 * sin (4 * (x - PI / 2)))
          by (unfold q'; destruct (Rle_dec x (PI / 2)); [ lra | ];
              destruct (Rle_dec (3 * PI / 4) x); [ lra | reflexivity ]).
        rewrite Hqx.
        replace (- 2 * sin (4 * (x - PI / 2))) with (- (2 * sin (4 * (x - PI / 2)))) by ring.
        rewrite Rabs_Ropp, Rabs_mult, (Rabs_pos_eq 2) by lra.
        apply Rle_trans with (2 * (4 * Rabs (x - 3 * PI / 4))).
        -- apply Rmult_le_compat_l; [ lra | ].
           pose proof (sin_lipschitz (4 * (x - PI / 2)) PI) as Hsl.
           replace (sin PI) with 0 in Hsl by (rewrite sin_PI; reflexivity).
           rewrite Rminus_0_r in Hsl.
           eapply Rle_trans; [ exact Hsl | ].
           replace (4 * (x - PI / 2) - PI) with (4 * (x - 3 * PI / 4)) by field.
           rewrite Rabs_mult, (Rabs_pos_eq 4) by lra; apply Rle_refl.
        -- apply Req_le; ring.
    + apply (continuity_pt_loceq q' (fun _ => 0) w (mkposreal (w - 3 * PI / 4) ltac:(simpl; lra))).
      * intros y Hy; simpl in Hy; apply Rabs_def2 in Hy; unfold q';
          destruct (Rle_dec y (PI / 2)); [ lra | ];
          destruct (Rle_dec (3 * PI / 4) y); [ reflexivity | lra ].
      * apply continuity_pt_const; intros a b; reflexivity.
Qed.

Lemma q_range : forall w, 0 <= q w <= 1.
Proof.
  intro w; pose proof PI_RGT_0.
  destruct (total_order_T w (PI / 2)) as [[Hlt | Heq] | Hgt].
  - rewrite q_lo by lra; lra.
  - subst; rewrite q_lo by lra; lra.
  - destruct (total_order_T w (3 * PI / 4)) as [[Hlt2 | Heq2] | Hgt3].
    + rewrite q_mid by lra; pose proof (COS_bound (4 * (w - PI / 2))); lra.
    + subst; rewrite q_hi by lra; lra.
    + rewrite q_hi by lra; lra.
Qed.

Definition qC1 : C1_fun :=
  mkC1 (c1 := q) (diff0 := fun w => exist _ (q' w) (q_deriv w)) q_cont.
Lemma qC1_val : forall w, qC1 w = q w. Proof. reflexivity. Qed.

(* ----------------------------------------------------------------- *)
(*  The even C¹ cutoff χ = q(·)·q(−·), and the positive C¹ sinc_mod.  *)
(* ----------------------------------------------------------------- *)

Definition chi2C1 : C1_fun := mult_C1 qC1 (comp_C1 qC1 negC1).
Lemma chi2_val : forall w, chi2C1 w = q w * q (- w).
Proof. reflexivity. Qed.

Lemma chi2_1 : forall w, - (PI / 2) <= w <= PI / 2 -> chi2C1 w = 1.
Proof. intros w Hw; rewrite chi2_val, (q_lo w) by lra; rewrite (q_lo (- w)) by lra; ring. Qed.

Lemma chi2_0 : forall w, 3 * PI / 4 <= w \/ w <= - (3 * PI / 4) -> chi2C1 w = 0.
Proof.
  intros w [Hge | Hle]; rewrite chi2_val.
  - rewrite (q_hi w) by lra; ring.
  - rewrite (q_hi (- w)) by lra; ring.
Qed.

Lemma chi2_range : forall w, 0 <= chi2C1 w <= 1.
Proof. intro w; rewrite chi2_val; pose proof (q_range w); pose proof (q_range (- w)); nra. Qed.

Definition sincmodC1 : C1_fun := plus_C1 (mult_C1 sincC1 chi2C1) (minus_C1 (const_C1 1) chi2C1).
Lemma sincmod_val : forall w, sincmodC1 w = sinc w * chi2C1 w + (1 - chi2C1 w).
Proof. reflexivity. Qed.

Lemma sinc_mod_pos : forall w, 0 < sincmodC1 w.
Proof.
  intro w; rewrite sincmod_val; pose proof PI_RGT_0; pose proof (chi2_range w) as Hr.
  destruct (Rle_lt_dec (3 * PI / 4) (Rabs w)) as [Hge | Hlt].
  - assert (Hc0 : chi2C1 w = 0).
    { apply chi2_0; destruct (Rle_lt_dec 0 w) as [Hw | Hw].
      - left; rewrite Rabs_pos_eq in Hge by lra; lra.
      - right; rewrite Rabs_left in Hge by lra; lra. }
    rewrite Hc0; replace (sinc w * 0 + (1 - 0)) with 1 by ring; lra.
  - assert (Hsp : 0 < sinc w) by (apply sinc_pos; apply Rabs_def2 in Hlt; lra).
    nra.
Qed.

Definition recsincC1 : C1_fun := recip_C1 sincmodC1 sinc_mod_pos.
Lemma recsinc_eq : forall w, - (PI / 2) <= w <= PI / 2 -> sincmodC1 w = sinc w.
Proof. intros w Hw; rewrite sincmod_val, (chi2_1 w Hw); ring. Qed.

(* ----------------------------------------------------------------- *)
(*  The localiser g = −2·had·recsinc(·/2) and its identity on [−π,π]. *)
(* ----------------------------------------------------------------- *)

Section Loc.
Variable t : R.
Hypothesis Ht : 0 < t.

Definition gloc : C1_fun := scal_C1 (-2) (mult_C1 (hadC1 t Ht) (comp_C1 recsincC1 halfC1)).
Lemma gloc_val : forall y, gloc y = -2 * (had t Ht y * (1 / sincmodC1 (/ 2 * y))).
Proof. reflexivity. Qed.

Theorem gloc_identity : forall y, - PI <= y <= PI ->
  gloc y * sin ((0 - y) / 2) = ftil t Ht y - ftil t Ht 0.
Proof.
  intros y [Hlo Hhi]; pose proof PI_RGT_0.
  assert (Hhalf : - (PI / 2) <= / 2 * y <= PI / 2) by lra.
  assert (Hsinc : 0 < sinc (/ 2 * y)) by (apply sinc_pos; lra).
  rewrite gloc_val, (recsinc_eq (/ 2 * y) Hhalf).
  pose proof (had_id t Ht y) as Hhi'.
  rewrite <- Hhi'.
  pose proof (sinc_id (/ 2 * y)) as Hsi.
  replace ((0 - y) / 2) with (- (/ 2 * y)) by field.
  rewrite sin_neg, <- Hsi.
  field; apply Rgt_not_eq; exact Hsinc.
Qed.

End Loc.

Print Assumptions gloc_identity.

(* ================================================================= *)
(*  END FourierLocalizeGauss.v                                       *)
(*  gloc t Ht is a global C1_fun with gloc y·sin((0−y)/2) = ftil y −   *)
(*  ftil 0 on [−π,π] — the localiser fed to fourier_pointwise_loc.    *)
(* ================================================================= *)
