(* ================================================================= *)
(*  CWindingOffCenter.v  (identity-theorem plan, brick B1 crux)        *)
(*                                                                    *)
(*  The OFF-CENTRE-POLE winding integral                              *)
(*     oint_{|z|=R} dz/(z-w) = 2 pi i    for  |w| < R,                  *)
(*  by PARAMETER DIFFERENTIATION (route 2 of docs/identity_theorem_    *)
(*  plan.md): slide the pole  w_s = s*w  from the centre (s=0) to w    *)
(*  (s=1); the winding W(s) has zero s-derivative (its derivative       *)
(*  integrand is a loop of an exact form), so W is constant and         *)
(*  W(1) = W(0) = 2 pi i (CWinding.winding_dz_z).                       *)
(*                                                                    *)
(*  Stage A here: preliminaries (pole stays inside; the denominator     *)
(*  z - w_s never vanishes on the circle; modulus lower bound          *)
(*  R - |w| > 0 via the reverse triangle inequality).                  *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra.
Require Import ComplexField Cmodulus CIntegral2 CPathIntegral CPathFTC CWinding
        Holomorphic CDeriv CHoloCalculus.
Open Scope R_scope.

(* reverse triangle inequality: |a| - |b| <= |a - b| *)
Lemma Cmod_rev_triangle : forall a b, Cmod a - Cmod b <= Cmod (Cminus a b).
Proof.
  intros a b.
  assert (Heq : Cadd (Cminus a b) b = a) by (apply Ceq; simpl; ring).
  pose proof (Cmod_triangle (Cminus a b) b) as HT.
  rewrite Heq in HT. lra.
Qed.

(* ---- a small C-algebra toolkit (the repo only ships Cinv_l) ---- *)
Lemma Cmul_comm : forall a b, Cmul a b = Cmul b a.
Proof. intros; apply Ceq; simpl; ring. Qed.
Lemma Cmul_assoc : forall a b c, Cmul (Cmul a b) c = Cmul a (Cmul b c).
Proof. intros; apply Ceq; simpl; ring. Qed.
Lemma Cmul_1_l : forall a, Cmul C1 a = a.
Proof. intros; apply Ceq; simpl; ring. Qed.
Lemma Cmul_1_r : forall a, Cmul a C1 = a.
Proof. intros; apply Ceq; simpl; ring. Qed.
Lemma Cmul_minus_r : forall a b c, Cmul (Cminus a b) c = Cminus (Cmul a c) (Cmul b c).
Proof. intros; apply Ceq; simpl; ring. Qed.
Lemma Cmul_C0_r : forall a, Cmul a C0 = C0.
Proof. intros; apply Ceq; simpl; ring. Qed.
Lemma Cinv_r : forall a, a <> C0 -> Cmul a (Cinv a) = C1.
Proof. intros a Ha; rewrite Cmul_comm; apply Cinv_l; exact Ha. Qed.
Lemma Cmul_eq0_l : forall a b, a <> C0 -> Cmul a b = C0 -> b = C0.
Proof.
  intros a b Ha Hab.
  rewrite <- (Cmul_1_l b), <- (Cinv_l a Ha), Cmul_assoc, Hab, Cmul_C0_r; reflexivity.
Qed.
Lemma Cmul_cancel_r : forall a b c, c <> C0 -> Cmul a c = Cmul b c -> a = b.
Proof.
  intros a b c Hc H.
  assert (Ha : a = Cmul (Cmul a c) (Cinv c))
    by (rewrite Cmul_assoc, (Cinv_r c Hc), Cmul_1_r; reflexivity).
  assert (Hb : b = Cmul (Cmul b c) (Cinv c))
    by (rewrite Cmul_assoc, (Cinv_r c Hc), Cmul_1_r; reflexivity).
  rewrite Ha, Hb, H; reflexivity.
Qed.
Lemma Cmul_swap : forall a b c, Cmul a (Cmul b c) = Cmul b (Cmul a c).
Proof. intros; apply Ceq; simpl; ring. Qed.
Lemma Cinv_l_mul : forall a Y, a <> C0 -> Cmul (Cinv a) (Cmul a Y) = Y.
Proof. intros a Y Ha; rewrite <- Cmul_assoc, (Cinv_l a Ha), Cmul_1_l; reflexivity. Qed.

(* the arc parametrisation is a genuine C^1 loop *)
Lemma arc_Re_deriv : forall r s,
  derivable_pt_lim (fun x => Re (arc r x)) s (Re (arc' r s)).
Proof.
  intros r s. unfold arc, arc'; cbn [Re Im].
  replace (- (r * sin s)) with (r * (- sin s)) by ring.
  apply (derivable_pt_lim_scal cos r s (- sin s) (derivable_pt_lim_cos s)).
Qed.

Lemma arc_Im_deriv : forall r s,
  derivable_pt_lim (fun x => Im (arc r x)) s (Im (arc' r s)).
Proof.
  intros r s. unfold arc, arc'; cbn [Re Im].
  apply (derivable_pt_lim_scal sin r s (cos s) (derivable_pt_lim_sin s)).
Qed.

Lemma arc_closed : forall r, arc r (2 * PI) = arc r 0.
Proof.
  intro r. unfold arc.
  rewrite sin_2PI, cos_2PI, sin_0, cos_0. apply Ceq; cbn [Re Im]; ring.
Qed.

(* continuity of 1/f where f is a nonvanishing continuous C-valued map *)
Lemma Ccont_inv : forall f, Ccont f -> (forall u, f u <> C0) ->
  Ccont (fun u => Cinv (f u)).
Proof.
  intros f [HfR HfI] Hne. split; intro x;
    [ change (continuity_pt
                (fun u => Re (f u) / (Re (f u) * Re (f u) + Im (f u) * Im (f u))) x)
    | change (continuity_pt
                (fun u => - Im (f u) / (Re (f u) * Re (f u) + Im (f u) * Im (f u))) x) ];
    apply continuity_pt_div;
    solve [ apply HfR | apply HfI | apply continuity_pt_opp; apply HfI
          | apply continuity_pt_plus; apply continuity_pt_mult;
              solve [ apply HfR | apply HfI ]
          | exact (Cnorm2_neq_0 (f x) (Hne x)) ].
Qed.

Lemma Cmul_self_ne0 : forall a, a <> C0 -> Cmul a a <> C0.
Proof.
  intros a Ha Hc. apply Ha, (proj1 (Cmod0 a)).
  pose proof (Cmod_nonneg a) as Hn.
  assert (H0 : Cmod a * Cmod a = 0)
    by (rewrite <- Cmod_mul, Hc; apply (proj2 (Cmod0 C0) eq_refl)).
  nra.
Qed.

Lemma Ccont_minus : forall f g, Ccont f -> Ccont g ->
  Ccont (fun u => Cminus (f u) (g u)).
Proof.
  intros f g [HfR HfI] [HgR HgI]; split; intro x;
    [ change (continuity_pt (fun u => Re (f u) - Re (g u)) x)
    | change (continuity_pt (fun u => Im (f u) - Im (g u)) x) ];
    apply continuity_pt_minus; solve [ apply HfR | apply HgR | apply HfI | apply HgI ].
Qed.

(* THE REMAINDER IDENTITY: the second-order remainder of 1/(z - s w) in s *)
(* collapses (after clearing denominators, the ring identity              *)
(* (B-A)^2 = (w d)^2 with B - A = w d) to  w^2 d^2 / (A B^2).              *)
Lemma rem_identity : forall A B w d : C,
  A <> C0 -> B <> C0 -> Cminus B A = Cmul w d ->
  Cminus (Cminus (Cinv A) (Cinv B)) (Cmul (Cmul w (Cinv (Cmul B B))) d)
  = Cmul (Cmul (Cmul w w) (Cmul d d)) (Cmul (Cinv A) (Cinv (Cmul B B))).
Proof.
  intros A B w d HA HB Hrel.
  assert (HBB : Cmul B B <> C0) by (apply Cmul_self_ne0; exact HB).
  assert (HX : Cmul A (Cmul B B) <> C0)
    by (intro Hc; apply HBB; exact (Cmul_eq0_l A (Cmul B B) HA Hc)).
  apply (Cmul_cancel_r _ _ (Cmul A (Cmul B B)) HX).
  assert (T1 : Cmul (Cinv A) (Cmul A (Cmul B B)) = Cmul B B)
    by (apply Cinv_l_mul; exact HA).
  assert (T2 : Cmul (Cinv B) (Cmul A (Cmul B B)) = Cmul A B)
    by (rewrite (Cmul_swap (Cinv B) A (Cmul B B)), (Cinv_l_mul B B HB); reflexivity).
  assert (T3 : Cmul (Cmul (Cmul w (Cinv (Cmul B B))) d) (Cmul A (Cmul B B))
             = Cmul (Cmul w d) A).
  { assert (H3a : Cmul (Cmul w (Cinv (Cmul B B))) d
                = Cmul (Cmul w d) (Cinv (Cmul B B))) by (apply Ceq; simpl; ring).
    rewrite H3a, Cmul_assoc, (Cmul_swap (Cinv (Cmul B B)) A (Cmul B B)),
      (Cinv_l (Cmul B B) HBB), Cmul_1_r; reflexivity. }
  assert (Hinner : Cmul (Cmul (Cinv A) (Cinv (Cmul B B))) (Cmul A (Cmul B B)) = C1)
    by (rewrite Cmul_assoc, (Cmul_swap (Cinv (Cmul B B)) A (Cmul B B)),
          (Cinv_l (Cmul B B) HBB), Cmul_1_r, (Cinv_l A HA); reflexivity).
  rewrite !Cmul_minus_r, T1, T2, T3.
  rewrite (Cmul_assoc (Cmul (Cmul w w) (Cmul d d))
            (Cmul (Cinv A) (Cinv (Cmul B B))) (Cmul A (Cmul B B))),
          Hinner, Cmul_1_r.
  assert (Hww : Cmul (Cmul w w) (Cmul d d) = Cmul (Cmul w d) (Cmul w d))
    by (apply Ceq; simpl; ring).
  rewrite Hww, <- Hrel. apply Ceq; simpl; ring.
Qed.

(* pulling the common factor arc' out of the remainder *)
Lemma factor_arc : forall iA iB iBB w a d : C,
  Cminus (Cminus (Cmul iA a) (Cmul iB a)) (Cmul (Cmul (Cmul w iBB) a) d)
  = Cmul (Cminus (Cminus iA iB) (Cmul (Cmul w iBB) d)) a.
Proof. intros; apply Ceq; simpl; ring. Qed.

(* Cmod of the unit and of an inverse *)
Lemma Cmod_C1 : Cmod C1 = 1.
Proof.
  unfold Cmod, Cnorm2, C1; cbn [Re Im].
  replace (1 * 1 + 0 * 0) with 1 by ring. apply sqrt_1.
Qed.

Lemma Cmod_inv : forall a, a <> C0 -> Cmod (Cinv a) = / Cmod a.
Proof.
  intros a Ha.
  assert (Hm : Cmod a <> 0) by (intro H; apply Ha, (proj1 (Cmod0 a) H)).
  apply (Rmult_eq_reg_r (Cmod a)); [ | exact Hm ].
  rewrite <- Cmod_mul, (Cinv_l a Ha), Cmod_C1.
  rewrite Rinv_l by exact Hm. reflexivity.
Qed.

Section OffCenterWinding.
Variable Rr : R.
Variable w : C.
Hypothesis HR : 0 < Rr.
Hypothesis Hw : Cmod w < Rr.

(* the sliding pole  w_s = s*w  and the winding integrand *)
Definition wp (s : R) : C := Cmul (RtoC s) w.
Definition wphi (s u : R) : C := Cmul (Cinv (Cminus (arc Rr u) (wp s))) (arc' Rr u).

(* the pole stays within |w| of the centre for s in [0,1] *)
Lemma wp_mod : forall s, 0 <= s <= 1 -> Cmod (wp s) <= Cmod w.
Proof.
  intros s Hs. unfold wp. rewrite Cmod_mul, Cmod_RtoC.
  rewrite (Rabs_pos_eq s) by lra.
  rewrite <- (Rmult_1_l (Cmod w)) at 2.
  apply Rmult_le_compat_r; [ apply Cmod_nonneg | lra ].
Qed.

(* modulus lower bound on the denominator: R - |w| > 0 *)
Lemma denom_lb : forall s u, 0 <= s <= 1 ->
  0 < Rr - Cmod w <= Cmod (Cminus (arc Rr u) (wp s)).
Proof.
  intros s u Hs. split; [ lra | ].
  eapply Rle_trans; [ | apply Cmod_rev_triangle ].
  rewrite (Cmod_arc Rr u) by lra.
  pose proof (wp_mod s Hs). lra.
Qed.

Lemma denom_ne : forall s u, 0 <= s <= 1 -> Cminus (arc Rr u) (wp s) <> C0.
Proof.
  intros s u Hs Hc.
  pose proof (denom_lb s u Hs) as [Hpos Hle].
  rewrite Hc, (proj2 (Cmod0 C0) eq_refl) in Hle. lra.
Qed.

(* the s-derivative of the winding integrand: w/(z - w_s)^2 * z' *)
Definition wdphi (s u : R) : C :=
  Cmul (Cmul w (Cinv (Cmul (Cminus (arc Rr u) (wp s)) (Cminus (arc Rr u) (wp s)))))
       (arc' Rr u).

(* its primitive (in z):  -w/(z - w_s) *)
Definition wprim (s : R) (z : C) : C := Cmul (Copp w) (Cinv (Cminus z (wp s))).

(* wprim s is a primitive of  z |-> w/(z - w_s)^2  on the circle *)
Lemma wprim_deriv : forall s u, 0 <= s <= 1 ->
  is_Cderiv (wprim s) (arc Rr u)
    (Cmul w (Cinv (Cmul (Cminus (arc Rr u) (wp s)) (Cminus (arc Rr u) (wp s))))).
Proof.
  intros s u Hs.
  assert (HDD : Cminus (arc Rr u) (wp s) <> C0) by (apply denom_ne; exact Hs).
  replace (Cmul w (Cinv (Cmul (Cminus (arc Rr u) (wp s)) (Cminus (arc Rr u) (wp s)))))
     with (Cmul (Copp w)
             (Cmul (Copp (Cinv (Cmul (Cminus (arc Rr u) (wp s)) (Cminus (arc Rr u) (wp s)))))
                   (Cminus C1 C0))).
  2:{ set (X := Cinv (Cmul (Cminus (arc Rr u) (wp s)) (Cminus (arc Rr u) (wp s)))).
      unfold Copp, Cmul, Cminus, C1, C0; apply Ceq; cbn [Re Im]; ring. }
  unfold wprim.
  apply (Cderiv_cscal (Copp w) (fun z => Cinv (Cminus z (wp s))) (arc Rr u)
           (Cmul (Copp (Cinv (Cmul (Cminus (arc Rr u) (wp s)) (Cminus (arc Rr u) (wp s)))))
                 (Cminus C1 C0))).
  apply (Cderiv_invc (fun z => Cminus z (wp s)) (arc Rr u) (Cminus C1 C0)); [ | exact HDD ].
  apply (Cderiv_minus (fun z => z) (fun _ => wp s) (arc Rr u) C1 C0);
    [ apply Cderiv_id | apply Cderiv_const ].
Qed.

(* continuity of the winding integrand and its s-derivative integrand *)
Lemma denom_cont : forall s, Ccont (fun u => Cminus (arc Rr u) (wp s)).
Proof. intro s; apply Ccont_minus; [ apply Ccont_arc | apply Ccont_const ]. Qed.

Lemma wphi_cont : forall s, 0 <= s <= 1 -> Ccont (fun u => wphi s u).
Proof.
  intros s Hs. unfold wphi. apply Ccont_mul; [ | apply Ccont_arc' ].
  apply Ccont_inv; [ apply denom_cont | intro u; apply denom_ne; exact Hs ].
Qed.

(* the derivative integrand written as f(z)*z' with f = fder s *)
Definition fder (s : R) (z : C) : C :=
  Cmul w (Cinv (Cmul (Cminus z (wp s)) (Cminus z (wp s)))).

Lemma wdphi_cont : forall s, 0 <= s <= 1 -> Ccont (fun u => wdphi s u).
Proof.
  intros s Hs. unfold wdphi. apply Ccont_mul; [ | apply Ccont_arc' ].
  apply Ccont_scal, Ccont_inv.
  - apply Ccont_mul; apply denom_cont.
  - intro u. apply Cmul_self_ne0, denom_ne; exact Hs.
Qed.

(* Jg = the closed-loop integral of the derivative integrand = 0,        *)
(* since fder s has the primitive wprim s and the arc is a closed loop.   *)
Lemma Jg_zero : forall s
  (Hf : Ccont (fun u => Cmul (fder s (arc Rr u)) (arc' Rr u))),
  0 <= s <= 1 ->
  pathint (arc Rr) (arc' Rr) (fder s) Hf 0 (2 * PI) = C0.
Proof.
  intros s Hf Hs.
  rewrite (pathint_FTC (wprim s) (fder s) (arc Rr) (arc' Rr) Hf 0 (2 * PI)).
  - rewrite arc_closed. unfold Cminus, C0; apply Ceq; cbn [Re Im]; ring.
  - generalize PI_RGT_0; lra.
  - intros u _. unfold fder. apply wprim_deriv; exact Hs.
  - intros u _; apply arc_Re_deriv.
  - intros u _; apply arc_Im_deriv.
Qed.

(* ---- Stage C pt4: the uniform first-order estimate Hunif ---- *)
Definition margin : R := (Rr - Cmod w) / 2.
Definition ballrad : R := (Rr - Cmod w) / (2 * (Cmod w + 1)).

Lemma margin_pos : 0 < margin.
Proof. unfold margin; lra. Qed.

Lemma ballrad_pos : 0 < ballrad.
Proof.
  unfold ballrad; apply Rdiv_lt_0_compat; [ lra | pose proof (Cmod_nonneg w); lra ].
Qed.

(* on the ball |s - s0| < ballrad (s0 in [0,1]) the pole stays margin away *)
Lemma denomA_lb : forall s s0 u, 0 <= s0 <= 1 -> Rabs (s - s0) < ballrad ->
  margin <= Cmod (Cminus (arc Rr u) (wp s)).
Proof.
  intros s s0 u Hs0 Hd.
  eapply Rle_trans; [ | apply Cmod_rev_triangle ].
  rewrite (Cmod_arc Rr u) by lra.
  assert (Hwp : Cmod (wp s) = Rabs s * Cmod w)
    by (unfold wp; rewrite Cmod_mul, Cmod_RtoC; reflexivity).
  rewrite Hwp.
  pose proof (Cmod_nonneg w) as HW.
  assert (Hs : Rabs s <= Rabs (s - s0) + 1).
  { pose proof (Rabs_triang (s - s0) s0) as Ht.
    replace (s - s0 + s0) with s in Ht by ring.
    assert (Rabs s0 <= 1) by (rewrite Rabs_pos_eq; lra). lra. }
  assert (H2 : 0 < 2 * (Cmod w + 1)) by lra.
  pose proof (Rmult_lt_compat_l (2 * (Cmod w + 1)) (Rabs (s - s0)) ballrad H2 Hd) as Hd2.
  unfold ballrad in Hd2.
  replace (2 * (Cmod w + 1) * ((Rr - Cmod w) / (2 * (Cmod w + 1)))) with (Rr - Cmod w)
    in Hd2 by (field; lra).
  unfold margin. nra.
Qed.

(* B - A = w * (s - s0):  the pole difference *)
Lemma poled_rel : forall s s0 u,
  Cminus (Cminus (arc Rr u) (wp s0)) (Cminus (arc Rr u) (wp s))
  = Cmul w (RtoC (s - s0)).
Proof. intros; unfold wp, RtoC; apply Ceq; simpl; ring. Qed.

(* THE UNIFORM FIRST-ORDER ESTIMATE (leibniz Hunif) *)
Lemma wphi_hunif : forall s0, 0 <= s0 <= 1 -> forall eps, 0 < eps ->
  exists del, 0 < del /\ forall s u, 0 <= u <= 2 * PI -> Rabs (s - s0) < del ->
    Cmod (Cminus (Cminus (wphi s u) (wphi s0 u)) (Cmul (wdphi s0 u) (RtoC (s - s0))))
    <= eps * Rabs (s - s0).
Proof.
  intros s0 Hs0 eps Heps.
  pose proof margin_pos as Hmp. pose proof (Cmod_nonneg w) as HW.
  set (Cc := Rr * (Cmod w * Cmod w) * (/ margin * / (margin * margin))).
  assert (Hinvm : 0 < / margin) by (apply Rinv_0_lt_compat; exact Hmp).
  assert (Hinvmm : 0 < / (margin * margin)) by (apply Rinv_0_lt_compat; nra).
  assert (HCc : 0 <= Cc)
    by (unfold Cc; apply Rmult_le_pos;
        [ apply Rmult_le_pos; [ lra | nra ] | apply Rmult_le_pos; lra ]).
  set (del := Rmin ballrad (eps / (Cc + 1))).
  exists del. split.
  - apply Rmin_glb_lt; [ apply ballrad_pos | apply Rdiv_lt_0_compat; lra ].
  - intros s u Hu Hsdel.
    assert (Hdb : Rabs (s - s0) < ballrad)
      by (eapply Rlt_le_trans; [ exact Hsdel | apply Rmin_l ]).
    assert (Hde : Rabs (s - s0) < eps / (Cc + 1))
      by (eapply Rlt_le_trans; [ exact Hsdel | apply Rmin_r ]).
    pose proof (denomA_lb s s0 u Hs0 Hdb) as HmA.
    assert (HmB : margin <= Cmod (Cminus (arc Rr u) (wp s0)))
      by (apply (denomA_lb s0 s0 u Hs0); rewrite Rminus_diag, Rabs_R0; apply ballrad_pos).
    set (A := Cminus (arc Rr u) (wp s)) in *.
    set (B := Cminus (arc Rr u) (wp s0)) in *.
    assert (HpA : 0 < Cmod A) by lra.
    assert (HpB : 0 < Cmod B) by lra.
    assert (HA0 : A <> C0)
      by (intro H; rewrite H, (proj2 (Cmod0 C0) eq_refl) in HmA; lra).
    assert (HB0 : B <> C0)
      by (intro H; rewrite H, (proj2 (Cmod0 C0) eq_refl) in HmB; lra).
    assert (Hfact : Cminus (Cminus (wphi s u) (wphi s0 u)) (Cmul (wdphi s0 u) (RtoC (s - s0)))
      = Cmul (Cmul (Cmul (Cmul w w) (Cmul (RtoC (s - s0)) (RtoC (s - s0))))
                   (Cmul (Cinv A) (Cinv (Cmul B B)))) (arc' Rr u)).
    { unfold wphi, wdphi; fold A B.
      rewrite factor_arc, (rem_identity A B w (RtoC (s - s0)) HA0 HB0 (poled_rel s s0 u));
        reflexivity. }
    rewrite Hfact, Cmod_mul, (Cmod_arc' Rr u ltac:(lra)).
    (* bound Cmod (product) * Rr  <=  Cc * |s-s0|^2  <=  eps * |s-s0| *)
    assert (HP : Cmod (Cmul (Cmul w w) (Cmul (RtoC (s - s0)) (RtoC (s - s0))))
               = Cmod w * Cmod w * (Rabs (s - s0) * Rabs (s - s0)))
      by (rewrite !Cmod_mul, !Cmod_RtoC; reflexivity).
    assert (HQ : Cmod (Cmul (Cinv A) (Cinv (Cmul B B))) <= / margin * / (margin * margin)).
    { rewrite Cmod_mul, (Cmod_inv A HA0), (Cmod_inv (Cmul B B) (Cmul_self_ne0 B HB0)), Cmod_mul.
      apply Rmult_le_compat.
      - left; apply Rinv_0_lt_compat; exact HpA.
      - left; apply Rinv_0_lt_compat; nra.
      - apply Rinv_le_contravar; [ exact Hmp | exact HmA ].
      - apply Rinv_le_contravar; [ nra | apply Rmult_le_compat; [ lra | lra | exact HmB | exact HmB ] ]. }
    apply Rle_trans with (Cc * (Rabs (s - s0) * Rabs (s - s0))).
    + rewrite Cmod_mul, HP.
      pose proof (Cmod_nonneg (Cmul (Cinv A) (Cinv (Cmul B B)))) as HQ0.
      unfold Cc.
      apply Rle_trans with
        (Cmod w * Cmod w * (Rabs (s - s0) * Rabs (s - s0))
         * (/ margin * / (margin * margin)) * Rr).
      * apply Rmult_le_compat_r; [ lra | ].
        apply Rmult_le_compat_l; [ apply Rmult_le_pos; apply Rmult_le_pos; try lra;
          apply Rabs_pos | exact HQ ].
      * apply Req_le; ring.
    + (* Cc * |s-s0|^2 <= eps * |s-s0| *)
      pose proof (Rabs_pos (s - s0)) as Hab.
      assert (Hcd : Cc * Rabs (s - s0) <= eps).
      { apply Rle_trans with (Cc * (eps / (Cc + 1))).
        - apply Rmult_le_compat_l; [ exact HCc | lra ].
        - apply (Rmult_le_reg_r (Cc + 1)); [ lra | ].
          replace (Cc * (eps / (Cc + 1)) * (Cc + 1)) with (Cc * eps) by (field; lra).
          nra. }
      apply Rle_trans with (Cc * Rabs (s - s0) * Rabs (s - s0)).
      * apply Req_le; ring.
      * apply Rmult_le_compat_r; [ exact Hab | exact Hcd ].
Qed.

End OffCenterWinding.

Print Assumptions Jg_zero.
