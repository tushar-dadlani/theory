(* ================================================================= *)
(*  CHorizMVT.v  --  a mean value estimate along a HORIZONTAL segment. *)
(*                                                                    *)
(*    horiz_mvt : f complex-differentiable with |f'| <= M on the       *)
(*      segment from b + i.g to a + i.g   ==>                          *)
(*        |f(a + i.g) - f(b + i.g)|  <=  2 (a - b) M                   *)
(*                                                                    *)
(*  This is the step that turns a derivative bound into a bound on a   *)
(*  DIFFERENCE, and it is what lets a zero of zeta at beta + i.gamma   *)
(*  control zeta at a + i.gamma with a > 1, where the 3-4-1 lower      *)
(*  bound (ZetaLowerBound.zeta_lower) lives.                           *)
(*                                                                    *)
(*  No complex FTC is needed, and that is the point.  A general mean   *)
(*  value theorem is FALSE for complex functions -- there need be no   *)
(*  single point where the derivative realises the difference quotient *)
(*  -- so the usual route is to integrate f' along a path, which drags *)
(*  in path integrals, primitives on a disk, and an ML inequality.     *)
(*  But the segment here is HORIZONTAL, so t |-> f(t + i.g) is a map   *)
(*  R -> C, and the REAL mean value theorem applies to its real and    *)
(*  imaginary parts SEPARATELY.  Two applications of MVT_cor2 and the  *)
(*  triangle inequality Cmod w <= |Re w| + |Im w| give the result --   *)
(*  at the cost of the harmless factor 2, since the two parts may be   *)
(*  realised at different interior points.                            *)
(*                                                                    *)
(*  The bridge lemma is is_Cderiv_real_dir: complex differentiability  *)
(*  at z, tested along REAL increments h, gives ordinary real          *)
(*  differentiability of Re f and Im f in the horizontal direction,    *)
(*  with derivatives Re f'(z) and Im f'(z).  Axiom-clean.              *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import ComplexField Cmodulus CSeries Holomorphic CDeriv.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  A.  components are dominated by the modulus                        *)
(* ----------------------------------------------------------------- *)
Lemma Re_le_Cmod : forall w, Rabs (Re w) <= Cmod w.
Proof.
  intro w. unfold Cmod, Cnorm2. rewrite <- (sqrt_Rsqr_abs (Re w)).
  apply sqrt_le_1_alt. unfold Rsqr. nra.
Qed.

Lemma Im_le_Cmod' : forall w, Rabs (Im w) <= Cmod w.
Proof.
  intro w. unfold Cmod, Cnorm2. rewrite <- (sqrt_Rsqr_abs (Im w)).
  apply sqrt_le_1_alt. unfold Rsqr. nra.
Qed.

Lemma abs_div_le : forall A h e, h <> 0 -> Rabs A <= e * Rabs h -> Rabs (A / h) <= e.
Proof.
  intros A h e Hh HA.
  assert (Hq : Rabs (A / h) * Rabs h = Rabs A)
    by (rewrite <- Rabs_mult; f_equal; field; exact Hh).
  assert (Hp : 0 < Rabs h) by (apply Rabs_pos_lt; exact Hh).
  nra.
Qed.

Lemma shift_real : forall x g h, Cadd (mkC x g) (RtoC h) = mkC (x + h) g.
Proof. intros x g h. apply Ceq; unfold Cadd, RtoC; cbn [Re Im]; ring. Qed.

(* ----------------------------------------------------------------- *)
(*  B.  the bridge: complex derivative ==> real directional derivative *)
(* ----------------------------------------------------------------- *)
Lemma is_Cderiv_real_dir_Re : forall f x g d,
  is_Cderiv f (mkC x g) d ->
  derivable_pt_lim (fun t => Re (f (mkC t g))) x (Re d).
Proof.
  intros f x g d Hd eps Heps.
  destruct (Hd (eps / 2) ltac:(lra)) as [del [Hdel Hb]].
  exists (mkposreal del Hdel). intros h Hh0 Hhd.
  assert (Hmod : Cmod (RtoC h) < del)
    by (rewrite Cmod_RtoC; cbn in Hhd; exact Hhd).
  pose proof (Hb (RtoC h) Hmod) as HB.
  rewrite shift_real in HB.
  assert (Habs : Rabs (Re (Cminus (Cminus (f (mkC (x + h) g)) (f (mkC x g)))
                                  (Cmul d (RtoC h))))
              <= eps / 2 * Rabs h).
  { eapply Rle_trans; [ apply Re_le_Cmod | ].
    rewrite Cmod_RtoC in HB. exact HB. }
  assert (Ere : Re (Cminus (Cminus (f (mkC (x + h) g)) (f (mkC x g)))
                           (Cmul d (RtoC h)))
              = Re (f (mkC (x + h) g)) - Re (f (mkC x g)) - Re d * h)
    by (unfold Cminus, Cmul, RtoC; cbn [Re Im]; ring).
  rewrite Ere in Habs.
  assert (Hh : Rabs h > 0) by (apply Rabs_pos_lt; exact Hh0).
  assert (Hdiv : Rabs ((Re (f (mkC (x + h) g)) - Re (f (mkC x g))) / h - Re d)
              <= eps / 2).
  { assert (E : (Re (f (mkC (x + h) g)) - Re (f (mkC x g))) / h - Re d
              = (Re (f (mkC (x + h) g)) - Re (f (mkC x g)) - Re d * h) / h)
      by (field; exact Hh0).
    rewrite E. apply abs_div_le; [ exact Hh0 | exact Habs ]. }
  lra.
Qed.

Lemma is_Cderiv_real_dir_Im : forall f x g d,
  is_Cderiv f (mkC x g) d ->
  derivable_pt_lim (fun t => Im (f (mkC t g))) x (Im d).
Proof.
  intros f x g d Hd eps Heps.
  destruct (Hd (eps / 2) ltac:(lra)) as [del [Hdel Hb]].
  exists (mkposreal del Hdel). intros h Hh0 Hhd.
  assert (Hmod : Cmod (RtoC h) < del)
    by (rewrite Cmod_RtoC; cbn in Hhd; exact Hhd).
  pose proof (Hb (RtoC h) Hmod) as HB.
  rewrite shift_real in HB.
  assert (Habs : Rabs (Im (Cminus (Cminus (f (mkC (x + h) g)) (f (mkC x g)))
                                  (Cmul d (RtoC h))))
              <= eps / 2 * Rabs h).
  { eapply Rle_trans; [ apply Im_le_Cmod' | ].
    rewrite Cmod_RtoC in HB. exact HB. }
  assert (Eim : Im (Cminus (Cminus (f (mkC (x + h) g)) (f (mkC x g)))
                           (Cmul d (RtoC h)))
              = Im (f (mkC (x + h) g)) - Im (f (mkC x g)) - Im d * h)
    by (unfold Cminus, Cmul, RtoC; cbn [Re Im]; ring).
  rewrite Eim in Habs.
  assert (Hh : Rabs h > 0) by (apply Rabs_pos_lt; exact Hh0).
  assert (Hdiv : Rabs ((Im (f (mkC (x + h) g)) - Im (f (mkC x g))) / h - Im d)
              <= eps / 2).
  { assert (E : (Im (f (mkC (x + h) g)) - Im (f (mkC x g))) / h - Im d
              = (Im (f (mkC (x + h) g)) - Im (f (mkC x g)) - Im d * h) / h)
      by (field; exact Hh0).
    rewrite E. apply abs_div_le; [ exact Hh0 | exact Habs ]. }
  lra.
Qed.

(* ----------------------------------------------------------------- *)
(*  C.  THE HORIZONTAL MEAN VALUE ESTIMATE                             *)
(* ----------------------------------------------------------------- *)
Theorem horiz_mvt : forall (f fd : C -> C) (b a g M : R),
  b <= a -> 0 <= M ->
  (forall x, b <= x <= a -> is_Cderiv f (mkC x g) (fd (mkC x g))) ->
  (forall x, b <= x <= a -> Cmod (fd (mkC x g)) <= M) ->
  Cmod (Cminus (f (mkC a g)) (f (mkC b g))) <= 2 * (a - b) * M.
Proof.
  intros f fd b a g M Hba HM Hder Hbd.
  destruct (Rle_lt_or_eq_dec b a Hba) as [Hlt | Heq].
  - (* b < a : two real mean value theorems *)
    assert (HRe : exists c, b < c < a /\
              Re (f (mkC a g)) - Re (f (mkC b g)) = Re (fd (mkC c g)) * (a - b)).
    { destruct (MVT_cor2 (fun t => Re (f (mkC t g)))
                         (fun t => Re (fd (mkC t g))) b a Hlt
                 (fun c Hc => is_Cderiv_real_dir_Re f c g _ (Hder c Hc)))
        as [c [Hc1 Hc2]].
      exists c; split; [ exact Hc2 | exact Hc1 ]. }
    assert (HIm : exists c, b < c < a /\
              Im (f (mkC a g)) - Im (f (mkC b g)) = Im (fd (mkC c g)) * (a - b)).
    { destruct (MVT_cor2 (fun t => Im (f (mkC t g)))
                         (fun t => Im (fd (mkC t g))) b a Hlt
                 (fun c Hc => is_Cderiv_real_dir_Im f c g _ (Hder c Hc)))
        as [c [Hc1 Hc2]].
      exists c; split; [ exact Hc2 | exact Hc1 ]. }
    destruct HRe as [c1 [Hc1r Hc1e]]. destruct HIm as [c2 [Hc2r Hc2e]].
    assert (B1 : Rabs (Re (fd (mkC c1 g))) <= M)
      by (eapply Rle_trans; [ apply Re_le_Cmod | apply Hbd; lra ]).
    assert (B2 : Rabs (Im (fd (mkC c2 g))) <= M)
      by (eapply Rle_trans; [ apply Im_le_Cmod' | apply Hbd; lra ]).
    eapply Rle_trans; [ apply Cmod_le_sum | ].
    assert (E1 : Re (Cminus (f (mkC a g)) (f (mkC b g)))
               = Re (fd (mkC c1 g)) * (a - b))
      by (unfold Cminus; cbn [Re]; lra).
    assert (E2 : Im (Cminus (f (mkC a g)) (f (mkC b g)))
               = Im (fd (mkC c2 g)) * (a - b))
      by (unfold Cminus; cbn [Im]; lra).
    rewrite E1, E2, !Rabs_mult, (Rabs_right (a - b) ltac:(lra)).
    nra.
  - (* b = a : the difference is 0 *)
    subst a.
    assert (E : Cminus (f (mkC b g)) (f (mkC b g)) = C0) by ring.
    rewrite E.
    assert (E0 : Cmod C0 = 0) by (apply (proj2 (Cmod0 C0)); reflexivity).
    rewrite E0. lra.
Qed.

Print Assumptions is_Cderiv_real_dir_Re.
Print Assumptions horiz_mvt.
