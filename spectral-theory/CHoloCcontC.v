(* ================================================================= *)
(*  CHoloCcontC.v  —  Hadamard keystone, brick 3 piece (b1):            *)
(*  a (pointwise) holomorphic function is path-continuous (CcontC).     *)
(*                                                                    *)
(*    holo_CcontC : (forall z, exists d, is_Cderiv F z d) -> CcontC F.  *)
(*                                                                    *)
(*  Needed to feed G = Log F (entire, brick 3 piece (a)) into the       *)
(*  holomorphic MEAN VALUE property (CCauchyFormula.meanval0/M_const),  *)
(*  whose F-argument must be CcontC.                                    *)
(*                                                                    *)
(*  Proof: for a continuous path g:R->C, F o g is continuous by         *)
(*  composing F's pointwise continuity (CHoloCalculus.is_Cderiv_cont)   *)
(*  with the Cmod-continuity of g (from Ccont g, using                  *)
(*  |Cmod(g x - g u0)| <= |Re(...)| + |Im(...)|).  Axiom-clean.         *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra.
Require Import ComplexField Cmodulus CIntegral2 CSegInt CHoloCalculus
        CDerivConst CSeries Holomorphic.
Open Scope R_scope.

Lemma Cmod_le_ReIm : forall c, Cmod c <= Rabs (Re c) + Rabs (Im c).
Proof.
  intro c. unfold Cmod.
  apply Rle_trans with (sqrt ((Rabs (Re c) + Rabs (Im c)) ^ 2)).
  - apply sqrt_le_1_alt. unfold Cnorm2.
    pose proof (Rabs_pos (Re c)); pose proof (Rabs_pos (Im c)).
    pose proof (Rsqr_abs (Re c)) as HR; pose proof (Rsqr_abs (Im c)) as HI.
    unfold Rsqr in HR, HI. nra.
  - replace ((Rabs (Re c) + Rabs (Im c)) ^ 2)
       with (Rsqr (Rabs (Re c) + Rabs (Im c))) by (unfold Rsqr; ring).
    rewrite sqrt_Rsqr by (apply Rplus_le_le_0_compat; apply Rabs_pos). apply Rle_refl.
Qed.

Theorem holo_CcontC : forall F, (forall z, exists d, is_Cderiv F z d) -> CcontC F.
Proof.
  intros F Hhol g Hg. destruct Hg as [HgRe HgIm].
  assert (comp : forall (proj : C -> R),
            (forall w, Rabs (proj w) <= Cmod w) ->
            (forall x y, proj (Cminus x y) = proj x - proj y) ->
            continuity (fun u => proj (F (g u)))).
  { intros proj Hproj Hpmin u0.
    unfold continuity_pt, continue_in, limit1_in.
    cbn [dist R_met]. unfold R_dist. cbv beta. intros eps Heps.
    destruct (Hhol (g u0)) as [d Hd].
    destruct (is_Cderiv_cont F (g u0) d Hd eps Heps) as [eta [Heta HF]].
    assert (Heta2 : 0 < eta / 2) by lra.
    destruct (HgRe u0 (eta / 2) Heta2) as [a1 [Ha1 HRe]].
    destruct (HgIm u0 (eta / 2) Heta2) as [a2 [Ha2 HIm]].
    cbn [dist R_met] in HRe, HIm. unfold R_dist in HRe, HIm. cbv beta in HRe, HIm.
    exists (Rmin a1 a2). split; [ apply Rmin_pos; assumption | ].
    intros x [Hdx Hxd].
    assert (Hx1 : Rabs (x - u0) < a1) by (eapply Rlt_le_trans; [ exact Hxd | apply Rmin_l ]).
    assert (Hx2 : Rabs (x - u0) < a2) by (eapply Rlt_le_trans; [ exact Hxd | apply Rmin_r ]).
    specialize (HRe x (conj Hdx Hx1)). specialize (HIm x (conj Hdx Hx2)).
    assert (Hcm : Cmod (Cminus (g x) (g u0)) < eta).
    { eapply Rle_lt_trans; [ apply Cmod_le_ReIm | ].
      rewrite ReCm, ImCm.
      apply Rlt_le_trans with (eta / 2 + eta / 2); [ | lra ].
      apply Rplus_lt_compat; assumption. }
    specialize (HF (Cminus (g x) (g u0)) Hcm).
    replace (Cadd (g u0) (Cminus (g x) (g u0))) with (g x) in HF by ring.
    change (dist R_met (proj (F (g x))) (proj (F (g u0))) < eps)
      with (Rabs (proj (F (g x)) - proj (F (g u0))) < eps).
    rewrite <- Hpmin.
    eapply Rle_lt_trans; [ apply Hproj | exact HF ]. }
  split; [ apply (comp Re Cmod_Re_le ReCm) | apply (comp Im Cmod_Im_le ImCm) ].
Qed.

(* ----------------------------------------------------------------- *)
(*  holomorphic ==> POINTWISE continuous.  is_Cderiv_cont states this   *)
(*  in increment form (F (z+h) vs F z); the two-point form is what      *)
(*  every disk lemma in this development actually asks for.            *)
(* ----------------------------------------------------------------- *)
Lemma holo_ptcont : forall F : C -> C,
  (forall z, exists d, is_Cderiv F z d) ->
  forall z eps, 0 < eps -> exists del, 0 < del /\
    forall z', Cmod (Cminus z' z) < del -> Cmod (Cminus (F z') (F z)) < eps.
Proof.
  intros F Hhol z eps Heps.
  destruct (Hhol z) as [d Hd].
  destruct (is_Cderiv_cont F z d Hd eps Heps) as [del [Hdel Hb]].
  exists del. split; [ exact Hdel | ].
  intros z' Hz'. specialize (Hb (Cminus z' z) Hz').
  replace (Cadd z (Cminus z' z)) with z' in Hb by ring.
  exact Hb.
Qed.

Print Assumptions holo_CcontC.
Print Assumptions holo_ptcont.
