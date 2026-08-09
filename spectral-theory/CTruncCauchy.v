(* ================================================================= *)
(*  CTruncCauchy.v  —  Milestone C, brick C4-5: Cauchy's integral       *)
(*  formula on Zagier's truncated contour  ∮_C F/z = 2πi·F(0).           *)
(*                                                                     *)
(*  Split F(z)/z = (F(z)−F(0))/z + F(0)/z (distributivity, holds        *)
(*  everywhere).  The first summand φ is holomorphic off 0, continuous  *)
(*  through 0 (removable), so its loop integral telescopes to 0 via the *)
(*  exceptional-point primitive PrimE (brick 3) + pathint_FTC.  The     *)
(*  second gives F(0)·∮_C dz/z = F(0)·2πi (brick 4, trunc_winding).      *)
(*                                                                     *)
(*  Conditional on the removable quotient φ being globally continuous   *)
(*  (CcontC) and satisfying the exceptional-point hypotheses — this is  *)
(*  the interface the Newman application supplies (the "extension"      *)
(*  concern:  the integral infrastructure needs GLOBAL continuity).     *)
(* ================================================================= *)

From Stdlib Require Import Reals Ratan Lra Lia.
Require Import ComplexField Cmodulus Holomorphic
        CIntegral2 CGoursatLin CLeibniz CPathIntegral CSegInt CWinding
        CPathFTC CPrimConv CGoursatExcept CTruncWind.
Open Scope R_scope.

(* ---- path-derivative facts for the arc and the chord ---- *)
Lemma arc_Re_deriv : forall Rr s,
  derivable_pt_lim (fun r => Re (arc Rr r)) s (Re (arc' Rr s)).
Proof.
  intros Rr s. unfold arc, arc'; cbn [Re Im].
  replace (- (Rr * sin s)) with (Rr * (- sin s)) by ring.
  exact (derivable_pt_lim_scal cos Rr s (- sin s) (derivable_pt_lim_cos s)).
Qed.

Lemma arc_Im_deriv : forall Rr s,
  derivable_pt_lim (fun r => Im (arc Rr r)) s (Im (arc' Rr s)).
Proof.
  intros Rr s. unfold arc, arc'; cbn [Re Im].
  exact (derivable_pt_lim_scal sin Rr s (cos s) (derivable_pt_lim_sin s)).
Qed.

Lemma chord_Re_deriv : forall (P Q : C) s,
  derivable_pt_lim (fun r => Re (seg P Q r)) s (Re (seg' P Q s)).
Proof.
  intros P Q s eps Heps. exists (mkposreal 1 Rlt_0_1). intros h Hh0 _.
  unfold seg, seg', Cadd, Cmul, Cminus, RtoC; cbn [Re Im].
  match goal with |- Rabs ?e < _ => replace e with 0 by (field; exact Hh0) end.
  rewrite Rabs_R0; exact Heps.
Qed.

Lemma chord_Im_deriv : forall (P Q : C) s,
  derivable_pt_lim (fun r => Im (seg P Q r)) s (Im (seg' P Q s)).
Proof.
  intros P Q s eps Heps. exists (mkposreal 1 Rlt_0_1). intros h Hh0 _.
  unfold seg, seg', Cadd, Cmul, Cminus, RtoC; cbn [Re Im].
  match goal with |- Rabs ?e < _ => replace e with 0 by (field; exact Hh0) end.
  rewrite Rabs_R0; exact Heps.
Qed.

(* ---- contour endpoints ---- *)
Lemma arc_neg : forall Rr alpha,
  arc Rr (- alpha) = mkC (Rr * cos alpha) (- (Rr * sin alpha)).
Proof.
  intros; unfold arc; rewrite cos_neg, sin_neg; apply Ceq; cbn; ring.
Qed.

Lemma seg_at0 : forall (P Q : C), seg P Q 0 = P.
Proof. intros; unfold seg, Cadd, Cmul, Cminus, RtoC; apply Ceq; cbn; ring. Qed.

Lemma seg_at1 : forall (P Q : C), seg P Q 1 = Q.
Proof. intros; unfold seg, Cadd, Cmul, Cminus, RtoC; apply Ceq; cbn; ring. Qed.

Lemma Ccont_seg_id : forall (P Q : C), Ccont (seg P Q).
Proof.
  intros P Q.
  apply (Ccont_seg_comp P Q (fun x => x)); intro x;
    apply derivable_continuous_pt, derivable_pt_id.
Qed.

Lemma Ccont_seg'_id : forall (P Q : C), Ccont (seg' P Q).
Proof. intros P Q; unfold seg'; apply Ccont_const. Qed.

(* ================================================================= *)
(*  THE TRUNCATED CAUCHY FORMULA.                                      *)
(*  φ is the removable quotient (F z − F 0)/z; the hypotheses on it are  *)
(*  the exceptional-point interface (brick 3) plus global continuity.   *)
(* ================================================================= *)
Section TruncCauchy.
Variables (Rr alpha : R).
Hypothesis HR : 0 < Rr.
Hypothesis Halpha : PI / 2 < alpha < PI.
Let Pc : C := mkC (Rr * cos alpha) (Rr * sin alpha).
Let Qc : C := mkC (Rr * cos alpha) (- (Rr * sin alpha)).

Variable U : C -> Prop.
Hypothesis HUconv : Convex U.
Hypothesis HUopen : Open U.
Hypothesis HU0 : U C0.
Hypothesis HarcU : forall s, - alpha <= s <= alpha -> U (arc Rr s).
Hypothesis HchordU : forall s, 0 <= s <= 1 -> U (seg Pc Qc s).
Variable z0 : C.
Hypothesis HUz0 : U z0.

Variable F : C -> C.
Variable phi : C -> C.
Hypothesis Hphic : CcontC phi.
Hypothesis Hpath_arc : forall s,
  phi (arc Rr s) = Cmul (Cminus (F (arc Rr s)) (F C0)) (Cinv (arc Rr s)).
Hypothesis Hpath_chord : forall s,
  phi (seg Pc Qc s) = Cmul (Cminus (F (seg Pc Qc s)) (F C0)) (Cinv (seg Pc Qc s)).
Hypothesis Hphi_hol : forall z, U z -> z <> C0 -> exists d, is_Cderiv phi z d.
Hypothesis Hphi_bd : exists M eta, 0 < eta /\
  forall w, Cmod (Cminus w C0) < eta -> Cmod (phi w) <= M.
Hypothesis Hphi_cont : forall z, U z -> forall eps, 0 < eps -> exists del, 0 < del /\
  forall w, Cmod (Cminus w z) < del -> Cmod (Cminus (phi w) (phi z)) < eps.
Hypothesis HcC : Ccont (fun u => Cmul (Cinv (seg Pc Qc u)) (seg' Pc Qc u)).

Theorem trunc_cauchy :
  forall (HfaF : Ccont (fun u => Cmul (Cmul (F (arc Rr u)) (Cinv (arc Rr u))) (arc' Rr u)))
         (HfcF : Ccont (fun u => Cmul (Cmul (F (seg Pc Qc u)) (Cinv (seg Pc Qc u))) (seg' Pc Qc u))),
  Cadd (pathint (arc Rr) (arc' Rr) (fun z => Cmul (F z) (Cinv z)) HfaF (- alpha) alpha)
       (pathint (seg Pc Qc) (seg' Pc Qc) (fun z => Cmul (F z) (Cinv z)) HfcF 0 1)
  = Cmul (F C0) (mkC 0 (2 * PI)).
Proof.
  intros HfaF HfcF. assert (HPI := PI_RGT_0).
  (* the exceptional-point primitive of phi and its derivative on U *)
  assert (HH : forall z, U z -> is_Cderiv (PrimE phi Hphic z0) z (phi z))
    by (intros z HUz;
        apply (PrimE_deriv U HUconv HUopen phi Hphic C0 HU0
                 Hphi_hol Hphi_bd Hphi_cont z0 HUz0 z HUz)).
  (* continuity witnesses for the phi path integrands *)
  assert (Hphiarc : Ccont (fun u => Cmul (phi (arc Rr u)) (arc' Rr u)))
    by (apply Ccont_mul; [ apply Hphic, Ccont_arc | apply Ccont_arc' ]).
  assert (Hphichord : Ccont (fun u => Cmul (phi (seg Pc Qc u)) (seg' Pc Qc u)))
    by (apply Ccont_mul; [ apply Hphic, Ccont_seg_id | apply Ccont_seg'_id ]).
  (* the phi loop integral telescopes to 0 (FTC on arc, then on chord) *)
  assert (Iarc_phi : pathint (arc Rr) (arc' Rr) phi Hphiarc (- alpha) alpha
                   = Cminus (PrimE phi Hphic z0 (arc Rr alpha))
                            (PrimE phi Hphic z0 (arc Rr (- alpha)))).
  { apply (pathint_FTC (PrimE phi Hphic z0) phi (arc Rr) (arc' Rr) Hphiarc (- alpha) alpha);
      [ lra | intros s Hs; apply HH, HarcU, Hs
      | intros s _; apply arc_Re_deriv | intros s _; apply arc_Im_deriv ]. }
  assert (Ichord_phi : pathint (seg Pc Qc) (seg' Pc Qc) phi Hphichord 0 1
                     = Cminus (PrimE phi Hphic z0 (seg Pc Qc 1))
                              (PrimE phi Hphic z0 (seg Pc Qc 0))).
  { apply (pathint_FTC (PrimE phi Hphic z0) phi (seg Pc Qc) (seg' Pc Qc) Hphichord 0 1);
      [ lra | intros s Hs; apply HH, HchordU, Hs
      | intros s _; apply chord_Re_deriv | intros s _; apply chord_Im_deriv ]. }
  assert (Hphisum : Cadd (pathint (arc Rr) (arc' Rr) phi Hphiarc (- alpha) alpha)
                         (pathint (seg Pc Qc) (seg' Pc Qc) phi Hphichord 0 1) = C0).
  { rewrite Iarc_phi, Ichord_phi, seg_at0, seg_at1.
    assert (Ha1 : arc Rr alpha = Pc) by reflexivity.
    assert (Ha2 : arc Rr (- alpha) = Qc) by (unfold Qc; apply arc_neg).
    rewrite Ha1, Ha2; ring. }
  (* split each piece:  F/z = phi + F0·(1/z) *)
  assert (Hwa := arc_int_cont Rr HR).
  assert (HscF0a : Ccont (fun u => Cmul (F C0) (Cmul (Cinv (arc Rr u)) (arc' Rr u))))
    by (apply Ccont_scal; exact Hwa).
  assert (Hsuma : Ccont (fun u => Cadd (Cmul (phi (arc Rr u)) (arc' Rr u))
                             (Cmul (F C0) (Cmul (Cinv (arc Rr u)) (arc' Rr u)))))
    by (apply Ccont_add; [ exact Hphiarc | exact HscF0a ]).
  assert (Harc_split :
    pathint (arc Rr) (arc' Rr) (fun z => Cmul (F z) (Cinv z)) HfaF (- alpha) alpha
    = Cadd (pathint (arc Rr) (arc' Rr) phi Hphiarc (- alpha) alpha)
           (Cmul (F C0) (pathint (arc Rr) (arc' Rr) Cinv Hwa (- alpha) alpha))).
  { unfold pathint.
    rewrite (Cintf_ext
               (fun u => Cmul (Cmul (F (arc Rr u)) (Cinv (arc Rr u))) (arc' Rr u))
               (fun u => Cadd (Cmul (phi (arc Rr u)) (arc' Rr u))
                              (Cmul (F C0) (Cmul (Cinv (arc Rr u)) (arc' Rr u))))
               HfaF Hsuma (- alpha) alpha);
      [ | intro u; rewrite Hpath_arc; ring ].
    rewrite (Cintf_add (fun u => Cmul (phi (arc Rr u)) (arc' Rr u))
               (fun u => Cmul (F C0) (Cmul (Cinv (arc Rr u)) (arc' Rr u)))
               Hphiarc HscF0a Hsuma (- alpha) alpha ltac:(lra)).
    rewrite (Cintf_cmul_l (F C0) (fun u => Cmul (Cinv (arc Rr u)) (arc' Rr u))
               Hwa HscF0a (- alpha) alpha ltac:(lra)).
    reflexivity. }
  assert (HscF0c : Ccont (fun u => Cmul (F C0) (Cmul (Cinv (seg Pc Qc u)) (seg' Pc Qc u))))
    by (apply Ccont_scal; exact HcC).
  assert (Hsumc : Ccont (fun u => Cadd (Cmul (phi (seg Pc Qc u)) (seg' Pc Qc u))
                             (Cmul (F C0) (Cmul (Cinv (seg Pc Qc u)) (seg' Pc Qc u)))))
    by (apply Ccont_add; [ exact Hphichord | exact HscF0c ]).
  assert (Hchord_split :
    pathint (seg Pc Qc) (seg' Pc Qc) (fun z => Cmul (F z) (Cinv z)) HfcF 0 1
    = Cadd (pathint (seg Pc Qc) (seg' Pc Qc) phi Hphichord 0 1)
           (Cmul (F C0) (pathint (seg Pc Qc) (seg' Pc Qc) Cinv HcC 0 1))).
  { unfold pathint.
    rewrite (Cintf_ext
               (fun u => Cmul (Cmul (F (seg Pc Qc u)) (Cinv (seg Pc Qc u))) (seg' Pc Qc u))
               (fun u => Cadd (Cmul (phi (seg Pc Qc u)) (seg' Pc Qc u))
                              (Cmul (F C0) (Cmul (Cinv (seg Pc Qc u)) (seg' Pc Qc u))))
               HfcF Hsumc 0 1);
      [ | intro u; rewrite Hpath_chord; ring ].
    rewrite (Cintf_add (fun u => Cmul (phi (seg Pc Qc u)) (seg' Pc Qc u))
               (fun u => Cmul (F C0) (Cmul (Cinv (seg Pc Qc u)) (seg' Pc Qc u)))
               Hphichord HscF0c Hsumc 0 1 ltac:(lra)).
    rewrite (Cintf_cmul_l (F C0) (fun u => Cmul (Cinv (seg Pc Qc u)) (seg' Pc Qc u))
               HcC HscF0c 0 1 ltac:(lra)).
    reflexivity. }
  (* the winding number (brick 4) *)
  assert (Hwind : Cadd (pathint (arc Rr) (arc' Rr) Cinv Hwa (- alpha) alpha)
                       (pathint (seg Pc Qc) (seg' Pc Qc) Cinv HcC 0 1) = mkC 0 (2 * PI))
    by exact (trunc_winding Rr alpha HR Halpha Hwa HcC).
  (* assemble *)
  rewrite Harc_split, Hchord_split.
  transitivity (Cadd (Cadd (pathint (arc Rr) (arc' Rr) phi Hphiarc (- alpha) alpha)
                           (pathint (seg Pc Qc) (seg' Pc Qc) phi Hphichord 0 1))
                     (Cmul (F C0)
                        (Cadd (pathint (arc Rr) (arc' Rr) Cinv Hwa (- alpha) alpha)
                              (pathint (seg Pc Qc) (seg' Pc Qc) Cinv HcC 0 1)))).
  - ring.
  - rewrite Hphisum, Hwind; ring.
Qed.

End TruncCauchy.

Print Assumptions trunc_cauchy.
