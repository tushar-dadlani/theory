(* ================================================================= *)
(*  CBorelBound.v  —  Borel-Caratheodory, Steps 5 onward.              *)
(*                                                                    *)
(*  Step 3 gave  G''(0) = A/PI  with  A = INT G(arc Rr t) . wgt Rr t.   *)
(*  Steps 2 and 4 gave  INT wgt = 0  and  INT conj(G(arc)) . wgt = 0.   *)
(*                                                                    *)
(*  STEP 5 (A_shift).  Those two zeros let A be rewritten with a REAL   *)
(*  integrand shifted by an ARBITRARY constant M:                       *)
(*                                                                    *)
(*    A = INT (2 Re G(arc Rr t) - 2 M) . wgt Rr t dt.                   *)
(*                                                                    *)
(*  2 Re x = x + conj x supplies the first zero (the conj half), and    *)
(*  INT wgt = 0 the second (the constant).  Choosing M := Mf Rr later   *)
(*  makes the scalar factor NON-POSITIVE, which is the whole point:     *)
(*  its absolute value is then 2M - 2 Re G, whose integral the mean     *)
(*  value property pins down exactly.  Axiom-clean.                    *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra.
Require Import ComplexField Cmodulus Holomorphic CDeriv CIntegral2 CSegInt
        CPathIntegral RootsOfUnity CImproperIntegral
        CIntfLinear CConjIntegral CArcWeight CConjHalf
        PerronRemovable CUnifCont CPrimitiveDisk CMeanValueDisk.
Open Scope R_scope.

Lemma RtoC_two_Re : forall w : C, RtoC (2 * Re w) = Cadd w (Cconj w).
Proof. intros [wr wi]. apply Ceq; cbn [Re Im RtoC Cadd Cconj]; ring. Qed.

Section BorelBound.

Variable G Gp : C -> C.
Variable Rr : R.
Hypothesis HR : 0 < Rr.
Hypothesis HGc : CcontC G.
Hypothesis HG : forall z, is_Cderiv G z (Gp z).

(* the three continuity facts the split needs *)
Definition HkerB : Ccont (fun t => Cmul (G (arc Rr t)) (wgt Rr t)) :=
  Ccont_G_wgt G Rr HR HGc.

Lemma HcjB : Ccont (fun t => Cmul (Cconj (G (arc Rr t))) (wgt Rr t)).
Proof.
  apply Ccont_mul.
  - apply Ccont_conj. exact (HGc (arc Rr) (Ccont_arc Rr)).
  - apply Ccont_wgt; exact HR.
Qed.

Lemma HconstB : forall c : C, Ccont (fun t => Cmul c (wgt Rr t)).
Proof. intro c. apply Ccont_scal. apply Ccont_wgt; exact HR. Qed.

(* ================================================================= *)
(*  STEP 5                                                             *)
(* ================================================================= *)
Theorem A_shift : forall (M : R)
  (Hsh : Ccont (fun t => Cmul (RtoC (2 * Re (G (arc Rr t)) - 2 * M)) (wgt Rr t))),
  Cintf (fun t => Cmul (RtoC (2 * Re (G (arc Rr t)) - 2 * M)) (wgt Rr t)) Hsh 0 (2 * PI)
  = Cintf (fun t => Cmul (G (arc Rr t)) (wgt Rr t)) HkerB 0 (2 * PI).
Proof.
  intros M Hsh.
  pose proof HcjB as Hcj.
  pose proof (HconstB (RtoC (- (2 * M)))) as H3.
  (* the inner sum: conj half + constant *)
  assert (Hin : Ccont (fun t => Cadd (Cmul (Cconj (G (arc Rr t))) (wgt Rr t))
                                     (Cmul (RtoC (- (2 * M))) (wgt Rr t))))
    by (apply Ccont_add; [ exact Hcj | exact H3 ]).
  assert (Hall : Ccont (fun t => Cadd (Cmul (G (arc Rr t)) (wgt Rr t))
                          (Cadd (Cmul (Cconj (G (arc Rr t))) (wgt Rr t))
                                (Cmul (RtoC (- (2 * M))) (wgt Rr t)))))
    by (apply Ccont_add; [ exact HkerB | exact Hin ]).
  (* pointwise split *)
  assert (Hpt : forall t,
    Cmul (RtoC (2 * Re (G (arc Rr t)) - 2 * M)) (wgt Rr t)
    = Cadd (Cmul (G (arc Rr t)) (wgt Rr t))
           (Cadd (Cmul (Cconj (G (arc Rr t))) (wgt Rr t))
                 (Cmul (RtoC (- (2 * M))) (wgt Rr t)))).
  { intro t.
    assert (Hs : RtoC (2 * Re (G (arc Rr t)) - 2 * M)
               = Cadd (Cadd (G (arc Rr t)) (Cconj (G (arc Rr t))))
                      (RtoC (- (2 * M)))).
    { rewrite <- RtoC_two_Re.
      destruct (G (arc Rr t)) as [gr gi].
      apply Ceq; cbn [Re Im RtoC Cadd]; ring. }
    rewrite Hs. ring. }
  rewrite (Cintf_ext _ _ Hsh Hall 0 (2 * PI) Hpt).
  rewrite (Cintf_add _ _ HkerB Hin Hall 0 (2 * PI)).
  rewrite (Cintf_add _ _ Hcj H3 Hin 0 (2 * PI)).
  (* the conjugate half is 0 (Step 4) *)
  rewrite (conj_half_zero G Gp Rr HR HGc HG Hcj).
  (* the constant term is 0 (Step 2) *)
  assert (Hwc : Ccont (wgt Rr)) by (apply Ccont_wgt; exact HR).
  rewrite (Cintf_scal (RtoC (- (2 * M))) (wgt Rr) Hwc H3 0 (2 * PI)).
  rewrite (Cintf_wgt_zero Rr Hwc HR).
  (* x + (0 + c*0) = x *)
  ring.
Qed.

(* ================================================================= *)
(*  STEP 7 -- the mean value property at the centre.                   *)
(*                                                                    *)
(*  This is what pins down INT Re G(arc Rr t) dt EXACTLY, and so turns  *)
(*  the Step 6 domination bound into something that actually decays.    *)
(*  Reuses CMeanValueDisk on a disk of radius Rr + 1 (G is entire, so   *)
(*  any radius does); the derivative's own regularity -- CcontC Gp and  *)
(*  uniform continuity along arcs -- comes from Gp being pointwise      *)
(*  continuous, which holo_ptcont gives from Gp holomorphic.           *)
(* ================================================================= *)
Hypothesis HGpptc : forall z eps, 0 < eps -> exists del, 0 < del /\
  forall z', Cmod (Cminus z' z) < del -> Cmod (Cminus (Gp z') (Gp z)) < eps.

Definition HGpc : CcontC Gp := ptcont_CcontC Gp HGpptc.

Theorem mean_value_G : forall (Hg : Ccont (fun t => G (arc Rr t))),
  Cintf (fun t => G (arc Rr t)) Hg 0 (2 * PI) = Cmul (RtoC (2 * PI)) (G C0).
Proof.
  intro Hg.
  assert (HGder : forall z, disk (Rr + 1) z -> is_Cderiv G z (Gp z))
    by (intros z _; apply HG).
  assert (HMconst : M G HGc Rr = M G HGc 0)
    by (apply (M_const_disk (Rr + 1) G Gp HGc HGpc HGder
                 (fun r0 eps He => arc_Fp_unif Gp HGpptc r0 eps He) Rr HR
                 ltac:(lra))).
  assert (HMval : M G HGc Rr = Cmul (RtoC (2 * PI)) (G C0))
    by (rewrite HMconst; apply meanval0_disk).
  rewrite <- HMval. unfold M, Fphi. apply Cintf_irrel.
Qed.

End BorelBound.

Print Assumptions A_shift.
Print Assumptions mean_value_G.
