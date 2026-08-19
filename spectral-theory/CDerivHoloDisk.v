(* ================================================================= *)
(*  CDerivHoloDisk.v  —  the derivative of a disk-holomorphic function  *)
(*  is itself holomorphic (holomorphic => twice differentiable).        *)
(*                                                                    *)
(*    deriv_holo_disk : F pointwise-continuous everywhere and           *)
(*      is_Cderiv F z (Fp z) on Cmod z < Rr + 1                         *)
(*        ==>  forall z, Cmod z < Rr / 2 -> exists d, is_Cderiv Fp z d. *)
(*                                                                    *)
(*  WHY THIS IS THE NEXT BRICK.  Every disk-hypothesis theorem in the   *)
(*  Jensen chain -- zero_free_MVP_disk, jensen_multi_zero_D,            *)
(*  jensen_count_D -- carries the hypothesis                            *)
(*      HGphol : forall z, Cmod z < R2 -> exists d, is_Cderiv Gp z d,   *)
(*  and nothing in the repo discharged it: a caller had to supply the   *)
(*  cofactor's SECOND derivative by hand.  Classically it is free       *)
(*  (holomorphic => analytic), and the identity-theorem tower already   *)
(*  contains the analytic engine -- it was just never phrased this way. *)
(*  It is also the prerequisite for the removable-singularity step of   *)
(*  the zero factorization F = (z - w) . H, the brick after this one.   *)
(*                                                                    *)
(*  PROOF.  Run CAnalyticTower's Cauchy-power tower                     *)
(*      fseq k = (k! / 2 pi i) . oint F(z)/(z-w)^{k+1} dz               *)
(*  on the circle |z| = Rr.  Three facts glue it:                       *)
(*    * fseq0_eq (CAnalyticTowerF): fseq 0 = F on Cmod w < Rr/2 -- the   *)
(*      Cauchy representation, itself cauchy_interior_dom;              *)
(*    * fseq_chain (CAnalyticTower): is_Cderiv (fseq k) z (fseq (S k) z)*)
(*      on the same disk;                                               *)
(*    * is_Cderiv_congr + is_Cderiv_unique: agreeing on a NEIGHBOURHOOD *)
(*      transports derivatives, so F' = fseq 1 pointwise on the inner   *)
(*      disk, and fseq 1 is differentiated by fseq 2.                   *)
(*  The circle bound Hgb that fseq_chain needs is free from CcontC via  *)
(*  CCircleBound.Ccont_circle_bounded.  Axiom-clean.                    *)
(*                                                                    *)
(*  The Rr/2 shrink is inherited from the tower (its clamp is exact     *)
(*  only on the half-radius disk) and costs nothing in practice: to get *)
(*  Fp holomorphic on Cmod z < R, run the theorem at Rr := 2 R.         *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra.
Require Import ComplexField Cmodulus Holomorphic CDeriv CIntegral2 CSegInt
        CPathIntegral PerronRemovable CDerivUnique CCircleBound
        CAnalyticTower CAnalyticTowerF.
Open Scope R_scope.

Section DerivHoloDisk.

Variable F Fp : C -> C.
Variable Rr : R.
Hypothesis HR : 0 < Rr.
Hypothesis HFptc : forall z eps, 0 < eps -> exists del, 0 < del /\
  forall z', Cmod (Cminus z' z) < del -> Cmod (Cminus (F z') (F z)) < eps.
Hypothesis HFp : forall z, Cmod z < Rr + 1 -> is_Cderiv F z (Fp z).

(* the two things the tower asks for, both free from the hypotheses *)
Definition HFc : CcontC F := ptcont_CcontC F HFptc.

Definition HFgb : exists Mg, 0 <= Mg /\ forall u, Cmod (F (arc Rr u)) <= Mg :=
  Ccont_circle_bounded F Rr HFc.

Lemma HFhol : forall z, Cmod z < Rr + 1 -> exists d, is_Cderiv F z d.
Proof. intros z Hz. exists (Fp z). apply HFp; exact Hz. Qed.

(* the Cauchy-power tower on the circle |z| = Rr *)
Definition fs (k : nat) : C -> C := fseq F Rr HR HFc k.

(* a point of the inner disk has a positive margin, and its neighbours
   of that radius are still in the inner disk *)
Lemma inner_margin : forall z, Cmod z < Rr / 2 -> 0 < Rr / 2 - Cmod z.
Proof. intros z Hz; lra. Qed.

Lemma inner_near : forall z w, Cmod z < Rr / 2 ->
  Cmod (Cminus w z) < Rr / 2 - Cmod z -> Cmod w < Rr / 2.
Proof.
  intros z w Hz Hw.
  assert (Htri : Cmod w <= Cmod (Cminus w z) + Cmod z)
    by (replace w with (Cadd (Cminus w z) z) at 1 by ring; apply Cmod_triangle).
  lra.
Qed.

(* --- Step 1: level 1 of the tower differentiates F itself ---------- *)
(* fseq_chain differentiates fseq 0, and fseq 0 agrees with F on the
   WHOLE inner disk (fseq0_eq), hence on a neighbourhood of z.          *)
Lemma F_deriv_fs1 : forall z, Cmod z < Rr / 2 -> is_Cderiv F z (fs 1 z).
Proof.
  intros z Hz.
  apply (is_Cderiv_congr F (fs 0) z (fs 1 z) (Rr / 2 - Cmod z)).
  - apply inner_margin; exact Hz.
  - intros w Hw. unfold fs. symmetry.
    exact (fseq0_eq F Rr HR HFc HFptc HFhol w (inner_near z w Hz Hw)).
  - unfold fs. exact (fseq_chain F Rr HR HFc HFgb 0 z Hz).
Qed.

(* --- Step 2: so Fp IS level 1, pointwise on the inner disk --------- *)
Lemma Fp_eq_fs1 : forall z, Cmod z < Rr / 2 -> Fp z = fs 1 z.
Proof.
  intros z Hz.
  apply (is_Cderiv_unique F z (Fp z) (fs 1 z)).
  - apply HFp; lra.
  - apply F_deriv_fs1; exact Hz.
Qed.

(* --- Step 3: level 1 is differentiated by level 2 ------------------ *)
Lemma Fp_deriv_fs2 : forall z, Cmod z < Rr / 2 -> is_Cderiv Fp z (fs 2 z).
Proof.
  intros z Hz.
  apply (is_Cderiv_congr Fp (fs 1) z (fs 2 z) (Rr / 2 - Cmod z)).
  - apply inner_margin; exact Hz.
  - intros w Hw. exact (Fp_eq_fs1 w (inner_near z w Hz Hw)).
  - unfold fs. exact (fseq_chain F Rr HR HFc HFgb 1 z Hz).
Qed.

Theorem deriv_holo_disk : forall z, Cmod z < Rr / 2 -> exists d, is_Cderiv Fp z d.
Proof. intros z Hz. exists (fs 2 z). apply Fp_deriv_fs2; exact Hz. Qed.

End DerivHoloDisk.

Print Assumptions deriv_holo_disk.

(* ----------------------------------------------------------------- *)
(*  Convenience form: to get Fp holomorphic on a TARGET disk of radius *)
(*  R2, run the tower on the circle of radius 2 R2.  This is the shape *)
(*  the Jensen disk lemmas ask for (their HGphol hypothesis).          *)
(* ----------------------------------------------------------------- *)
Corollary deriv_holo_radius : forall (F Fp : C -> C) (R2 : R),
  0 < R2 ->
  (forall z eps, 0 < eps -> exists del, 0 < del /\
     forall z', Cmod (Cminus z' z) < del -> Cmod (Cminus (F z') (F z)) < eps) ->
  (forall z, Cmod z < 2 * R2 + 1 -> is_Cderiv F z (Fp z)) ->
  forall z, Cmod z < R2 -> exists d, is_Cderiv Fp z d.
Proof.
  intros F Fp R2 HR2 HFptc HFp z Hz.
  apply (deriv_holo_disk F Fp (2 * R2)); [ lra | exact HFptc | exact HFp | lra ].
Qed.

Print Assumptions deriv_holo_radius.
