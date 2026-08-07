(* ================================================================= *)
(*  CFTC.v  —  the C-valued fundamental theorem of calculus for the     *)
(*  complex power kernel gC s x = x^{-s}, in the REAL base variable x.   *)
(*                                                                    *)
(*  gderivC s x = -s x^{-s-1} = d/dx (x^{-s}) (RegC_deriv/ImgC_deriv),   *)
(*  and it is continuous on x>0, hence Riemann-integrable on [a,b]       *)
(*  (0<a<=b).  Componentwise FTC (stdlib FTC_antideriv) gives            *)
(*     ∫_a^b Re(gderivC s x) dx = Re(gC s b) - Re(gC s a),  and Im,      *)
(*  i.e.  ∫_a^b gderivC s x dx = gC s b - gC s a  (C-valued).            *)
(*  Consequently  k^{-s} - (k+1)^{-s} = ∫_k^{k+1} s x^{-s-1} dx.         *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia FunctionalExtensionality.
Require Import ComplexField Cmodulus CexpFull CPowBase CZetaTerm ContinuousCoV.
Open Scope R_scope.

Section FTC.
Variable s : C.

(* ---- continuity of the components of x^{-s} and of gderivC ---- *)
Lemma Re_Cpw_cont : forall w x, 0 < x -> continuity_pt (fun t => Re (Cpw t w)) x.
Proof.
  intros w x Hx; apply derivable_continuous_pt.
  exists (Re (Cmul w (Cpw x (Cminus w C1)))); apply Re_Cpw_deriv; exact Hx.
Qed.

Lemma Im_Cpw_cont : forall w x, 0 < x -> continuity_pt (fun t => Im (Cpw t w)) x.
Proof.
  intros w x Hx; apply derivable_continuous_pt.
  exists (Im (Cmul w (Cpw x (Cminus w C1)))); apply Im_Cpw_deriv; exact Hx.
Qed.

Lemma Re_gderivC_cont : forall x, 0 < x -> continuity_pt (fun t => Re (gderivC s t)) x.
Proof.
  intros x Hx.
  assert (Heq : (fun t => Re (gderivC s t))
    = (fun t => Re (Copp s) * Re (Cpw t (Cminus (Copp s) C1))
                - Im (Copp s) * Im (Cpw t (Cminus (Copp s) C1)))).
  { apply functional_extensionality; intro t; unfold gderivC, Cmul; cbn [Re Im]; ring. }
  rewrite Heq.
  apply continuity_pt_minus; apply continuity_pt_mult;
    solve [ apply continuity_pt_const; intros a b; reflexivity
          | apply Re_Cpw_cont; exact Hx | apply Im_Cpw_cont; exact Hx ].
Qed.

Lemma Im_gderivC_cont : forall x, 0 < x -> continuity_pt (fun t => Im (gderivC s t)) x.
Proof.
  intros x Hx.
  assert (Heq : (fun t => Im (gderivC s t))
    = (fun t => Re (Copp s) * Im (Cpw t (Cminus (Copp s) C1))
                + Im (Copp s) * Re (Cpw t (Cminus (Copp s) C1)))).
  { apply functional_extensionality; intro t; unfold gderivC, Cmul; cbn [Re Im]; ring. }
  rewrite Heq.
  apply continuity_pt_plus; apply continuity_pt_mult;
    solve [ apply continuity_pt_const; intros a b; reflexivity
          | apply Re_Cpw_cont; exact Hx | apply Im_Cpw_cont; exact Hx ].
Qed.

(* ---- Riemann integrability on [a,b], 0 < a <= b ---- *)
Lemma Re_gderivC_RI : forall a b, 0 < a -> a <= b ->
  Riemann_integrable (fun u => Re (gderivC s u)) a b.
Proof.
  intros a b Ha Hab; apply continuity_implies_RiemannInt; [ exact Hab | ].
  intros x [Hx1 Hx2]; apply Re_gderivC_cont; lra.
Qed.

Lemma Im_gderivC_RI : forall a b, 0 < a -> a <= b ->
  Riemann_integrable (fun u => Im (gderivC s u)) a b.
Proof.
  intros a b Ha Hab; apply continuity_implies_RiemannInt; [ exact Hab | ].
  intros x [Hx1 Hx2]; apply Im_gderivC_cont; lra.
Qed.

(* ---- the componentwise FTC ---- *)
Lemma Re_gC_FTC : forall a b (Ha : 0 < a) (Hab : a <= b),
  RiemannInt (Re_gderivC_RI a b Ha Hab) = Re (gC s b) - Re (gC s a).
Proof.
  intros a b Ha Hab.
  apply (FTC_antideriv (fun u => Re (gderivC s u)) (fun t => Re (gC s t)) a b Hab).
  - intros x [Hx1 Hx2]; apply Re_gderivC_cont; lra.
  - split; [ | exact Hab ].
    intros x [Hx1 Hx2].
    assert (Hx0 : 0 < x) by lra.
    exists (exist _ (Re (gderivC s x)) (RegC_deriv s x Hx0)); reflexivity.
Qed.

Lemma Im_gC_FTC : forall a b (Ha : 0 < a) (Hab : a <= b),
  RiemannInt (Im_gderivC_RI a b Ha Hab) = Im (gC s b) - Im (gC s a).
Proof.
  intros a b Ha Hab.
  apply (FTC_antideriv (fun u => Im (gderivC s u)) (fun t => Im (gC s t)) a b Hab).
  - intros x [Hx1 Hx2]; apply Im_gderivC_cont; lra.
  - split; [ | exact Hab ].
    intros x [Hx1 Hx2].
    assert (Hx0 : 0 < x) by lra.
    exists (exist _ (Im (gderivC s x)) (ImgC_deriv s x Hx0)); reflexivity.
Qed.

(* ---- the C-valued FTC, packaged ---- *)
Definition CgderivInt (a b : R) (Ha : 0 < a) (Hab : a <= b) : C :=
  mkC (RiemannInt (Re_gderivC_RI a b Ha Hab)) (RiemannInt (Im_gderivC_RI a b Ha Hab)).

Theorem gC_FTC : forall a b (Ha : 0 < a) (Hab : a <= b),
  CgderivInt a b Ha Hab = Cminus (gC s b) (gC s a).
Proof.
  intros a b Ha Hab; unfold CgderivInt, Cminus.
  apply Ceq; cbn [Re Im]; [ apply Re_gC_FTC | apply Im_gC_FTC ].
Qed.

End FTC.

Print Assumptions gC_FTC.

(* ================================================================= *)
(*  END CFTC.v  —  the C-valued FTC for x^{-s}.                         *)
(* ================================================================= *)
