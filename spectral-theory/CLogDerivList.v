(* ================================================================= *)
(*  CLogDerivList.v  --  the log-derivative of a list product.        *)
(*                                                                    *)
(*  For F = prodfac l . G, away from the points of l and off the       *)
(*  zeros of G,                                                        *)
(*                                                                    *)
(*      F'/F  =  sum_{w in l} 1/(z-w)  +  G'/G.                        *)
(*                                                                    *)
(*  This is the pointwise half of the argument principle.  Note the    *)
(*  list l is allowed to REPEAT: a zero of multiplicity m appears m    *)
(*  times, and the sum then carries m/(z-w).  That is what lets the    *)
(*  whole development dodge the order-of-vanishing brick               *)
(*  f = (z-a)^m . g, which does not exist in this repository -- the    *)
(*  caller supplies multiplicity by repetition, exactly as             *)
(*  CZeroListFactor.DivBy_cons and XiZeroDensity.xi_count_peel do.     *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia List FunctionalExtensionality.
Require Import ComplexField Cmodulus Holomorphic CDeriv CDerivUnique
        CHoloCalculus CZetaDeriv2 JensenMultiZero.
Import ListNotations.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  The sum of simple poles attached to a list.                        *)
(* ----------------------------------------------------------------- *)

Fixpoint lsum (l : list C) (z : C) : C :=
  match l with
  | nil => C0
  | w :: l' => Cadd (Cinv (Cminus z w)) (lsum l' z)
  end.

Lemma prodfac_ne0 : forall (l : list C) (z : C),
  (forall w, In w l -> z <> w) -> prodfac l z <> C0.
Proof.
  induction l as [ | w l' IH ]; intros z Hne; simpl.
  - intro Hc; apply (f_equal Re) in Hc; cbn in Hc; lra.
  - apply Cmul_ne0.
    + intro Hc.
      assert (Hz : z = w)
        by (replace z with (Cadd (Cminus z w) w) by ring; rewrite Hc; ring).
      apply (Hne w (or_introl eq_refl)); exact Hz.
    + apply IH; intros v Hv; apply Hne; right; exact Hv.
Qed.

(* ----------------------------------------------------------------- *)
(*  The product rule, in log-derivative form, along the list.          *)
(* ----------------------------------------------------------------- *)

Lemma mul_logderiv : forall f g z a b,
  is_Cderiv f z (Cmul a (f z)) -> is_Cderiv g z (Cmul b (g z)) ->
  is_Cderiv (fun w => Cmul (f w) (g w)) z (Cmul (Cadd a b) (Cmul (f z) (g z))).
Proof.
  intros f g z a b Hf Hg.
  apply (is_Cderiv_eq _ _ (Cadd (Cmul (Cmul a (f z)) (g z))
                                (Cmul (f z) (Cmul b (g z)))));
    [ apply Cderiv_mul; assumption | ring ].
Qed.

Lemma prodfac_logderiv : forall (l : list C) (z : C),
  (forall w, In w l -> z <> w) ->
  is_Cderiv (prodfac l) z (Cmul (lsum l z) (prodfac l z)).
Proof.
  induction l as [ | w l' IH ]; intros z Hne.
  - simpl; apply (is_Cderiv_eq (fun _ : C => C1) z C0);
      [ apply Cderiv_const | ring ].
  - assert (Hw : Cminus z w <> C0).
    { intro Hc.
      assert (Hz : z = w)
        by (replace z with (Cadd (Cminus z w) w) by ring; rewrite Hc; ring).
      apply (Hne w (or_introl eq_refl)); exact Hz. }
    assert (Htl : forall v, In v l' -> z <> v)
      by (intros v Hv; apply Hne; right; exact Hv).
    assert (Hlin : is_Cderiv (fun u => Cminus u w) z
                     (Cmul (Cinv (Cminus z w)) (Cminus z w))).
    { apply (is_Cderiv_eq _ _ (Cminus C1 C0));
        [ apply Cderiv_minus; [ apply Cderiv_id | apply Cderiv_const ]
        | field; exact Hw ]. }
    apply (is_Cderiv_eq _ _
             (Cmul (Cadd (Cinv (Cminus z w)) (lsum l' z))
                   (Cmul (Cminus z w) (prodfac l' z))));
      [ apply (mul_logderiv (fun u => Cminus u w) (prodfac l') z
                 (Cinv (Cminus z w)) (lsum l' z));
          [ exact Hlin | apply IH; exact Htl ]
      | simpl; reflexivity ].
Qed.

(* ----------------------------------------------------------------- *)
(*  The split.                                                         *)
(* ----------------------------------------------------------------- *)

Theorem prodG_logderiv : forall (G : C -> C) (l : list C) (z dG : C),
  (forall w, In w l -> z <> w) -> G z <> C0 -> is_Cderiv G z dG ->
  is_Cderiv (fun u => Cmul (prodfac l u) (G u)) z
    (Cmul (Cadd (lsum l z) (Cmul dG (Cinv (G z)))) (Cmul (prodfac l z) (G z))).
Proof.
  intros G l z dG Hne HG HdG.
  apply mul_logderiv; [ apply prodfac_logderiv; exact Hne | ].
  apply (is_Cderiv_eq _ _ dG); [ exact HdG | field; exact HG ].
Qed.

Theorem logderiv_split : forall (F G : C -> C) (l : list C) (z dF dG : C),
  (forall u, F u = Cmul (prodfac l u) (G u)) ->
  (forall w, In w l -> z <> w) -> G z <> C0 ->
  is_Cderiv F z dF -> is_Cderiv G z dG ->
  Cmul dF (Cinv (F z)) = Cadd (lsum l z) (Cmul dG (Cinv (G z))).
Proof.
  intros F G l z dF dG Heq Hne HG HdF HdG.
  assert (Hpf : prodfac l z <> C0) by (apply prodfac_ne0; exact Hne).
  assert (HFz : F z <> C0) by (rewrite Heq; apply Cmul_ne0; assumption).
  assert (HdF2 : is_Cderiv F z
    (Cmul (Cadd (lsum l z) (Cmul dG (Cinv (G z)))) (Cmul (prodfac l z) (G z)))).
  { apply (is_Cderiv_ext (fun u => Cmul (prodfac l u) (G u)));
      [ intro u; symmetry; apply Heq
      | apply prodG_logderiv; assumption ]. }
  assert (Huniq := is_Cderiv_unique F z _ _ HdF HdF2).
  rewrite Huniq, Heq; field.
  split; assumption.
Qed.

Print Assumptions prodfac_logderiv.
Print Assumptions logderiv_split.

(* ================================================================= *)
(*  END CLogDerivList.v -- F'/F = sum 1/(z-w) + G'/G, multiplicity     *)
(*  carried by repetition in l.                                        *)
(* ================================================================= *)
