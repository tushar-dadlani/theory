(* ================================================================= *)
(*  CPathLift.v  --  a continuous argument along a path, WITHOUT a    *)
(*  complex logarithm.                                                *)
(*                                                                    *)
(*  CPolarPath.pathint_logderiv_phase takes the polar data (Lg, ph) as *)
(*  hypotheses.  This file shows the data is not an extra assumption:  *)
(*  any pair of real functions whose derivatives are the two           *)
(*  components of the log-derivative along the path, and which match   *)
(*  F at the STARTING POINT, automatically satisfies                   *)
(*                                                                    *)
(*      F (gam u) = exp (Lg u) . (cos (ph u), sin (ph u))              *)
(*                                                                    *)
(*  for every u in [a,b].  So exactly one branch choice is made, at    *)
(*  u = a, and everything after it is forced.  That is the honest      *)
(*  content of a continuous argument, and it needs no Clog/Carg.       *)
(*                                                                    *)
(*  Method: the two error functions                                    *)
(*      Br = (P cos ph + Qi sin ph) e^{-Lg} - 1                        *)
(*      Bi = (Qi cos ph - P sin ph) e^{-Lg}                            *)
(*  have IDENTICALLY ZERO derivative -- the e^{-Lg} factor is what     *)
(*  makes this exact rather than merely a linear ODE, since without it *)
(*  one only gets S' = q1 S -- so null_derivative_loc pins them at     *)
(*  their value at a, namely 0.  Rotating back recovers P and Qi.      *)
(* ================================================================= *)

From Stdlib Require Import Reals Ranalysis Lra Lia FunctionalExtensionality.
Require Import ComplexField Cmodulus Holomorphic CIntegral2 CSegInt
        CPathIntegral CPathFTC ContinuousCoV.
Open Scope R_scope.

Lemma dpl_eq : forall f x l l',
  derivable_pt_lim f x l -> l = l' -> derivable_pt_lim f x l'.
Proof. intros f x l l' H E; rewrite <- E; exact H. Qed.

Section Lift.

Variables (F Fd : C -> C) (gam gam' : R -> C) (Lg ph : R -> R) (a b : R).

Hypothesis Hab : a <= b.
Hypothesis HgR : forall u, derivable_pt_lim (fun s => Re (gam s)) u (Re (gam' u)).
Hypothesis HgI : forall u, derivable_pt_lim (fun s => Im (gam s)) u (Im (gam' u)).
Hypothesis HF  : forall u, is_Cderiv F (gam u) (Fd (gam u)).
Hypothesis Hne : forall u, F (gam u) <> C0.

Let Qlog (u : R) : C := Cmul (Cmul (Fd (gam u)) (Cinv (F (gam u)))) (gam' u).
Let q1 (u : R) : R := Re (Qlog u).
Let q2 (u : R) : R := Im (Qlog u).
Let P (u : R) : R := Re (F (gam u)).
Let Qi (u : R) : R := Im (F (gam u)).

Hypothesis HLd : forall u, derivable_pt_lim Lg u (q1 u).
Hypothesis Hpd : forall u, derivable_pt_lim ph u (q2 u).
Hypothesis HstartR : P a = exp (Lg a) * cos (ph a).
Hypothesis HstartI : Qi a = exp (Lg a) * sin (ph a).

(* ---- the path derivatives of the two components ---- *)

Lemma logderiv_recover : forall u,
  Cmul (Fd (gam u)) (gam' u) = Cmul (Qlog u) (F (gam u)).
Proof. intro u; unfold Qlog; field; apply Hne. Qed.

Lemma HP : forall u, derivable_pt_lim P u (q1 u * P u - q2 u * Qi u).
Proof.
  intro u.
  assert (Hd := Cderiv_path_Re F gam gam' u (Fd (gam u)) (HF u) (HgR u) (HgI u)).
  assert (Heq : Re (Cmul (Fd (gam u)) (gam' u)) = q1 u * P u - q2 u * Qi u)
    by (rewrite logderiv_recover; unfold q1, q2, P, Qi;
        cbn [Re Im Cmul]; ring).
  rewrite <- Heq; exact Hd.
Qed.

Lemma HQi : forall u, derivable_pt_lim Qi u (q1 u * Qi u + q2 u * P u).
Proof.
  intro u.
  assert (Hd := Cderiv_path_Im F gam gam' u (Fd (gam u)) (HF u) (HgR u) (HgI u)).
  assert (Heq : Im (Cmul (Fd (gam u)) (gam' u)) = q1 u * Qi u + q2 u * P u)
    by (rewrite logderiv_recover; unfold q1, q2, P, Qi;
        cbn [Re Im Cmul]; ring).
  rewrite <- Heq; exact Hd.
Qed.

(* ---- the two error functions have identically zero derivative ---- *)

Let Ee (u : R) : R := exp (- Lg u).
Let Br (u : R) : R := (P u * cos (ph u) + Qi u * sin (ph u)) * Ee u - 1.
Let Bi (u : R) : R := (Qi u * cos (ph u) - P u * sin (ph u)) * Ee u.

Lemma HEe : forall u, derivable_pt_lim Ee u (exp (- Lg u) * (- q1 u)).
Proof.
  intro u; unfold Ee.
  apply (derivable_pt_lim_comp (fun s => - Lg s) exp u (- q1 u) (exp (- Lg u)));
    [ apply derivable_pt_lim_opp; apply HLd | apply derivable_pt_lim_exp ].
Qed.

Lemma Hcosph : forall u,
  derivable_pt_lim (fun s => cos (ph s)) u (- sin (ph u) * q2 u).
Proof.
  intro u; apply (derivable_pt_lim_comp ph cos u (q2 u) (- sin (ph u)));
    [ apply Hpd | apply derivable_pt_lim_cos ].
Qed.

Lemma Hsinph : forall u,
  derivable_pt_lim (fun s => sin (ph s)) u (cos (ph u) * q2 u).
Proof.
  intro u; apply (derivable_pt_lim_comp ph sin u (q2 u) (cos (ph u)));
    [ apply Hpd | apply derivable_pt_lim_sin ].
Qed.

Lemma HS : forall u,
  derivable_pt_lim (fun s => P s * cos (ph s) + Qi s * sin (ph s)) u
    ((q1 u * P u - q2 u * Qi u) * cos (ph u) + P u * (- sin (ph u) * q2 u)
     + ((q1 u * Qi u + q2 u * P u) * sin (ph u) + Qi u * (cos (ph u) * q2 u))).
Proof.
  intro u.
  apply (derivable_pt_lim_plus (fun s => P s * cos (ph s))
           (fun s => Qi s * sin (ph s)) u
           ((q1 u * P u - q2 u * Qi u) * cos (ph u) + P u * (- sin (ph u) * q2 u))
           ((q1 u * Qi u + q2 u * P u) * sin (ph u) + Qi u * (cos (ph u) * q2 u))).
  - apply (derivable_pt_lim_mult P (fun s => cos (ph s)) u
             (q1 u * P u - q2 u * Qi u) (- sin (ph u) * q2 u));
      [ apply HP | apply Hcosph ].
  - apply (derivable_pt_lim_mult Qi (fun s => sin (ph s)) u
             (q1 u * Qi u + q2 u * P u) (cos (ph u) * q2 u));
      [ apply HQi | apply Hsinph ].
Qed.

Lemma HT : forall u,
  derivable_pt_lim (fun s => Qi s * cos (ph s) - P s * sin (ph s)) u
    ((q1 u * Qi u + q2 u * P u) * cos (ph u) + Qi u * (- sin (ph u) * q2 u)
     - ((q1 u * P u - q2 u * Qi u) * sin (ph u) + P u * (cos (ph u) * q2 u))).
Proof.
  intro u.
  apply (derivable_pt_lim_minus (fun s => Qi s * cos (ph s))
           (fun s => P s * sin (ph s)) u
           ((q1 u * Qi u + q2 u * P u) * cos (ph u) + Qi u * (- sin (ph u) * q2 u))
           ((q1 u * P u - q2 u * Qi u) * sin (ph u) + P u * (cos (ph u) * q2 u))).
  - apply (derivable_pt_lim_mult Qi (fun s => cos (ph s)) u
             (q1 u * Qi u + q2 u * P u) (- sin (ph u) * q2 u));
      [ apply HQi | apply Hcosph ].
  - apply (derivable_pt_lim_mult P (fun s => sin (ph s)) u
             (q1 u * P u - q2 u * Qi u) (cos (ph u) * q2 u));
      [ apply HP | apply Hsinph ].
Qed.

Lemma HBr : forall u, derivable_pt_lim Br u 0.
Proof.
  intro u; unfold Br; eapply dpl_eq.
  - apply (derivable_pt_lim_minus
             (fun s => (P s * cos (ph s) + Qi s * sin (ph s)) * Ee s)
             (fun _ => 1) u).
    + apply (derivable_pt_lim_mult
               (fun s => P s * cos (ph s) + Qi s * sin (ph s)) Ee u);
        [ apply HS | apply HEe ].
    + apply derivable_pt_lim_const.
  - unfold Ee; ring.
Qed.

Lemma HBi : forall u, derivable_pt_lim Bi u 0.
Proof.
  intro u; unfold Bi; eapply dpl_eq.
  - apply (derivable_pt_lim_mult
             (fun s => Qi s * cos (ph s) - P s * sin (ph s)) Ee u);
      [ apply HT | apply HEe ].
  - unfold Ee; ring.
Qed.

(* ---- zero derivative on [a,b] pins both error functions at 0 ---- *)

Lemma exp_cancel : forall x, exp x * exp (- x) = 1.
Proof.
  intro x; rewrite <- exp_plus.
  replace (x + - x) with 0 by ring; apply exp_0.
Qed.

Lemma Br_const : forall u, a <= u <= b -> Br u = Br a.
Proof.
  intros u Hu.
  pose (pr := fun (x : R) (_ : a < x < b) =>
                exist (fun l => derivable_pt_lim Br x l) 0 (HBr x)).
  assert (Hcont : forall x, a <= x <= b -> continuity_pt Br x)
    by (intros x _; apply derivable_continuous_pt;
        exists 0; apply HBr).
  assert (Hd : forall (x : R) (Pf : a < x < b), derive_pt Br x (pr x Pf) = 0)
    by (intros x Pf; unfold pr, derive_pt; cbn [proj1_sig]; reflexivity).
  exact (null_derivative_loc Br a b pr Hcont Hd u Hu).
Qed.

Lemma Bi_const : forall u, a <= u <= b -> Bi u = Bi a.
Proof.
  intros u Hu.
  pose (pr := fun (x : R) (_ : a < x < b) =>
                exist (fun l => derivable_pt_lim Bi x l) 0 (HBi x)).
  assert (Hcont : forall x, a <= x <= b -> continuity_pt Bi x)
    by (intros x _; apply derivable_continuous_pt;
        exists 0; apply HBi).
  assert (Hd : forall (x : R) (Pf : a < x < b), derive_pt Bi x (pr x Pf) = 0)
    by (intros x Pf; unfold pr, derive_pt; cbn [proj1_sig]; reflexivity).
  exact (null_derivative_loc Bi a b pr Hcont Hd u Hu).
Qed.

Lemma Br_a : Br a = 0.
Proof.
  unfold Br, Ee; rewrite HstartR, HstartI.
  assert (Hsc : cos (ph a) * cos (ph a) + sin (ph a) * sin (ph a) = 1)
    by (pose proof (sin2_cos2 (ph a)); unfold Rsqr in *; lra).
  replace (exp (Lg a) * cos (ph a) * cos (ph a)
           + exp (Lg a) * sin (ph a) * sin (ph a))
    with (exp (Lg a) * (cos (ph a) * cos (ph a) + sin (ph a) * sin (ph a)))
    by ring.
  rewrite Hsc, Rmult_1_r, exp_cancel; ring.
Qed.

Lemma Bi_a : Bi a = 0.
Proof. unfold Bi, Ee; rewrite HstartR, HstartI; ring. Qed.

(* ================================================================= *)
(*  THE LIFT.                                                         *)
(* ================================================================= *)

Theorem path_polar_lift : forall u, a <= u <= b ->
  Re (F (gam u)) = exp (Lg u) * cos (ph u)
  /\ Im (F (gam u)) = exp (Lg u) * sin (ph u).
Proof.
  intros u Hu.
  assert (Hne0 : exp (- Lg u) <> 0) by (apply Rgt_not_eq; apply exp_pos).
  assert (Hsc : cos (ph u) * cos (ph u) + sin (ph u) * sin (ph u) = 1)
    by (pose proof (sin2_cos2 (ph u)); unfold Rsqr in *; lra).
  assert (E1 : (P u * cos (ph u) + Qi u * sin (ph u)) * exp (- Lg u) = 1).
  { pose proof (Br_const u Hu) as H; rewrite Br_a in H; unfold Br, Ee in H; lra. }
  assert (E2 : (Qi u * cos (ph u) - P u * sin (ph u)) * exp (- Lg u) = 0).
  { pose proof (Bi_const u Hu) as H; rewrite Bi_a in H; unfold Bi, Ee in H; lra. }
  assert (HS2 : P u * cos (ph u) + Qi u * sin (ph u) = exp (Lg u)).
  { apply (Rmult_eq_reg_r (exp (- Lg u))); [ | exact Hne0 ].
    rewrite E1, exp_cancel; reflexivity. }
  assert (HT2 : Qi u * cos (ph u) - P u * sin (ph u) = 0).
  { apply (Rmult_eq_reg_r (exp (- Lg u))); [ | exact Hne0 ].
    rewrite E2; ring. }
  split.
  - assert (Hx : P u * (cos (ph u) * cos (ph u) + sin (ph u) * sin (ph u))
               = (P u * cos (ph u) + Qi u * sin (ph u)) * cos (ph u)
                 - (Qi u * cos (ph u) - P u * sin (ph u)) * sin (ph u)) by ring.
    rewrite Hsc, Rmult_1_r, HS2, HT2 in Hx.
    change (P u = exp (Lg u) * cos (ph u)); rewrite Hx; ring.
  - assert (Hx : Qi u * (cos (ph u) * cos (ph u) + sin (ph u) * sin (ph u))
               = (P u * cos (ph u) + Qi u * sin (ph u)) * sin (ph u)
                 + (Qi u * cos (ph u) - P u * sin (ph u)) * cos (ph u)) by ring.
    rewrite Hsc, Rmult_1_r, HS2, HT2 in Hx.
    change (Qi u = exp (Lg u) * sin (ph u)); rewrite Hx; ring.
Qed.

End Lift.

Print Assumptions path_polar_lift.

(* ================================================================= *)
(*  END CPathLift.v -- one branch choice at the start point, and the   *)
(*  whole continuous argument is forced.                               *)
(* ================================================================= *)
