(* ================================================================= *)
(*  XiTwoSided.v  —  the two-sided literal functional equation.       *)
(*                                                                    *)
(*  Riemann's functional equation written with ζ at BOTH points:      *)
(*                                                                    *)
(*    π^{−s/2}·Γ(s/2)·ζ(s) = π^{−(1−s)/2}·Γ((1−s)/2)·ζ(1−s).           *)
(*                                                                    *)
(*  The left side uses the genuine ζ (zeta_cont, s>1); the right      *)
(*  side needs ζ at 1−s < 0, supplied by the continued zeta           *)
(*    ζ_ext(x) := J(x)·π^{x/2}/Γ_ext(x/2),                             *)
(*  which agrees with the series-defined ζ on (1,∞) (zeta_ext_agree)  *)
(*  and uses GammaExtend's Γ_ext (GamH) at the reflected argument.    *)
(*  The completed ξ(x):=π^{−x/2}·Γ_ext(x/2)·ζ_ext(x) equals J(x)        *)
(*  wherever Γ_ext(x/2)≠0, and J is symmetric — so ξ(s)=ξ(1−s).        *)
(*  Both sides are meromorphic; the identity holds away from the      *)
(*  Γ-poles / ζ-trivial-zeros (x/2 ∉ {0,−1,−2,…}).                    *)
(*  No new axioms (classical Reals only).                            *)
(* ================================================================= *)

From Stdlib Require Import Reals Rpower Lra Lia.
Require Import GammaReal GammaExtend MellinTail RiemannThetaFE ZetaCompleted
        XiReflection Ell2ZetaCont.
Open Scope R_scope.

(* --- a total Γ_ext (GamH) via GammaExtend, at a canonical level --- *)

Definition lvl (a : R) : nat := S (proj1_sig (nat_gt (- a))).

Lemma lvl_pos : forall a, 0 < a + INR (lvl a).
Proof. intro a; unfold lvl; destruct (nat_gt (- a)) as [n Hn]; simpl proj1_sig; lra. Qed.

Definition GamH (a : R) : R := GamN a (lvl a) (lvl_pos a).

Lemma GamH_eq_pos : forall a (Ha : 0 < a), GamH a = Gam a Ha.
Proof. intros a Ha; unfold GamH; apply (GamN_pos (lvl a) a Ha). Qed.

(* --- avoiding the poles: a is not a nonpositive integer --- *)

Definition not_nonpos_int (a : R) : Prop := forall n : nat, a <> - INR n.

Lemma prodshift_ne0 : forall a N, not_nonpos_int a -> prodshift a N <> 0.
Proof.
  intros a N Hnn; induction N.
  - simpl; apply R1_neq_R0.
  - cbn [prodshift]; apply Rmult_integral_contrapositive_currified.
    + intro Hc; apply (Hnn N); lra.
    + exact IHN.
Qed.

Lemma GamH_ne0 : forall a, not_nonpos_int a -> GamH a <> 0.
Proof.
  intros a Hnn; unfold GamH, GamN, Rdiv.
  apply Rmult_integral_contrapositive_currified.
  - apply Rgt_not_eq; apply Gam_pos.
  - apply Rinv_neq_0_compat; apply prodshift_ne0; exact Hnn.
Qed.

(* --- the continued zeta and the completed ξ --- *)

Definition zeta_ext (x : R) : R := J x * Rpower PI (x / 2) / GamH (x / 2).

Definition Xic (x : R) : R := Rpower PI (- (x / 2)) * GamH (x / 2) * zeta_ext x.

(* ξ(x) = J(x) wherever Γ_ext(x/2) ≠ 0 *)
Lemma Xic_eq_J : forall x, not_nonpos_int (x / 2) -> Xic x = J x.
Proof.
  intros x Hnn; unfold Xic, zeta_ext; rewrite (Rpower_Ropp PI (x / 2)).
  field; split;
    [ apply GamH_ne0; exact Hnn | apply Rgt_not_eq; unfold Rpower; apply exp_pos ].
Qed.

(* the continued zeta agrees with the genuine ζ on (1,∞) *)
Lemma zeta_ext_agree : forall s (Hs0 : 0 < s) (Hs1 : s <> 1) (Hs2 : 0 < s / 2), 1 < s ->
  zeta_ext s = zeta_cont s Hs0 Hs1.
Proof.
  intros s Hs0 Hs1 Hs2 Hs.
  rewrite (zeta_solved s Hs0 Hs1 Hs2 Hs); unfold zeta_ext.
  rewrite (GamH_eq_pos (s / 2) Hs2); reflexivity.
Qed.

(* the completed ξ is symmetric: ξ(s) = ξ(1−s) *)
Theorem Xic_symmetric : forall s,
  not_nonpos_int (s / 2) -> not_nonpos_int ((1 - s) / 2) -> s <> 0 -> s <> 1 ->
  Xic s = Xic (1 - s).
Proof.
  intros s Hns Hnr Hs0 Hs1.
  rewrite (Xic_eq_J s Hns), (Xic_eq_J (1 - s) Hnr); apply J_symmetric; assumption.
Qed.

(* ---- the two-sided literal functional equation ----
   left: genuine ζ (s>1); right: continued ζ_ext at 1−s<0. *)
Theorem two_sided_reflection : forall s (Hs0 : 0 < s) (Hs1 : s <> 1) (Hs2 : 0 < s / 2),
  1 < s -> not_nonpos_int ((1 - s) / 2) ->
  Rpower PI (- (s / 2)) * Gam (s / 2) Hs2 * zeta_cont s Hs0 Hs1
  = Rpower PI (- ((1 - s) / 2)) * GamH ((1 - s) / 2) * zeta_ext (1 - s).
Proof.
  intros s Hs0 Hs1 Hs2 Hs Hnr.
  rewrite (zeta_completed_eq_J s Hs0 Hs1 Hs2 Hs), (J_symmetric s ltac:(lra) ltac:(lra)).
  change (Rpower PI (- ((1 - s) / 2)) * GamH ((1 - s) / 2) * zeta_ext (1 - s))
    with (Xic (1 - s)).
  symmetry; apply (Xic_eq_J (1 - s) Hnr).
Qed.

Print Assumptions two_sided_reflection.
Print Assumptions Xic_symmetric.

(* ================================================================= *)
(*  END XiTwoSided.v.                                                 *)
(*  π^{−s/2}Γ(s/2)ζ(s) = π^{−(1−s)/2}Γ((1−s)/2)ζ(1−s), and ξ(s)=ξ(1−s).*)
(* ================================================================= *)
