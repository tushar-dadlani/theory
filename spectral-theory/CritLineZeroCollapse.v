(* ================================================================= *)
(*  CritLineZeroCollapse.v  —  the conditional-existence capstone.       *)
(*                                                                    *)
(*  Ties together, on the critical line s = 1/2 + i t, the four proven     *)
(*  pillars of this development into ONE statement:                        *)
(*                                                                    *)
(*   (i)   xi is real on the line and continuous  (xir t = Re XiC(1/2+it), *)
(*         CoherenceSingularity / ZeroCounting.xir_continuity_pt);         *)
(*   (ii)  the IVT hook  ZeroCounting.sign_change_zero_up/_down:  a sign    *)
(*         change of xir forces a genuine zero XiC(1/2+it) = 0 strictly     *)
(*         inside;                                                         *)
(*   (iii) the strip equivalence  GammaCNe0.XiC_zero_iff_zetaC_zero_final:  *)
(*         on 0 < Re < 1 that xi-zero IS a zetaC zero;                      *)
(*   (iv)  the complex collapse  EtaZetaStripC.crit_line_zero_iff_collapse: *)
(*         a zetaC zero on the line IS the complex alternating sum          *)
(*         sum (-1)^i (i+1)^{-(1/2+it)} collapsing to 0 at infinity.        *)
(*                                                                    *)
(*   crit_sign_change_gives_zero_collapse :  IF xir changes sign on [a,b]   *)
(*     (xir a . xir b < 0) THEN there is a t in (a,b) with                  *)
(*        XiC(1/2+it) = 0,  zetaC(1/2+it) = 0,  and the complex alternating *)
(*        sum COLLAPSING to 0 at infinity -- one honest object.            *)
(*   crit_sign_change_gives_mirror_collapse : the functional equation       *)
(*     (XiC_symmetric / XiC_zero_reflect) hands the mirror zero at 1/2 - it *)
(*     for free -- it collapses too.                                       *)
(*                                                                    *)
(*  HONEST HORIZON.  This is CONDITIONAL.  The single remaining input is a  *)
(*  PROVEN sign change  xir a . xir b < 0  at two concrete t (bracketing    *)
(*  the first zero t ~ 14.13).  Establishing it needs rigorous interval     *)
(*  arithmetic on the theta-tail TC(1/2+it) -- infrastructure this repo     *)
(*  does NOT have.  So NO nontrivial zero is exhibited unconditionally      *)
(*  here; existence is reduced to that one crisp numeric fact.  And RH --   *)
(*  that EVERY nontrivial zero lies on the line -- is untouched and stays   *)
(*  open (only ONE zero would follow from one sign change).                 *)
(*                                                                    *)
(*  Axioms: standard classical-Reals only.                            *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import ComplexField Cmodulus
        RiemannXiEntire CoherenceSingularity BerryKeatingDilation ZeroCounting
        CZeta CZetaStripId GammaCNe0 ZetaZeroPairing EtaZetaStripC.
Open Scope R_scope.

(* Re(1/2 + it) = 1/2 < 1: the crit line sits in the open strip. *)
Lemma crit_Re_lt1 : forall t, Re (crit t) < 1.
Proof. intro t. unfold crit; cbn [Re]; lra. Qed.

(* a product < 0 splits into the two opposite-sign cases *)
Lemma opp_signs : forall x y, x * y < 0 -> (x < 0 /\ 0 < y) \/ (0 < x /\ y < 0).
Proof.
  intros x y H. destruct (Rtotal_order x 0) as [Hx | [Hx | Hx]].
  - left; split; [ exact Hx | nra ].
  - subst x; rewrite Rmult_0_l in H; lra.
  - right; split; [ exact Hx | nra ].
Qed.

(* 1 - (1/2 + it) = 1/2 - it = crit(-t): the reflection lands back on the line *)
Lemma crit_reflect_eq : forall t, Cminus C1 (crit t) = crit (- t).
Proof. intro t. unfold crit, Cminus, C1; apply Ceq; cbn [Re Im]; lra. Qed.

(* ===== THE CONDITIONAL-EXISTENCE CAPSTONE ===== *)
(* A sign change of xir on [a,b] produces a t whose critical-line point is
   simultaneously a xi-zero, a zetaC-zero, and the complex alternating sum
   collapsing to 0 at infinity. *)
Theorem crit_sign_change_gives_zero_collapse :
  forall a b, a < b -> xir a * xir b < 0 ->
  exists t, a < t < b
         /\ XiC (crit t) = C0
         /\ zetaC (crit t) (crit_pos t) (crit_H1 t) = C0
         /\ ccollapses (ceta_partial (crit t)).
Proof.
  intros a b Hab Hopp.
  assert (Hz : exists t, a < t < b /\ spec Bxi t).
  { destruct (opp_signs _ _ Hopp) as [[Ha Hb] | [Ha Hb]].
    - exact (sign_change_zero_up a b Hab Ha Hb).
    - exact (sign_change_zero_down a b Hab Ha Hb). }
  destruct Hz as [t [Ht Hspec]].
  assert (HXi : XiC (crit t) = C0)
    by (apply (proj1 (spec_Bxi_zero t)); exact Hspec).
  assert (Hzeta : zetaC (crit t) (crit_pos t) (crit_H1 t) = C0).
  { apply (proj1 (XiC_zero_iff_zetaC_zero_final (crit t) (crit_pos t) (crit_H1 t)
                    (crit_Re_lt1 t))).
    exact HXi. }
  exists t. split; [ exact Ht | ]. split; [ exact HXi | ]. split; [ exact Hzeta | ].
  apply (proj2 (crit_line_zero_iff_collapse t (crit_pos t) (crit_H1 t))). exact Hzeta.
Qed.

(* ===== the functional-equation mirror collapses too ===== *)
(* XiC_symmetric / XiC_zero_reflect pairs the zero at 1/2 + it with its mirror
   at 1/2 - it = crit(-t); by the same chain that mirror is a collapse. *)
Corollary crit_sign_change_gives_mirror_collapse :
  forall a b, a < b -> xir a * xir b < 0 ->
  exists t, a < t < b
         /\ ccollapses (ceta_partial (crit t))
         /\ ccollapses (ceta_partial (crit (- t))).
Proof.
  intros a b Hab Hopp.
  destruct (crit_sign_change_gives_zero_collapse a b Hab Hopp)
    as [t [Ht [HXi [_ Hcol]]]].
  exists t. split; [ exact Ht | ]. split; [ exact Hcol | ].
  assert (HXim : XiC (crit (- t)) = C0)
    by (rewrite <- crit_reflect_eq; apply XiC_zero_reflect; exact HXi).
  assert (Hzm : zetaC (crit (- t)) (crit_pos (- t)) (crit_H1 (- t)) = C0).
  { apply (proj1 (XiC_zero_iff_zetaC_zero_final (crit (- t)) (crit_pos (- t))
                    (crit_H1 (- t)) (crit_Re_lt1 (- t)))).
    exact HXim. }
  apply (proj2 (crit_line_zero_iff_collapse (- t) (crit_pos (- t)) (crit_H1 (- t)))).
  exact Hzm.
Qed.

Print Assumptions crit_sign_change_gives_zero_collapse.
Print Assumptions crit_sign_change_gives_mirror_collapse.
