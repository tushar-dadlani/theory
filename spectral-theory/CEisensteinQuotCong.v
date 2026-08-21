(* ================================================================= *)
(*  CEisensteinQuotCong.v  —  equality in  Z[om][zeta_p] / theta.     *)
(*                                                                    *)
(*    cconst c   : the constant element of the group ring              *)
(*    qceq d f g : f = g modulo the ideal (N, d)                       *)
(*    qceq_iff   : ... equivalently, f - g is a constant plus a        *)
(*                 multiple of d                                       *)
(*    qceq_cemb  : on scalars it is just divisibility of the           *)
(*                 difference by d                                     *)
(*    cemb_mul, cemb_pow, cpow_mul : the algebra the endgame needs     *)
(*                                                                    *)
(*  THE ENDGAME NEEDS BOTH QUOTIENTS AT ONCE.  ceq (E3) works modulo   *)
(*  the ideal (N), which is what turns the group ring into            *)
(*  Z[om][zeta_p]; ccong (E5b) works modulo a coefficient, which is    *)
(*  what the Frobenius produces.  Relation (A) is obtained by putting  *)
(*  a ceq fact and a ccong fact side by side, so it lives in the       *)
(*  common refinement: equality modulo (N, theta).  qceq is that.      *)
(*                                                                    *)
(*  STATED IN Pi-FORM for the same reason as ceq: the difference of    *)
(*  differences is divisible by d.  The exists-form is available       *)
(*  through qceq_iff and is used only where a witness is genuinely     *)
(*  wanted -- in the multiplication congruence, where the constant     *)
(*  gets multiplied by the sum of the other factor's coefficients.     *)
(*  There it is extracted at a single index, so no choice is needed.   *)
(*                                                                    *)
(*  qceq_cemb IS WHAT MAKES THE SCAFFOLDING DISAPPEAR.  Two scalars    *)
(*  are congruent in the quotient exactly when their difference is     *)
(*  divisible by d in Z[om] -- because cemb a - cemb b is the constant *)
(*  a - b at index 0 and zero elsewhere, so being constant modulo d    *)
(*  forces d | a - b.  That is the step where the group ring is        *)
(*  discharged and the argument returns to Z[om].                      *)
(*  Axiom-free.                                                        *)
(* ================================================================= *)

From Stdlib Require Import ZArith Znumtheory Arith Lia List Permutation
        Setoid Ring Ring_theory RelationClasses Morphisms.
Require Import ZmodPStar CEisenstein CEisensteinUnits CEisensteinDiv
        CEisensteinGcd CEisensteinSplit CEisensteinUFD CEisensteinResidue
        CEisensteinFermat CEisensteinSum CEisensteinJacobi CEisensteinNormJ
        CycIndex CEisensteinCyc CEisensteinCycQuot CEisensteinBinomial
        CEisensteinFrobenius.
Import ListNotations.
Open Scope Z_scope.

Section QuotCong.

Variable p : nat.
Hypothesis Hp1 : (1 <= p)%nat.

Instance cyc_equiv3 : Equivalence (beq p).
Proof.
  constructor; [ exact (beq_refl p) | exact (beq_sym p) | exact (beq_trans p) ].
Defined.
Instance cadd_Proper3 : Proper (beq p ==> beq p ==> beq p) cadd.
Proof. intros x x' Hx y y' Hy. apply beq_cadd; assumption. Qed.
Instance cmul_Proper3 : Proper (beq p ==> beq p ==> beq p) (cmul p).
Proof. intros x x' Hx y y' Hy. apply beq_cmul; assumption. Qed.
Instance copp_Proper3 : Proper (beq p ==> beq p) copp.
Proof. intros x x' Hx. apply beq_copp; assumption. Qed.
Add Ring CycR3 : (cyc_ring p Hp1) (setoid cyc_equiv3 (cyc_ext p Hp1)).

(* ----------------------------------------------------------------- *)
(*  A.  algebra of the scalar embedding                                *)
(* ----------------------------------------------------------------- *)
Lemma cemb_mul : forall a b,
  beq p (cemb p (emul a b)) (cmul p (cemb p a) (cemb p b)).
Proof.
  intros a b.
  apply (beq_trans p _ (cscale a (cemb p b))).
  - intros u _. unfold cemb, cscale. ring.
  - apply cscale_cmul; exact Hp1.
Qed.

Lemma cemb_pow : forall a k,
  beq p (cemb p (epow a k)) (cpow p (cemb p a) k).
Proof.
  intros a k. induction k as [| k IH].
  - cbn [epow cpow]. intros u _. unfold cemb, cscale. ring.
  - replace (cpow p (cemb p a) (S k))
      with (cmul p (cemb p a) (cpow p (cemb p a) k)) by reflexivity.
    replace (epow a (S k)) with (emul a (epow a k)) by reflexivity.
    apply (beq_trans p _ (cmul p (cemb p a) (cemb p (epow a k))));
      [ apply cemb_mul | ].
    exact (beq_cmul p Hp1 _ _ _ _ (beq_refl p _) IH).
Qed.

Lemma cpow_add : forall f m k,
  beq p (cpow p f (m + k)%nat) (cmul p (cpow p f m) (cpow p f k)).
Proof.
  intros f m k. induction m as [| m IH].
  - cbn [cpow Nat.add]. apply beq_sym, cmul_1_l; exact Hp1.
  - replace ((S m) + k)%nat with (S (m + k)) by lia.
    replace (cpow p f (S (m + k))) with (cmul p f (cpow p f (m + k))) by reflexivity.
    replace (cpow p f (S m)) with (cmul p f (cpow p f m)) by reflexivity.
    apply (beq_trans p _ (cmul p f (cmul p (cpow p f m) (cpow p f k))));
      [ exact (beq_cmul p Hp1 _ _ _ _ (beq_refl p _) IH) | ].
    ring.
Qed.

Lemma cpow_mul : forall f m k,
  beq p (cpow p f (m * k)%nat) (cpow p (cpow p f m) k).
Proof.
  intros f m k. induction k as [| k IH].
  - rewrite Nat.mul_0_r. apply beq_refl.
  - replace (m * S k)%nat with (m + m * k)%nat by lia.
    replace (cpow p (cpow p f m) (S k))
      with (cmul p (cpow p f m) (cpow p (cpow p f m) k)) by reflexivity.
    apply (beq_trans p _ (cmul p (cpow p f m) (cpow p f (m * k))));
      [ apply cpow_add | ].
    exact (beq_cmul p Hp1 _ _ _ _ (beq_refl p _) IH).
Qed.

(* ----------------------------------------------------------------- *)
(*  B.  the combined congruence                                        *)
(* ----------------------------------------------------------------- *)
Definition cconst (c : Eis) : Cyc := fun _ => c.

Definition qceq (d : Eis) (f g : Cyc) : Prop :=
  forall u v, (u < p)%nat -> (v < p)%nat ->
    edvd d (esub (esub (f u) (g u)) (esub (f v) (g v))).

Lemma qceq_refl : forall d f, qceq d f f.
Proof. intros d f u v _ _. exists ezero. ring. Qed.

Lemma qceq_sym : forall d f g, qceq d f g -> qceq d g f.
Proof.
  intros d f g H u v Hu Hv. destruct (H u v Hu Hv) as [c Hc].
  exists (eopp c).
  assert (E : esub (esub (g u) (f u)) (esub (g v) (f v))
              = eopp (esub (esub (f u) (g u)) (esub (f v) (g v)))) by ring.
  rewrite E, Hc. ring.
Qed.

Lemma qceq_trans : forall d f g h, qceq d f g -> qceq d g h -> qceq d f h.
Proof.
  intros d f g h H1 H2 u v Hu Hv.
  destruct (H1 u v Hu Hv) as [c Hc]. destruct (H2 u v Hu Hv) as [e He].
  exists (eadd c e).
  assert (E : esub (esub (f u) (h u)) (esub (f v) (h v))
              = eadd (esub (esub (f u) (g u)) (esub (f v) (g v)))
                     (esub (esub (g u) (h u)) (esub (g v) (h v)))) by ring.
  rewrite E, Hc, He. ring.
Qed.

Lemma qceq_of_beq : forall d f g, beq p f g -> qceq d f g.
Proof.
  intros d f g H u v Hu Hv. rewrite (H u Hu), (H v Hv). exists ezero. ring.
Qed.

Lemma qceq_of_ceq : forall d f g, ceq p f g -> qceq d f g.
Proof.
  intros d f g H u v Hu Hv. rewrite (H u v Hu Hv). exists ezero. ring.
Qed.

Lemma qceq_of_ccong : forall d f g, ccong p d f g -> qceq d f g.
Proof.
  intros d f g H u v Hu Hv.
  destruct (H u Hu) as [c Hc]. destruct (H v Hv) as [e He].
  exists (esub c e). rewrite Hc, He. ring.
Qed.

(* the exists-form, used where a witness is genuinely wanted *)
Lemma qceq_iff : forall d f g,
  qceq d f g <-> exists c, forall u, (u < p)%nat -> edvd d (esub (f u) (eadd (g u) c)).
Proof.
  intros d f g. split.
  - intro H. exists (esub (f 0%nat) (g 0%nat)). intros u Hu.
    destruct (H u 0%nat Hu ltac:(lia)) as [c Hc]. exists c.
    rewrite <- Hc. ring.
  - intros [c Hc] u v Hu Hv.
    destruct (Hc u Hu) as [x Hx]. destruct (Hc v Hv) as [y Hy].
    exists (esub x y).
    assert (E : esub (esub (f u) (g u)) (esub (f v) (g v))
                = esub (esub (f u) (eadd (g u) c)) (esub (f v) (eadd (g v) c)))
      by ring.
    rewrite E, Hx, Hy. ring.
Qed.

Lemma qceq_cadd : forall d f f' g g', qceq d f f' -> qceq d g g' ->
  qceq d (cadd f g) (cadd f' g').
Proof.
  intros d f f' g g' H1 H2 u v Hu Hv.
  destruct (H1 u v Hu Hv) as [c Hc]. destruct (H2 u v Hu Hv) as [e He].
  exists (eadd c e). unfold cadd.
  assert (E : esub (esub (eadd (f u) (g u)) (eadd (f' u) (g' u)))
                   (esub (eadd (f v) (g v)) (eadd (f' v) (g' v)))
              = eadd (esub (esub (f u) (f' u)) (esub (f v) (f' v)))
                     (esub (esub (g u) (g' u)) (esub (g v) (g' v)))) by ring.
  rewrite E, Hc, He. ring.
Qed.

Lemma qceq_cmul_r : forall d f g g', qceq d g g' ->
  qceq d (cmul p f g) (cmul p f g').
Proof.
  intros d f g g' H.
  destruct (proj1 (qceq_iff d g g') H) as [c Hc].
  apply (proj2 (qceq_iff d (cmul p f g) (cmul p f g'))).
  exists (emul (Esum f (seq 0 p)) c). intros n _.
  unfold cmul, cadd.
  assert (E : Esum (fun i => emul (f i)
                      (esub (g (msub p n i)) (eadd (g' (msub p n i)) c)))
                   (seq 0 p)
              = esub (Esum (fun i => emul (f i) (g (msub p n i))) (seq 0 p))
                     (eadd (Esum (fun i => emul (f i) (g' (msub p n i))) (seq 0 p))
                           (emul (Esum f (seq 0 p)) c))).
  { rewrite <- Esum_scale_r, <- Esum_add, <- Esum_sub.
    apply Esum_ext. intros i _. ring. }
  rewrite <- E. apply Esum_dvd. intros i _.
  destruct (Hc (msub p n i) ltac:(apply msub_lt; exact Hp1)) as [x Hx].
  exists (emul (f i) x). rewrite Hx. ring.
Qed.

Lemma qceq_cmul_l : forall d f f' g, qceq d f f' ->
  qceq d (cmul p f g) (cmul p f' g).
Proof.
  intros d f f' g H.
  apply (qceq_trans _ _ (cmul p g f)); [ apply qceq_of_beq, cmul_comm; exact Hp1 | ].
  apply (qceq_trans _ _ (cmul p g f')); [ apply qceq_cmul_r; exact H | ].
  apply qceq_of_beq, cmul_comm; exact Hp1.
Qed.

Lemma qceq_cmul : forall d f f' g g', qceq d f f' -> qceq d g g' ->
  qceq d (cmul p f g) (cmul p f' g').
Proof.
  intros d f f' g g' H1 H2.
  apply (qceq_trans _ _ (cmul p f' g)); [ apply qceq_cmul_l; exact H1 | ].
  apply qceq_cmul_r; exact H2.
Qed.

Lemma qceq_cpow : forall d f f' k, qceq d f f' ->
  qceq d (cpow p f k) (cpow p f' k).
Proof.
  intros d f f' k H. induction k as [| k IH]; cbn [cpow].
  - apply qceq_refl.
  - apply qceq_cmul; assumption.
Qed.

(* ----------------------------------------------------------------- *)
(*  C.  scalars: the group ring discharges                             *)
(* ----------------------------------------------------------------- *)
Theorem qceq_cemb : (2 <= p)%nat -> forall d a b,
  qceq d (cemb p a) (cemb p b) -> edvd d (esub a b).
Proof.
  intros Hp2 d a b H.
  destruct (H 0%nat 1%nat ltac:(lia) ltac:(lia)) as [c Hc].
  exists c. rewrite <- Hc. unfold cemb, cscale, cone.
  rewrite (cdelta_hit p 0), (cdelta_miss p Hp1 0 1 ltac:(lia) ltac:(lia) ltac:(lia)).
  ring.
Qed.

End QuotCong.

Print Assumptions cpow_mul.
Print Assumptions qceq_iff.
Print Assumptions qceq_cmul.
Print Assumptions qceq_cemb.
