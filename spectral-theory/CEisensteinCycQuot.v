(* ================================================================= *)
(*  CEisensteinCycQuot.v  —  the quotient  Z[om][zeta_p].             *)
(*                                                                    *)
(*    cN            : 1 + x + ... + x^{p-1}, the all-ones element      *)
(*    ceq p f g     : equality modulo the ideal (cN)                   *)
(*    ceq_iff_ideal : ... and that really is the ideal                 *)
(*    ceq_coeff     : the extraction workhorse                         *)
(*    cone_ne_czero, czeta_primitive, cemb_inj : nondegeneracy         *)
(*    cyc_orthogonality : sum_k zeta^{km} = 0 for p not dividing m     *)
(*                                                                    *)
(*  THE QUOTIENT IS BY THE CONSTANTS, and that is the whole trick.     *)
(*  In Z[om][x]/(x^p - 1) the element N = 1 + x + ... + x^{p-1}        *)
(*  satisfies x.N = N, so the ideal it generates is exactly            *)
(*  { c.N : c in Eis } -- the constant functions.  Quotienting by it   *)
(*  gives Z[om][x]/(Phi_p) = Z[om][zeta_p], with no polynomial         *)
(*  division anywhere.                                                 *)
(*                                                                    *)
(*  STATED IN Pi-FORM, NOT exists-FORM, and the difference is not      *)
(*  cosmetic.  The natural reading is: there is a constant c with     *)
(*  f u = g u + c.  But then in the congruence lemma for sums, the     *)
(*  witness c sits under the binder over the index, and assembling     *)
(*  the sum's witness means building a function k |-> c_k -- a choice  *)
(*  principle over an unbounded type, which this development forbids.  *)
(*  So ceq says instead that the DIFFERENCE TAKES THE SAME VALUE AT    *)
(*  EVERY INDEX.  Same content, no witness to invent: reflexivity,     *)
(*  symmetry, transitivity and every congruence lemma become ring      *)
(*  identities in Eis.  ceq_iff_ideal records that the two readings    *)
(*  agree, so the claim about the ideal is on the record rather than   *)
(*  in a comment.                                                      *)
(*                                                                    *)
(*  NONDEGENERACY IS WHERE THE GROUP-RING PRESENTATION PAYS.  In the   *)
(*  polynomial-quotient presentation, 1 <> 0 and the primitivity of    *)
(*  zeta cost a Bezout argument (QPolyQuot.zeta_primitive); here they  *)
(*  are two-point refutations, because a delta is visibly not a        *)
(*  constant.  Orthogonality is the same story: sum_k zeta^{km} IS the *)
(*  all-ones element, since k |-> km permutes Z/p, and the all-ones    *)
(*  element is what we quotiented by.                                  *)
(*                                                                    *)
(*  WHAT IS DELIBERATELY NOT PROVED: that this ring is an integral     *)
(*  domain.  That needs Phi_p irreducible over Z[om], a real theorem   *)
(*  being skipped exactly as QPolyQuot skipped it.  So NOTHING         *)
(*  DOWNSTREAM MAY CANCEL BY A NON-UNIT.  The reciprocity argument     *)
(*  complies: its one cancellation is by the Gauss sum, which is an    *)
(*  explicit unit modulo theta because g.conj(g) = p.                  *)
(*  Axiom-free.                                                        *)
(* ================================================================= *)

From Stdlib Require Import ZArith Znumtheory Arith Lia List Permutation Ring.
Require Import ZmodPStar CEisenstein CEisensteinUnits CEisensteinDiv
        CEisensteinGcd CEisensteinSplit CEisensteinUFD CEisensteinResidue
        CEisensteinFermat CEisensteinCubicMul CEisensteinCubicSupp
        CEisensteinCubicFun CEisensteinSum CEisensteinJacobi CEisensteinNormJ
        CycIndex CEisensteinCyc.
Import ListNotations.
Open Scope Z_scope.

Lemma Esum_sub : forall f g l,
  Esum (fun x => esub (f x) (g x)) l = esub (Esum f l) (Esum g l).
Proof.
  intros f g l. induction l as [| x l IH]; [ cbn; unfold Esum; cbn; ring | ].
  rewrite !Esum_cons, IH. ring.
Qed.

Lemma esub_ezero : forall z, esub z ezero = z.
Proof. intro z. ring. Qed.

Lemma econj_sub : forall x y, econj (esub x y) = esub (econj x) (econj y).
Proof.
  intros [a b] [c d]. unfold econj, esub, eadd, eopp; cbn [ea eb].
  apply Eis_eq; ring.
Qed.

Section Quotient.

Variable p : nat.
Hypothesis Hp1 : (1 <= p)%nat.

(* ----------------------------------------------------------------- *)
(*  A.  the ideal, and the quotient equality                           *)
(* ----------------------------------------------------------------- *)
Definition cN : Cyc := fun _ => eone.

Definition ceq (f g : Cyc) : Prop :=
  forall u v, (u < p)%nat -> (v < p)%nat -> esub (f u) (g u) = esub (f v) (g v).

Lemma ceq_refl : forall f, ceq f f.
Proof. intros f u v _ _. ring. Qed.

Lemma ceq_sym : forall f g, ceq f g -> ceq g f.
Proof.
  intros f g H u v Hu Hv. pose proof (H u v Hu Hv) as Huv.
  assert (E1 : esub (g u) (f u) = eopp (esub (f u) (g u))) by ring.
  assert (E2 : esub (g v) (f v) = eopp (esub (f v) (g v))) by ring.
  rewrite E1, E2, Huv. reflexivity.
Qed.

Lemma ceq_trans : forall f g h, ceq f g -> ceq g h -> ceq f h.
Proof.
  intros f g h H1 H2 u v Hu Hv.
  pose proof (H1 u v Hu Hv) as A. pose proof (H2 u v Hu Hv) as B.
  assert (E1 : esub (f u) (h u) = eadd (esub (f u) (g u)) (esub (g u) (h u))) by ring.
  assert (E2 : esub (f v) (h v) = eadd (esub (f v) (g v)) (esub (g v) (h v))) by ring.
  rewrite E1, E2, A, B. reflexivity.
Qed.

Lemma beq_ceq : forall f g, beq p f g -> ceq f g.
Proof.
  intros f g H u v Hu Hv.
  rewrite (H u Hu), (H v Hv). ring.
Qed.

(* the workhorse: a ceq lets you compare coefficient differences *)
Lemma ceq_coeff : forall f g u v, ceq f g -> (u < p)%nat -> (v < p)%nat ->
  esub (f u) (f v) = esub (g u) (g v).
Proof.
  intros f g u v H Hu Hv. pose proof (H u v Hu Hv) as Huv.
  assert (E : esub (f u) (f v)
              = eadd (esub (g u) (g v))
                     (esub (esub (f u) (g u)) (esub (f v) (g v)))) by ring.
  rewrite Huv in E. rewrite E. ring.
Qed.

(* and it really is the quotient by the ideal generated by cN *)
Theorem ceq_iff_ideal : forall f g,
  ceq f g <-> exists c : Eis, forall u, (u < p)%nat -> f u = eadd (g u) c.
Proof.
  intros f g. split.
  - intro H. exists (esub (f 0%nat) (g 0%nat)). intros u Hu.
    rewrite <- (H u 0%nat Hu ltac:(lia)). ring.
  - intros [c Hc] u v Hu Hv.
    rewrite (Hc u Hu), (Hc v Hv). ring.
Qed.

Lemma cN_ceq_czero : ceq cN czero.
Proof. intros u v _ _. unfold cN, czero. ring. Qed.

(* ----------------------------------------------------------------- *)
(*  B.  ceq is a ring congruence                                       *)
(* ----------------------------------------------------------------- *)
Lemma ceq_cadd : forall f f' g g', ceq f f' -> ceq g g' -> ceq (cadd f g) (cadd f' g').
Proof.
  intros f f' g g' H1 H2 u v Hu Hv. unfold cadd.
  assert (E : forall a b, esub (eadd (f a) (g a)) (eadd (f' b) (g' b))
              = eadd (esub (f a) (f' b)) (esub (g a) (g' b))) by (intros; ring).
  rewrite !E. rewrite (H1 u v Hu Hv), (H2 u v Hu Hv). reflexivity.
Qed.

Lemma ceq_copp : forall f f', ceq f f' -> ceq (copp f) (copp f').
Proof.
  intros f f' H u v Hu Hv. unfold copp.
  assert (E : forall a, esub (eopp (f a)) (eopp (f' a)) = eopp (esub (f a) (f' a)))
    by (intro; ring).
  rewrite !E, (H u v Hu Hv). reflexivity.
Qed.

Lemma ceq_cscale : forall c f f', ceq f f' -> ceq (cscale c f) (cscale c f').
Proof.
  intros c f f' H u v Hu Hv. unfold cscale.
  assert (E : forall a, esub (emul c (f a)) (emul c (f' a)) = emul c (esub (f a) (f' a)))
    by (intro; ring).
  rewrite !E, (H u v Hu Hv). reflexivity.
Qed.

Lemma ceq_cbar : forall f f', ceq f f' -> ceq (cbar f) (cbar f').
Proof.
  intros f f' H u v Hu Hv. unfold cbar.
  rewrite <- !econj_sub, (H u v Hu Hv). reflexivity.
Qed.

Lemma ceq_Csum : forall F G l,
  (forall k, In k l -> ceq (F k) (G k)) -> ceq (Csum F l) (Csum G l).
Proof.
  intros F G l H u v Hu Hv. unfold Csum.
  rewrite <- !Esum_sub. apply Esum_ext. intros k Hk.
  apply (H k Hk); assumption.
Qed.

(* multiplication: the difference is a constant, and a constant
   convolved with anything depends only on the sum of its coefficients *)
Lemma ceq_cmul_r : forall f g g', ceq g g' -> ceq (cmul p f g) (cmul p f g').
Proof.
  intros f g g' H.
  destruct (proj1 (ceq_iff_ideal g g') H) as [c Hc].
  intros u v Hu Hv. unfold cmul.
  rewrite <- !Esum_sub.
  assert (E : forall n, Esum (fun i => esub (emul (f i) (g (msub p n i)))
                                            (emul (f i) (g' (msub p n i)))) (seq 0 p)
                        = emul (Esum f (seq 0 p)) c).
  { intro n. rewrite <- (Esum_scale_r c f (seq 0 p)).
    apply Esum_ext. intros i Hi. apply in_seq in Hi.
    rewrite (Hc (msub p n i) ltac:(apply msub_lt; exact Hp1)). ring. }
  rewrite !E. reflexivity.
Qed.

Lemma ceq_cmul_l : forall f f' g, ceq f f' -> ceq (cmul p f g) (cmul p f' g).
Proof.
  intros f f' g H.
  apply (ceq_trans _ (cmul p g f)); [ apply beq_ceq, cmul_comm; exact Hp1 | ].
  apply (ceq_trans _ (cmul p g f')); [ apply ceq_cmul_r; exact H | ].
  apply beq_ceq, cmul_comm; exact Hp1.
Qed.

Lemma ceq_cmul : forall f f' g g', ceq f f' -> ceq g g' ->
  ceq (cmul p f g) (cmul p f' g').
Proof.
  intros f f' g g' H1 H2.
  apply (ceq_trans _ (cmul p f' g)); [ apply ceq_cmul_l; exact H1 | ].
  apply ceq_cmul_r; exact H2.
Qed.

Lemma ceq_cpow : forall f f' k, ceq f f' -> ceq (cpow p f k) (cpow p f' k).
Proof.
  intros f f' k H. induction k as [| k IH]; cbn [cpow].
  - apply ceq_refl.
  - apply ceq_cmul; assumption.
Qed.

(* ----------------------------------------------------------------- *)
(*  C.  the quotient is not degenerate                                 *)
(* ----------------------------------------------------------------- *)
Lemma cdelta_ne_const : forall a b, (2 <= p)%nat -> (a < p)%nat -> (b < p)%nat ->
  a <> b -> ~ ceq (cdelta p a) (cdelta p b).
Proof.
  intros a b Hp2 Ha Hb Hab H.
  pose proof (H a b Ha Hb) as He.
  rewrite (cdelta_hit p a), (cdelta_miss p Hp1 b a Hb Ha Hab) in He.
  rewrite (cdelta_miss p Hp1 a b Ha Hb ltac:(auto)), (cdelta_hit p b) in He.
  rewrite esub_ezero in He.
  assert (E : esub ezero eone = eopp eone) by ring.
  rewrite E in He. cbn in He. discriminate He.
Qed.

Theorem cone_ne_czero : (2 <= p)%nat -> ~ ceq (cone p) czero.
Proof.
  intros Hp2 H.
  pose proof (H 0%nat 1%nat ltac:(lia) ltac:(lia)) as He.
  unfold cone, czero in He.
  rewrite (cdelta_hit p 0), (cdelta_miss p Hp1 0 1 ltac:(lia) ltac:(lia) ltac:(lia)) in He.
  rewrite !esub_ezero in He. cbn in He. discriminate He.
Qed.

Theorem czeta_primitive : (2 <= p)%nat -> forall m, (0 < m < p)%nat ->
  ~ ceq (cpow p (czeta p) m) (cone p).
Proof.
  intros Hp2 m Hm H.
  assert (Hb : beq p (cpow p (czeta p) m) (cdelta p m)).
  { pose proof (cpow_czeta p Hp1 Hp2 m) as Hc.
    rewrite (Nat.mod_small m p) in Hc by lia. exact Hc. }
  apply (cdelta_ne_const m 0 Hp2 ltac:(lia) ltac:(lia) ltac:(lia)).
  apply (ceq_trans _ (cpow p (czeta p) m));
    [ apply ceq_sym, beq_ceq; exact Hb | exact H ].
Qed.

Theorem cemb_inj : (2 <= p)%nat -> forall a b, ceq (cemb p a) (cemb p b) -> a = b.
Proof.
  intros Hp2 a b H.
  pose proof (H 0%nat 1%nat ltac:(lia) ltac:(lia)) as He.
  unfold cemb, cscale, cone in He.
  rewrite (cdelta_hit p 0), (cdelta_miss p Hp1 0 1 ltac:(lia) ltac:(lia) ltac:(lia)) in He.
  assert (E1 : emul a eone = a) by ring.
  assert (E2 : emul b eone = b) by ring.
  assert (E3 : emul a ezero = ezero) by ring.
  assert (E4 : emul b ezero = ezero) by ring.
  rewrite E1, E2, E3, E4, esub_ezero in He.
  apply esub_eq_zero. rewrite He. ring.
Qed.

(* ----------------------------------------------------------------- *)
(*  D.  orthogonality                                                  *)
(* ----------------------------------------------------------------- *)
Theorem cyc_orthogonality : prime (Z.of_nat p) -> (2 <= p)%nat ->
  forall m, ~ Nat.divide p m ->
  ceq (Csum (fun k => cpow p (czeta p) (k * m)%nat) (seq 0 p)) czero.
Proof.
  intros Hp Hp2 m Hm.
  apply (ceq_trans _ cN); [ | exact cN_ceq_czero ].
  apply beq_ceq. intros u Hu.
  (* replace each power by its delta *)
  assert (Hb : Csum (fun k => cpow p (czeta p) (k * m)%nat) (seq 0 p) u
               = Esum (fun k => cdelta p ((k * m) mod p)%nat u) (seq 0 p)).
  { unfold Csum. apply Esum_ext. intros k _.
    exact (cpow_czeta p Hp1 Hp2 (k * m)%nat u Hu). }
  rewrite Hb.
  (* k |-> k m permutes Z/p, so the sum is the all-ones coefficient *)
  assert (Hc : Esum (fun k => cdelta p ((k * m) mod p)%nat u) (seq 0 p)
               = Esum (fun k => cdelta p ((m * k) mod p)%nat u) (seq 0 p)).
  { apply Esum_ext. intros k _. rewrite Nat.mul_comm. reflexivity. }
  rewrite Hc, (Esum_mulperm p Hp1 Hp (fun j => cdelta p j u) m Hm).
  (* now the sum is over all deltas, and only j = u survives *)
  rewrite (Esum_del (fun j => cdelta p j u) u (seq 0 p)
             (seq_NoDup _ _) ltac:(apply in_seq; lia)).
  rewrite (cdelta_hit p u).
  assert (Hz : Esum (fun j => cdelta p j u) (del u (seq 0 p)) = ezero).
  { apply Esum_zero_ext. intros j Hj.
    apply In_del in Hj as [Hin Hne]. apply in_seq in Hin.
    apply (cdelta_miss p Hp1 j u); lia. }
  rewrite Hz. unfold cN. ring.
Qed.

End Quotient.

Print Assumptions ceq_iff_ideal.
Print Assumptions ceq_coeff.
Print Assumptions ceq_cmul.
Print Assumptions czeta_primitive.
Print Assumptions cyc_orthogonality.
