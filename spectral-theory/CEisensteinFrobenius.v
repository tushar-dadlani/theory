(* ================================================================= *)
(*  CEisensteinFrobenius.v  —  the Frobenius on the group ring.       *)
(*                                                                    *)
(*    ccong d f g      : coefficientwise congruence modulo d           *)
(*    cmono c t        : the monomial c.x^t                            *)
(*    cmono_mul/pow    : monomials multiply by adding exponents        *)
(*    monomial_decomp  : every element is the sum of its monomials     *)
(*    frob_add         : (a+b)^q = a^q + b^q  mod q                    *)
(*    frob_Csum        : ... and the same for a sum of any length      *)
(*    frob_pow         : f^q = sum_t (f t)^q x^{tq}  mod q             *)
(*                                                                    *)
(*  THIS IS THE STEP THE JACOBI SUM COULD NOT TAKE.  Reciprocity needs *)
(*  an object on which the q-power map does something, and modulo a    *)
(*  split prime of Z[om] it does nothing at all -- Z[om]/theta is      *)
(*  F_q, where x |-> x^q is the identity.  In the group ring it moves: *)
(*  the exponent t becomes tq.  frob_pow is exactly that motion, and   *)
(*  it is the whole reason the cyclotomic layer was built.             *)
(*                                                                    *)
(*  THE FRESHMAN'S DREAM IS NOW SHORT because E5a registered Cyc as a  *)
(*  setoid ring.  Expand by the binomial theorem, peel off the two end *)
(*  terms -- which are b^q and a^q, since C(q,0) = C(q,q) = 1 -- and   *)
(*  observe that every middle coefficient is divisible by q.  The      *)
(*  quotients C(q,k)/q are given by an explicit division rather than   *)
(*  extracted from the divisibility proof, so no choice principle is   *)
(*  needed to assemble them into a function of k.                      *)
(*                                                                    *)
(*  THE MONOMIAL DECOMPOSITION IS WHAT MAKES frob_pow FALL OUT.  An    *)
(*  element of the group ring is the sum of its own monomials, one per *)
(*  index, and a monomial's q-th power is computed by cmono_pow --     *)
(*  coefficient to the q-th, exponent times q.  So the general         *)
(*  Frobenius is frob_Csum applied to that decomposition, with no      *)
(*  further computation.                                               *)
(*                                                                    *)
(*  ccong IS COEFFICIENTWISE and says nothing about the quotient by N. *)
(*  That is deliberate: numerically the Frobenius identity holds       *)
(*  EXACTLY modulo theta, not merely modulo the ideal, so weakening it *)
(*  to ceq would throw away information the endgame may want.          *)
(*  Axiom-free.                                                        *)
(* ================================================================= *)

From Stdlib Require Import ZArith Znumtheory Arith Lia List Permutation
        Setoid Ring Ring_theory RelationClasses Morphisms.
Require Import ZmodPStar BitDensity CEisenstein CEisensteinUnits CEisensteinDiv
        CEisensteinGcd CEisensteinSplit CEisensteinUFD CEisensteinResidue
        CEisensteinFermat CEisensteinCubicMul CEisensteinCubicSupp
        CEisensteinCubicFun CEisensteinSum CEisensteinJacobi CEisensteinNormJ
        CycIndex CEisensteinCyc CEisensteinCycQuot CEisensteinBinomial.
Import ListNotations.
Open Scope Z_scope.

Lemma Esum_dvd : forall d f l,
  (forall x, In x l -> edvd d (f x)) -> edvd d (Esum f l).
Proof.
  intros d f l. induction l as [| x l IH]; intro H.
  - exists ezero. rewrite Esum_nil. ring.
  - rewrite Esum_cons. apply edvd_add;
      [ apply H; left; reflexivity
      | apply IH; intros y Hy; apply H; right; exact Hy ].
Qed.

Section Frob.

Variable p : nat.
Hypothesis Hp1 : (1 <= p)%nat.

(* the setoid ring again -- the registration does not cross a section *)
Instance cyc_equiv' : Equivalence (beq p).
Proof.
  constructor; [ exact (beq_refl p) | exact (beq_sym p) | exact (beq_trans p) ].
Defined.

Instance cadd_Proper' : Proper (beq p ==> beq p ==> beq p) cadd.
Proof. intros x x' Hx y y' Hy. apply beq_cadd; assumption. Qed.
Instance cmul_Proper' : Proper (beq p ==> beq p ==> beq p) (cmul p).
Proof. intros x x' Hx y y' Hy. apply beq_cmul; assumption. Qed.
Instance copp_Proper' : Proper (beq p ==> beq p) copp.
Proof. intros x x' Hx. apply beq_copp; assumption. Qed.

Add Ring CycR2 : (cyc_ring p Hp1) (setoid cyc_equiv' (cyc_ext p Hp1)).

(* ----------------------------------------------------------------- *)
(*  A.  congruence of group-ring elements modulo a coefficient         *)
(* ----------------------------------------------------------------- *)
Definition ccong (d : Eis) (f g : Cyc) : Prop :=
  forall u, (u < p)%nat -> edvd d (esub (f u) (g u)).

Lemma ccong_refl : forall d f, ccong d f f.
Proof. intros d f u _. exists ezero. ring. Qed.

Lemma ccong_of_beq : forall d f g, beq p f g -> ccong d f g.
Proof.
  intros d f g H u Hu. rewrite (H u Hu). exists ezero. ring.
Qed.

Lemma ccong_sym : forall d f g, ccong d f g -> ccong d g f.
Proof.
  intros d f g H u Hu. destruct (H u Hu) as [c Hc]. exists (eopp c).
  assert (E : esub (g u) (f u) = eopp (esub (f u) (g u))) by ring.
  rewrite E, Hc. ring.
Qed.

Lemma ccong_trans : forall d f g h, ccong d f g -> ccong d g h -> ccong d f h.
Proof.
  intros d f g h H1 H2 u Hu.
  destruct (H1 u Hu) as [c Hc]. destruct (H2 u Hu) as [e He].
  exists (eadd c e).
  assert (E : esub (f u) (h u) = eadd (esub (f u) (g u)) (esub (g u) (h u))) by ring.
  rewrite E, Hc, He. ring.
Qed.

Lemma ccong_cadd : forall d f f' g g', ccong d f f' -> ccong d g g' ->
  ccong d (cadd f g) (cadd f' g').
Proof.
  intros d f f' g g' H1 H2 u Hu.
  destruct (H1 u Hu) as [c Hc]. destruct (H2 u Hu) as [e He].
  exists (eadd c e). unfold cadd.
  assert (E : esub (eadd (f u) (g u)) (eadd (f' u) (g' u))
              = eadd (esub (f u) (f' u)) (esub (g u) (g' u))) by ring.
  rewrite E, Hc, He. ring.
Qed.

Lemma ccong_weaken : forall d d' f g, edvd d' d -> ccong d f g -> ccong d' f g.
Proof.
  intros d d' f g Hd H u Hu. apply (edvd_trans d' d); [ exact Hd | apply H; exact Hu ].
Qed.

(* ----------------------------------------------------------------- *)
(*  B.  monomials                                                      *)
(* ----------------------------------------------------------------- *)
Lemma madd_msub_l : forall n a, (n < p)%nat -> (a < p)%nat ->
  madd p a (msub p n a) = n.
Proof.
  intros n a Hn Ha. apply (cgp_eq p Hp1); [ apply madd_lt; exact Hp1 | lia | ].
  destruct (madd_cg p Hp1 a (msub p n a)) as [c Hc].
  destruct (msub_cg p Hp1 n a ltac:(lia)) as [e He].
  exists (c + e). lia.
Qed.

Lemma cpow_czero : forall k, (1 <= k)%nat -> beq p (cpow p czero k) czero.
Proof.
  intros k Hk. destruct k as [| k]; [ lia | ].
  replace (cpow p czero (S k)) with (cmul p czero (cpow p czero k)) by reflexivity.
  apply cmul_0_l.
Qed.

Definition cmono (c : Eis) (t : nat) : Cyc := cscale c (cdelta p t).

Lemma cdelta_mul : forall a b, (a < p)%nat -> (b < p)%nat ->
  beq p (cmul p (cdelta p a) (cdelta p b)) (cdelta p (madd p a b)).
Proof.
  intros a b Ha Hb n Hn.
  rewrite (cmul_delta_l p Hp1 a (cdelta p b) Ha n Hn). cbn beta.
  unfold cdelta.
  rewrite (Nat.mod_small (msub p n a) p) by (apply msub_lt; exact Hp1).
  rewrite (Nat.mod_small b p) by lia.
  rewrite (Nat.mod_small n p) by lia.
  rewrite (Nat.mod_small (madd p a b) p) by (apply madd_lt; exact Hp1).
  destruct (Nat.eqb_spec (msub p n a) b) as [E1 | E1];
  destruct (Nat.eqb_spec n (madd p a b)) as [E2 | E2]; try reflexivity.
  - exfalso. apply E2. rewrite <- E1, madd_msub_l; [ reflexivity | lia | lia ].
  - exfalso. apply E1. rewrite E2.
    rewrite madd_comm, (madd_msub_id p Hp1 b a Hb Ha). reflexivity.
Qed.

Lemma cmono_mul : forall c1 c2 a b, (a < p)%nat -> (b < p)%nat ->
  beq p (cmul p (cmono c1 a) (cmono c2 b)) (cmono (emul c1 c2) (madd p a b)).
Proof.
  intros c1 c2 a b Ha Hb. unfold cmono.
  apply (beq_trans p _ (cscale c1 (cmul p (cdelta p a) (cscale c2 (cdelta p b))))).
  { apply beq_sym, cscale_cmul_assoc. }
  apply (beq_trans p _ (cscale c1 (cscale c2 (cmul p (cdelta p a) (cdelta p b))))).
  { apply beq_cscale. intros n _. unfold cmul, cscale.
    rewrite <- (Esum_scale_l c2
      (fun i => emul (cdelta p a i) (cdelta p b (msub p n i))) (seq 0 p)).
    apply Esum_ext. intros i _. ring. }
  apply (beq_trans p _ (cscale c1 (cscale c2 (cdelta p (madd p a b))))).
  { apply beq_cscale, beq_cscale, cdelta_mul; assumption. }
  intros u _. unfold cscale. ring.
Qed.

Lemma madd_mulmod : forall t k, (t < p)%nat ->
  madd p t ((t * k) mod p)%nat = ((t * S k) mod p)%nat.
Proof.
  intros t k Ht. apply (cgp_eq p Hp1);
    [ apply madd_lt; exact Hp1 | apply Nat.mod_upper_bound; lia | ].
  destruct (madd_cg p Hp1 t ((t * k) mod p)%nat) as [a Ha].
  destruct (cgp_mod p Hp1 (t * k)%nat) as [b Hb]. rewrite Nat2Z.inj_mul in Hb.
  destruct (cgp_mod p Hp1 (t * S k)%nat) as [c Hc]. rewrite Nat2Z.inj_mul in Hc.
  exists (a + b - c).
  rewrite Nat2Z.inj_succ in Hc. lia.
Qed.

Lemma cmono_pow : forall c t k, (t < p)%nat ->
  beq p (cpow p (cmono c t) k) (cmono (epow c k) ((t * k) mod p)%nat).
Proof.
  intros c t k Ht. induction k as [| k IH].
  - rewrite Nat.mul_0_r, Nat.Div0.mod_0_l. cbn [cpow epow].
    unfold cmono, cone, cscale. intros u _. ring.
  - replace (cpow p (cmono c t) (S k))
      with (cmul p (cmono c t) (cpow p (cmono c t) k)) by reflexivity.
    apply (beq_trans p _ (cmul p (cmono c t) (cmono (epow c k) ((t * k) mod p)%nat))).
    { exact (beq_cmul p Hp1 _ _ _ _ (beq_refl p _) IH). }
    apply (beq_trans p _ (cmono (emul c (epow c k))
                                (madd p t ((t * k) mod p)%nat))).
    { apply cmono_mul; [ exact Ht | apply Nat.mod_upper_bound; lia ]. }
    rewrite (madd_mulmod t k Ht). apply beq_refl.
Qed.

Theorem monomial_decomp : forall f,
  beq p f (Csum (fun t => cmono (f t) t) (seq 0 p)).
Proof.
  intros f u Hu. unfold Csum, cmono, cscale.
  rewrite (Esum_del (fun t => emul (f t) (cdelta p t u)) u (seq 0 p)
             (seq_NoDup _ _) ltac:(apply in_seq; lia)).
  rewrite (cdelta_hit p u).
  assert (Hz : Esum (fun t => emul (f t) (cdelta p t u)) (del u (seq 0 p)) = ezero).
  { apply Esum_zero_ext. intros t Ht.
    apply In_del in Ht as [Hin Hne]. apply in_seq in Hin.
    rewrite (cdelta_miss p Hp1 t u ltac:(lia) ltac:(lia) ltac:(auto)). ring. }
  rewrite Hz. ring.
Qed.

(* ----------------------------------------------------------------- *)
(*  C.  the freshman's dream                                           *)
(* ----------------------------------------------------------------- *)
Variable q : nat.
Hypothesis Hq : prime (Z.of_nat q).

Lemma Hq2 : (2 <= q)%nat. Proof. destruct Hq; lia. Qed.

Definition dq (k : nat) : nat := (binomial q k / q)%nat.

Lemma dq_spec : forall k, (0 < k < q)%nat -> binomial q k = (q * dq k)%nat.
Proof.
  intros k Hk. unfold dq.
  destruct (prime_dvd_binom q Hq k Hk) as [c Hc].
  rewrite Hc, Nat.div_mul by (pose proof Hq2; lia). lia.
Qed.

Lemma ccong_cnat_mul : forall Y,
  ccong (eZ (Z.of_nat q)) (cmul p (cnat p q) Y) czero.
Proof.
  intros Y u _. unfold cmul, czero, cnat, cemb, cscale.
  assert (E : esub (Esum (fun i => emul (emul (eZ (Z.of_nat q)) (cone p i))
                                        (Y (msub p u i))) (seq 0 p)) ezero
              = Esum (fun i => emul (eZ (Z.of_nat q))
                        (emul (cone p i) (Y (msub p u i)))) (seq 0 p)).
  { assert (E0 : forall z : Eis, esub z ezero = z) by (intro; ring).
    rewrite E0. apply Esum_ext. intros i _. ring. }
  rewrite E. apply Esum_dvd. intros i _.
  exists (emul (cone p i) (Y (msub p u i))). reflexivity.
Qed.

Theorem frob_add : forall a b,
  ccong (eZ (Z.of_nat q)) (cpow p (cadd a b) q)
        (cadd (cpow p a q) (cpow p b q)).
Proof.
  intros a b.
  (* the binomial expansion, split at both ends *)
  assert (Hs : beq p (Csum (bterm p a b q) (seq 0 (S q)))
                     (cadd (bterm p a b q 0)
                       (cadd (Csum (bterm p a b q) (seq 1 (q - 1)))
                             (bterm p a b q q)))).
  { assert (Hl : seq 0 (S q) = 0%nat :: seq 1 (q - 1) ++ [q]).
    { cbn [seq]. f_equal.
      replace q with (S (q - 1)) at 1 by (pose proof Hq2; lia).
      rewrite seq_S. repeat f_equal. pose proof Hq2; lia. }
    rewrite Hl, Csum_cons. apply beq_cadd; [ apply beq_refl | ].
    apply (beq_trans p _ (cadd (Csum (bterm p a b q) (seq 1 (q - 1)))
                               (Csum (bterm p a b q) [q]))).
    { apply Csum_app_beq. }
    apply beq_cadd; [ apply beq_refl | ].
    rewrite Csum_cons, Csum_nil. intros v _. unfold cadd, czero. ring. }
  (* the two ends are the pure powers *)
  assert (H0 : beq p (bterm p a b q 0) (cpow p b q)).
  { unfold bterm. rewrite binom_0_r.
    replace (q - 0)%nat with q by lia.
    replace (cpow p a 0) with (cone p) by reflexivity.
    rewrite (cnat_1 p). ring. }
  assert (Hq' : beq p (bterm p a b q q) (cpow p a q)).
  { unfold bterm. rewrite binom_diag.
    replace (q - q)%nat with 0%nat by lia.
    replace (cpow p b 0) with (cone p) by reflexivity.
    rewrite (cnat_1 p). ring. }
  (* the middle is q times something *)
  assert (Hm : beq p (Csum (bterm p a b q) (seq 1 (q - 1)))
                     (cmul p (cnat p q)
                        (Csum (fun k => cmul p (cnat p (dq k))
                                 (cmul p (cpow p a k) (cpow p b (q - k))))
                              (seq 1 (q - 1))))).
  { apply (beq_trans p _ (Csum (fun k => cmul p (cnat p q)
                             (cmul p (cnat p (dq k))
                                (cmul p (cpow p a k) (cpow p b (q - k)))))
                             (seq 1 (q - 1)))).
    - apply beq_Csum. intros k Hk. apply in_seq in Hk.
      unfold bterm. rewrite (dq_spec k ltac:(pose proof Hq2; lia)).
      rewrite (cnat_mul p Hp1). ring.
    - apply beq_sym, Csum_cmul_l. }
  (* assemble *)
  apply (ccong_trans _ _ (cadd (cpow p b q)
           (cadd (cmul p (cnat p q)
                    (Csum (fun k => cmul p (cnat p (dq k))
                             (cmul p (cpow p a k) (cpow p b (q - k))))
                          (seq 1 (q - 1))))
                 (cpow p a q)))).
  { apply ccong_of_beq.
    apply (beq_trans p _ (Csum (bterm p a b q) (seq 0 (S q))));
      [ exact (binom_thm p Hp1 a b q) | ].
    apply (beq_trans p _ (cadd (bterm p a b q 0)
             (cadd (Csum (bterm p a b q) (seq 1 (q - 1))) (bterm p a b q q))));
      [ exact Hs | ].
    apply beq_cadd; [ exact H0 | apply beq_cadd; [ exact Hm | exact Hq' ] ]. }
  apply (ccong_trans _ _ (cadd (cpow p b q) (cadd czero (cpow p a q)))).
  { apply ccong_cadd; [ apply ccong_refl | ].
    apply ccong_cadd; [ apply ccong_cnat_mul | apply ccong_refl ]. }
  apply ccong_of_beq. ring.
Qed.

Theorem frob_Csum : forall F l,
  ccong (eZ (Z.of_nat q)) (cpow p (Csum F l) q)
        (Csum (fun k => cpow p (F k) q) l).
Proof.
  intros F l. induction l as [| x l IH].
  - rewrite !Csum_nil. apply ccong_of_beq.
    apply cpow_czero. pose proof Hq2; lia.
  - rewrite !Csum_cons.
    apply (ccong_trans _ _ (cadd (cpow p (F x) q) (cpow p (Csum F l) q)));
      [ apply frob_add | ].
    apply ccong_cadd; [ apply ccong_refl | exact IH ].
Qed.

(* ----------------------------------------------------------------- *)
(*  D.  the Frobenius                                                  *)
(* ----------------------------------------------------------------- *)
Theorem frob_pow : forall f,
  ccong (eZ (Z.of_nat q)) (cpow p f q)
        (Csum (fun t => cmono (epow (f t) q) ((t * q) mod p)%nat) (seq 0 p)).
Proof.
  intro f.
  apply (ccong_trans _ _ (cpow p (Csum (fun t => cmono (f t) t) (seq 0 p)) q)).
  { apply ccong_of_beq. exact (beq_cpow p Hp1 _ _ q (monomial_decomp f)). }
  apply (ccong_trans _ _ (Csum (fun t => cpow p (cmono (f t) t) q) (seq 0 p)));
    [ apply frob_Csum | ].
  apply ccong_of_beq. apply beq_Csum. intros t Ht. apply in_seq in Ht.
  apply cmono_pow. lia.
Qed.

End Frob.

Print Assumptions cmono_pow.
Print Assumptions monomial_decomp.
Print Assumptions frob_add.
Print Assumptions frob_pow.
