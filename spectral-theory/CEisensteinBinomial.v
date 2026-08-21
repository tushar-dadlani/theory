(* ================================================================= *)
(*  CEisensteinBinomial.v  —  Cyc as a RING, and the binomial theorem. *)
(*                                                                    *)
(*    binom_absorb     : k C(n,k) = n C(n-1,k-1)                       *)
(*    prime_dvd_binom  : q | C(q,k)  for 0 < k < q                     *)
(*    cyc_ring/cyc_ext : Cyc registered as a SETOID RING under beq     *)
(*    cnat             : naturals as group-ring elements               *)
(*    Csum_cmul_l, Csum_add, Csum_seq_cons, Csum_seq_snoc              *)
(*    binom_thm        : (a+b)^n = sum_k C(n,k) a^k b^{n-k}  in Cyc    *)
(*                                                                    *)
(*  THE SETOID RING IS THE POINT OF THIS FILE.  E2 deliberately did    *)
(*  not register one: equality on Cyc is the hand-rolled beq, not      *)
(*  Leibniz, and the plan assumed that meant living without the ring   *)
(*  tactic and rewriting every rearrangement by hand.  That assumption *)
(*  was wrong.  Add Ring accepts a SETOID ring -- carrier, equivalence *)
(*  and Proper morphisms -- and beq supplies all three.  So ring fires *)
(*  on group-ring goals after all, and the binomial theorem costs a    *)
(*  fraction of what it otherwise would.                               *)
(*                                                                    *)
(*  The registration does NOT survive the section, because p is a      *)
(*  section variable; each consumer re-registers in thirty lines.      *)
(*  That is a small price for turning every algebraic step below into  *)
(*  one word.                                                          *)
(*                                                                    *)
(*  q DIVIDES C(q,k) comes from the absorption identity                *)
(*  k C(n,k) = n C(n-1,k-1), proved by induction on n from the Pascal  *)
(*  recurrence already in BitDensity.  Then q | k C(q,k) and q does    *)
(*  not divide k, so q | C(q,k) by primality.  No factorials appear.   *)
(*                                                                    *)
(*  WHAT COST MOST WAS NOT THE ALGEBRA BUT THE REDUCTION.  cbn refuses *)
(*  to reduce binomial n 0 for symbolic n -- the fixpoint matches on   *)
(*  the first argument -- so a goal can end up with C(S n,0) reduced   *)
(*  to 1 on one side and C(n,0) stuck on the other, and ring then      *)
(*  fails on two atoms that are equal but not syntactically so.  Every *)
(*  definitional step here is therefore done by an explicit replace    *)
(*  ... by reflexivity rather than left to cbn.                        *)
(*  Axiom-free.                                                        *)
(* ================================================================= *)

From Stdlib Require Import ZArith Znumtheory Arith Lia List Permutation
        Setoid Ring Ring_theory RelationClasses Morphisms.
Require Import ZmodPStar BitDensity CEisenstein CEisensteinUnits CEisensteinDiv
        CEisensteinGcd CEisensteinSplit CEisensteinUFD CEisensteinResidue
        CEisensteinFermat CEisensteinCubicMul CEisensteinCubicSupp
        CEisensteinCubicFun CEisensteinSum CEisensteinJacobi CEisensteinNormJ
        CycIndex CEisensteinCyc CEisensteinCycQuot CEisensteinGaussSum.
Import ListNotations.
Open Scope Z_scope.

(* ----------------------------------------------------------------- *)
(*  A.  binomial coefficients: q divides C(q,k) for 0 < k < q          *)
(* ----------------------------------------------------------------- *)
Lemma binom_S : forall n k,
  binomial (S n) (S k) = (binomial n k + binomial n (S k))%nat.
Proof. reflexivity. Qed.

Lemma binom_1 : forall n, binomial n 1 = n.
Proof.
  induction n as [| n IH]; [ reflexivity | ].
  rewrite binom_S, binom_0_r, IH. lia.
Qed.

(* the absorption identity  k C(n,k) = n C(n-1,k-1)  *)
Lemma binom_absorb : forall n k,
  (S k * binomial (S n) (S k) = S n * binomial n k)%nat.
Proof.
  induction n as [| n IH]; intro k.
  - rewrite binom_S. destruct k as [| k]; cbn [binomial]; lia.
  - destruct k as [| k].
    + rewrite binom_S, binom_0_r, binom_1. lia.
    + pose proof (IH k) as I1. pose proof (IH (S k)) as I2.
      rewrite !binom_S. rewrite binom_S in I1, I2.
      set (A := binomial n k) in *.
      set (B := binomial n (S k)) in *.
      set (C := binomial n (S (S k))) in *.
      nia.
Qed.

Theorem prime_dvd_binom : forall q, prime (Z.of_nat q) ->
  forall k, (0 < k < q)%nat -> Nat.divide q (binomial q k).
Proof.
  intros q Hq k Hk.
  assert (Hq2 : (2 <= q)%nat) by (destruct Hq; lia).
  assert (Hk1 : k = S (k - 1)) by lia.
  assert (Hq1 : q = S (q - 1)) by lia.
  pose proof (binom_absorb (q - 1) (k - 1)) as H.
  rewrite <- Hk1, <- Hq1 in H.
  assert (Hd : Nat.divide q (k * binomial q k)%nat)
    by (exists (binomial (q - 1) (k - 1)); lia).
  destruct (prime_mult_nat q k (binomial q k) Hq Hd) as [H1 | H1].
  - exfalso. apply (unit_not_div q k ltac:(lia)). exact H1.
  - exact H1.
Qed.

Lemma Esum_app : forall f l1 l2,
  Esum f (l1 ++ l2) = eadd (Esum f l1) (Esum f l2).
Proof.
  intros f l1 l2. induction l1 as [| a l1 IH]; [ cbn; unfold Esum; cbn; ring | ].
  cbn [app]. rewrite !Esum_cons, IH. ring.
Qed.

(* ----------------------------------------------------------------- *)
(*  B.  Cyc as a SETOID RING, so that ring fires on group-ring goals   *)
(* ----------------------------------------------------------------- *)
Section Binom.

Variable p : nat.
Hypothesis Hp1 : (1 <= p)%nat.

Instance cyc_equiv : Equivalence (beq p).
Proof.
  constructor; [ exact (beq_refl p) | exact (beq_sym p) | exact (beq_trans p) ].
Defined.

Lemma cyc_ring : ring_theory czero (cone p) cadd (cmul p) csub copp (beq p).
Proof.
  constructor.
  - intro x. apply cadd_0_l.
  - intros x y. apply cadd_comm.
  - intros x y z. apply beq_sym, cadd_assoc.
  - intro x. apply cmul_1_l; exact Hp1.
  - intros x y. apply cmul_comm; exact Hp1.
  - intros x y z. apply beq_sym, cmul_assoc; exact Hp1.
  - intros x y z.
    apply (beq_trans p _ (cmul p z (cadd x y))); [ apply cmul_comm; exact Hp1 | ].
    apply (beq_trans p _ (cadd (cmul p z x) (cmul p z y)));
      [ apply cmul_distr_l; exact Hp1 | ].
    apply beq_cadd; apply cmul_comm; exact Hp1.
  - intros x y. apply csub_spec.
  - intro x. apply cadd_opp.
Qed.

Lemma cyc_ext : ring_eq_ext cadd (cmul p) copp (beq p).
Proof.
  constructor.
  - intros x x' Hx y y' Hy. apply beq_cadd; assumption.
  - intros x x' Hx y y' Hy. apply beq_cmul; assumption.
  - intros x x' Hx. apply beq_copp; assumption.
Qed.

Add Ring CycR : cyc_ring (setoid cyc_equiv cyc_ext).

(* natural numbers as ring elements *)
Definition cnat (c : nat) : Cyc := cemb p (eZ (Z.of_nat c)).

Lemma cnat_add : forall a b, beq p (cnat (a + b)%nat) (cadd (cnat a) (cnat b)).
Proof.
  intros a b. unfold cnat. rewrite Nat2Z.inj_add, <- eZ_add. apply cemb_add.
Qed.

Lemma cnat_mul : forall a b, beq p (cnat (a * b)%nat) (cmul p (cnat a) (cnat b)).
Proof.
  intros a b.
  apply (beq_trans p _ (cscale (eZ (Z.of_nat a)) (cnat b))).
  - intros u _. unfold cnat, cemb, cscale.
    rewrite Nat2Z.inj_mul, eZ_mul. ring.
  - unfold cnat at 2. apply cscale_cmul; exact Hp1.
Qed.

Lemma cnat_0 : beq p (cnat 0) czero.
Proof.
  intros u _. unfold cnat, cemb, cscale, czero.
  assert (E : eZ (Z.of_nat 0) = ezero) by reflexivity. rewrite E. ring.
Qed.

Lemma cnat_1 : beq p (cnat 1) (cone p).
Proof.
  intros u _. unfold cnat, cemb, cscale.
  assert (E : eZ (Z.of_nat 1) = eone) by reflexivity. rewrite E. ring.
Qed.

(* ----------------------------------------------------------------- *)
(*  C.  sums of ring elements                                          *)
(* ----------------------------------------------------------------- *)
Lemma Csum_nil : forall F, Csum F [] = czero.
Proof. reflexivity. Qed.

Lemma Csum_cons : forall F x l, Csum F (x :: l) = cadd (F x) (Csum F l).
Proof. reflexivity. Qed.

Lemma Csum_app_beq : forall F l1 l2,
  beq p (Csum F (l1 ++ l2)) (cadd (Csum F l1) (Csum F l2)).
Proof.
  intros F l1 l2 u _. unfold Csum, cadd.
  rewrite <- Esum_app. reflexivity.
Qed.

Lemma Csum_add : forall F G l,
  beq p (Csum (fun k => cadd (F k) (G k)) l) (cadd (Csum F l) (Csum G l)).
Proof.
  intros F G l u _. unfold Csum, cadd. rewrite <- Esum_add. reflexivity.
Qed.

Lemma Csum_cmul_l : forall f G l,
  beq p (cmul p f (Csum G l)) (Csum (fun k => cmul p f (G k)) l).
Proof.
  intros f G l n _. unfold cmul, Csum.
  rewrite Esum_swap. apply Esum_ext. intros i _.
  rewrite <- Esum_scale_l. reflexivity.
Qed.

Lemma Csum_seq_cons : forall F m,
  beq p (Csum F (seq 0 (S m))) (cadd (F 0%nat) (Csum (fun j => F (S j)) (seq 0 m))).
Proof.
  intros F m u _. cbn [seq]. unfold Csum, cadd. rewrite Esum_cons. f_equal.
  unfold Esum. rewrite <- seq_shift, map_map. reflexivity.
Qed.

Lemma Csum_seq_snoc : forall F m,
  beq p (Csum F (seq 0 (S m))) (cadd (Csum F (seq 0 m)) (F m)).
Proof.
  intros F m. rewrite seq_S.
  apply (beq_trans p _ (cadd (Csum F (seq 0 m)) (Csum F [(0 + m)%nat]))).
  - apply Csum_app_beq.
  - apply beq_cadd; [ apply beq_refl | ].
    rewrite Csum_cons, Csum_nil. replace (0 + m)%nat with m by lia.
    intros u _. unfold cadd, czero. ring.
Qed.

(* setoid rewriting under beq, so that rewrite works inside ring goals *)
Instance cadd_Proper : Proper (beq p ==> beq p ==> beq p) cadd.
Proof. intros x x' Hx y y' Hy. apply beq_cadd; assumption. Qed.

Instance cmul_Proper : Proper (beq p ==> beq p ==> beq p) (cmul p).
Proof. intros x x' Hx y y' Hy. apply beq_cmul; assumption. Qed.

Instance copp_Proper : Proper (beq p ==> beq p) copp.
Proof. intros x x' Hx. apply beq_copp; assumption. Qed.

(* ----------------------------------------------------------------- *)
(*  D.  the binomial theorem                                           *)
(* ----------------------------------------------------------------- *)
Definition bterm (a b : Cyc) (m k : nat) : Cyc :=
  cmul p (cnat (binomial m k)) (cmul p (cpow p a k) (cpow p b (m - k))).

Lemma bterm_zero : forall a b n j, (n < j)%nat -> beq p (bterm a b n j) czero.
Proof.
  intros a b n j Hj. unfold bterm.
  rewrite (binom_gt n j Hj), cnat_0. ring.
Qed.

Lemma bterm_split : forall a b n j, (j <= n)%nat ->
  beq p (bterm a b (S n) (S j))
        (cadd (cmul p a (bterm a b n j)) (cmul p b (bterm a b n (S j)))).
Proof.
  intros a b n j Hj. unfold bterm.
  replace (S n - S j)%nat with (n - j)%nat by lia.
  rewrite binom_S, cnat_add.
  destruct (Nat.eq_dec j n) as [-> | Hne].
  - rewrite (binom_gt n (S n) ltac:(lia)), cnat_0.
    replace (n - n)%nat with 0%nat by lia.
    replace (cpow p a (S n)) with (cmul p a (cpow p a n)) by reflexivity.
    replace (cpow p b 0) with (cone p) by reflexivity.
    ring.
  - replace (n - j)%nat with (S (n - S j))%nat by lia.
    replace (cpow p a (S j)) with (cmul p a (cpow p a j)) by reflexivity.
    replace (cpow p b (S (n - S j))) with (cmul p b (cpow p b (n - S j)))
      by reflexivity.
    ring.
Qed.

Lemma bterm_first : forall a b n,
  beq p (bterm a b (S n) 0) (cmul p b (bterm a b n 0)).
Proof.
  intros a b n. unfold bterm. rewrite !binom_0_r.
  replace (S n - 0)%nat with (S n) by lia.
  replace (n - 0)%nat with n by lia.
  replace (cpow p a 0) with (cone p) by reflexivity.
  replace (cpow p b (S n)) with (cmul p b (cpow p b n)) by reflexivity.
  ring.
Qed.

Theorem binom_thm : forall a b n,
  beq p (cpow p (cadd a b) n) (Csum (bterm a b n) (seq 0 (S n))).
Proof.
  intros a b n. induction n as [| n IH].
  - cbn [seq]. rewrite Csum_cons, Csum_nil. unfold bterm.
    replace (binomial 0 0) with 1%nat by reflexivity.
    replace (0 - 0)%nat with 0%nat by reflexivity.
    replace (cpow p a 0) with (cone p) by reflexivity.
    replace (cpow p b 0) with (cone p) by reflexivity.
    replace (cpow p (cadd a b) 0) with (cone p) by reflexivity.
    rewrite cnat_1. ring.
  - (* the left side, expanded by the induction hypothesis *)
    assert (L : beq p (cpow p (cadd a b) (S n))
                      (cadd (Csum (fun k => cmul p a (bterm a b n k)) (seq 0 (S n)))
                            (Csum (fun k => cmul p b (bterm a b n k)) (seq 0 (S n))))).
    { replace (cpow p (cadd a b) (S n))
        with (cmul p (cadd a b) (cpow p (cadd a b) n)) by reflexivity.
      apply (beq_trans p _ (cmul p (cadd a b) (Csum (bterm a b n) (seq 0 (S n))))).
      { exact (beq_cmul p Hp1 (cadd a b) (cadd a b) (cpow p (cadd a b) n)
                 (Csum (bterm a b n) (seq 0 (S n))) (beq_refl p _) IH). }
      apply (beq_trans p _
               (Csum (fun k => cmul p (cadd a b) (bterm a b n k)) (seq 0 (S n)))).
      { apply Csum_cmul_l. }
      apply (beq_trans p _
               (Csum (fun k => cadd (cmul p a (bterm a b n k))
                                    (cmul p b (bterm a b n k))) (seq 0 (S n)))).
      { apply beq_Csum. intros k _. ring. }
      apply Csum_add. }
    (* the right side, split by Pascal *)
    assert (R : beq p (Csum (bterm a b (S n)) (seq 0 (S (S n))))
                      (cadd (Csum (fun k => cmul p a (bterm a b n k)) (seq 0 (S n)))
                            (Csum (fun k => cmul p b (bterm a b n k)) (seq 0 (S n))))).
    { apply (beq_trans p _ (cadd (bterm a b (S n) 0)
               (Csum (fun j => bterm a b (S n) (S j)) (seq 0 (S n))))).
      { apply Csum_seq_cons. }
      apply (beq_trans p _ (cadd (cmul p b (bterm a b n 0))
               (Csum (fun j => cadd (cmul p a (bterm a b n j))
                                    (cmul p b (bterm a b n (S j)))) (seq 0 (S n))))).
      { apply beq_cadd; [ apply bterm_first | ].
        apply beq_Csum. intros j Hj. apply in_seq in Hj. apply bterm_split. lia. }
      apply (beq_trans p _ (cadd (cmul p b (bterm a b n 0))
               (cadd (Csum (fun k => cmul p a (bterm a b n k)) (seq 0 (S n)))
                     (Csum (fun j => cmul p b (bterm a b n (S j))) (seq 0 (S n)))))).
      { apply beq_cadd; [ apply beq_refl | apply Csum_add ]. }
      apply (beq_trans p _ (cadd (cmul p b (bterm a b n 0))
               (cadd (Csum (fun k => cmul p a (bterm a b n k)) (seq 0 (S n)))
                     (Csum (fun j => cmul p b (bterm a b n (S j))) (seq 0 n))))).
      { apply beq_cadd; [ apply beq_refl | ].
        apply beq_cadd; [ apply beq_refl | ].
        apply (beq_trans p _
                 (cadd (Csum (fun j => cmul p b (bterm a b n (S j))) (seq 0 n))
                       (cmul p b (bterm a b n (S n))))).
        { apply Csum_seq_snoc. }
        rewrite (bterm_zero a b n (S n) ltac:(lia)). ring. }
      apply (beq_trans p _
               (cadd (Csum (fun k => cmul p a (bterm a b n k)) (seq 0 (S n)))
                     (cadd (cmul p b (bterm a b n 0))
                           (Csum (fun j => cmul p b (bterm a b n (S j))) (seq 0 n))))).
      { ring. }
      apply beq_cadd; [ apply beq_refl | ].
      apply beq_sym. exact (Csum_seq_cons (fun k => cmul p b (bterm a b n k)) n). }
    exact (beq_trans p _ _ _ L (beq_sym p _ _ R)).
Qed.

End Binom.

Print Assumptions binom_absorb.
Print Assumptions prime_dvd_binom.
