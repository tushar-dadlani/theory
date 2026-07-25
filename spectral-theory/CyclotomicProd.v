(* ================================================================= *)
(*  CyclotomicProd.v                                                 *)
(*                                                                    *)
(*  THE CYCLOTOMIC PRODUCT IDENTITY  ∏_{d|n} Φ_d = X^n − 1          *)
(*  (brick 7, culmination), and its consequence Φ_n(a) ∣ a^n − 1.    *)
(*                                                                    *)
(*  Proved by strong induction over ℚ[X]: the proper-divisor factors  *)
(*  Φ_d are pairwise coprime (squarefreeness of X^n−1 + the gcd/      *)
(*  sublist tools), so ∏_{d|n,d<n}Φ_d ∣ X^n−1; the monic-division     *)
(*  remainder is then zero, giving the identity, transferred back to  *)
(*  ℤ at integer arguments.  AXIOM-FREE.                             *)
(* ================================================================= *)

From Stdlib Require Import QArith Qcanon List Lia Arith ZArith Permutation.
Import ListNotations.
Require Import IntPoly PolyDiv PolyDivComp Totient
        QPoly QPolyDiv QPolyDeg QPolyGcd QPolyCoeffPIT QPolyMul QPolyDeriv
        QPolyCoprime QPolyRoot QPolySqfree QPolyEmbed QPolyTransfer
        Cyclotomic QProd QPolyProdDvd.
Open Scope Qc_scope.

Definition Dprod (n : nat) : poly :=
  fold_right (fun d acc => pmul (Phi d) acc) [1%Z] (properdivs n).

(* ----------------------------------------------------------------- *)
(*  eval-congruence + monic helpers                                 *)
(* ----------------------------------------------------------------- *)
Lemma qdivides_ext_r : forall p q1 q2,
  (forall x, qeval q1 x = qeval q2 x) -> qdivides p q1 -> qdivides p q2.
Proof. intros p q1 q2 H [r Hr]; exists r; intro x; rewrite <- H; apply Hr. Qed.

Lemma qdivides_ext_l : forall p1 p2 q,
  (forall x, qeval p1 x = qeval p2 x) -> qdivides p1 q -> qdivides p2 q.
Proof. intros p1 p2 q H [r Hr]; exists r; intro x; rewrite Hr, H; reflexivity. Qed.

Lemma qsqfree_ext : forall M1 M2,
  (forall x, qeval M1 x = qeval M2 x) -> qsqfree M1 -> qsqfree M2.
Proof. intros M1 M2 H HM h [r Hr]; apply HM; exists r; intro x; rewrite H; apply Hr. Qed.

Lemma qcopr_sym : forall A B, qcopr A B -> qcopr B A.
Proof. intros A B H d Hda Hdb; apply H; assumption. Qed.

Lemma qmonic_qnorm_nz : forall g d, qmonic g d -> qnorm g <> [].
Proof.
  intros g d [Hl Hd] Hz; pose proof (qnorm_all_zero g Hz d) as Hc;
    rewrite Hl in Hc; apply qc_one_neq_zero; exact Hc.
Qed.

Lemma qmonic_qdeg : forall g d, qmonic g d -> qdeg g = d.
Proof.
  intros g d [Hl Hd]; assert (qdeg g <= d)%nat by (apply qdegle_qdeg; exact Hd).
  assert (d <= qdeg g)%nat.
  { destruct (le_gt_dec d (qdeg g)) as [Hle | Hgt]; [ exact Hle | ].
    exfalso; assert (qcoeff g d = 0) by (apply (qdegle_above g); exact Hgt).
    rewrite Hl in H0; apply qc_one_neq_zero; exact H0. }
  lia.
Qed.

(* ----------------------------------------------------------------- *)
(*  divisor-list facts                                              *)
(* ----------------------------------------------------------------- *)
Lemma in_divisors_iff : forall m d,
  In d (divisors m) <-> (Nat.divide d m /\ 1 <= d <= m)%nat.
Proof.
  intros m d; unfold divisors; rewrite filter_In, in_seq; split.
  - intros [Hs Hmod]; split; [ apply Nat.Lcm0.mod_divide; apply Nat.eqb_eq; exact Hmod | lia ].
  - intros [Hdvd Hb]; split; [ lia | apply Nat.eqb_eq; apply Nat.Lcm0.mod_divide; exact Hdvd ].
Qed.

Lemma in_properdivs_iff : forall m d,
  In d (properdivs m) <-> (Nat.divide d m /\ 1 <= d < m)%nat.
Proof.
  intros m d; unfold properdivs; rewrite filter_In, in_divisors_iff, Nat.ltb_lt; split.
  - intros [[Hdvd Hb] Hlt]; split; [ exact Hdvd | lia ].
  - intros [Hdvd Hb]; split; [ split; [ exact Hdvd | lia ] | lia ].
Qed.

Lemma divisors_incl_properdivs : forall g i, Nat.divide g i -> (g < i)%nat ->
  incl (divisors g) (properdivs i).
Proof.
  intros g i Hgi Hlt d Hd; rewrite in_divisors_iff in Hd; destruct Hd as [Hdg Hb].
  apply in_properdivs_iff; split; [ apply (Nat.divide_trans d g i Hdg Hgi) | ].
  destruct Hdg as [k Hk]; split; [ lia | ].
  assert (d <= g)%nat by (apply Nat.divide_pos_le; [ lia | exists k; exact Hk ]); lia.
Qed.

Lemma properdivs_nodup : forall n, NoDup (properdivs n).
Proof. intro n; apply NoDup_filter, divisors_nodup. Qed.

(* ----------------------------------------------------------------- *)
(*  emb transfers for Dprod                                          *)
(* ----------------------------------------------------------------- *)
Lemma qcoeff_emb : forall p i, qcoeff (emb p) i = Z2Qc (coeff p i).
Proof.
  intros p i; unfold qcoeff, coeff, emb.
  replace (0%Qc) with (Z2Qc 0%Z) at 1 by apply Z2Qc_0.
  rewrite map_nth; reflexivity.
Qed.

Lemma emb_degle : forall p k, degle p k -> qdegle (emb p) k.
Proof. intros p k H i Hi; rewrite qcoeff_emb, (H i Hi); apply Z2Qc_0. Qed.

Lemma emb_monic : forall p d, monic p d -> qmonic (emb p) d.
Proof.
  intros p d [Hl Hd]; split; [ rewrite qcoeff_emb, Hl; apply Z2Qc_1 | apply emb_degle; exact Hd ].
Qed.

Lemma emb_Dprod : forall n x, qeval (emb (Dprod n)) x = qeval (qprod (properdivs n)) x.
Proof.
  intros n x; unfold Dprod; generalize (properdivs n) as l; intro l.
  induction l as [|a l IH]; [ reflexivity | ].
  cbn [fold_right]; rewrite emb_pmul, qeval_mul, IH, <- qeval_qprod_cons; reflexivity.
Qed.

Lemma Dprod_monic : forall n, (1 <= n)%nat -> monic (Dprod n) (n - phi n).
Proof.
  intros n Hn; unfold Dprod.
  replace (n - phi n)%nat
    with (fold_right (fun d acc => (phi d + acc)%nat) 0%nat (properdivs n))
    by (rewrite fold_phi_sum, sum_properdivs_phi by lia; reflexivity).
  apply monic_fold_pmul; intros d Hd; apply cyclotomic_monic; apply (properdivs_ge1 n d Hd).
Qed.

Lemma Phi_eq : forall m,
  Phi (S (S m)) = fst (pdivmod (S (S m)) (Xn1 (S (S m))) (Dprod (S (S m)))
                        (S (S m) - phi (S (S m)))).
Proof.
  intro m; unfold Phi; rewrite (Phi_f_SS (S m) m); f_equal; f_equal.
  unfold Dprod; apply fold_pmul_ext; intros d Hd.
  pose proof (properdivs_lt _ _ Hd) as Hlt.
  unfold Phi; rewrite (Phi_f_indep d (S m) ltac:(lia)); reflexivity.
Qed.

(* Φ_d divides X^d − 1, given the identity holds at d *)
Lemma Phi_dvd_own : forall d, (1 <= d)%nat ->
  (forall x, qeval (qXn1 d) x = qeval (qprod (divisors d)) x) ->
  qdivides (emb (Phi d)) (qXn1 d).
Proof.
  intros d Hd Hid.
  apply (qdivides_ext_r (emb (Phi d)) (qprod (divisors d)) (qXn1 d));
    [ intro y; symmetry; apply Hid | ].
  apply qdivides_qprod_in, in_divisors_iff; split; [ apply Nat.divide_refl | lia ].
Qed.

(* ================================================================= *)
(*  THE PRODUCT IDENTITY, over ℚ, by strong induction               *)
(* ================================================================= *)
Theorem cyclotomic_prod : forall n, (1 <= n)%nat ->
  forall x, qeval (qXn1 n) x = qeval (qprod (divisors n)) x.
Proof.
  intro n; induction n as [n IH] using lt_wf_ind; intros Hn x.
  destruct n as [|[|m]].
  - lia.
  - change (divisors 1) with [1%nat]; rewrite qeval_qprod_cons, qeval_qprod_nil.
    change (Phi 1) with (Xn1 1); rewrite emb_Xn1; ring.
  - set (N := S (S m)) in *.
    assert (Heach : forall d, In d (properdivs N) -> qdivides (emb (Phi d)) (qXn1 N)).
    { intros d Hd; pose proof (properdivs_lt _ _ Hd) as Hlt;
        pose proof (properdivs_ge1 _ _ Hd) as Hge.
      apply in_properdivs_iff in Hd; destruct Hd as [Hdvd _].
      apply (qdivides_trans (emb (Phi d)) (qXn1 d) (qXn1 N)).
      - apply Phi_dvd_own; [ lia | intro y; apply (IH d Hlt Hge y) ].
      - apply qXn1_dvd; exact Hdvd. }
    (* coprimality helper for the smaller-index factorisation *)
    assert (Hhalf : forall i j, In i (properdivs N) -> (Nat.gcd i j < i)%nat ->
                      (1 <= j)%nat -> (j < N)%nat -> Nat.divide (Nat.gcd i j) j ->
                      qcopr (emb (Phi i)) (emb (Phi j))).
    { intros i j Hi Hglt Hj1 HjN Hgj h Hhi Hhj.
      pose proof (properdivs_lt _ _ Hi) as HiN; pose proof (properdivs_ge1 _ _ Hi) as Hi1.
      assert (Hidvd : Nat.divide i N) by (apply in_properdivs_iff in Hi; tauto).
      set (g := Nat.gcd i j).
      assert (Hg1 : (1 <= g)%nat)
        by (unfold g; destruct (Nat.gcd i j) eqn:E; [ apply Nat.gcd_eq_0 in E; lia | lia ]).
      assert (Hgi : Nat.divide g i) by (unfold g; apply Nat.gcd_divide_l).
      assert (HXi : forall y, qeval (qXn1 i) y = qeval (emb (Phi i)) y * qeval (emb (Dprod i)) y).
      { intro y; rewrite (IH i HiN Hi1 y),
          (qprod_perm _ _ (divisors_perm i Hi1) y), qeval_qprod_cons, emb_Dprod; reflexivity. }
      assert (Hcopi : qcopr (emb (Phi i)) (emb (Dprod i))).
      { apply qsqfree_mul_copr.
        - apply (qsqfree_ext (qXn1 i) (qmul (emb (Phi i)) (emb (Dprod i))));
            [ intro y; rewrite HXi, qeval_mul; reflexivity | apply qsqfree_Xn1; lia ].
        - apply (qmonic_qnorm_nz _ (phi i)); apply emb_monic, cyclotomic_monic; lia.
        - apply (qmonic_qnorm_nz _ (i - phi i)); apply emb_monic, Dprod_monic; lia. }
      assert (HhXg : qdivides h (qXn1 g)).
      { apply (qdiv_gcd h i j).
        - apply (qdivides_trans h (emb (Phi i)) (qXn1 i));
            [ exact Hhi | apply Phi_dvd_own; [ lia | intro y; apply (IH i HiN Hi1 y) ] ].
        - apply (qdivides_trans h (emb (Phi j)) (qXn1 j));
            [ exact Hhj | apply Phi_dvd_own; [ lia | intro y; apply (IH j HjN Hj1 y) ] ]. }
      assert (HXgDi : qdivides (qXn1 g) (emb (Dprod i))).
      { apply (qdivides_ext_r (qXn1 g) (qprod (properdivs i)) (emb (Dprod i)));
          [ intro y; symmetry; apply emb_Dprod | ].
        apply (qdivides_ext_l (qprod (divisors g)) (qXn1 g) (qprod (properdivs i)));
          [ intro y; symmetry; apply (IH g ltac:(lia) Hg1 y) | ].
        apply qdivides_qprod_incl;
          [ apply divisors_incl_properdivs; assumption | apply divisors_nodup | apply properdivs_nodup ]. }
      apply (Hcopi h Hhi (qdivides_trans h (qXn1 g) (emb (Dprod i)) HhXg HXgDi)). }
    assert (Hcop : forall i j, In i (properdivs N) -> In j (properdivs N) -> i <> j ->
                   qcopr (emb (Phi i)) (emb (Phi j))).
    { intros i j Hi Hj Hne.
      pose proof (properdivs_lt _ _ Hi) as HiN; pose proof (properdivs_ge1 _ _ Hi) as Hi1.
      pose proof (properdivs_lt _ _ Hj) as HjN; pose proof (properdivs_ge1 _ _ Hj) as Hj1.
      assert (Hle : (Nat.gcd i j <= i)%nat)
        by (apply Nat.divide_pos_le; [ lia | apply Nat.gcd_divide_l ]).
      destruct (Nat.eq_dec (Nat.gcd i j) i) as [Hgi | Hgi].
      - (* gcd = i ⟹ i | j, i < j : symmetric argument on j *)
        apply qcopr_sym; apply (Hhalf j i Hj).
        + rewrite Nat.gcd_comm, Hgi.
          assert (Nat.divide i j) by (rewrite <- Hgi; apply Nat.gcd_divide_r).
          assert (i <= j)%nat by (apply Nat.divide_pos_le; [ lia | assumption ]); lia.
        + exact Hi1.
        + exact HiN.
        + rewrite Nat.gcd_comm; apply Nat.gcd_divide_l.
      - apply (Hhalf i j Hi ltac:(lia) Hj1 HjN (Nat.gcd_divide_r i j)). }
    (* Dprod_N ∣ X^N − 1 over ℚ *)
    assert (HDdvd : qdivides (emb (Dprod N)) (qXn1 N)).
    { apply (qdivides_ext_l (qprod (properdivs N)) (emb (Dprod N)));
        [ intro y; symmetry; apply emb_Dprod | ].
      apply qprod_dvd; [ apply properdivs_nodup | exact Heach | exact Hcop ]. }
    (* the ℤ pdivmod decomposition *)
    assert (Hd1 : (1 <= N - phi N)%nat) by (pose proof (phi_lt N ltac:(lia)); lia).
    pose proof (pdivmod_spec (Dprod N) (N - phi N) Hd1 (Dprod_monic N ltac:(lia))
                  N (Xn1 N) (proj2 (monic_Xn1 N ltac:(lia)))) as [Hev [Hrdeg _]].
    pose proof (Phi_eq m) as HPeq; fold N in HPeq; rewrite <- HPeq in Hev.
    set (R := snd (pdivmod N (Xn1 N) (Dprod N) (N - phi N))) in *.
    (* embedded decomposition holds for all y *)
    assert (Hemb : forall y, qeval (qXn1 N) y
                   = qeval (emb (Phi N)) y * qeval (emb (Dprod N)) y + qeval (emb R) y).
    { intro y.
      transitivity (qeval (qadd (qmul (emb (Phi N)) (emb (Dprod N))) (emb R)) y);
        [ | rewrite qeval_add, qeval_mul; reflexivity ].
      rewrite <- (emb_Xn1 N); revert y; apply qeval_ext_Z; intro a.
      rewrite qeval_add, qeval_mul, !qeval_emb, <- Z2Qc_mul, <- Z2Qc_add, (Hev a); reflexivity. }
    (* the remainder vanishes *)
    assert (HembR : forall y, qeval (emb R) y = 0).
    { apply qeval_qnorm_nil; apply (qdiv_deg_zero (emb (Dprod N)) (emb R)).
      - rewrite (qmonic_qdeg _ (N - phi N)); [ lia | apply emb_monic, Dprod_monic; lia ].
      - destruct HDdvd as [Q HQ]; exists (qsub Q (emb (Phi N))); intro y.
        rewrite qeval_sub; specialize (HQ y); specialize (Hemb y); rewrite Hemb in HQ.
        transitivity (qeval (emb (Dprod N)) y * qeval Q y
                      - qeval (emb (Phi N)) y * qeval (emb (Dprod N)) y);
          [ rewrite <- HQ; ring | ring ].
      - rewrite (qmonic_qdeg _ (N - phi N)); [ apply emb_degle; exact Hrdeg
                                             | apply emb_monic, Dprod_monic; lia ]. }
    rewrite (qprod_perm _ _ (divisors_perm N ltac:(lia)) x), qeval_qprod_cons, <- (emb_Dprod N x).
    rewrite (Hemb x), (HembR x); ring.
Qed.

(* ================================================================= *)
(*  Consequences over ℤ                                             *)
(* ================================================================= *)
Theorem cyclotomic_prod_Z : forall n, (1 <= n)%nat ->
  forall a : Z, eval (Xn1 n) a = (eval (Phi n) a * eval (Dprod n) a)%Z.
Proof.
  intros n Hn a; apply Z2Qc_inj.
  rewrite <- (qeval_emb (Xn1 n) a), emb_Xn1, (cyclotomic_prod n Hn (Z2Qc a)).
  rewrite (qprod_perm _ _ (divisors_perm n Hn) (Z2Qc a)), qeval_qprod_cons, <- (emb_Dprod n).
  rewrite Z2Qc_mul, <- !(qeval_emb); reflexivity.
Qed.

Theorem Phi_dvd_Xn1 : forall n, (1 <= n)%nat ->
  forall a : Z, (eval (Phi n) a | eval (Xn1 n) a)%Z.
Proof.
  intros n Hn a; exists (eval (Dprod n) a).
  rewrite (cyclotomic_prod_Z n Hn a); ring.
Qed.

Corollary Phi_dvd_pow : forall n, (1 <= n)%nat ->
  forall a : Z, (eval (Phi n) a | a ^ Z.of_nat n - 1)%Z.
Proof.
  intros n Hn a; rewrite <- (eval_Xn1 n a); apply Phi_dvd_Xn1; exact Hn.
Qed.

Print Assumptions Phi_dvd_pow.

(* ================================================================= *)
(*  END CyclotomicProd.v                                             *)
(*  ∏_{d|n} Φ_d = X^n − 1; hence Φ_n(a) ∣ a^n − 1.  Closed under the  *)
(*  global context (axiom-free).                                     *)
(* ================================================================= *)
