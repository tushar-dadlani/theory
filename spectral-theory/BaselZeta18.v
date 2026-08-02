(* ================================================================= *)
(*  BaselZeta18.v  —  the eighteenth-power cotangent sum, toward ζ(18).*)
(*  Sigma cot^18 = closed poly / 194896477400625,                     *)
(*  zeta(18) = 43867*pi^18/38979295480125.  Vieta ladder extended to   *)
(*  the NINTH symmetric function e9 (Newton p9, 31 terms; PFR_tenth    *)
(*  with sign (-1)^9 = -).  Axiom-clean.                               *)
(* ================================================================= *)

From Stdlib Require Import Reals List Lia Lra Factorial Binomial ZArith.
Import ListNotations.
Require Import BaselVieta BaselCotPoly BaselZeta4 BaselZeta6 BaselZeta8 BaselZeta10 BaselZeta12 BaselZeta14 BaselZeta16 BaselZeta18Poly.
Open Scope R_scope.

Fixpoint e9 (rs : list R) : R :=
  match rs with
  | [] => 0
  | r :: p => e9 p + r * e8 p
  end.

Lemma newton9 : forall rs,
  fold_right Rplus 0 (map (fun r => r * r * r * r * r * r * r * r * r) rs)
  = (fold_right Rplus 0 rs)^9
    - 9*(fold_right Rplus 0 rs)^7*(e2 rs)
    + 27*(fold_right Rplus 0 rs)^5*(e2 rs)^2
    + 9*(fold_right Rplus 0 rs)^6*(e3 rs)
    - 30*(fold_right Rplus 0 rs)^3*(e2 rs)^3
    - 45*(fold_right Rplus 0 rs)^4*(e2 rs)*(e3 rs)
    - 9*(fold_right Rplus 0 rs)^5*(e4 rs)
    + 9*(fold_right Rplus 0 rs)*(e2 rs)^4
    + 54*(fold_right Rplus 0 rs)^2*(e2 rs)^2*(e3 rs)
    + 18*(fold_right Rplus 0 rs)^3*(e3 rs)^2
    + 36*(fold_right Rplus 0 rs)^3*(e2 rs)*(e4 rs)
    + 9*(fold_right Rplus 0 rs)^4*(e5 rs)
    - 9*(e2 rs)^3*(e3 rs)
    - 27*(fold_right Rplus 0 rs)*(e2 rs)*(e3 rs)^2
    - 27*(fold_right Rplus 0 rs)*(e2 rs)^2*(e4 rs)
    - 27*(fold_right Rplus 0 rs)^2*(e3 rs)*(e4 rs)
    - 27*(fold_right Rplus 0 rs)^2*(e2 rs)*(e5 rs)
    - 9*(fold_right Rplus 0 rs)^3*(e6 rs)
    + 3*(e3 rs)^3
    + 18*(e2 rs)*(e3 rs)*(e4 rs)
    + 9*(e2 rs)^2*(e5 rs)
    + 9*(fold_right Rplus 0 rs)*(e4 rs)^2
    + 18*(fold_right Rplus 0 rs)*(e3 rs)*(e5 rs)
    + 18*(fold_right Rplus 0 rs)*(e2 rs)*(e6 rs)
    + 9*(fold_right Rplus 0 rs)^2*(e7 rs)
    - 9*(e4 rs)*(e5 rs)
    - 9*(e3 rs)*(e6 rs)
    - 9*(e2 rs)*(e7 rs)
    - 9*(fold_right Rplus 0 rs)*(e8 rs)
    + 9*(e9 rs).
Proof.
  induction rs as [| r p IH]; cbn [fold_right map e2 e3 e4 e5 e6 e7 e8 e9]; [ ring | ].
  rewrite IH; ring.
Qed.

Lemma PFR_tenth : forall rs, (9 <= length rs)%nat ->
  nth (pred (pred (pred (pred (pred (pred (pred (pred (pred (length rs)))))))))) (PFR rs) 0 = - e9 rs.
Proof.
  induction rs as [| r0 rs IH]; intro Hlen; [ cbn in Hlen; lia | ].
  destruct rs as [| r1 rs']; [ cbn in Hlen; lia | ].
  destruct rs' as [| r2 rs'']; [ cbn in Hlen; lia | ].
  destruct rs'' as [| r3 rs''']; [ cbn in Hlen; lia | ].
  destruct rs''' as [| r4 rs'''']; [ cbn in Hlen; lia | ].
  destruct rs'''' as [| r5 rs''''']; [ cbn in Hlen; lia | ].
  destruct rs''''' as [| r6 rs'''''']; [ cbn in Hlen; lia | ].
  destruct rs'''''' as [| r7 rs''''''']; [ cbn in Hlen; lia | ].
  destruct rs''''''' as [| r8 rs'''''''']; [ cbn in Hlen; lia | ].
  destruct rs'''''''' as [| r9 rs'''''''''].
  - cbn [PFR length pred nth Xsub Padd Pscale map fold_right e2 e3 e4 e5 e6 e7 e8 e9]; ring.
  - change (PFR (r0 :: r1 :: r2 :: r3 :: r4 :: r5 :: r6 :: r7 :: r8 :: r9 :: rs'''''''''))
      with (Xsub r0 (PFR (r1 :: r2 :: r3 :: r4 :: r5 :: r6 :: r7 :: r8 :: r9 :: rs'''''''''))).
    cbn [length pred].
    unfold Xsub; rewrite nth_Padd, nth_Pscale.
    change (nth (S (length rs''''''''')) (0 :: PFR (r1 :: r2 :: r3 :: r4 :: r5 :: r6 :: r7 :: r8 :: r9 :: rs''''''''')) 0)
      with (nth (length rs''''''''') (PFR (r1 :: r2 :: r3 :: r4 :: r5 :: r6 :: r7 :: r8 :: r9 :: rs''''''''')) 0).
    pose proof (IH ltac:(cbn [length]; lia)) as HIH; cbn [length pred] in HIH.
    pose proof (PFR_ninth (r1 :: r2 :: r3 :: r4 :: r5 :: r6 :: r7 :: r8 :: r9 :: rs''''''''') ltac:(cbn [length]; lia)) as HPF;
      cbn [length pred] in HPF.
    rewrite HIH, HPF.
    change (e9 (r0 :: r1 :: r2 :: r3 :: r4 :: r5 :: r6 :: r7 :: r8 :: r9 :: rs'''''''''))
      with (e9 (r1 :: r2 :: r3 :: r4 :: r5 :: r6 :: r7 :: r8 :: r9 :: rs''''''''') + r0 * e8 (r1 :: r2 :: r3 :: r4 :: r5 :: r6 :: r7 :: r8 :: r9 :: rs''''''''')).
    ring.
Qed.

Lemma Plist_tenth : forall m, (9 <= m)%nat ->
  nth (pred (pred (pred (pred (pred (pred (pred (pred (pred m))))))))) (Plist m) 0 = - Binomial.C (2 * m + 1) 19.
Proof.
  intros m Hm; unfold Plist.
  set (g := fun i => (-1) ^ (m - i) * Binomial.C (2 * m + 1) (2 * (m - i) + 1)).
  rewrite (@nth_indep R (map g (seq 0 (S m))) (pred (pred (pred (pred (pred (pred (pred (pred (pred m))))))))) 0 (g 0%nat))
    by (rewrite length_map, length_seq; lia).
  rewrite (map_nth g (seq 0 (S m)) 0%nat (pred (pred (pred (pred (pred (pred (pred (pred (pred m)))))))))), seq_nth by lia.
  cbn [Nat.add]. unfold g. replace (m - pred (pred (pred (pred (pred (pred (pred (pred (pred m)))))))))%nat with 9%nat by lia.
  cbn [pow]. change (2 * 9 + 1)%nat with 19%nat. ring.
Qed.

Lemma fact_down18 : forall m, (9 <= m)%nat ->
  fact (2 * m)
  = ((2*m) * (2*m-1) * (2*m-2) * (2*m-3) * (2*m-4) * (2*m-5) * (2*m-6) * (2*m-7) * (2*m-8) * (2*m-9) * (2*m-10) * (2*m-11) * (2*m-12) * (2*m-13) * (2*m-14) * (2*m-15) * (2*m-16) * (2*m-17) * fact (2*m-18)) %nat.
Proof.
  intros m Hm; replace (2 * m)%nat with (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (2*m-18))))))))))))))))))) by lia.
  cbn [fact].
  replace (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (2*m-18))))))))))))))))))-1)%nat with (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (2*m-18))))))))))))))))))%nat by lia.
  replace (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (2*m-18))))))))))))))))))-2)%nat with (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (2*m-18)))))))))))))))))%nat by lia.
  replace (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (2*m-18))))))))))))))))))-3)%nat with (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (2*m-18))))))))))))))))%nat by lia.
  replace (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (2*m-18))))))))))))))))))-4)%nat with (S (S (S (S (S (S (S (S (S (S (S (S (S (S (2*m-18)))))))))))))))%nat by lia.
  replace (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (2*m-18))))))))))))))))))-5)%nat with (S (S (S (S (S (S (S (S (S (S (S (S (S (2*m-18))))))))))))))%nat by lia.
  replace (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (2*m-18))))))))))))))))))-6)%nat with (S (S (S (S (S (S (S (S (S (S (S (S (2*m-18)))))))))))))%nat by lia.
  replace (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (2*m-18))))))))))))))))))-7)%nat with (S (S (S (S (S (S (S (S (S (S (S (2*m-18))))))))))))%nat by lia.
  replace (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (2*m-18))))))))))))))))))-8)%nat with (S (S (S (S (S (S (S (S (S (S (2*m-18)))))))))))%nat by lia.
  replace (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (2*m-18))))))))))))))))))-9)%nat with (S (S (S (S (S (S (S (S (S (2*m-18))))))))))%nat by lia.
  replace (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (2*m-18))))))))))))))))))-10)%nat with (S (S (S (S (S (S (S (S (2*m-18)))))))))%nat by lia.
  replace (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (2*m-18))))))))))))))))))-11)%nat with (S (S (S (S (S (S (S (2*m-18))))))))%nat by lia.
  replace (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (2*m-18))))))))))))))))))-12)%nat with (S (S (S (S (S (S (2*m-18)))))))%nat by lia.
  replace (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (2*m-18))))))))))))))))))-13)%nat with (S (S (S (S (S (2*m-18))))))%nat by lia.
  replace (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (2*m-18))))))))))))))))))-14)%nat with (S (S (S (S (2*m-18)))))%nat by lia.
  replace (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (2*m-18))))))))))))))))))-15)%nat with (S (S (S (2*m-18))))%nat by lia.
  replace (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (2*m-18))))))))))))))))))-16)%nat with (S (S (2*m-18)))%nat by lia.
  replace (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (2*m-18))))))))))))))))))-17)%nat with (S (2*m-18))%nat by lia.
  replace (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (2*m-18))))))))))))))))))-18)%nat with (2*m-18)%nat by lia.
  cbn [fact]; ring.
Qed.

Lemma C_ratio19 : forall m, (9 <= m)%nat ->
  Binomial.C (2 * m + 1) 19 / Binomial.C (2 * m + 1) 1
  = (2*INR m)*(2*INR m-1)*(2*INR m-2)*(2*INR m-3)*(2*INR m-4)*(2*INR m-5)*(2*INR m-6)*(2*INR m-7)*(2*INR m-8)*(2*INR m-9)*(2*INR m-10)*(2*INR m-11)*(2*INR m-12)*(2*INR m-13)*(2*INR m-14)*(2*INR m-15)*(2*INR m-16)*(2*INR m-17) / 121645100408832000.
Proof.
  intros m Hm.
  assert (Hmpos : 9 <= INR m) by (replace 9 with (INR 9) by (simpl; ring); apply le_INR; lia).
  remember (2 * INR m * (2 * INR m - 1) * (2 * INR m - 2) * (2 * INR m - 3) * (2 * INR m - 4) * (2 * INR m - 5) * (2 * INR m - 6) * (2 * INR m - 7) * (2 * INR m - 8) * (2 * INR m - 9) * (2 * INR m - 10) * (2 * INR m - 11) * (2 * INR m - 12) * (2 * INR m - 13) * (2 * INR m - 14) * (2 * INR m - 15) * (2 * INR m - 16) * (2 * INR m - 17)) as P eqn:HP.
  assert (HPne : P <> 0)
    by (rewrite HP; apply Rgt_not_eq; repeat apply Rmult_lt_0_compat; lra).
  assert (Hstep : INR (fact (2 * m)) = P * INR (fact (2 * m - 18))).
  { rewrite HP, (fact_down18 m Hm), !mult_INR, !minus_INR by lia.
    replace (INR (2 * m)) with (2 * INR m) by (rewrite mult_INR; simpl (INR 2); ring).
    replace (INR 1) with 1 by (simpl; ring);
    replace (INR 2) with 2 by (simpl; ring);
    replace (INR 3) with 3 by (simpl; ring);
    replace (INR 4) with 4 by (simpl; ring);
    replace (INR 5) with 5 by (simpl; ring);
    replace (INR 6) with 6 by (simpl; ring);
    replace (INR 7) with 7 by (simpl; ring);
    replace (INR 8) with 8 by (simpl; ring);
    replace (INR 9) with 9 by (simpl; ring);
    replace (INR 10) with 10 by (simpl; ring);
    replace (INR 11) with 11 by (simpl; ring);
    replace (INR 12) with 12 by (simpl; ring);
    replace (INR 13) with 13 by (simpl; ring);
    replace (INR 14) with 14 by (simpl; ring);
    replace (INR 15) with 15 by (simpl; ring);
    replace (INR 16) with 16 by (simpl; ring);
    replace (INR 17) with 17 by (simpl; ring).
    ring. }
  unfold Binomial.C.
  replace (2 * m + 1 - 1)%nat with (2 * m)%nat by lia.
  replace (2 * m + 1 - 19)%nat with (2 * m - 18)%nat by lia.
  assert (Hf1 : INR (fact 1) = 1) by (simpl; ring).
  assert (Hf19 : INR (fact 19) = 121645100408832000)
    by (cbn [fact]; rewrite !mult_INR, !INR_IZR_INZ, <- !mult_IZR; f_equal).
  rewrite Hf1, Hf19, Hstep.
  field; repeat split; try apply INR_fact_neq_0; try exact HPne.
Qed.

Lemma cot_e9 : forall m, (9 <= m)%nat ->
  e9 (map (fun k => Rcot (theta m k) ^ 2) (seq 1 m))
  = (2*INR m)*(2*INR m-1)*(2*INR m-2)*(2*INR m-3)*(2*INR m-4)*(2*INR m-5)*(2*INR m-6)*(2*INR m-7)*(2*INR m-8)*(2*INR m-9)*(2*INR m-10)*(2*INR m-11)*(2*INR m-12)*(2*INR m-13)*(2*INR m-14)*(2*INR m-15)*(2*INR m-16)*(2*INR m-17) / 121645100408832000.
Proof.
  intros m Hm.
  set (rs := map (fun k => Rcot (theta m k) ^ 2) (seq 1 m)).
  assert (Hlen_rs : length rs = m) by (unfold rs; rewrite length_map, length_seq; reflexivity).
  assert (Hnd : NoDup rs).
  { unfold rs; apply NoDup_map_inj; [ | apply seq_NoDup ].
    intros a b Ha Hb Heq; apply in_seq in Ha; apply in_seq in Hb;
      apply (rsq_inj m a b); [ lia | lia | lia | lia | exact Heq ]. }
  assert (Hne : rs <> [])
    by (unfold rs; intro HH; apply (f_equal (@length R)) in HH;
        rewrite length_map, length_seq in HH; cbn in HH; lia).
  assert (Hroots : forall r, In r rs -> Peval (Plist m) r = 0).
  { intros r Hr; unfold rs in Hr; apply in_map_iff in Hr; destruct Hr as [k [Hk Hink]].
    apply in_seq in Hink; subst r; rewrite Peval_Plist; apply root_of; lia. }
  assert (Hlead : nth (length rs) (Plist m) 0 <> 0)
    by (rewrite Hlen_rs, Plist_leading, C_n_1 by lia; apply not_0_INR; lia).
  assert (Hpl : length (Plist m) = S (length rs)) by (rewrite Plist_length, Hlen_rs; reflexivity).
  pose proof (vieta_coeff (Plist m) rs (pred (pred (pred (pred (pred (pred (pred (pred (pred (length rs)))))))))) Hpl Hne Hnd Hroots Hlead) as HV.
  rewrite (PFR_tenth rs ltac:(rewrite Hlen_rs; lia)) in HV.
  rewrite Hlen_rs in HV.
  rewrite (Plist_tenth m Hm), (Plist_leading m), (C_n_1 (2 * m + 1) ltac:(lia)) in HV.
  fold rs.
  assert (Hne1 : INR (2 * m + 1) <> 0) by (apply not_0_INR; lia).
  pose proof (C_ratio19 m Hm) as HC19; rewrite (C_n_1 (2 * m + 1) ltac:(lia)) in HC19.
  replace (INR (2 * m + 1) * - e9 rs) with (- (INR (2 * m + 1) * e9 rs)) in HV by ring.
  assert (HV' : INR (2 * m + 1) * e9 rs = Binomial.C (2 * m + 1) 19) by lra.
  apply (Rmult_eq_reg_l (INR (2 * m + 1))); [ | exact Hne1 ].
  rewrite <- HC19; replace (INR (2 * m + 1) * (Binomial.C (2 * m + 1) 19 / INR (2 * m + 1)))
    with (Binomial.C (2 * m + 1) 19) by (field; exact Hne1).
  exact HV'.
Qed.

Lemma cot_e9_exp : forall m, (9 <= m)%nat ->
  e9 (map (fun k => Rcot (theta m k) ^ 2) (seq 1 m))
  = (262144*INR m^18 - 20054016*INR m^17 + 708575232*INR m^16 - 15341322240*INR m^15 + 227681599488*INR m^14 - 2454739402752*INR m^13 + 19878800441344*INR m^12 - 123295117271040*INR m^11 + 591795092308992*INR m^10 - 2205749914587648*INR m^9 + 6367192396271616*INR m^8 - 14109243671577600*INR m^7 + 23616809551000576*INR m^6 - 29097596987011584*INR m^5 + 25333023611639808*INR m^4 - 14572819556997120*INR m^3 + 4893622362316800*INR m^2 - 711374856192000*INR m) / 121645100408832000.
Proof. intros m Hm; rewrite (cot_e9 m Hm); unfold Rdiv; apply Rmult_eq_compat_r; ring. Qed.

Theorem cot18_sum : forall m, (9 <= m)%nat ->
  sum_f_R0 (fun k => Rcot (INR (S k) * PI / INR (2 * m + 1)) ^ 18) (m - 1)
  = (57497354240 * INR m ^ 18 + 517476188160 * INR m ^ 17 + 1348049829888 * INR m ^ 16 - 945061625856 * INR m ^ 15 - 8729222676480 * INR m ^ 14 - 3512869355520 * INR m ^ 13 + 27870040670208 * INR m ^ 12 + 17404258222080 * INR m ^ 11 - 63854225021952 * INR m ^ 10 - 30585496898560 * INR m ^ 9 + 114647373646848 * INR m ^ 8 + 11944485550080 * INR m ^ 7 - 151382565118080 * INR m ^ 6 + 58945806642816 * INR m ^ 5 + 114858861928128 * INR m ^ 4 - 140954177203200 * INR m ^ 3 + 62637378970950 * INR m ^ 2 - 10257709336875 * INR m) / 194896477400625.
Proof.
  intros m Hm.
  transitivity (fold_right Rplus 0
                  (map (fun r => r * r * r * r * r * r * r * r * r) (map (fun k => Rcot (theta m k) ^ 2) (seq 1 m)))).
  - rewrite map_map.
    rewrite (fold_right_map_seq
               (fun k => Rcot (theta m k) ^ 2 * (Rcot (theta m k) ^ 2) * (Rcot (theta m k) ^ 2)
                         * (Rcot (theta m k) ^ 2) * (Rcot (theta m k) ^ 2) * (Rcot (theta m k) ^ 2)
                         * (Rcot (theta m k) ^ 2) * (Rcot (theta m k) ^ 2) * (Rcot (theta m k) ^ 2)) m ltac:(lia)).
    apply sum_eq; intros k _; unfold theta; ring.
  - rewrite newton9, (cot_e2_exp m ltac:(lia)), (cot_e3_exp m ltac:(lia)), (cot_e4_exp m ltac:(lia)),
      (cot_e5_exp m ltac:(lia)), (cot_e6_exp m ltac:(lia)), (cot_e7_exp m ltac:(lia)),
      (cot_e8_exp m ltac:(lia)), (cot_e9_exp m Hm).
    replace (fold_right Rplus 0 (map (fun k => Rcot (theta m k) ^ 2) (seq 1 m)))
      with (INR m * (2 * INR m - 1) / 3).
    2:{ rewrite (fold_right_map_seq (fun k => Rcot (theta m k) ^ 2) m ltac:(lia)).
        rewrite <- (cot_sq_sum m ltac:(lia)); apply sum_eq; intros k _; unfold theta; reflexivity. }
    exact (cot18_poly_id (INR m)).
Qed.

Print Assumptions cot18_sum.
