(* ================================================================= *)
(*  BaselZeta16.v  —  the sixteenth-power cotangent sum, toward ζ(16). *)
(*                                                                    *)
(*  Σcot¹⁶(kπ/(2m+1)) = closed poly / 488462349375, with ζ(16) =       *)
(*  3617·π¹⁶/325641566250 (3617 = numerator of B₁₆).  Vieta ladder     *)
(*  extended to the EIGHTH symmetric function e₈ (Newton p₈, 22 terms; *)
(*  PFR_ninth with sign (−1)⁸ = +).  Axiom-clean.  Performance notes   *)
(*  as in BaselZeta12.v: C_ratio17 keeps the 16-factor product opaque  *)
(*  and evaluates INR(fact 17) symbolically; cot16_sum closes by       *)
(*  [exact] against BaselZeta16Poly.                                  *)
(* ================================================================= *)

From Stdlib Require Import Reals List Lia Lra Factorial Binomial ZArith.
Import ListNotations.
Require Import BaselVieta BaselCotPoly BaselZeta4 BaselZeta6 BaselZeta8 BaselZeta10 BaselZeta12 BaselZeta14 BaselZeta16Poly.
Open Scope R_scope.

Fixpoint e8 (rs : list R) : R :=
  match rs with
  | [] => 0
  | r :: p => e8 p + r * e7 p
  end.

Lemma newton8 : forall rs,
  fold_right Rplus 0 (map (fun r => r * r * r * r * r * r * r * r) rs)
  = (fold_right Rplus 0 rs)^8
    - 8*(fold_right Rplus 0 rs)^6*(e2 rs)
    + 20*(fold_right Rplus 0 rs)^4*(e2 rs)^2
    + 8*(fold_right Rplus 0 rs)^5*(e3 rs)
    - 16*(fold_right Rplus 0 rs)^2*(e2 rs)^3
    - 32*(fold_right Rplus 0 rs)^3*(e2 rs)*(e3 rs)
    - 8*(fold_right Rplus 0 rs)^4*(e4 rs)
    + 2*(e2 rs)^4
    + 24*(fold_right Rplus 0 rs)*(e2 rs)^2*(e3 rs)
    + 12*(fold_right Rplus 0 rs)^2*(e3 rs)^2
    + 24*(fold_right Rplus 0 rs)^2*(e2 rs)*(e4 rs)
    + 8*(fold_right Rplus 0 rs)^3*(e5 rs)
    - 8*(e2 rs)*(e3 rs)^2
    - 8*(e2 rs)^2*(e4 rs)
    - 16*(fold_right Rplus 0 rs)*(e3 rs)*(e4 rs)
    - 16*(fold_right Rplus 0 rs)*(e2 rs)*(e5 rs)
    - 8*(fold_right Rplus 0 rs)^2*(e6 rs)
    + 4*(e4 rs)^2
    + 8*(e3 rs)*(e5 rs)
    + 8*(e2 rs)*(e6 rs)
    + 8*(fold_right Rplus 0 rs)*(e7 rs)
    - 8*(e8 rs).
Proof.
  induction rs as [| r p IH]; cbn [fold_right map e2 e3 e4 e5 e6 e7 e8]; [ ring | ].
  rewrite IH; ring.
Qed.

Lemma PFR_ninth : forall rs, (8 <= length rs)%nat ->
  nth (pred (pred (pred (pred (pred (pred (pred (pred (length rs))))))))) (PFR rs) 0 = e8 rs.
Proof.
  induction rs as [| r0 rs IH]; intro Hlen; [ cbn in Hlen; lia | ].
  destruct rs as [| r1 rs']; [ cbn in Hlen; lia | ].
  destruct rs' as [| r2 rs'']; [ cbn in Hlen; lia | ].
  destruct rs'' as [| r3 rs''']; [ cbn in Hlen; lia | ].
  destruct rs''' as [| r4 rs'''']; [ cbn in Hlen; lia | ].
  destruct rs'''' as [| r5 rs''''']; [ cbn in Hlen; lia | ].
  destruct rs''''' as [| r6 rs'''''']; [ cbn in Hlen; lia | ].
  destruct rs'''''' as [| r7 rs''''''']; [ cbn in Hlen; lia | ].
  destruct rs''''''' as [| r8 rs''''''''].
  - cbn [PFR length pred nth Xsub Padd Pscale map fold_right e2 e3 e4 e5 e6 e7 e8]; ring.
  - change (PFR (r0 :: r1 :: r2 :: r3 :: r4 :: r5 :: r6 :: r7 :: r8 :: rs''''''''))
      with (Xsub r0 (PFR (r1 :: r2 :: r3 :: r4 :: r5 :: r6 :: r7 :: r8 :: rs''''''''))).
    cbn [length pred].
    unfold Xsub; rewrite nth_Padd, nth_Pscale.
    change (nth (S (length rs'''''''')) (0 :: PFR (r1 :: r2 :: r3 :: r4 :: r5 :: r6 :: r7 :: r8 :: rs'''''''')) 0)
      with (nth (length rs'''''''') (PFR (r1 :: r2 :: r3 :: r4 :: r5 :: r6 :: r7 :: r8 :: rs'''''''')) 0).
    pose proof (IH ltac:(cbn [length]; lia)) as HIH; cbn [length pred] in HIH.
    pose proof (PFR_eighth (r1 :: r2 :: r3 :: r4 :: r5 :: r6 :: r7 :: r8 :: rs'''''''') ltac:(cbn [length]; lia)) as HPF;
      cbn [length pred] in HPF.
    rewrite HIH, HPF.
    change (e8 (r0 :: r1 :: r2 :: r3 :: r4 :: r5 :: r6 :: r7 :: r8 :: rs''''''''))
      with (e8 (r1 :: r2 :: r3 :: r4 :: r5 :: r6 :: r7 :: r8 :: rs'''''''') + r0 * e7 (r1 :: r2 :: r3 :: r4 :: r5 :: r6 :: r7 :: r8 :: rs'''''''')).
    ring.
Qed.

Lemma Plist_ninth : forall m, (8 <= m)%nat ->
  nth (pred (pred (pred (pred (pred (pred (pred (pred m)))))))) (Plist m) 0 = Binomial.C (2 * m + 1) 17.
Proof.
  intros m Hm; unfold Plist.
  set (g := fun i => (-1) ^ (m - i) * Binomial.C (2 * m + 1) (2 * (m - i) + 1)).
  rewrite (@nth_indep R (map g (seq 0 (S m))) (pred (pred (pred (pred (pred (pred (pred (pred m)))))))) 0 (g 0%nat))
    by (rewrite length_map, length_seq; lia).
  rewrite (map_nth g (seq 0 (S m)) 0%nat (pred (pred (pred (pred (pred (pred (pred (pred m))))))))), seq_nth by lia.
  cbn [Nat.add]. unfold g. replace (m - pred (pred (pred (pred (pred (pred (pred (pred m))))))))%nat with 8%nat by lia.
  cbn [pow]. change (2 * 8 + 1)%nat with 17%nat. ring.
Qed.

Lemma fact_down16 : forall m, (8 <= m)%nat ->
  fact (2 * m)
  = ((2*m) * (2*m-1) * (2*m-2) * (2*m-3) * (2*m-4) * (2*m-5) * (2*m-6) * (2*m-7)
     * (2*m-8) * (2*m-9) * (2*m-10) * (2*m-11) * (2*m-12) * (2*m-13) * (2*m-14) * (2*m-15)
     * fact (2*m-16)) %nat.
Proof.
  intros m Hm; replace (2 * m)%nat with (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (2 * m - 16))))))))))))))))) by lia.
  cbn [fact].
  replace (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (2*m-16))))))))))))))))-1)%nat with (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (2*m-16)))))))))))))))) by lia.
  replace (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (2*m-16))))))))))))))))-2)%nat with (S (S (S (S (S (S (S (S (S (S (S (S (S (S (2*m-16))))))))))))))) by lia.
  replace (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (2*m-16))))))))))))))))-3)%nat with (S (S (S (S (S (S (S (S (S (S (S (S (S (2*m-16)))))))))))))) by lia.
  replace (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (2*m-16))))))))))))))))-4)%nat with (S (S (S (S (S (S (S (S (S (S (S (S (2*m-16))))))))))))) by lia.
  replace (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (2*m-16))))))))))))))))-5)%nat with (S (S (S (S (S (S (S (S (S (S (S (2*m-16)))))))))))) by lia.
  replace (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (2*m-16))))))))))))))))-6)%nat with (S (S (S (S (S (S (S (S (S (S (2*m-16))))))))))) by lia.
  replace (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (2*m-16))))))))))))))))-7)%nat with (S (S (S (S (S (S (S (S (S (2*m-16)))))))))) by lia.
  replace (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (2*m-16))))))))))))))))-8)%nat with (S (S (S (S (S (S (S (S (2*m-16))))))))) by lia.
  replace (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (2*m-16))))))))))))))))-9)%nat with (S (S (S (S (S (S (S (2*m-16)))))))) by lia.
  replace (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (2*m-16))))))))))))))))-10)%nat with (S (S (S (S (S (S (2*m-16))))))) by lia.
  replace (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (2*m-16))))))))))))))))-11)%nat with (S (S (S (S (S (2*m-16)))))) by lia.
  replace (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (2*m-16))))))))))))))))-12)%nat with (S (S (S (S (2*m-16))))) by lia.
  replace (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (2*m-16))))))))))))))))-13)%nat with (S (S (S (2*m-16)))) by lia.
  replace (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (2*m-16))))))))))))))))-14)%nat with (S (S (2*m-16))) by lia.
  replace (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (2*m-16))))))))))))))))-15)%nat with (S (2*m-16)) by lia.
  replace (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (2*m-16))))))))))))))))-16)%nat with (2*m-16)%nat by lia.
  cbn [fact]; ring.
Qed.

Lemma C_ratio17 : forall m, (8 <= m)%nat ->
  Binomial.C (2 * m + 1) 17 / Binomial.C (2 * m + 1) 1
  = (2*INR m)*(2*INR m-1)*(2*INR m-2)*(2*INR m-3)*(2*INR m-4)*(2*INR m-5)*(2*INR m-6)*(2*INR m-7)
    *(2*INR m-8)*(2*INR m-9)*(2*INR m-10)*(2*INR m-11)*(2*INR m-12)*(2*INR m-13)*(2*INR m-14)*(2*INR m-15) / 355687428096000.
Proof.
  intros m Hm.
  assert (Hmpos : 8 <= INR m) by (replace 8 with (INR 8) by (simpl; ring); apply le_INR; lia).
  remember (2 * INR m * (2 * INR m - 1) * (2 * INR m - 2) * (2 * INR m - 3) * (2 * INR m - 4)
            * (2 * INR m - 5) * (2 * INR m - 6) * (2 * INR m - 7) * (2 * INR m - 8) * (2 * INR m - 9)
            * (2 * INR m - 10) * (2 * INR m - 11) * (2 * INR m - 12) * (2 * INR m - 13)
            * (2 * INR m - 14) * (2 * INR m - 15)) as P eqn:HP.
  assert (HPne : P <> 0)
    by (rewrite HP; apply Rgt_not_eq; repeat apply Rmult_lt_0_compat; lra).
  assert (Hstep : INR (fact (2 * m)) = P * INR (fact (2 * m - 16))).
  { rewrite HP, (fact_down16 m Hm), !mult_INR, !minus_INR by lia.
    replace (INR (2 * m)) with (2 * INR m) by (rewrite mult_INR; simpl (INR 2); ring).
    replace (INR 1) with 1 by (simpl; ring); replace (INR 2) with 2 by (simpl; ring);
    replace (INR 3) with 3 by (simpl; ring); replace (INR 4) with 4 by (simpl; ring);
    replace (INR 5) with 5 by (simpl; ring); replace (INR 6) with 6 by (simpl; ring);
    replace (INR 7) with 7 by (simpl; ring); replace (INR 8) with 8 by (simpl; ring);
    replace (INR 9) with 9 by (simpl; ring); replace (INR 10) with 10 by (simpl; ring);
    replace (INR 11) with 11 by (simpl; ring); replace (INR 12) with 12 by (simpl; ring);
    replace (INR 13) with 13 by (simpl; ring); replace (INR 14) with 14 by (simpl; ring);
    replace (INR 15) with 15 by (simpl; ring). ring. }
  unfold Binomial.C.
  replace (2 * m + 1 - 1)%nat with (2 * m)%nat by lia.
  replace (2 * m + 1 - 17)%nat with (2 * m - 16)%nat by lia.
  assert (Hf1 : INR (fact 1) = 1) by (simpl; ring).
  assert (Hf17 : INR (fact 17) = 355687428096000)
    by (cbn [fact]; rewrite !mult_INR, !INR_IZR_INZ, <- !mult_IZR; f_equal).
  rewrite Hf1, Hf17, Hstep.
  field; repeat split; try apply INR_fact_neq_0; try exact HPne.
Qed.

Lemma cot_e8 : forall m, (8 <= m)%nat ->
  e8 (map (fun k => Rcot (theta m k) ^ 2) (seq 1 m))
  = (2*INR m)*(2*INR m-1)*(2*INR m-2)*(2*INR m-3)*(2*INR m-4)*(2*INR m-5)*(2*INR m-6)*(2*INR m-7)
    *(2*INR m-8)*(2*INR m-9)*(2*INR m-10)*(2*INR m-11)*(2*INR m-12)*(2*INR m-13)*(2*INR m-14)*(2*INR m-15) / 355687428096000.
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
  pose proof (vieta_coeff (Plist m) rs (pred (pred (pred (pred (pred (pred (pred (pred (length rs))))))))) Hpl Hne Hnd Hroots Hlead) as HV.
  rewrite (PFR_ninth rs ltac:(rewrite Hlen_rs; lia)) in HV.
  rewrite Hlen_rs in HV.
  rewrite (Plist_ninth m Hm), (Plist_leading m), (C_n_1 (2 * m + 1) ltac:(lia)) in HV.
  fold rs.
  assert (Hne1 : INR (2 * m + 1) <> 0) by (apply not_0_INR; lia).
  pose proof (C_ratio17 m Hm) as HC17; rewrite (C_n_1 (2 * m + 1) ltac:(lia)) in HC17.
  apply (Rmult_eq_reg_l (INR (2 * m + 1))); [ | exact Hne1 ].
  rewrite <- HC17; replace (INR (2 * m + 1) * (Binomial.C (2 * m + 1) 17 / INR (2 * m + 1)))
    with (Binomial.C (2 * m + 1) 17) by (field; exact Hne1).
  symmetry; exact HV.
Qed.

Lemma cot_e8_exp : forall m, (8 <= m)%nat ->
  e8 (map (fun k => Rcot (theta m k) ^ 2) (seq 1 m))
  = (65536*INR m^16 - 3932160*INR m^15 + 107806720*INR m^14 - 1789132800*INR m^13
     + 20068851712*INR m^12 - 160887767040*INR m^11 + 950370037760*INR m^10 - 4202305536000*INR m^9
     + 13985569165568*INR m^8 - 34918810967040*INR m^7 + 64619014853120*INR m^6 - 86618027059200*INR m^5
     + 80911931261184*INR m^4 - 49326540917760*INR m^3 + 17356652006400*INR m^2 - 2615348736000*INR m) / 355687428096000.
Proof. intros m Hm; rewrite (cot_e8 m Hm); unfold Rdiv; apply Rmult_eq_compat_r; ring. Qed.

Theorem cot16_sum : forall m, (8 <= m)%nat ->
  sum_f_R0 (fun k => Rcot (INR (S k) * PI / INR (2 * m + 1)) ^ 16) (m - 1)
  = (355565568 * INR m ^ 16 + 2844524544 * INR m ^ 15 + 5987696640 * INR m ^ 14 - 7865303040 * INR m ^ 13
     - 37908242432 * INR m ^ 12 + 4225351680 * INR m ^ 11 + 113821052928 * INR m ^ 10 + 3943976960 * INR m ^ 9
     - 229552173312 * INR m ^ 8 + 36110638080 * INR m ^ 7 + 320686408960 * INR m ^ 6 - 178793005824 * INR m ^ 5
     - 249204536352 * INR m ^ 4 + 355069137600 * INR m ^ 3 - 168379722000 * INR m ^ 2 + 28733079375 * INR m) / 488462349375.
Proof.
  intros m Hm.
  transitivity (fold_right Rplus 0
                  (map (fun r => r * r * r * r * r * r * r * r) (map (fun k => Rcot (theta m k) ^ 2) (seq 1 m)))).
  - rewrite map_map.
    rewrite (fold_right_map_seq
               (fun k => Rcot (theta m k) ^ 2 * (Rcot (theta m k) ^ 2) * (Rcot (theta m k) ^ 2)
                         * (Rcot (theta m k) ^ 2) * (Rcot (theta m k) ^ 2) * (Rcot (theta m k) ^ 2)
                         * (Rcot (theta m k) ^ 2) * (Rcot (theta m k) ^ 2)) m ltac:(lia)).
    apply sum_eq; intros k _; unfold theta; ring.
  - rewrite newton8, (cot_e2_exp m ltac:(lia)), (cot_e3_exp m ltac:(lia)), (cot_e4_exp m ltac:(lia)),
      (cot_e5_exp m ltac:(lia)), (cot_e6_exp m ltac:(lia)), (cot_e7_exp m ltac:(lia)), (cot_e8_exp m Hm).
    replace (fold_right Rplus 0 (map (fun k => Rcot (theta m k) ^ 2) (seq 1 m)))
      with (INR m * (2 * INR m - 1) / 3).
    2:{ rewrite (fold_right_map_seq (fun k => Rcot (theta m k) ^ 2) m ltac:(lia)).
        rewrite <- (cot_sq_sum m ltac:(lia)); apply sum_eq; intros k _; unfold theta; reflexivity. }
    exact (cot16_poly_id (INR m)).
Qed.

Print Assumptions cot16_sum.

(* ================================================================= *)
(*  END BaselZeta16.v.                                                *)
(* ================================================================= *)
