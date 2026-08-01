(* ================================================================= *)
(*  BaselZeta14.v  —  the fourteenth-power cotangent sum, toward ζ(14).*)
(*                                                                    *)
(*  Σcot¹⁴(kπ/(2m+1)) = closed poly / 273648375, with ζ(14) =          *)
(*  2·π¹⁴/18243225.  Vieta ladder extended to the SEVENTH symmetric    *)
(*  function e₇ (Newton p₇, PFR_eighth with sign (−1)⁷ = −).           *)
(*  Axiom-clean.  Performance notes as in BaselZeta12.v:               *)
(*   - C_ratio15 keeps the 14-factor product opaque and evaluates      *)
(*     INR(fact 15) symbolically (a plain vm_compute would materialise *)
(*     a 1.3-trillion unary nat);                                     *)
(*   - cot14_sum closes by [exact] against BaselZeta14Poly.           *)
(* ================================================================= *)

From Stdlib Require Import Reals List Lia Lra Factorial Binomial ZArith.
Import ListNotations.
Require Import BaselVieta BaselCotPoly BaselZeta4 BaselZeta6 BaselZeta8 BaselZeta10 BaselZeta12 BaselZeta14Poly.
Open Scope R_scope.

Fixpoint e7 (rs : list R) : R :=
  match rs with
  | [] => 0
  | r :: p => e7 p + r * e6 p
  end.

Lemma newton7 : forall rs,
  fold_right Rplus 0 (map (fun r => r * r * r * r * r * r * r) rs)
  = (fold_right Rplus 0 rs)^7
    - 7*(fold_right Rplus 0 rs)^5*(e2 rs)
    + 14*(fold_right Rplus 0 rs)^3*(e2 rs)^2
    + 7*(fold_right Rplus 0 rs)^4*(e3 rs)
    - 7*(fold_right Rplus 0 rs)*(e2 rs)^3
    - 21*(fold_right Rplus 0 rs)^2*(e2 rs)*(e3 rs)
    - 7*(fold_right Rplus 0 rs)^3*(e4 rs)
    + 7*(e2 rs)^2*(e3 rs)
    + 7*(fold_right Rplus 0 rs)*(e3 rs)^2
    + 14*(fold_right Rplus 0 rs)*(e2 rs)*(e4 rs)
    + 7*(fold_right Rplus 0 rs)^2*(e5 rs)
    - 7*(e3 rs)*(e4 rs)
    - 7*(e2 rs)*(e5 rs)
    - 7*(fold_right Rplus 0 rs)*(e6 rs)
    + 7*(e7 rs).
Proof.
  induction rs as [| r p IH]; cbn [fold_right map e2 e3 e4 e5 e6 e7]; [ ring | ].
  rewrite IH; ring.
Qed.

Lemma PFR_eighth : forall rs, (7 <= length rs)%nat ->
  nth (pred (pred (pred (pred (pred (pred (pred (length rs)))))))) (PFR rs) 0 = - e7 rs.
Proof.
  induction rs as [| r0 rs IH]; intro Hlen; [ cbn in Hlen; lia | ].
  destruct rs as [| r1 rs']; [ cbn in Hlen; lia | ].
  destruct rs' as [| r2 rs'']; [ cbn in Hlen; lia | ].
  destruct rs'' as [| r3 rs''']; [ cbn in Hlen; lia | ].
  destruct rs''' as [| r4 rs'''']; [ cbn in Hlen; lia | ].
  destruct rs'''' as [| r5 rs''''']; [ cbn in Hlen; lia | ].
  destruct rs''''' as [| r6 rs'''''']; [ cbn in Hlen; lia | ].
  destruct rs'''''' as [| r7 rs'''''''].
  - cbn [PFR length pred nth Xsub Padd Pscale map fold_right e2 e3 e4 e5 e6 e7]; ring.
  - change (PFR (r0 :: r1 :: r2 :: r3 :: r4 :: r5 :: r6 :: r7 :: rs'''''''))
      with (Xsub r0 (PFR (r1 :: r2 :: r3 :: r4 :: r5 :: r6 :: r7 :: rs'''''''))).
    cbn [length pred].
    unfold Xsub; rewrite nth_Padd, nth_Pscale.
    change (nth (S (length rs''''''')) (0 :: PFR (r1 :: r2 :: r3 :: r4 :: r5 :: r6 :: r7 :: rs''''''')) 0)
      with (nth (length rs''''''') (PFR (r1 :: r2 :: r3 :: r4 :: r5 :: r6 :: r7 :: rs''''''')) 0).
    pose proof (IH ltac:(cbn [length]; lia)) as HIH; cbn [length pred] in HIH.
    pose proof (PFR_seventh (r1 :: r2 :: r3 :: r4 :: r5 :: r6 :: r7 :: rs''''''') ltac:(cbn [length]; lia)) as HPF;
      cbn [length pred] in HPF.
    rewrite HIH, HPF.
    change (e7 (r0 :: r1 :: r2 :: r3 :: r4 :: r5 :: r6 :: r7 :: rs'''''''))
      with (e7 (r1 :: r2 :: r3 :: r4 :: r5 :: r6 :: r7 :: rs''''''') + r0 * e6 (r1 :: r2 :: r3 :: r4 :: r5 :: r6 :: r7 :: rs''''''')).
    ring.
Qed.

Lemma Plist_eighth : forall m, (7 <= m)%nat ->
  nth (pred (pred (pred (pred (pred (pred (pred m))))))) (Plist m) 0 = - Binomial.C (2 * m + 1) 15.
Proof.
  intros m Hm; unfold Plist.
  set (g := fun i => (-1) ^ (m - i) * Binomial.C (2 * m + 1) (2 * (m - i) + 1)).
  rewrite (@nth_indep R (map g (seq 0 (S m))) (pred (pred (pred (pred (pred (pred (pred m))))))) 0 (g 0%nat))
    by (rewrite length_map, length_seq; lia).
  rewrite (map_nth g (seq 0 (S m)) 0%nat (pred (pred (pred (pred (pred (pred (pred m)))))))), seq_nth by lia.
  cbn [Nat.add]. unfold g. replace (m - pred (pred (pred (pred (pred (pred (pred m)))))))%nat with 7%nat by lia.
  cbn [pow]. change (2 * 7 + 1)%nat with 15%nat. ring.
Qed.

Lemma fact_down14 : forall m, (7 <= m)%nat ->
  fact (2 * m)
  = ((2*m) * (2*m-1) * (2*m-2) * (2*m-3) * (2*m-4) * (2*m-5) * (2*m-6) * (2*m-7)
     * (2*m-8) * (2*m-9) * (2*m-10) * (2*m-11) * (2*m-12) * (2*m-13) * fact (2*m-14)) %nat.
Proof.
  intros m Hm; replace (2 * m)%nat with (S (S (S (S (S (S (S (S (S (S (S (S (S (S (2 * m - 14)))))))))))))) ) by lia.
  cbn [fact].
  replace (S (S (S (S (S (S (S (S (S (S (S (S (S (S (2*m-14)))))))))))))) - 1)%nat with (S (S (S (S (S (S (S (S (S (S (S (S (S (2*m-14))))))))))))) ) by lia.
  replace (S (S (S (S (S (S (S (S (S (S (S (S (S (S (2*m-14)))))))))))))) - 2)%nat with (S (S (S (S (S (S (S (S (S (S (S (S (2*m-14)))))))))))) ) by lia.
  replace (S (S (S (S (S (S (S (S (S (S (S (S (S (S (2*m-14)))))))))))))) - 3)%nat with (S (S (S (S (S (S (S (S (S (S (S (2*m-14))))))))))) ) by lia.
  replace (S (S (S (S (S (S (S (S (S (S (S (S (S (S (2*m-14)))))))))))))) - 4)%nat with (S (S (S (S (S (S (S (S (S (S (2*m-14)))))))))) ) by lia.
  replace (S (S (S (S (S (S (S (S (S (S (S (S (S (S (2*m-14)))))))))))))) - 5)%nat with (S (S (S (S (S (S (S (S (S (2*m-14))))))))) ) by lia.
  replace (S (S (S (S (S (S (S (S (S (S (S (S (S (S (2*m-14)))))))))))))) - 6)%nat with (S (S (S (S (S (S (S (S (2*m-14)))))))) ) by lia.
  replace (S (S (S (S (S (S (S (S (S (S (S (S (S (S (2*m-14)))))))))))))) - 7)%nat with (S (S (S (S (S (S (S (2*m-14))))))) ) by lia.
  replace (S (S (S (S (S (S (S (S (S (S (S (S (S (S (2*m-14)))))))))))))) - 8)%nat with (S (S (S (S (S (S (2*m-14)))))) ) by lia.
  replace (S (S (S (S (S (S (S (S (S (S (S (S (S (S (2*m-14)))))))))))))) - 9)%nat with (S (S (S (S (S (2*m-14))))) ) by lia.
  replace (S (S (S (S (S (S (S (S (S (S (S (S (S (S (2*m-14)))))))))))))) - 10)%nat with (S (S (S (S (2*m-14)))) ) by lia.
  replace (S (S (S (S (S (S (S (S (S (S (S (S (S (S (2*m-14)))))))))))))) - 11)%nat with (S (S (S (2*m-14))) ) by lia.
  replace (S (S (S (S (S (S (S (S (S (S (S (S (S (S (2*m-14)))))))))))))) - 12)%nat with (S (S (2*m-14)) ) by lia.
  replace (S (S (S (S (S (S (S (S (S (S (S (S (S (S (2*m-14)))))))))))))) - 13)%nat with (S (2*m-14) ) by lia.
  replace (S (S (S (S (S (S (S (S (S (S (S (S (S (S (2*m-14)))))))))))))) - 14)%nat with (2*m-14)%nat by lia.
  cbn [fact]; ring.
Qed.

Lemma C_ratio15 : forall m, (7 <= m)%nat ->
  Binomial.C (2 * m + 1) 15 / Binomial.C (2 * m + 1) 1
  = (2*INR m)*(2*INR m-1)*(2*INR m-2)*(2*INR m-3)*(2*INR m-4)*(2*INR m-5)*(2*INR m-6)
    *(2*INR m-7)*(2*INR m-8)*(2*INR m-9)*(2*INR m-10)*(2*INR m-11)*(2*INR m-12)*(2*INR m-13) / 1307674368000.
Proof.
  intros m Hm.
  assert (Hmpos : 7 <= INR m) by (replace 7 with (INR 7) by (simpl; ring); apply le_INR; lia).
  remember (2 * INR m * (2 * INR m - 1) * (2 * INR m - 2) * (2 * INR m - 3) * (2 * INR m - 4)
            * (2 * INR m - 5) * (2 * INR m - 6) * (2 * INR m - 7) * (2 * INR m - 8) * (2 * INR m - 9)
            * (2 * INR m - 10) * (2 * INR m - 11) * (2 * INR m - 12) * (2 * INR m - 13)) as P eqn:HP.
  assert (HPne : P <> 0)
    by (rewrite HP; apply Rgt_not_eq; repeat apply Rmult_lt_0_compat; lra).
  assert (Hstep : INR (fact (2 * m)) = P * INR (fact (2 * m - 14))).
  { rewrite HP, (fact_down14 m Hm), !mult_INR, !minus_INR by lia.
    replace (INR (2 * m)) with (2 * INR m) by (rewrite mult_INR; simpl (INR 2); ring).
    replace (INR 1) with 1 by (simpl; ring); replace (INR 2) with 2 by (simpl; ring);
    replace (INR 3) with 3 by (simpl; ring); replace (INR 4) with 4 by (simpl; ring);
    replace (INR 5) with 5 by (simpl; ring); replace (INR 6) with 6 by (simpl; ring);
    replace (INR 7) with 7 by (simpl; ring); replace (INR 8) with 8 by (simpl; ring);
    replace (INR 9) with 9 by (simpl; ring); replace (INR 10) with 10 by (simpl; ring);
    replace (INR 11) with 11 by (simpl; ring); replace (INR 12) with 12 by (simpl; ring);
    replace (INR 13) with 13 by (simpl; ring). ring. }
  unfold Binomial.C.
  replace (2 * m + 1 - 1)%nat with (2 * m)%nat by lia.
  replace (2 * m + 1 - 15)%nat with (2 * m - 14)%nat by lia.
  assert (Hf1 : INR (fact 1) = 1) by (simpl; ring).
  assert (Hf15 : INR (fact 15) = 1307674368000)
    by (cbn [fact]; rewrite !mult_INR, !INR_IZR_INZ, <- !mult_IZR; f_equal).
  rewrite Hf1, Hf15, Hstep.
  field; repeat split; try apply INR_fact_neq_0; try exact HPne.
Qed.

Lemma cot_e7 : forall m, (7 <= m)%nat ->
  e7 (map (fun k => Rcot (theta m k) ^ 2) (seq 1 m))
  = (2*INR m)*(2*INR m-1)*(2*INR m-2)*(2*INR m-3)*(2*INR m-4)*(2*INR m-5)*(2*INR m-6)
    *(2*INR m-7)*(2*INR m-8)*(2*INR m-9)*(2*INR m-10)*(2*INR m-11)*(2*INR m-12)*(2*INR m-13) / 1307674368000.
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
  pose proof (vieta_coeff (Plist m) rs (pred (pred (pred (pred (pred (pred (pred (length rs)))))))) Hpl Hne Hnd Hroots Hlead) as HV.
  rewrite (PFR_eighth rs ltac:(rewrite Hlen_rs; lia)) in HV.
  rewrite Hlen_rs in HV.
  rewrite (Plist_eighth m Hm), (Plist_leading m), (C_n_1 (2 * m + 1) ltac:(lia)) in HV.
  fold rs.
  assert (Hne1 : INR (2 * m + 1) <> 0) by (apply not_0_INR; lia).
  pose proof (C_ratio15 m Hm) as HC15; rewrite (C_n_1 (2 * m + 1) ltac:(lia)) in HC15.
  replace (INR (2 * m + 1) * - e7 rs) with (- (INR (2 * m + 1) * e7 rs)) in HV by ring.
  assert (HV' : INR (2 * m + 1) * e7 rs = Binomial.C (2 * m + 1) 15) by lra.
  apply (Rmult_eq_reg_l (INR (2 * m + 1))); [ | exact Hne1 ].
  rewrite <- HC15; replace (INR (2 * m + 1) * (Binomial.C (2 * m + 1) 15 / INR (2 * m + 1)))
    with (Binomial.C (2 * m + 1) 15) by (field; exact Hne1).
  exact HV'.
Qed.

Lemma cot_e7_exp : forall m, (7 <= m)%nat ->
  e7 (map (fun k => Rcot (theta m k) ^ 2) (seq 1 m))
  = (16384*INR m^14 - 745472*INR m^13 + 15282176*INR m^12 - 186554368*INR m^11
     + 1509860352*INR m^10 - 8534862336*INR m^9 + 34569337088*INR m^8 - 101240723584*INR m^7
     + 213511602304*INR m^6 - 318646520192*INR m^5 + 325020049536*INR m^4 - 212773736448*INR m^3
     + 79211036160*INR m^2 - 12454041600*INR m) / 1307674368000.
Proof. intros m Hm; rewrite (cot_e7 m Hm); unfold Rdiv; apply Rmult_eq_compat_r; ring. Qed.

Theorem cot14_sum : forall m, (7 <= m)%nat ->
  sum_f_R0 (fun k => Rcot (INR (S k) * PI / INR (2 * m + 1)) ^ 14) (m - 1)
  = (491520 * INR m ^ 14 + 3440640 * INR m ^ 13 + 5521408 * INR m ^ 12 - 11599872 * INR m ^ 11
     - 33297408 * INR m ^ 10 + 21847040 * INR m ^ 9 + 87991296 * INR m ^ 8 - 47290368 * INR m ^ 7
     - 139644800 * INR m ^ 6 + 113541504 * INR m ^ 5 + 113995584 * INR m ^ 4 - 198457344 * INR m ^ 3
     + 101829150 * INR m ^ 2 - 18243225 * INR m) / 273648375.
Proof.
  intros m Hm.
  transitivity (fold_right Rplus 0
                  (map (fun r => r * r * r * r * r * r * r) (map (fun k => Rcot (theta m k) ^ 2) (seq 1 m)))).
  - rewrite map_map.
    rewrite (fold_right_map_seq
               (fun k => Rcot (theta m k) ^ 2 * (Rcot (theta m k) ^ 2) * (Rcot (theta m k) ^ 2)
                         * (Rcot (theta m k) ^ 2) * (Rcot (theta m k) ^ 2) * (Rcot (theta m k) ^ 2)
                         * (Rcot (theta m k) ^ 2)) m ltac:(lia)).
    apply sum_eq; intros k _; unfold theta; ring.
  - rewrite newton7, (cot_e2_exp m ltac:(lia)), (cot_e3_exp m ltac:(lia)), (cot_e4_exp m ltac:(lia)),
      (cot_e5_exp m ltac:(lia)), (cot_e6_exp m ltac:(lia)), (cot_e7_exp m Hm).
    replace (fold_right Rplus 0 (map (fun k => Rcot (theta m k) ^ 2) (seq 1 m)))
      with (INR m * (2 * INR m - 1) / 3).
    2:{ rewrite (fold_right_map_seq (fun k => Rcot (theta m k) ^ 2) m ltac:(lia)).
        rewrite <- (cot_sq_sum m ltac:(lia)); apply sum_eq; intros k _; unfold theta; reflexivity. }
    exact (cot14_poly_id (INR m)).
Qed.

Print Assumptions cot14_sum.

(* ================================================================= *)
(*  END BaselZeta14.v.                                                *)
(* ================================================================= *)
