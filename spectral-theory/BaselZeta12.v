(* ================================================================= *)
(*  BaselZeta12.v  —  the twelfth-power cotangent sum, toward ζ(12).   *)
(*                                                                    *)
(*  Σcot¹²(kπ/(2m+1)) = closed poly / 638512875, whose leading         *)
(*  coefficient 2830336 = 691·4096 encodes the Bernoulli irregular     *)
(*  prime 691 (ζ(12)=691π¹²/638512875).                                *)
(*                                                                    *)
(*  Newton p₆ = e₁⁶ − 6e₁⁴e₂ + 6e₁³e₃ + 9e₁²e₂² − 6e₁²e₄ − 12e₁e₂e₃    *)
(*    + 6e₁e₅ − 2e₂³ + 6e₂e₄ + 3e₃² − 6e₆, with                        *)
(*    e₆ = C(2m+1,13)/C(2m+1,1) via a Vieta lemma for the SIXTH         *)
(*    symmetric function (PFR_seventh, sign (−1)⁶ = +).  Axiom-clean.  *)
(* ================================================================= *)

From Stdlib Require Import Reals List Lia Lra Factorial Binomial ZArith.
Import ListNotations.
Require Import BaselVieta BaselCotPoly BaselZeta4 BaselZeta6 BaselZeta8 BaselZeta10 BaselZeta12Poly.
Open Scope R_scope.

Fixpoint e6 (rs : list R) : R :=
  match rs with
  | [] => 0
  | r :: p => e6 p + r * e5 p
  end.

Lemma newton6 : forall rs,
  fold_right Rplus 0 (map (fun r => r * r * r * r * r * r) rs)
  = (fold_right Rplus 0 rs) ^ 6 - 6 * (fold_right Rplus 0 rs) ^ 4 * (e2 rs)
    + 6 * (fold_right Rplus 0 rs) ^ 3 * (e3 rs) + 9 * (fold_right Rplus 0 rs) ^ 2 * (e2 rs) ^ 2
    - 6 * (fold_right Rplus 0 rs) ^ 2 * (e4 rs) - 12 * (fold_right Rplus 0 rs) * (e2 rs) * (e3 rs)
    + 6 * (fold_right Rplus 0 rs) * (e5 rs) - 2 * (e2 rs) ^ 3 + 6 * (e2 rs) * (e4 rs)
    + 3 * (e3 rs) ^ 2 - 6 * (e6 rs).
Proof.
  induction rs as [| r p IH]; cbn [fold_right map e2 e3 e4 e5 e6]; [ ring | ].
  rewrite IH; ring.
Qed.

Lemma PFR_seventh : forall rs, (6 <= length rs)%nat ->
  nth (pred (pred (pred (pred (pred (pred (length rs))))))) (PFR rs) 0 = e6 rs.
Proof.
  induction rs as [| r0 rs IH]; intro Hlen; [ cbn in Hlen; lia | ].
  destruct rs as [| r1 rs']; [ cbn in Hlen; lia | ].
  destruct rs' as [| r2 rs'']; [ cbn in Hlen; lia | ].
  destruct rs'' as [| r3 rs''']; [ cbn in Hlen; lia | ].
  destruct rs''' as [| r4 rs'''']; [ cbn in Hlen; lia | ].
  destruct rs'''' as [| r5 rs''''']; [ cbn in Hlen; lia | ].
  destruct rs''''' as [| r6 rs''''''].
  - cbn [PFR length pred nth Xsub Padd Pscale map fold_right e2 e3 e4 e5 e6]; ring.
  - change (PFR (r0 :: r1 :: r2 :: r3 :: r4 :: r5 :: r6 :: rs''''''))
      with (Xsub r0 (PFR (r1 :: r2 :: r3 :: r4 :: r5 :: r6 :: rs''''''))).
    cbn [length pred].
    unfold Xsub; rewrite nth_Padd, nth_Pscale.
    change (nth (S (length rs'''''')) (0 :: PFR (r1 :: r2 :: r3 :: r4 :: r5 :: r6 :: rs'''''')) 0)
      with (nth (length rs'''''') (PFR (r1 :: r2 :: r3 :: r4 :: r5 :: r6 :: rs'''''')) 0).
    pose proof (IH ltac:(cbn [length]; lia)) as HIH; cbn [length pred] in HIH.
    pose proof (PFR_sixth (r1 :: r2 :: r3 :: r4 :: r5 :: r6 :: rs'''''') ltac:(cbn [length]; lia)) as HPF;
      cbn [length pred] in HPF.
    rewrite HIH, HPF.
    change (e6 (r0 :: r1 :: r2 :: r3 :: r4 :: r5 :: r6 :: rs''''''))
      with (e6 (r1 :: r2 :: r3 :: r4 :: r5 :: r6 :: rs'''''') + r0 * e5 (r1 :: r2 :: r3 :: r4 :: r5 :: r6 :: rs'''''')).
    ring.
Qed.

Lemma Plist_seventh : forall m, (6 <= m)%nat ->
  nth (pred (pred (pred (pred (pred (pred m)))))) (Plist m) 0 = Binomial.C (2 * m + 1) 13.
Proof.
  intros m Hm; unfold Plist.
  set (g := fun i => (-1) ^ (m - i) * Binomial.C (2 * m + 1) (2 * (m - i) + 1)).
  rewrite (@nth_indep R (map g (seq 0 (S m))) (pred (pred (pred (pred (pred (pred m)))))) 0 (g 0%nat))
    by (rewrite length_map, length_seq; lia).
  rewrite (map_nth g (seq 0 (S m)) 0%nat (pred (pred (pred (pred (pred (pred m))))))), seq_nth by lia.
  cbn [Nat.add]. unfold g. replace (m - pred (pred (pred (pred (pred (pred m))))))%nat with 6%nat by lia.
  cbn [pow]. change (2 * 6 + 1)%nat with 13%nat. ring.
Qed.

Lemma fact_down12 : forall m, (6 <= m)%nat ->
  fact (2 * m)
  = ((2*m) * (2*m-1) * (2*m-2) * (2*m-3) * (2*m-4) * (2*m-5) * (2*m-6) * (2*m-7)
     * (2*m-8) * (2*m-9) * (2*m-10) * (2*m-11) * fact (2*m-12)) %nat.
Proof.
  intros m Hm; replace (2 * m)%nat with (S (S (S (S (S (S (S (S (S (S (S (S (2 * m - 12)))))))))))) ) by lia.
  cbn [fact].
  replace (S (S (S (S (S (S (S (S (S (S (S (S (2*m-12)))))))))))) - 1)%nat with (S (S (S (S (S (S (S (S (S (S (S (2*m-12))))))))))) ) by lia.
  replace (S (S (S (S (S (S (S (S (S (S (S (S (2*m-12)))))))))))) - 2)%nat with (S (S (S (S (S (S (S (S (S (S (2*m-12)))))))))) ) by lia.
  replace (S (S (S (S (S (S (S (S (S (S (S (S (2*m-12)))))))))))) - 3)%nat with (S (S (S (S (S (S (S (S (S (2*m-12))))))))) ) by lia.
  replace (S (S (S (S (S (S (S (S (S (S (S (S (2*m-12)))))))))))) - 4)%nat with (S (S (S (S (S (S (S (S (2*m-12)))))))) ) by lia.
  replace (S (S (S (S (S (S (S (S (S (S (S (S (2*m-12)))))))))))) - 5)%nat with (S (S (S (S (S (S (S (2*m-12))))))) ) by lia.
  replace (S (S (S (S (S (S (S (S (S (S (S (S (2*m-12)))))))))))) - 6)%nat with (S (S (S (S (S (S (2*m-12)))))) ) by lia.
  replace (S (S (S (S (S (S (S (S (S (S (S (S (2*m-12)))))))))))) - 7)%nat with (S (S (S (S (S (2*m-12))))) ) by lia.
  replace (S (S (S (S (S (S (S (S (S (S (S (S (2*m-12)))))))))))) - 8)%nat with (S (S (S (S (2*m-12)))) ) by lia.
  replace (S (S (S (S (S (S (S (S (S (S (S (S (2*m-12)))))))))))) - 9)%nat with (S (S (S (2*m-12))) ) by lia.
  replace (S (S (S (S (S (S (S (S (S (S (S (S (2*m-12)))))))))))) - 10)%nat with (S (S (2*m-12)) ) by lia.
  replace (S (S (S (S (S (S (S (S (S (S (S (S (2*m-12)))))))))))) - 11)%nat with (S (2*m-12) ) by lia.
  replace (S (S (S (S (S (S (S (S (S (S (S (S (2*m-12)))))))))))) - 12)%nat with (2*m-12)%nat by lia.
  cbn [fact]; ring.
Qed.

Lemma C_ratio13 : forall m, (6 <= m)%nat ->
  Binomial.C (2 * m + 1) 13 / Binomial.C (2 * m + 1) 1
  = (2*INR m)*(2*INR m-1)*(2*INR m-2)*(2*INR m-3)*(2*INR m-4)*(2*INR m-5)
    *(2*INR m-6)*(2*INR m-7)*(2*INR m-8)*(2*INR m-9)*(2*INR m-10)*(2*INR m-11) / 6227020800.
Proof.
  intros m Hm.
  assert (Hmpos : 6 <= INR m) by (replace 6 with (INR 6) by (simpl; ring); apply le_INR; lia).
  (* Keep the 12-factor product as an opaque atom P: [field] never expands it
     (a degree-12 expansion that otherwise blows up), and its one occurrence is
     supplied via the factorial relation Hstep (a single fast [ring]). *)
  remember (2 * INR m * (2 * INR m - 1) * (2 * INR m - 2) * (2 * INR m - 3)
            * (2 * INR m - 4) * (2 * INR m - 5) * (2 * INR m - 6) * (2 * INR m - 7)
            * (2 * INR m - 8) * (2 * INR m - 9) * (2 * INR m - 10) * (2 * INR m - 11)) as P eqn:HP.
  assert (HPne : P <> 0)
    by (rewrite HP; apply Rgt_not_eq; repeat apply Rmult_lt_0_compat; lra).
  assert (Hstep : INR (fact (2 * m)) = P * INR (fact (2 * m - 12))).
  { rewrite HP, (fact_down12 m Hm), !mult_INR, !minus_INR by lia.
    replace (INR (2 * m)) with (2 * INR m) by (rewrite mult_INR; simpl (INR 2); ring).
    replace (INR 1) with 1 by (simpl; ring); replace (INR 2) with 2 by (simpl; ring);
    replace (INR 3) with 3 by (simpl; ring); replace (INR 4) with 4 by (simpl; ring);
    replace (INR 5) with 5 by (simpl; ring); replace (INR 6) with 6 by (simpl; ring);
    replace (INR 7) with 7 by (simpl; ring); replace (INR 8) with 8 by (simpl; ring);
    replace (INR 9) with 9 by (simpl; ring); replace (INR 10) with 10 by (simpl; ring);
    replace (INR 11) with 11 by (simpl; ring). ring. }
  unfold Binomial.C.
  replace (2 * m + 1 - 1)%nat with (2 * m)%nat by lia.
  replace (2 * m + 1 - 13)%nat with (2 * m - 12)%nat by lia.
  assert (Hf1 : INR (fact 1) = 1) by (simpl; ring).
  (* Evaluate INR (fact 13) WITHOUT materialising the 6.2-billion unary nat:
     expand fact symbolically, push through INR/IZR, compute the product in Z. *)
  assert (Hf13 : INR (fact 13) = 6227020800)
    by (cbn [fact]; rewrite !mult_INR, !INR_IZR_INZ, <- !mult_IZR; f_equal).
  rewrite Hf1, Hf13, Hstep.
  field; repeat split; try apply INR_fact_neq_0; try exact HPne.
Qed.

Lemma cot_e6 : forall m, (6 <= m)%nat ->
  e6 (map (fun k => Rcot (theta m k) ^ 2) (seq 1 m))
  = (2*INR m)*(2*INR m-1)*(2*INR m-2)*(2*INR m-3)*(2*INR m-4)*(2*INR m-5)
    *(2*INR m-6)*(2*INR m-7)*(2*INR m-8)*(2*INR m-9)*(2*INR m-10)*(2*INR m-11) / 6227020800.
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
  pose proof (vieta_coeff (Plist m) rs (pred (pred (pred (pred (pred (pred (length rs))))))) Hpl Hne Hnd Hroots Hlead) as HV.
  rewrite (PFR_seventh rs ltac:(rewrite Hlen_rs; lia)) in HV.
  rewrite Hlen_rs in HV.
  rewrite (Plist_seventh m Hm), (Plist_leading m), (C_n_1 (2 * m + 1) ltac:(lia)) in HV.
  fold rs.
  assert (Hne1 : INR (2 * m + 1) <> 0) by (apply not_0_INR; lia).
  pose proof (C_ratio13 m Hm) as HC13; rewrite (C_n_1 (2 * m + 1) ltac:(lia)) in HC13.
  apply (Rmult_eq_reg_l (INR (2 * m + 1))); [ | exact Hne1 ].
  rewrite <- HC13; replace (INR (2 * m + 1) * (Binomial.C (2 * m + 1) 13 / INR (2 * m + 1)))
    with (Binomial.C (2 * m + 1) 13) by (field; exact Hne1).
  symmetry; exact HV.
Qed.

(* Pre-expanded polynomial forms of the elementary symmetric functions.
   Expanding the 8/10/12-factor products ONCE via [ring] here (fast, Horner
   form) keeps the final [field] in cot12_sum from a ~2^k-term product blowup. *)
Lemma cot_e2_exp : forall m, (2 <= m)%nat ->
  e2 (map (fun k => Rcot (theta m k) ^ 2) (seq 1 m))
  = (16*INR m^4 - 48*INR m^3 + 44*INR m^2 - 12*INR m) / 120.
Proof. intros m Hm; rewrite (cot_e2 m Hm); unfold Rdiv; apply Rmult_eq_compat_r; ring. Qed.

Lemma cot_e3_exp : forall m, (3 <= m)%nat ->
  e3 (map (fun k => Rcot (theta m k) ^ 2) (seq 1 m))
  = (64*INR m^6 - 480*INR m^5 + 1360*INR m^4 - 1800*INR m^3 + 1096*INR m^2 - 240*INR m) / 5040.
Proof. intros m Hm; rewrite (cot_e3 m Hm); unfold Rdiv; apply Rmult_eq_compat_r; ring. Qed.

Lemma cot_e4_exp : forall m, (4 <= m)%nat ->
  e4 (map (fun k => Rcot (theta m k) ^ 2) (seq 1 m))
  = (256*INR m^8 - 3584*INR m^7 + 20608*INR m^6 - 62720*INR m^5 + 108304*INR m^4
     - 105056*INR m^3 + 52272*INR m^2 - 10080*INR m) / 362880.
Proof. intros m Hm; rewrite (cot_e4 m Hm); unfold Rdiv; apply Rmult_eq_compat_r; ring. Qed.

Lemma cot_e5_exp : forall m, (5 <= m)%nat ->
  e5 (map (fun k => Rcot (theta m k) ^ 2) (seq 1 m))
  = (1024*INR m^10 - 23040*INR m^9 + 222720*INR m^8 - 1209600*INR m^7 + 4049472*INR m^6
     - 8618400*INR m^5 + 11578880*INR m^4 - 9381600*INR m^3 + 4106304*INR m^2 - 725760*INR m) / 39916800.
Proof. intros m Hm; rewrite (cot_e5 m Hm); unfold Rdiv; apply Rmult_eq_compat_r; ring. Qed.

Lemma cot_e6_exp : forall m, (6 <= m)%nat ->
  e6 (map (fun k => Rcot (theta m k) ^ 2) (seq 1 m))
  = (4096*INR m^12 - 135168*INR m^11 + 1971200*INR m^10 - 16727040*INR m^9 + 91500288*INR m^8
     - 337607424*INR m^7 + 853730240*INR m^6 - 1471863360*INR m^5 + 1684129216*INR m^4
     - 1207343808*INR m^3 + 482175360*INR m^2 - 79833600*INR m) / 6227020800.
Proof. intros m Hm; rewrite (cot_e6 m Hm); unfold Rdiv; apply Rmult_eq_compat_r; ring. Qed.

Theorem cot12_sum : forall m, (6 <= m)%nat ->
  sum_f_R0 (fun k => Rcot (INR (S k) * PI / INR (2 * m + 1)) ^ 12) (m - 1)
  = (2830336 * INR m ^ 12 + 16982016 * INR m ^ 11 + 18745344 * INR m ^ 10
     - 61941760 * INR m ^ 9 - 104698368 * INR m ^ 8 + 139659264 * INR m ^ 7
     + 218421760 * INR m ^ 6 - 280499712 * INR m ^ 5 - 195670872 * INR m ^ 4
     + 456378192 * INR m ^ 3 - 258446700 * INR m ^ 2 + 49116375 * INR m) / 638512875.
Proof.
  intros m Hm.
  transitivity (fold_right Rplus 0
                  (map (fun r => r * r * r * r * r * r) (map (fun k => Rcot (theta m k) ^ 2) (seq 1 m)))).
  - rewrite map_map.
    rewrite (fold_right_map_seq
               (fun k => Rcot (theta m k) ^ 2 * (Rcot (theta m k) ^ 2) * (Rcot (theta m k) ^ 2)
                         * (Rcot (theta m k) ^ 2) * (Rcot (theta m k) ^ 2) * (Rcot (theta m k) ^ 2)) m ltac:(lia)).
    apply sum_eq; intros k _; unfold theta; ring.
  - rewrite newton6, (cot_e2_exp m ltac:(lia)), (cot_e3_exp m ltac:(lia)), (cot_e4_exp m ltac:(lia)),
      (cot_e5_exp m ltac:(lia)), (cot_e6_exp m Hm).
    replace (fold_right Rplus 0 (map (fun k => Rcot (theta m k) ^ 2) (seq 1 m)))
      with (INR m * (2 * INR m - 1) / 3).
    2:{ rewrite (fold_right_map_seq (fun k => Rcot (theta m k) ^ 2) m ltac:(lia)).
        rewrite <- (cot_sq_sum m ltac:(lia)); apply sum_eq; intros k _; unfold theta; reflexivity. }
    exact (cot12_poly_id (INR m)).
Qed.

Print Assumptions cot12_sum.

(* ================================================================= *)
(*  END BaselZeta12.v.                                                *)
(* ================================================================= *)
