(* ================================================================= *)
(*  BaselZeta10.v  —  the tenth-power cotangent sum, toward ζ(10).     *)
(*                                                                    *)
(*    Σcot¹⁰(kπ/(2m+1)) = (1024m¹⁰+5120m⁹+3072m⁸−18432m⁷−15424m⁶       *)
(*      +39744m⁵+16736m⁴−64512m³+41562m²−8505m)/93555.                *)
(*                                                                    *)
(*  Newton: Σr⁵ = (Σr)⁵ − 5(Σr)³e₂ + 5(Σr)²e₃ + 5(Σr)e₂² − 5(Σr)e₄    *)
(*                − 5e₂e₃ + 5e₅, with e₅ = C(2m+1,11)/C(2m+1,1) via a  *)
(*  Vieta lemma for the FIFTH symmetric function (PFR_sixth).         *)
(*  Axiom-clean.                                                     *)
(* ================================================================= *)

From Stdlib Require Import Reals List Lia Lra Factorial Binomial.
Import ListNotations.
Require Import BaselVieta BaselCotPoly BaselZeta4 BaselZeta6 BaselZeta8.
Open Scope R_scope.

Fixpoint e5 (rs : list R) : R :=
  match rs with
  | [] => 0
  | r :: p => e5 p + r * e4 p
  end.

Lemma newton5 : forall rs,
  fold_right Rplus 0 (map (fun r => r * r * r * r * r) rs)
  = (fold_right Rplus 0 rs) ^ 5 - 5 * (fold_right Rplus 0 rs) ^ 3 * (e2 rs)
    + 5 * (fold_right Rplus 0 rs) ^ 2 * (e3 rs) + 5 * (fold_right Rplus 0 rs) * (e2 rs) ^ 2
    - 5 * (fold_right Rplus 0 rs) * (e4 rs) - 5 * (e2 rs) * (e3 rs) + 5 * (e5 rs).
Proof.
  induction rs as [| r p IH]; cbn [fold_right map e2 e3 e4 e5]; [ ring | ].
  rewrite IH; ring.
Qed.

Lemma PFR_sixth : forall rs, (5 <= length rs)%nat ->
  nth (pred (pred (pred (pred (pred (length rs)))))) (PFR rs) 0 = - e5 rs.
Proof.
  induction rs as [| r0 rs IH]; intro Hlen; [ cbn in Hlen; lia | ].
  destruct rs as [| r1 rs']; [ cbn in Hlen; lia | ].
  destruct rs' as [| r2 rs'']; [ cbn in Hlen; lia | ].
  destruct rs'' as [| r3 rs''']; [ cbn in Hlen; lia | ].
  destruct rs''' as [| r4 rs'''']; [ cbn in Hlen; lia | ].
  destruct rs'''' as [| r5 rs'''''].
  - cbn [PFR length pred nth Xsub Padd Pscale map fold_right e2 e3 e4 e5]; ring.
  - change (PFR (r0 :: r1 :: r2 :: r3 :: r4 :: r5 :: rs'''''))
      with (Xsub r0 (PFR (r1 :: r2 :: r3 :: r4 :: r5 :: rs'''''))).
    cbn [length pred].
    unfold Xsub; rewrite nth_Padd, nth_Pscale.
    change (nth (S (length rs''''')) (0 :: PFR (r1 :: r2 :: r3 :: r4 :: r5 :: rs''''')) 0)
      with (nth (length rs''''') (PFR (r1 :: r2 :: r3 :: r4 :: r5 :: rs''''')) 0).
    pose proof (IH ltac:(cbn [length]; lia)) as HIH; cbn [length pred] in HIH.
    pose proof (PFR_fifth (r1 :: r2 :: r3 :: r4 :: r5 :: rs''''') ltac:(cbn [length]; lia)) as HPF;
      cbn [length pred] in HPF.
    rewrite HIH, HPF.
    change (e5 (r0 :: r1 :: r2 :: r3 :: r4 :: r5 :: rs'''''))
      with (e5 (r1 :: r2 :: r3 :: r4 :: r5 :: rs''''') + r0 * e4 (r1 :: r2 :: r3 :: r4 :: r5 :: rs''''')).
    ring.
Qed.

Lemma Plist_sixth : forall m, (5 <= m)%nat ->
  nth (pred (pred (pred (pred (pred m))))) (Plist m) 0 = - Binomial.C (2 * m + 1) 11.
Proof.
  intros m Hm; unfold Plist.
  set (g := fun i => (-1) ^ (m - i) * Binomial.C (2 * m + 1) (2 * (m - i) + 1)).
  rewrite (@nth_indep R (map g (seq 0 (S m))) (pred (pred (pred (pred (pred m))))) 0 (g 0%nat))
    by (rewrite length_map, length_seq; lia).
  rewrite (map_nth g (seq 0 (S m)) 0%nat (pred (pred (pred (pred (pred m)))))), seq_nth by lia.
  cbn [Nat.add]. unfold g. replace (m - pred (pred (pred (pred (pred m)))))%nat with 5%nat by lia.
  cbn [pow]. change (2 * 5 + 1)%nat with 11%nat. ring.
Qed.

Lemma fact_down10 : forall m, (5 <= m)%nat ->
  fact (2 * m)
  = ((2*m) * ((2*m-1) * ((2*m-2) * ((2*m-3) * ((2*m-4) * ((2*m-5) * ((2*m-6) *
      ((2*m-7) * ((2*m-8) * ((2*m-9) * fact (2*m-10))))))))))) %nat.
Proof.
  intros m Hm; replace (2 * m)%nat with (S (S (S (S (S (S (S (S (S (S (2 * m - 10)))))))))) ) by lia.
  cbn [fact].
  replace (S (S (S (S (S (S (S (S (S (S (2*m-10)))))))))) - 1)%nat with (S (S (S (S (S (S (S (S (S (2*m-10))))))))) ) by lia.
  replace (S (S (S (S (S (S (S (S (S (S (2*m-10)))))))))) - 2)%nat with (S (S (S (S (S (S (S (S (2*m-10)))))))) ) by lia.
  replace (S (S (S (S (S (S (S (S (S (S (2*m-10)))))))))) - 3)%nat with (S (S (S (S (S (S (S (2*m-10))))))) ) by lia.
  replace (S (S (S (S (S (S (S (S (S (S (2*m-10)))))))))) - 4)%nat with (S (S (S (S (S (S (2*m-10)))))) ) by lia.
  replace (S (S (S (S (S (S (S (S (S (S (2*m-10)))))))))) - 5)%nat with (S (S (S (S (S (2*m-10))))) ) by lia.
  replace (S (S (S (S (S (S (S (S (S (S (2*m-10)))))))))) - 6)%nat with (S (S (S (S (2*m-10)))) ) by lia.
  replace (S (S (S (S (S (S (S (S (S (S (2*m-10)))))))))) - 7)%nat with (S (S (S (2*m-10))) ) by lia.
  replace (S (S (S (S (S (S (S (S (S (S (2*m-10)))))))))) - 8)%nat with (S (S (2*m-10)) ) by lia.
  replace (S (S (S (S (S (S (S (S (S (S (2*m-10)))))))))) - 9)%nat with (S (2*m-10) ) by lia.
  replace (S (S (S (S (S (S (S (S (S (S (2*m-10)))))))))) - 10)%nat with (2*m-10)%nat by lia.
  cbn [fact]; ring.
Qed.

Lemma C_ratio11 : forall m, (5 <= m)%nat ->
  Binomial.C (2 * m + 1) 11 / Binomial.C (2 * m + 1) 1
  = (2*INR m)*(2*INR m-1)*(2*INR m-2)*(2*INR m-3)*(2*INR m-4)*(2*INR m-5)
    *(2*INR m-6)*(2*INR m-7)*(2*INR m-8)*(2*INR m-9) / 39916800.
Proof.
  intros m Hm; unfold Binomial.C.
  replace (2 * m + 1 - 1)%nat with (2 * m)%nat by lia.
  replace (2 * m + 1 - 11)%nat with (2 * m - 10)%nat by lia.
  rewrite (fact_down10 m Hm).
  rewrite !mult_INR, !minus_INR by lia.
  assert (Hf1 : INR (fact 1) = 1) by (simpl; ring).
  assert (Hf11 : INR (fact 11) = 39916800)
    by (rewrite INR_IZR_INZ; f_equal; vm_compute; reflexivity).
  rewrite Hf1, Hf11.
  replace (INR (2 * m)) with (2 * INR m) by (rewrite mult_INR; simpl (INR 2); ring).
  replace (INR 1) with 1 by (simpl; ring).
  replace (INR 2) with 2 by (simpl; ring). replace (INR 3) with 3 by (simpl; ring).
  replace (INR 4) with 4 by (simpl; ring). replace (INR 5) with 5 by (simpl; ring).
  replace (INR 6) with 6 by (simpl; ring). replace (INR 7) with 7 by (simpl; ring).
  replace (INR 8) with 8 by (simpl; ring). replace (INR 9) with 9 by (simpl; ring).
  assert (H1 : INR (fact (2 * m + 1)) <> 0) by apply INR_fact_neq_0.
  assert (H2 : INR (fact (2 * m - 10)) <> 0) by apply INR_fact_neq_0.
  assert (Hmpos : 5 <= INR m) by (replace 5 with (INR 5) by (simpl; ring); apply le_INR; lia).
  field; repeat split; try assumption; lra.
Qed.

Lemma cot_e5 : forall m, (5 <= m)%nat ->
  e5 (map (fun k => Rcot (theta m k) ^ 2) (seq 1 m))
  = (2*INR m)*(2*INR m-1)*(2*INR m-2)*(2*INR m-3)*(2*INR m-4)*(2*INR m-5)
    *(2*INR m-6)*(2*INR m-7)*(2*INR m-8)*(2*INR m-9) / 39916800.
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
  pose proof (vieta_coeff (Plist m) rs (pred (pred (pred (pred (pred (length rs)))))) Hpl Hne Hnd Hroots Hlead) as HV.
  rewrite (PFR_sixth rs ltac:(rewrite Hlen_rs; lia)) in HV.
  rewrite Hlen_rs in HV.
  rewrite (Plist_sixth m Hm), (Plist_leading m), (C_n_1 (2 * m + 1) ltac:(lia)) in HV.
  fold rs.
  assert (Hne1 : INR (2 * m + 1) <> 0) by (apply not_0_INR; lia).
  pose proof (C_ratio11 m Hm) as HC11; rewrite (C_n_1 (2 * m + 1) ltac:(lia)) in HC11.
  replace (INR (2 * m + 1) * - e5 rs) with (- (INR (2 * m + 1) * e5 rs)) in HV by ring.
  assert (HV' : INR (2 * m + 1) * e5 rs = Binomial.C (2 * m + 1) 11) by lra.
  apply (Rmult_eq_reg_l (INR (2 * m + 1))); [ | exact Hne1 ].
  rewrite <- HC11; replace (INR (2 * m + 1) * (Binomial.C (2 * m + 1) 11 / INR (2 * m + 1)))
    with (Binomial.C (2 * m + 1) 11) by (field; exact Hne1).
  exact HV'.
Qed.

Theorem cot10_sum : forall m, (5 <= m)%nat ->
  sum_f_R0 (fun k => Rcot (INR (S k) * PI / INR (2 * m + 1)) ^ 10) (m - 1)
  = (1024 * INR m ^ 10 + 5120 * INR m ^ 9 + 3072 * INR m ^ 8 - 18432 * INR m ^ 7
     - 15424 * INR m ^ 6 + 39744 * INR m ^ 5 + 16736 * INR m ^ 4 - 64512 * INR m ^ 3
     + 41562 * INR m ^ 2 - 8505 * INR m) / 93555.
Proof.
  intros m Hm.
  transitivity (fold_right Rplus 0
                  (map (fun r => r * r * r * r * r) (map (fun k => Rcot (theta m k) ^ 2) (seq 1 m)))).
  - rewrite map_map.
    rewrite (fold_right_map_seq
               (fun k => Rcot (theta m k) ^ 2 * (Rcot (theta m k) ^ 2) * (Rcot (theta m k) ^ 2)
                         * (Rcot (theta m k) ^ 2) * (Rcot (theta m k) ^ 2)) m ltac:(lia)).
    apply sum_eq; intros k _; unfold theta; ring.
  - rewrite newton5, (cot_e2 m ltac:(lia)), (cot_e3 m ltac:(lia)), (cot_e4 m ltac:(lia)),
      (cot_e5 m Hm).
    replace (fold_right Rplus 0 (map (fun k => Rcot (theta m k) ^ 2) (seq 1 m)))
      with (INR m * (2 * INR m - 1) / 3).
    2:{ rewrite (fold_right_map_seq (fun k => Rcot (theta m k) ^ 2) m ltac:(lia)).
        rewrite <- (cot_sq_sum m ltac:(lia)); apply sum_eq; intros k _; unfold theta; reflexivity. }
    field.
Qed.

Print Assumptions cot10_sum.

(* ================================================================= *)
(*  END BaselZeta10.v.                                                *)
(* ================================================================= *)
