(* ================================================================= *)
(*  BaselZeta8.v  —  the eighth-power cotangent sum, toward ζ(8).      *)
(*                                                                    *)
(*    Σcot⁸(kπ/(2m+1))                                                *)
(*      = (384m⁸+1536m⁷+128m⁶−4992m⁵−528m⁴+9056m³−6984m²+1575m)/14175.*)
(*                                                                    *)
(*  Newton: Σr⁴ = (Σr)⁴ − 4(Σr)²e₂ + 4(Σr)e₃ + 2e₂² − 4e₄, with       *)
(*  e₄ = C(2m+1,9)/C(2m+1,1) via a Vieta lemma for the FOURTH          *)
(*  symmetric function (PFR_fifth — new).  Axiom-clean.              *)
(* ================================================================= *)

From Stdlib Require Import Reals List Lia Lra Factorial Binomial.
Import ListNotations.
Require Import BaselVieta BaselCotPoly BaselZeta4 BaselZeta6.
Open Scope R_scope.

Fixpoint e4 (rs : list R) : R :=
  match rs with
  | [] => 0
  | r :: p => e4 p + r * e3 p
  end.

Lemma newton4 : forall rs,
  fold_right Rplus 0 (map (fun r => r * r * r * r) rs)
  = (fold_right Rplus 0 rs) ^ 4 - 4 * (fold_right Rplus 0 rs) ^ 2 * (e2 rs)
    + 4 * (fold_right Rplus 0 rs) * (e3 rs) + 2 * (e2 rs) ^ 2 - 4 * (e4 rs).
Proof.
  induction rs as [| r p IH]; cbn [fold_right map e2 e3 e4]; [ ring | ].
  rewrite IH; ring.
Qed.

Lemma PFR_fifth : forall rs, (4 <= length rs)%nat ->
  nth (pred (pred (pred (pred (length rs))))) (PFR rs) 0 = e4 rs.
Proof.
  induction rs as [| r0 rs IH]; intro Hlen; [ cbn in Hlen; lia | ].
  destruct rs as [| r1 rs']; [ cbn in Hlen; lia | ].
  destruct rs' as [| r2 rs'']; [ cbn in Hlen; lia | ].
  destruct rs'' as [| r3 rs''']; [ cbn in Hlen; lia | ].
  destruct rs''' as [| r4 rs''''].
  - cbn [PFR length pred nth Xsub Padd Pscale map fold_right e2 e3 e4]; ring.
  - change (PFR (r0 :: r1 :: r2 :: r3 :: r4 :: rs''''))
      with (Xsub r0 (PFR (r1 :: r2 :: r3 :: r4 :: rs''''))).
    cbn [length pred].
    unfold Xsub; rewrite nth_Padd, nth_Pscale.
    change (nth (S (length rs'''')) (0 :: PFR (r1 :: r2 :: r3 :: r4 :: rs'''')) 0)
      with (nth (length rs'''') (PFR (r1 :: r2 :: r3 :: r4 :: rs'''')) 0).
    pose proof (IH ltac:(cbn [length]; lia)) as HIH; cbn [length pred] in HIH.
    pose proof (PFR_fourth (r1 :: r2 :: r3 :: r4 :: rs'''') ltac:(cbn [length]; lia)) as HPF;
      cbn [length pred] in HPF.
    rewrite HIH, HPF.
    change (e4 (r0 :: r1 :: r2 :: r3 :: r4 :: rs''''))
      with (e4 (r1 :: r2 :: r3 :: r4 :: rs'''') + r0 * e3 (r1 :: r2 :: r3 :: r4 :: rs'''')).
    ring.
Qed.

Lemma Plist_fifth : forall m, (4 <= m)%nat ->
  nth (pred (pred (pred (pred m)))) (Plist m) 0 = Binomial.C (2 * m + 1) 9.
Proof.
  intros m Hm; unfold Plist.
  set (g := fun i => (-1) ^ (m - i) * Binomial.C (2 * m + 1) (2 * (m - i) + 1)).
  rewrite (@nth_indep R (map g (seq 0 (S m))) (pred (pred (pred (pred m)))) 0 (g 0%nat))
    by (rewrite length_map, length_seq; lia).
  rewrite (map_nth g (seq 0 (S m)) 0%nat (pred (pred (pred (pred m))))), seq_nth by lia.
  cbn [Nat.add]. unfold g. replace (m - pred (pred (pred (pred m))))%nat with 4%nat by lia.
  cbn [pow]. change (2 * 4 + 1)%nat with 9%nat. ring.
Qed.

Lemma fact_down8 : forall m, (4 <= m)%nat ->
  fact (2 * m)
  = ((2*m) * ((2*m-1) * ((2*m-2) * ((2*m-3) * ((2*m-4) * ((2*m-5) *
      ((2*m-6) * ((2*m-7) * fact (2*m-8))))))))) %nat.
Proof.
  intros m Hm; replace (2 * m)%nat with (S (S (S (S (S (S (S (S (2 * m - 8))))))))) by lia.
  cbn [fact].
  replace (S (S (S (S (S (S (S (S (2*m-8)))))))) - 1)%nat with (S (S (S (S (S (S (S (2*m-8)))))))) by lia.
  replace (S (S (S (S (S (S (S (S (2*m-8)))))))) - 2)%nat with (S (S (S (S (S (S (2*m-8))))))) by lia.
  replace (S (S (S (S (S (S (S (S (2*m-8)))))))) - 3)%nat with (S (S (S (S (S (2*m-8)))))) by lia.
  replace (S (S (S (S (S (S (S (S (2*m-8)))))))) - 4)%nat with (S (S (S (S (2*m-8))))) by lia.
  replace (S (S (S (S (S (S (S (S (2*m-8)))))))) - 5)%nat with (S (S (S (2*m-8)))) by lia.
  replace (S (S (S (S (S (S (S (S (2*m-8)))))))) - 6)%nat with (S (S (2*m-8))) by lia.
  replace (S (S (S (S (S (S (S (S (2*m-8)))))))) - 7)%nat with (S (2*m-8)) by lia.
  replace (S (S (S (S (S (S (S (S (2*m-8)))))))) - 8)%nat with (2*m-8)%nat by lia.
  cbn [fact]; ring.
Qed.

Lemma C_ratio9 : forall m, (4 <= m)%nat ->
  Binomial.C (2 * m + 1) 9 / Binomial.C (2 * m + 1) 1
  = (2*INR m)*(2*INR m-1)*(2*INR m-2)*(2*INR m-3)*(2*INR m-4)*(2*INR m-5)*(2*INR m-6)*(2*INR m-7)
    / 362880.
Proof.
  intros m Hm; unfold Binomial.C.
  replace (2 * m + 1 - 1)%nat with (2 * m)%nat by lia.
  replace (2 * m + 1 - 9)%nat with (2 * m - 8)%nat by lia.
  rewrite (fact_down8 m Hm).
  rewrite !mult_INR, !minus_INR by lia.
  assert (Hf1 : INR (fact 1) = 1) by (simpl; ring).
  assert (Hf9 : INR (fact 9) = 362880)
    by (rewrite INR_IZR_INZ; f_equal; vm_compute; reflexivity).
  rewrite Hf1, Hf9.
  replace (INR (2 * m)) with (2 * INR m) by (rewrite mult_INR; simpl (INR 2); ring).
  replace (INR 1) with 1 by (simpl; ring).
  replace (INR 2) with 2 by (simpl; ring). replace (INR 3) with 3 by (simpl; ring).
  replace (INR 4) with 4 by (simpl; ring). replace (INR 5) with 5 by (simpl; ring).
  replace (INR 6) with 6 by (simpl; ring). replace (INR 7) with 7 by (simpl; ring).
  assert (H1 : INR (fact (2 * m + 1)) <> 0) by apply INR_fact_neq_0.
  assert (H2 : INR (fact (2 * m - 8)) <> 0) by apply INR_fact_neq_0.
  assert (Hmpos : 4 <= INR m) by (replace 4 with (INR 4) by (simpl; ring); apply le_INR; lia).
  field; repeat split; try assumption; lra.
Qed.

Lemma cot_e4 : forall m, (4 <= m)%nat ->
  e4 (map (fun k => Rcot (theta m k) ^ 2) (seq 1 m))
  = (2*INR m)*(2*INR m-1)*(2*INR m-2)*(2*INR m-3)*(2*INR m-4)*(2*INR m-5)*(2*INR m-6)*(2*INR m-7)
    / 362880.
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
  pose proof (vieta_coeff (Plist m) rs (pred (pred (pred (pred (length rs))))) Hpl Hne Hnd Hroots Hlead) as HV.
  rewrite (PFR_fifth rs ltac:(rewrite Hlen_rs; lia)) in HV.
  rewrite Hlen_rs in HV.
  rewrite (Plist_fifth m Hm), (Plist_leading m), (C_n_1 (2 * m + 1) ltac:(lia)) in HV.
  fold rs.
  assert (Hne1 : INR (2 * m + 1) <> 0) by (apply not_0_INR; lia).
  pose proof (C_ratio9 m Hm) as HC9; rewrite (C_n_1 (2 * m + 1) ltac:(lia)) in HC9.
  apply (Rmult_eq_reg_l (INR (2 * m + 1))); [ | exact Hne1 ].
  rewrite <- HC9; replace (INR (2 * m + 1) * (Binomial.C (2 * m + 1) 9 / INR (2 * m + 1)))
    with (Binomial.C (2 * m + 1) 9) by (field; exact Hne1).
  rewrite <- HV; ring.
Qed.

Theorem cot8_sum : forall m, (4 <= m)%nat ->
  sum_f_R0 (fun k => Rcot (INR (S k) * PI / INR (2 * m + 1)) ^ 8) (m - 1)
  = (384 * INR m ^ 8 + 1536 * INR m ^ 7 + 128 * INR m ^ 6 - 4992 * INR m ^ 5
     - 528 * INR m ^ 4 + 9056 * INR m ^ 3 - 6984 * INR m ^ 2 + 1575 * INR m) / 14175.
Proof.
  intros m Hm.
  transitivity (fold_right Rplus 0
                  (map (fun r => r * r * r * r) (map (fun k => Rcot (theta m k) ^ 2) (seq 1 m)))).
  - rewrite map_map.
    rewrite (fold_right_map_seq
               (fun k => Rcot (theta m k) ^ 2 * (Rcot (theta m k) ^ 2)
                         * (Rcot (theta m k) ^ 2) * (Rcot (theta m k) ^ 2)) m ltac:(lia)).
    apply sum_eq; intros k _; unfold theta; ring.
  - rewrite newton4, (cot_e2 m ltac:(lia)), (cot_e3 m ltac:(lia)), (cot_e4 m Hm).
    replace (fold_right Rplus 0 (map (fun k => Rcot (theta m k) ^ 2) (seq 1 m)))
      with (INR m * (2 * INR m - 1) / 3).
    2:{ rewrite (fold_right_map_seq (fun k => Rcot (theta m k) ^ 2) m ltac:(lia)).
        rewrite <- (cot_sq_sum m ltac:(lia)); apply sum_eq; intros k _; unfold theta; reflexivity. }
    field.
Qed.

Print Assumptions cot8_sum.

(* ================================================================= *)
(*  END BaselZeta8.v.                                                 *)
(* ================================================================= *)
