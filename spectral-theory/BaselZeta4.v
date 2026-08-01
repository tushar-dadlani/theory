(* ================================================================= *)
(*  BaselZeta4.v  —  the fourth-power cotangent sum, toward ζ(4).      *)
(*                                                                    *)
(*    Σ_{k=1}^m cot⁴(kπ/(2m+1)) = m(2m−1)(4m²+10m−9)/45.               *)
(*                                                                    *)
(*  The roots r_k = cot²(kπ/(2m+1)) of Pcot m satisfy (Newton)         *)
(*    Σ r_k² = (Σ r_k)² − 2·e₂,                                        *)
(*  where e₁ = Σ r_k = C(2m+1,3)/C(2m+1,1) = m(2m−1)/3 (cot_sq_sum)     *)
(*  and e₂ = C(2m+1,5)/C(2m+1,1) via a Vieta lemma for the SECOND       *)
(*  symmetric function (vieta_e2, PFR_third — new; the repo had only   *)
(*  the sum-of-roots case).  No new axioms (classical Reals only).     *)
(* ================================================================= *)

From Stdlib Require Import Reals List Lia Lra Factorial Binomial.
Import ListNotations.
Require Import BaselVieta BaselCotPoly.
Open Scope R_scope.

(* --- the second elementary symmetric function of a list --- *)

Fixpoint e2 (rs : list R) : R :=
  match rs with
  | [] => 0
  | r :: p => e2 p + r * fold_right Rplus 0 p
  end.

(* --- Newton's identity  Σ rᵢ² = (Σ rᵢ)² − 2 e₂  --- *)

Lemma newton2 : forall rs,
  fold_right Rplus 0 (map (fun r => r * r) rs) = (fold_right Rplus 0 rs) ^ 2 - 2 * e2 rs.
Proof.
  induction rs as [| r p IH]; cbn [fold_right map e2]; [ ring | ].
  rewrite IH; ring.
Qed.

(* --- Vieta:  every coefficient of p matches am · (coeff of ∏(x−rᵢ)) --- *)

Lemma vieta_coeff : forall (p rs : list R) i,
  length p = S (length rs) -> rs <> [] -> NoDup rs ->
  (forall r, In r rs -> Peval p r = 0) ->
  nth (length rs) p 0 <> 0 ->
  nth i p 0 = nth (length rs) p 0 * nth i (PFR rs) 0.
Proof.
  intros p rs i Hlen Hne Hnd Hroots Hlead.
  set (am := nth (length rs) p 0) in *.
  set (D := Padd p (Pscale (-1) (Pscale am (PFR rs)))).
  assert (HDlen : length D = S (length rs))
    by (unfold D; rewrite length_Padd, !length_Pscale, PFR_length, Hlen; lia).
  assert (HnthD : forall j, nth j D 0 = nth j p 0 - am * nth j (PFR rs) 0)
    by (intro j; unfold D; rewrite nth_Padd, nth_Pscale, nth_Pscale; ring).
  assert (HDlead : nth (length rs) D 0 = 0)
    by (rewrite HnthD, PFR_leading; unfold am; ring).
  assert (HDne : D <> []) by (intro HH; rewrite HH in HDlen; cbn in HDlen; lia).
  assert (HlastD : last D 0 = 0)
    by (rewrite last_nth by exact HDne; rewrite HDlen; cbn [pred]; exact HDlead).
  assert (HDroot : forall r, In r rs -> Peval D r = 0)
    by (intros r Hr; unfold D; rewrite Peval_add, Peval_scale, Peval_scale,
          (PFR_root rs r Hr), (Hroots r Hr); ring).
  assert (HDzero : forall x, Peval D x = 0).
  { intro x; rewrite <- (Peval_removelast0 D x HlastD).
    apply (too_many_roots (length rs) (removelast D) rs); [ | reflexivity | exact Hnd | ].
    - rewrite length_removelast_cons by exact HDne; rewrite HDlen; cbn [pred]; lia.
    - intros r Hr; rewrite (Peval_removelast0 D r HlastD); apply HDroot; exact Hr. }
  pose proof (poly_fun_zero_coeffs D HDzero i) as HDc; rewrite HnthD in HDc; lra.
Qed.

(* --- PFR_third: the x^{m−2} coefficient of ∏(x−rᵢ) is e₂ --- *)

Lemma PFR_third : forall rs, (2 <= length rs)%nat ->
  nth (pred (pred (length rs))) (PFR rs) 0 = e2 rs.
Proof.
  induction rs as [| r0 rs IH]; intro Hlen; [ cbn in Hlen; lia | ].
  destruct rs as [| r1 rs']; [ cbn in Hlen; lia | ].
  destruct rs' as [| r2 rs''].
  - cbn [PFR length pred nth Xsub Padd Pscale map fold_right e2]; ring.
  - change (PFR (r0 :: r1 :: r2 :: rs'')) with (Xsub r0 (PFR (r1 :: r2 :: rs''))).
    cbn [length pred].
    unfold Xsub; rewrite nth_Padd, nth_Pscale.
    change (nth (S (length rs'')) (0 :: PFR (r1 :: r2 :: rs'')) 0)
      with (nth (length rs'') (PFR (r1 :: r2 :: rs'')) 0).
    pose proof (IH ltac:(cbn [length]; lia)) as HIH; cbn [length pred] in HIH.
    pose proof (PFR_second (r1 :: r2 :: rs'') ltac:(discriminate)) as HPS;
      cbn [length pred] in HPS.
    rewrite HIH, HPS.
    change (e2 (r0 :: r1 :: r2 :: rs''))
      with (e2 (r1 :: r2 :: rs'') + r0 * fold_right Rplus 0 (r1 :: r2 :: rs'')).
    ring.
Qed.

(* --- Plist_third: the (m−2) coefficient of Pcot is C(2m+1,5) --- *)

Lemma Plist_third : forall m, (2 <= m)%nat ->
  nth (pred (pred m)) (Plist m) 0 = Binomial.C (2 * m + 1) 5.
Proof.
  intros m Hm; unfold Plist.
  set (g := fun i => (-1) ^ (m - i) * Binomial.C (2 * m + 1) (2 * (m - i) + 1)).
  rewrite (@nth_indep R (map g (seq 0 (S m))) (pred (pred m)) 0 (g 0%nat))
    by (rewrite length_map, length_seq; lia).
  rewrite (map_nth g (seq 0 (S m)) 0%nat (pred (pred m))), seq_nth by lia.
  cbn [Nat.add]. unfold g. replace (m - pred (pred m))%nat with 2%nat by lia.
  cbn [pow]. change (2 * 2 + 1)%nat with 5%nat. ring.
Qed.

(* --- binomial arithmetic: C(2m+1,5)/C(2m+1,1) --- *)

Lemma fact_down4 : forall m, (2 <= m)%nat ->
  fact (2 * m) = ((2 * m) * ((2 * m - 1) * ((2 * m - 2) * ((2 * m - 3) * fact (2 * m - 4)))))%nat.
Proof.
  intros m Hm; replace (2 * m)%nat with (S (S (S (S (2 * m - 4))))) by lia.
  cbn [fact].
  replace (S (S (S (S (2 * m - 4)))) - 1)%nat with (S (S (S (2 * m - 4)))) by lia.
  replace (S (S (S (S (2 * m - 4)))) - 2)%nat with (S (S (2 * m - 4))) by lia.
  replace (S (S (S (S (2 * m - 4)))) - 3)%nat with (S (2 * m - 4)) by lia.
  replace (S (S (S (S (2 * m - 4)))) - 4)%nat with (2 * m - 4)%nat by lia.
  cbn [fact]; ring.
Qed.

Lemma C_ratio5 : forall m, (2 <= m)%nat ->
  Binomial.C (2 * m + 1) 5 / Binomial.C (2 * m + 1) 1
  = (2 * INR m) * (2 * INR m - 1) * (2 * INR m - 2) * (2 * INR m - 3) / 120.
Proof.
  intros m Hm; unfold Binomial.C.
  replace (2 * m + 1 - 1)%nat with (2 * m)%nat by lia.
  replace (2 * m + 1 - 5)%nat with (2 * m - 4)%nat by lia.
  rewrite (fact_down4 m Hm).
  rewrite !mult_INR, !minus_INR by lia.
  simpl (fact 1); simpl (fact 5); simpl (INR 1); simpl (INR 5).
  replace (INR (2 * m)) with (2 * INR m) by (rewrite mult_INR; simpl (INR 2); ring).
  replace (INR 2) with 2 by (simpl; ring). replace (INR 3) with 3 by (simpl; ring).
  replace (INR 4) with 4 by (simpl; ring). replace (INR 120) with 120 by (simpl; ring).
  assert (H1 : INR (fact (2 * m + 1)) <> 0) by apply INR_fact_neq_0.
  assert (H2 : INR (fact (2 * m - 4)) <> 0) by apply INR_fact_neq_0.
  assert (Hmpos : 2 <= INR m) by (replace 2 with (INR 2) by (simpl; ring); apply le_INR; lia).
  field; repeat split; try assumption; lra.
Qed.

(* --- e₂ of the cotangent roots --- *)

Lemma cot_e2 : forall m, (2 <= m)%nat ->
  e2 (map (fun k => Rcot (theta m k) ^ 2) (seq 1 m))
  = (2 * INR m) * (2 * INR m - 1) * (2 * INR m - 2) * (2 * INR m - 3) / 120.
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
  pose proof (vieta_coeff (Plist m) rs (pred (pred (length rs))) Hpl Hne Hnd Hroots Hlead) as HV.
  rewrite (PFR_third rs ltac:(rewrite Hlen_rs; lia)) in HV.
  rewrite Hlen_rs in HV.
  rewrite (Plist_third m Hm), (Plist_leading m), (C_n_1 (2 * m + 1) ltac:(lia)) in HV.
  fold rs.
  assert (Hne1 : INR (2 * m + 1) <> 0) by (apply not_0_INR; lia).
  pose proof (C_ratio5 m Hm) as HC5; rewrite (C_n_1 (2 * m + 1) ltac:(lia)) in HC5.
  apply (Rmult_eq_reg_l (INR (2 * m + 1))); [ | exact Hne1 ].
  rewrite <- HV, <- HC5; field; exact Hne1.
Qed.

(* --- the fourth-power cotangent sum --- *)

Theorem cot4_sum : forall m, (2 <= m)%nat ->
  sum_f_R0 (fun k => Rcot (INR (S k) * PI / INR (2 * m + 1)) ^ 4) (m - 1)
  = INR m * (2 * INR m - 1) * (4 * INR m ^ 2 + 10 * INR m - 9) / 45.
Proof.
  intros m Hm.
  transitivity (fold_right Rplus 0
                  (map (fun r => r * r) (map (fun k => Rcot (theta m k) ^ 2) (seq 1 m)))).
  - rewrite map_map.
    rewrite (fold_right_map_seq
               (fun k => Rcot (theta m k) ^ 2 * (Rcot (theta m k) ^ 2)) m ltac:(lia)).
    apply sum_eq; intros k _; unfold theta; ring.
  - rewrite newton2, (cot_e2 m Hm).
    replace (fold_right Rplus 0 (map (fun k => Rcot (theta m k) ^ 2) (seq 1 m)))
      with (INR m * (2 * INR m - 1) / 3).
    2:{ rewrite (fold_right_map_seq (fun k => Rcot (theta m k) ^ 2) m ltac:(lia)).
        rewrite <- (cot_sq_sum m ltac:(lia)); apply sum_eq; intros k _; unfold theta; reflexivity. }
    field.
Qed.

Print Assumptions cot4_sum.

(* ================================================================= *)
(*  END BaselZeta4.v.  Σ cot⁴(kπ/(2m+1)) = m(2m−1)(4m²+10m−9)/45.       *)
(* ================================================================= *)
