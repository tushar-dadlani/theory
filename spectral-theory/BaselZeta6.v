(* ================================================================= *)
(*  BaselZeta6.v  —  the sixth-power cotangent sum, toward ζ(6).       *)
(*                                                                    *)
(*    Σ_{k=1}^m cot⁶(kπ/(2m+1))                                        *)
(*      = (64m⁶+192m⁵−96m⁴−512m³+522m²−135m)/945.                     *)
(*                                                                    *)
(*  The roots r_k = cot²(kπ/(2m+1)) satisfy (Newton)                   *)
(*    Σ r_k³ = (Σr_k)³ − 3(Σr_k)·e₂ + 3·e₃,                            *)
(*  where e₂ = C(2m+1,5)/C(2m+1,1) (BaselZeta4) and                    *)
(*  e₃ = C(2m+1,7)/C(2m+1,1) via a Vieta lemma for the THIRD symmetric *)
(*  function (vieta_coeff + PFR_fourth — new).  Axiom-clean.          *)
(* ================================================================= *)

From Stdlib Require Import Reals List Lia Lra Factorial Binomial.
Import ListNotations.
Require Import BaselVieta BaselCotPoly BaselZeta4.
Open Scope R_scope.

(* --- the third elementary symmetric function, and Newton for p₃ --- *)

Fixpoint e3 (rs : list R) : R :=
  match rs with
  | [] => 0
  | r :: p => e3 p + r * e2 p
  end.

Lemma newton3 : forall rs,
  fold_right Rplus 0 (map (fun r => r * r * r) rs)
  = (fold_right Rplus 0 rs) ^ 3 - 3 * (fold_right Rplus 0 rs) * (e2 rs) + 3 * (e3 rs).
Proof.
  induction rs as [| r p IH]; cbn [fold_right map e2 e3]; [ ring | ].
  rewrite IH; ring.
Qed.

(* --- PFR_fourth: the x^{m−3} coefficient of ∏(x−rᵢ) is −e₃ --- *)

Lemma PFR_fourth : forall rs, (3 <= length rs)%nat ->
  nth (pred (pred (pred (length rs)))) (PFR rs) 0 = - e3 rs.
Proof.
  induction rs as [| r0 rs IH]; intro Hlen; [ cbn in Hlen; lia | ].
  destruct rs as [| r1 rs']; [ cbn in Hlen; lia | ].
  destruct rs' as [| r2 rs'']; [ cbn in Hlen; lia | ].
  destruct rs'' as [| r3 rs'''].
  - cbn [PFR length pred nth Xsub Padd Pscale map fold_right e2 e3]; ring.
  - change (PFR (r0 :: r1 :: r2 :: r3 :: rs''')) with (Xsub r0 (PFR (r1 :: r2 :: r3 :: rs'''))).
    cbn [length pred].
    unfold Xsub; rewrite nth_Padd, nth_Pscale.
    change (nth (S (length rs''')) (0 :: PFR (r1 :: r2 :: r3 :: rs''')) 0)
      with (nth (length rs''') (PFR (r1 :: r2 :: r3 :: rs''')) 0).
    pose proof (IH ltac:(cbn [length]; lia)) as HIH; cbn [length pred] in HIH.
    pose proof (PFR_third (r1 :: r2 :: r3 :: rs''') ltac:(cbn [length]; lia)) as HPT;
      cbn [length pred] in HPT.
    rewrite HIH, HPT.
    change (e3 (r0 :: r1 :: r2 :: r3 :: rs'''))
      with (e3 (r1 :: r2 :: r3 :: rs''') + r0 * e2 (r1 :: r2 :: r3 :: rs''')).
    ring.
Qed.

(* --- Plist_fourth: the (m−3) coefficient of Pcot is −C(2m+1,7) --- *)

Lemma Plist_fourth : forall m, (3 <= m)%nat ->
  nth (pred (pred (pred m))) (Plist m) 0 = - Binomial.C (2 * m + 1) 7.
Proof.
  intros m Hm; unfold Plist.
  set (g := fun i => (-1) ^ (m - i) * Binomial.C (2 * m + 1) (2 * (m - i) + 1)).
  rewrite (@nth_indep R (map g (seq 0 (S m))) (pred (pred (pred m))) 0 (g 0%nat))
    by (rewrite length_map, length_seq; lia).
  rewrite (map_nth g (seq 0 (S m)) 0%nat (pred (pred (pred m)))), seq_nth by lia.
  cbn [Nat.add]. unfold g. replace (m - pred (pred (pred m)))%nat with 3%nat by lia.
  cbn [pow]. change (2 * 3 + 1)%nat with 7%nat. ring.
Qed.

(* --- binomial arithmetic: C(2m+1,7)/C(2m+1,1) --- *)

Lemma fact_down6 : forall m, (3 <= m)%nat ->
  fact (2 * m)
  = ((2*m) * ((2*m-1) * ((2*m-2) * ((2*m-3) * ((2*m-4) * ((2*m-5) * fact (2*m-6)))))))%nat.
Proof.
  intros m Hm; replace (2 * m)%nat with (S (S (S (S (S (S (2 * m - 6))))))) by lia.
  cbn [fact].
  replace (S (S (S (S (S (S (2*m-6)))))) - 1)%nat with (S (S (S (S (S (2*m-6)))))) by lia.
  replace (S (S (S (S (S (S (2*m-6)))))) - 2)%nat with (S (S (S (S (2*m-6))))) by lia.
  replace (S (S (S (S (S (S (2*m-6)))))) - 3)%nat with (S (S (S (2*m-6)))) by lia.
  replace (S (S (S (S (S (S (2*m-6)))))) - 4)%nat with (S (S (2*m-6))) by lia.
  replace (S (S (S (S (S (S (2*m-6)))))) - 5)%nat with (S (2*m-6)) by lia.
  replace (S (S (S (S (S (S (2*m-6)))))) - 6)%nat with (2*m-6)%nat by lia.
  cbn [fact]; ring.
Qed.

Lemma C_ratio7 : forall m, (3 <= m)%nat ->
  Binomial.C (2 * m + 1) 7 / Binomial.C (2 * m + 1) 1
  = (2*INR m) * (2*INR m-1) * (2*INR m-2) * (2*INR m-3) * (2*INR m-4) * (2*INR m-5) / 5040.
Proof.
  intros m Hm; unfold Binomial.C.
  replace (2 * m + 1 - 1)%nat with (2 * m)%nat by lia.
  replace (2 * m + 1 - 7)%nat with (2 * m - 6)%nat by lia.
  rewrite (fact_down6 m Hm).
  rewrite !mult_INR, !minus_INR by lia.
  assert (Hf1 : INR (fact 1) = 1) by (simpl; ring).
  assert (Hf7 : INR (fact 7) = 5040)
    by (rewrite INR_IZR_INZ; f_equal; vm_compute; reflexivity).
  rewrite Hf1, Hf7.
  replace (INR (2 * m)) with (2 * INR m) by (rewrite mult_INR; simpl (INR 2); ring).
  replace (INR 1) with 1 by (simpl; ring).
  replace (INR 2) with 2 by (simpl; ring). replace (INR 3) with 3 by (simpl; ring).
  replace (INR 4) with 4 by (simpl; ring). replace (INR 5) with 5 by (simpl; ring).
  replace (INR 6) with 6 by (simpl; ring).
  assert (H1 : INR (fact (2 * m + 1)) <> 0) by apply INR_fact_neq_0.
  assert (H2 : INR (fact (2 * m - 6)) <> 0) by apply INR_fact_neq_0.
  assert (Hmpos : 3 <= INR m) by (replace 3 with (INR 3) by (simpl; ring); apply le_INR; lia).
  field; repeat split; try assumption; lra.
Qed.

(* --- e₃ of the cotangent roots --- *)

Lemma cot_e3 : forall m, (3 <= m)%nat ->
  e3 (map (fun k => Rcot (theta m k) ^ 2) (seq 1 m))
  = (2*INR m) * (2*INR m-1) * (2*INR m-2) * (2*INR m-3) * (2*INR m-4) * (2*INR m-5) / 5040.
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
  pose proof (vieta_coeff (Plist m) rs (pred (pred (pred (length rs)))) Hpl Hne Hnd Hroots Hlead) as HV.
  rewrite (PFR_fourth rs ltac:(rewrite Hlen_rs; lia)) in HV.
  rewrite Hlen_rs in HV.
  rewrite (Plist_fourth m Hm), (Plist_leading m), (C_n_1 (2 * m + 1) ltac:(lia)) in HV.
  fold rs.
  assert (Hne1 : INR (2 * m + 1) <> 0) by (apply not_0_INR; lia).
  pose proof (C_ratio7 m Hm) as HC7; rewrite (C_n_1 (2 * m + 1) ltac:(lia)) in HC7.
  replace (INR (2 * m + 1) * - e3 rs) with (- (INR (2 * m + 1) * e3 rs)) in HV by ring.
  assert (HV' : INR (2 * m + 1) * e3 rs = Binomial.C (2 * m + 1) 7) by lra.
  apply (Rmult_eq_reg_l (INR (2 * m + 1))); [ | exact Hne1 ].
  rewrite <- HC7; replace (INR (2 * m + 1) * (Binomial.C (2 * m + 1) 7 / INR (2 * m + 1)))
    with (Binomial.C (2 * m + 1) 7) by (field; exact Hne1).
  exact HV'.
Qed.

(* --- the sixth-power cotangent sum --- *)

Theorem cot6_sum : forall m, (3 <= m)%nat ->
  sum_f_R0 (fun k => Rcot (INR (S k) * PI / INR (2 * m + 1)) ^ 6) (m - 1)
  = (64 * INR m ^ 6 + 192 * INR m ^ 5 - 96 * INR m ^ 4 - 512 * INR m ^ 3
     + 522 * INR m ^ 2 - 135 * INR m) / 945.
Proof.
  intros m Hm.
  transitivity (fold_right Rplus 0
                  (map (fun r => r * r * r) (map (fun k => Rcot (theta m k) ^ 2) (seq 1 m)))).
  - rewrite map_map.
    rewrite (fold_right_map_seq
               (fun k => Rcot (theta m k) ^ 2 * (Rcot (theta m k) ^ 2) * (Rcot (theta m k) ^ 2))
               m ltac:(lia)).
    apply sum_eq; intros k _; unfold theta; ring.
  - rewrite newton3, (cot_e2 m ltac:(lia)), (cot_e3 m Hm).
    replace (fold_right Rplus 0 (map (fun k => Rcot (theta m k) ^ 2) (seq 1 m)))
      with (INR m * (2 * INR m - 1) / 3).
    2:{ rewrite (fold_right_map_seq (fun k => Rcot (theta m k) ^ 2) m ltac:(lia)).
        rewrite <- (cot_sq_sum m ltac:(lia)); apply sum_eq; intros k _; unfold theta; reflexivity. }
    field.
Qed.

Print Assumptions cot6_sum.

(* ================================================================= *)
(*  END BaselZeta6.v.  Σ cot⁶ = (64m⁶+192m⁵−96m⁴−512m³+522m²−135m)/945.*)
(* ================================================================= *)
