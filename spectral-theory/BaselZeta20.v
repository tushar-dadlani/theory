(* ================================================================= *)
(*  BaselZeta20.v  —  the twentieth-power cotangent sum, toward zeta(20).*)
(*  Sigma cot^20 = closed poly / 32157918771103125,                   *)
(*  zeta(20)=174611*pi^20/1531329465290625.  Vieta ladder extended to  *)
(*  the TENTH symmetric function e10 (Newton p10, 42 terms; PFR_eleventh*)
(*  with sign (-1)^10 = +).  Axiom-clean.                              *)
(* ================================================================= *)

From Stdlib Require Import Reals List Lia Lra Factorial Binomial ZArith.
Import ListNotations.
Require Import BaselVieta BaselCotPoly BaselZeta4 BaselZeta6 BaselZeta8 BaselZeta10 BaselZeta12 BaselZeta14 BaselZeta16 BaselZeta18 BaselZeta20Poly.
Open Scope R_scope.

Fixpoint e10 (rs : list R) : R :=
  match rs with
  | [] => 0
  | r :: p => e10 p + r * e9 p
  end.

Lemma newton10 : forall rs,
  fold_right Rplus 0 (map (fun r => r * r * r * r * r * r * r * r * r * r) rs)
  = (fold_right Rplus 0 rs)^10
    - 10*(fold_right Rplus 0 rs)^8*(e2 rs)
    + 35*(fold_right Rplus 0 rs)^6*(e2 rs)^2
    + 10*(fold_right Rplus 0 rs)^7*(e3 rs)
    - 50*(fold_right Rplus 0 rs)^4*(e2 rs)^3
    - 60*(fold_right Rplus 0 rs)^5*(e2 rs)*(e3 rs)
    - 10*(fold_right Rplus 0 rs)^6*(e4 rs)
    + 25*(fold_right Rplus 0 rs)^2*(e2 rs)^4
    + 100*(fold_right Rplus 0 rs)^3*(e2 rs)^2*(e3 rs)
    + 25*(fold_right Rplus 0 rs)^4*(e3 rs)^2
    + 50*(fold_right Rplus 0 rs)^4*(e2 rs)*(e4 rs)
    + 10*(fold_right Rplus 0 rs)^5*(e5 rs)
    - 2*(e2 rs)^5
    - 40*(fold_right Rplus 0 rs)*(e2 rs)^3*(e3 rs)
    - 60*(fold_right Rplus 0 rs)^2*(e2 rs)*(e3 rs)^2
    - 60*(fold_right Rplus 0 rs)^2*(e2 rs)^2*(e4 rs)
    - 40*(fold_right Rplus 0 rs)^3*(e3 rs)*(e4 rs)
    - 40*(fold_right Rplus 0 rs)^3*(e2 rs)*(e5 rs)
    - 10*(fold_right Rplus 0 rs)^4*(e6 rs)
    + 15*(e2 rs)^2*(e3 rs)^2
    + 10*(e2 rs)^3*(e4 rs)
    + 10*(fold_right Rplus 0 rs)*(e3 rs)^3
    + 60*(fold_right Rplus 0 rs)*(e2 rs)*(e3 rs)*(e4 rs)
    + 30*(fold_right Rplus 0 rs)*(e2 rs)^2*(e5 rs)
    + 15*(fold_right Rplus 0 rs)^2*(e4 rs)^2
    + 30*(fold_right Rplus 0 rs)^2*(e3 rs)*(e5 rs)
    + 30*(fold_right Rplus 0 rs)^2*(e2 rs)*(e6 rs)
    + 10*(fold_right Rplus 0 rs)^3*(e7 rs)
    - 10*(e3 rs)^2*(e4 rs)
    - 10*(e2 rs)*(e4 rs)^2
    - 20*(e2 rs)*(e3 rs)*(e5 rs)
    - 10*(e2 rs)^2*(e6 rs)
    - 20*(fold_right Rplus 0 rs)*(e4 rs)*(e5 rs)
    - 20*(fold_right Rplus 0 rs)*(e3 rs)*(e6 rs)
    - 20*(fold_right Rplus 0 rs)*(e2 rs)*(e7 rs)
    - 10*(fold_right Rplus 0 rs)^2*(e8 rs)
    + 5*(e5 rs)^2
    + 10*(e4 rs)*(e6 rs)
    + 10*(e3 rs)*(e7 rs)
    + 10*(e2 rs)*(e8 rs)
    + 10*(fold_right Rplus 0 rs)*(e9 rs)
    - 10*(e10 rs).
Proof.
  induction rs as [| r p IH]; cbn [fold_right map e2 e3 e4 e5 e6 e7 e8 e9 e10]; [ ring | ].
  rewrite IH; ring.
Qed.

Lemma PFR_eleventh : forall rs, (10 <= length rs)%nat ->
  nth (pred (pred (pred (pred (pred (pred (pred (pred (pred (pred (length rs))))))))))) (PFR rs) 0 = e10 rs.
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
  destruct rs'''''''' as [| r9 rs''''''''']; [ cbn in Hlen; lia | ].
  destruct rs''''''''' as [| r10 rs''''''''''].
  - cbn [PFR length pred nth Xsub Padd Pscale map fold_right e2 e3 e4 e5 e6 e7 e8 e9 e10]; ring.
  - change (PFR (r0 :: r1 :: r2 :: r3 :: r4 :: r5 :: r6 :: r7 :: r8 :: r9 :: r10 :: rs''''''''''))
      with (Xsub r0 (PFR (r1 :: r2 :: r3 :: r4 :: r5 :: r6 :: r7 :: r8 :: r9 :: r10 :: rs''''''''''))).
    cbn [length pred].
    unfold Xsub; rewrite nth_Padd, nth_Pscale.
    change (nth (S (length rs'''''''''')) (0 :: PFR (r1 :: r2 :: r3 :: r4 :: r5 :: r6 :: r7 :: r8 :: r9 :: r10 :: rs'''''''''')) 0)
      with (nth (length rs'''''''''') (PFR (r1 :: r2 :: r3 :: r4 :: r5 :: r6 :: r7 :: r8 :: r9 :: r10 :: rs'''''''''')) 0).
    pose proof (IH ltac:(cbn [length]; lia)) as HIH; cbn [length pred] in HIH.
    pose proof (PFR_tenth (r1 :: r2 :: r3 :: r4 :: r5 :: r6 :: r7 :: r8 :: r9 :: r10 :: rs'''''''''') ltac:(cbn [length]; lia)) as HPF;
      cbn [length pred] in HPF.
    rewrite HIH, HPF.
    change (e10 (r0 :: r1 :: r2 :: r3 :: r4 :: r5 :: r6 :: r7 :: r8 :: r9 :: r10 :: rs''''''''''))
      with (e10 (r1 :: r2 :: r3 :: r4 :: r5 :: r6 :: r7 :: r8 :: r9 :: r10 :: rs'''''''''') + r0 * e9 (r1 :: r2 :: r3 :: r4 :: r5 :: r6 :: r7 :: r8 :: r9 :: r10 :: rs'''''''''')).
    ring.
Qed.

Lemma Plist_eleventh : forall m, (10 <= m)%nat ->
  nth (pred (pred (pred (pred (pred (pred (pred (pred (pred (pred (m))))))))))) (Plist m) 0 = Binomial.C (2 * m + 1) 21.
Proof.
  intros m Hm; unfold Plist.
  set (g := fun i => (-1) ^ (m - i) * Binomial.C (2 * m + 1) (2 * (m - i) + 1)).
  rewrite (@nth_indep R (map g (seq 0 (S m))) (pred (pred (pred (pred (pred (pred (pred (pred (pred (pred (m))))))))))) 0 (g 0%nat))
    by (rewrite length_map, length_seq; lia).
  rewrite (map_nth g (seq 0 (S m)) 0%nat (pred (pred (pred (pred (pred (pred (pred (pred (pred (pred (m)))))))))))), seq_nth by lia.
  cbn [Nat.add]. unfold g. replace (m - pred (pred (pred (pred (pred (pred (pred (pred (pred (pred (m)))))))))))%nat with 10%nat by lia.
  cbn [pow]. change (2 * 10 + 1)%nat with 21%nat. ring.
Qed.

Lemma fact_down20 : forall m, (10 <= m)%nat ->
  fact (2 * m)
  = ((2*m) * (2*m-1) * (2*m-2) * (2*m-3) * (2*m-4) * (2*m-5) * (2*m-6) * (2*m-7) * (2*m-8) * (2*m-9) * (2*m-10) * (2*m-11) * (2*m-12) * (2*m-13) * (2*m-14) * (2*m-15) * (2*m-16) * (2*m-17) * (2*m-18) * (2*m-19) * fact (2*m-20)) %nat.
Proof.
  intros m Hm; replace (2 * m)%nat with (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (2*m-20))))))))))))))))))))) by lia.
  cbn [fact].
  replace (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (2*m-20))))))))))))))))))))-1)%nat with (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (2*m-20))))))))))))))))))))%nat by lia.
  replace (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (2*m-20))))))))))))))))))))-2)%nat with (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (2*m-20)))))))))))))))))))%nat by lia.
  replace (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (2*m-20))))))))))))))))))))-3)%nat with (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (2*m-20))))))))))))))))))%nat by lia.
  replace (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (2*m-20))))))))))))))))))))-4)%nat with (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (2*m-20)))))))))))))))))%nat by lia.
  replace (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (2*m-20))))))))))))))))))))-5)%nat with (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (2*m-20))))))))))))))))%nat by lia.
  replace (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (2*m-20))))))))))))))))))))-6)%nat with (S (S (S (S (S (S (S (S (S (S (S (S (S (S (2*m-20)))))))))))))))%nat by lia.
  replace (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (2*m-20))))))))))))))))))))-7)%nat with (S (S (S (S (S (S (S (S (S (S (S (S (S (2*m-20))))))))))))))%nat by lia.
  replace (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (2*m-20))))))))))))))))))))-8)%nat with (S (S (S (S (S (S (S (S (S (S (S (S (2*m-20)))))))))))))%nat by lia.
  replace (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (2*m-20))))))))))))))))))))-9)%nat with (S (S (S (S (S (S (S (S (S (S (S (2*m-20))))))))))))%nat by lia.
  replace (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (2*m-20))))))))))))))))))))-10)%nat with (S (S (S (S (S (S (S (S (S (S (2*m-20)))))))))))%nat by lia.
  replace (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (2*m-20))))))))))))))))))))-11)%nat with (S (S (S (S (S (S (S (S (S (2*m-20))))))))))%nat by lia.
  replace (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (2*m-20))))))))))))))))))))-12)%nat with (S (S (S (S (S (S (S (S (2*m-20)))))))))%nat by lia.
  replace (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (2*m-20))))))))))))))))))))-13)%nat with (S (S (S (S (S (S (S (2*m-20))))))))%nat by lia.
  replace (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (2*m-20))))))))))))))))))))-14)%nat with (S (S (S (S (S (S (2*m-20)))))))%nat by lia.
  replace (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (2*m-20))))))))))))))))))))-15)%nat with (S (S (S (S (S (2*m-20))))))%nat by lia.
  replace (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (2*m-20))))))))))))))))))))-16)%nat with (S (S (S (S (2*m-20)))))%nat by lia.
  replace (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (2*m-20))))))))))))))))))))-17)%nat with (S (S (S (2*m-20))))%nat by lia.
  replace (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (2*m-20))))))))))))))))))))-18)%nat with (S (S (2*m-20)))%nat by lia.
  replace (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (2*m-20))))))))))))))))))))-19)%nat with (S (2*m-20))%nat by lia.
  replace (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (2*m-20))))))))))))))))))))-20)%nat with (2*m-20)%nat by lia.
  cbn [fact]; ring.
Qed.

Lemma C_ratio21 : forall m, (10 <= m)%nat ->
  Binomial.C (2 * m + 1) 21 / Binomial.C (2 * m + 1) 1
  = (2*INR m)*(2*INR m-1)*(2*INR m-2)*(2*INR m-3)*(2*INR m-4)*(2*INR m-5)*(2*INR m-6)*(2*INR m-7)*(2*INR m-8)*(2*INR m-9)*(2*INR m-10)*(2*INR m-11)*(2*INR m-12)*(2*INR m-13)*(2*INR m-14)*(2*INR m-15)*(2*INR m-16)*(2*INR m-17)*(2*INR m-18)*(2*INR m-19) / 51090942171709440000.
Proof.
  intros m Hm.
  assert (Hmpos : 10 <= INR m) by (replace 10 with (INR 10) by (simpl; ring); apply le_INR; lia).
  remember (2 * INR m * (2 * INR m - 1) * (2 * INR m - 2) * (2 * INR m - 3) * (2 * INR m - 4) * (2 * INR m - 5) * (2 * INR m - 6) * (2 * INR m - 7) * (2 * INR m - 8) * (2 * INR m - 9) * (2 * INR m - 10) * (2 * INR m - 11) * (2 * INR m - 12) * (2 * INR m - 13) * (2 * INR m - 14) * (2 * INR m - 15) * (2 * INR m - 16) * (2 * INR m - 17) * (2 * INR m - 18) * (2 * INR m - 19)) as P eqn:HP.
  assert (HPne : P <> 0)
    by (rewrite HP; apply Rgt_not_eq; repeat apply Rmult_lt_0_compat; lra).
  assert (Hstep : INR (fact (2 * m)) = P * INR (fact (2 * m - 20))).
  { rewrite HP, (fact_down20 m Hm), !mult_INR, !minus_INR by lia.
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
    replace (INR 17) with 17 by (simpl; ring);
    replace (INR 18) with 18 by (simpl; ring);
    replace (INR 19) with 19 by (simpl; ring).
    ring. }
  unfold Binomial.C.
  replace (2 * m + 1 - 1)%nat with (2 * m)%nat by lia.
  replace (2 * m + 1 - 21)%nat with (2 * m - 20)%nat by lia.
  assert (Hf1 : INR (fact 1) = 1) by (simpl; ring).
  assert (Hf21 : INR (fact 21) = 51090942171709440000)
    by (cbn [fact]; rewrite !mult_INR, !INR_IZR_INZ, <- !mult_IZR; f_equal).
  rewrite Hf1, Hf21, Hstep.
  field; repeat split; try apply INR_fact_neq_0; try exact HPne.
Qed.

Lemma cot_e10 : forall m, (10 <= m)%nat ->
  e10 (map (fun k => Rcot (theta m k) ^ 2) (seq 1 m))
  = (2*INR m)*(2*INR m-1)*(2*INR m-2)*(2*INR m-3)*(2*INR m-4)*(2*INR m-5)*(2*INR m-6)*(2*INR m-7)*(2*INR m-8)*(2*INR m-9)*(2*INR m-10)*(2*INR m-11)*(2*INR m-12)*(2*INR m-13)*(2*INR m-14)*(2*INR m-15)*(2*INR m-16)*(2*INR m-17)*(2*INR m-18)*(2*INR m-19) / 51090942171709440000.
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
  pose proof (vieta_coeff (Plist m) rs (pred (pred (pred (pred (pred (pred (pred (pred (pred (pred (length rs))))))))))) Hpl Hne Hnd Hroots Hlead) as HV.
  rewrite (PFR_eleventh rs ltac:(rewrite Hlen_rs; lia)) in HV.
  rewrite Hlen_rs in HV.
  rewrite (Plist_eleventh m Hm), (Plist_leading m), (C_n_1 (2 * m + 1) ltac:(lia)) in HV.
  fold rs.
  assert (Hne1 : INR (2 * m + 1) <> 0) by (apply not_0_INR; lia).
  pose proof (C_ratio21 m Hm) as HC21; rewrite (C_n_1 (2 * m + 1) ltac:(lia)) in HC21.
  apply (Rmult_eq_reg_l (INR (2 * m + 1))); [ | exact Hne1 ].
  rewrite <- HC21; replace (INR (2 * m + 1) * (Binomial.C (2 * m + 1) 21 / INR (2 * m + 1)))
    with (Binomial.C (2 * m + 1) 21) by (field; exact Hne1).
  symmetry; exact HV.
Qed.

Lemma cot_e10_exp : forall m, (10 <= m)%nat ->
  e10 (map (fun k => Rcot (theta m k) ^ 2) (seq 1 m))
  = (1048576*INR m^20 - 99614720*INR m^19 + 4407951360*INR m^18 - 120658329600*INR m^17 + 2288316973056*INR m^16 - 31914128179200*INR m^15 + 339033024593920*INR m^14 - 2803732577484800*INR m^13 + 18289568798232576*INR m^12 - 94782766595911680*INR m^11 + 391088184834247680*INR m^10 - 1281975682799385600*INR m^9 + 3316131069425637376*INR m^8 - 6689395630401628160*INR m^7 + 10331503137927613440*INR m^6 - 11884313195047296000*INR m^5 + 9761857211847868416*INR m^4 - 5348877842729226240*INR m^3 + 1726260587270553600*INR m^2 - 243290200817664000*INR m) / 51090942171709440000.
Proof. intros m Hm; rewrite (cot_e10 m Hm); unfold Rdiv; apply Rmult_eq_compat_r; ring. Qed.

Theorem cot20_sum : forall m, (10 <= m)%nat ->
  sum_f_R0 (fun k => Rcot (INR (S k) * PI / INR (2 * m + 1)) ^ 20) (m - 1)
  = (3844950982656*INR m^20 + 38449509826560*INR m^19 + 119388082012160*INR m^18 - 21318291947520*INR m^17 - 771123004047360*INR m^16 - 718092745310208*INR m^15 + 2467296918896640*INR m^14 + 3308066966077440*INR m^13 - 5889732931153920*INR m^12 - 7865002973306880*INR m^11 + 12213336262662144*INR m^10 + 11220114565253120*INR m^9 - 21448526762288640*INR m^8 - 7029281395845120*INR m^7 + 28018193075781120*INR m^6 - 7417429978747392*INR m^5 - 21102679424539800*INR m^4 + 23032396562850000*INR m^3 - 9688684255267500*INR m^2 + 1531329465290625*INR m) / 32157918771103125.
Proof.
  intros m Hm.
  transitivity (fold_right Rplus 0
                  (map (fun r => r * r * r * r * r * r * r * r * r * r) (map (fun k => Rcot (theta m k) ^ 2) (seq 1 m)))).
  - rewrite map_map.
    rewrite (fold_right_map_seq
               (fun k => Rcot (theta m k) ^ 2 * (Rcot (theta m k) ^ 2) * (Rcot (theta m k) ^ 2) * (Rcot (theta m k) ^ 2) * (Rcot (theta m k) ^ 2) * (Rcot (theta m k) ^ 2) * (Rcot (theta m k) ^ 2) * (Rcot (theta m k) ^ 2) * (Rcot (theta m k) ^ 2) * (Rcot (theta m k) ^ 2)) m ltac:(lia)).
    apply sum_eq; intros k _; unfold theta; ring.
  - rewrite newton10, (cot_e2_exp m ltac:(lia)), (cot_e3_exp m ltac:(lia)), (cot_e4_exp m ltac:(lia)), (cot_e5_exp m ltac:(lia)), (cot_e6_exp m ltac:(lia)), (cot_e7_exp m ltac:(lia)), (cot_e8_exp m ltac:(lia)), (cot_e9_exp m ltac:(lia)), (cot_e10_exp m Hm).
    replace (fold_right Rplus 0 (map (fun k => Rcot (theta m k) ^ 2) (seq 1 m)))
      with (INR m * (2 * INR m - 1) / 3).
    2:{ rewrite (fold_right_map_seq (fun k => Rcot (theta m k) ^ 2) m ltac:(lia)).
        rewrite <- (cot_sq_sum m ltac:(lia)); apply sum_eq; intros k _; unfold theta; reflexivity. }
    exact (cot20_poly_id (INR m)).
Qed.

Print Assumptions cot20_sum.
