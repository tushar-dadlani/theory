(* ================================================================= *)
(*  RiemannSumGeneral.v  —  the general continuous-f Riemann sum         *)
(*  over the primorial grid converges to the integral.                  *)
(*                                                                    *)
(*  Generalizes PrimorialRiemann.riemann_grid_id (f(x)=x) to every       *)
(*  continuous f on [0,1]:  the left Riemann sum (1/N) sum_{j<N} f(j/N)   *)
(*  over N cells converges, as N -> oo, to RiemannInt f; hence over the   *)
(*  nat-valued primorial grid too.  Built from Stdlib's RiemannInt via    *)
(*  Heine (uniform continuity) + partition additivity + a per-cell        *)
(*  modulus bound.  Axiom-clean.                                         *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import PrimorialRiemann.
Open Scope R_scope.

(* partial sum sum_{j<k} g j *)
Fixpoint psum (g : nat -> R) (k : nat) : R :=
  match k with 0 => 0 | S k' => psum g k' + g k' end.

Lemma sum_f_R0_psum : forall g m, sum_f_R0 g m = psum g (S m).
Proof.
  intros g m. induction m as [| m IH]; [ simpl; ring | ].
  rewrite tech5, IH. simpl. ring.
Qed.

Lemma psum_le : forall (g h : nat -> R) k,
  (forall j, (j < k)%nat -> g j <= h j) -> psum g k <= psum h k.
Proof.
  intros g h k. induction k as [| k IH]; intro Hle; simpl; [ lra | ].
  apply Rplus_le_compat; [ apply IH; intros j Hj; apply Hle; lia | apply Hle; lia ].
Qed.

Lemma psum_const : forall c k, psum (fun _ => c) k = INR k * c.
Proof.
  intros c k. induction k as [| k IH]; [ simpl; ring | ].
  cbn [psum]. rewrite IH, S_INR. ring.
Qed.

Lemma psum_Rabs_triang : forall (g : nat -> R) k, Rabs (psum g k) <= psum (fun j => Rabs (g j)) k.
Proof.
  intros g k. induction k as [| k IH]; simpl; [ rewrite Rabs_R0; lra | ].
  eapply Rle_trans; [ apply Rabs_triang | apply Rplus_le_compat; [ exact IH | apply Rle_refl ] ].
Qed.

Lemma psum_scal : forall (a : R) (g : nat -> R) k,
  a * psum g k = psum (fun j => a * g j) k.
Proof.
  intros a g k. induction k as [| k IH]; [ simpl; ring | ].
  cbn [psum]. rewrite <- IH. ring.
Qed.

Lemma psum_minus : forall (g h : nat -> R) k,
  psum g k - psum h k = psum (fun j => g j - h j) k.
Proof.
  intros g h k. induction k as [| k IH]; [ simpl; ring | ].
  cbn [psum]. rewrite <- IH. ring.
Qed.

(* the grid points INR k / INR N in [0,1] *)
Lemma xk_nonneg : forall N k, (0 < N)%nat -> 0 <= INR k / INR N.
Proof.
  intros N k HN. unfold Rdiv. apply Rmult_le_pos;
    [ apply pos_INR | left; apply Rinv_0_lt_compat; apply lt_0_INR; lia ].
Qed.

Lemma xk_mono : forall N j, (0 < N)%nat -> INR j / INR N <= INR (S j) / INR N.
Proof.
  intros N j HN. unfold Rdiv. apply Rmult_le_compat_r;
    [ left; apply Rinv_0_lt_compat; apply lt_0_INR; lia | apply le_INR; lia ].
Qed.

Lemma xk_le1 : forall N k, (0 < N)%nat -> (k <= N)%nat -> INR k / INR N <= 1.
Proof.
  intros N k HN Hk. assert (HN0 : 0 < INR N) by (apply lt_0_INR; lia).
  apply Rmult_le_reg_r with (INR N); [ lra | ].
  unfold Rdiv; rewrite Rmult_assoc, Rinv_l by lra.
  rewrite Rmult_1_r, Rmult_1_l. apply le_INR; lia.
Qed.

Lemma xk_diff : forall N j, (0 < N)%nat -> INR (S j) / INR N - INR j / INR N = / INR N.
Proof.
  intros N j HN. rewrite S_INR. field. apply not_0_INR; lia.
Qed.

Section RS.
Variable f : R -> R.
Hypothesis Hc : forall x, 0 <= x <= 1 -> continuity_pt f x.

Lemma f_int : forall a b, 0 <= a -> a <= b -> b <= 1 -> Riemann_integrable f a b.
Proof.
  intros a b Ha Hab Hb; apply continuity_implies_RiemannInt;
    [ exact Hab | intros x Hx; apply Hc; lra ].
Qed.

(* the (proof-irrelevant) integral value over [a,b] subset [0,1] *)
Definition iv (a b : R) : R :=
  match Rle_dec 0 a with
  | left Ha => match Rle_dec a b with
               | left Hab => match Rle_dec b 1 with
                             | left Hb => RiemannInt (f_int a b Ha Hab Hb)
                             | right _ => 0 end
               | right _ => 0 end
  | right _ => 0 end.

Lemma iv_val : forall a b (Ha : 0 <= a) (Hab : a <= b) (Hb : b <= 1),
  iv a b = RiemannInt (f_int a b Ha Hab Hb).
Proof.
  intros a b Ha Hab Hb. unfold iv.
  destruct (Rle_dec 0 a) as [Ha'|Hn]; [ | exfalso; lra ].
  destruct (Rle_dec a b) as [Hab'|Hn]; [ | exfalso; lra ].
  destruct (Rle_dec b 1) as [Hb'|Hn]; [ | exfalso; lra ].
  apply RiemannInt_P5.
Qed.

Lemma iv_same : forall a, 0 <= a -> a <= 1 -> iv a a = 0.
Proof.
  intros a Ha Ha1. rewrite (iv_val a a Ha (Rle_refl a) Ha1). apply RiemannInt_P9.
Qed.

Lemma iv_add : forall a b c, 0 <= a -> a <= b -> b <= c -> c <= 1 ->
  iv a c = iv a b + iv b c.
Proof.
  intros a b c Ha Hab Hbc Hc1.
  assert (Hb0 : 0 <= b) by lra. assert (Hb1 : b <= 1) by lra.
  assert (Hac : a <= c) by lra.
  rewrite (iv_val a c Ha Hac Hc1), (iv_val a b Ha Hab Hb1), (iv_val b c Hb0 Hbc Hc1).
  symmetry.
  apply (RiemannInt_P26 (f_int a b Ha Hab Hb1) (f_int b c Hb0 Hbc Hc1) (f_int a c Ha Hac Hc1)).
Qed.

(* partition additivity: int_0^{k/N} f = sum_{j<k} int_{j/N}^{(j+1)/N} f  (k <= N) *)
Lemma partition_additive : forall (N : nat), (1 <= N)%nat -> forall k, (k <= N)%nat ->
  iv 0 (INR k / INR N)
  = psum (fun j => iv (INR j / INR N) (INR (S j) / INR N)) k.
Proof.
  intros N HN. assert (HN0 : 0 < INR N) by (apply lt_0_INR; lia).
  induction k as [| k IH]; intro Hk.
  - cbn [psum]. change (INR 0) with 0.
    replace (0 / INR N) with 0 by (field; lra).
    apply iv_same; lra.
  - assert (Hkk : (k <= N)%nat) by lia.
    assert (Hbnd : INR (S k) / INR N <= 1)
      by (apply Rmult_le_reg_r with (INR N); [ lra | ];
          unfold Rdiv; rewrite Rmult_assoc, Rinv_l by lra;
          rewrite Rmult_1_r, Rmult_1_l; apply le_INR; lia).
    assert (Hkle : INR k / INR N <= INR (S k) / INR N)
      by (apply Rmult_le_compat_r; [ left; apply Rinv_0_lt_compat; lra | apply le_INR; lia ]).
    assert (Hk0 : 0 <= INR k / INR N)
      by (apply Rmult_le_pos; [ apply pos_INR | left; apply Rinv_0_lt_compat; lra ]).
    cbn [psum]. rewrite <- IH by exact Hkk.
    apply (iv_add 0 (INR k / INR N) (INR (S k) / INR N)); lra.
Qed.

(* per-cell bound: |int_a^b f - (b-a).f(a)| <= eps.(b-a), given the modulus of
   continuity holds on the cell.  Standard: replace f(a) by the constant integral,
   take the difference under one integral (P13/P10/P15), bound |.| by int|.| (P16/P17),
   and dominate the integrand by eps (P19). *)
Lemma cell_bound : forall a b eps (Ha : 0 <= a) (Hab : a <= b) (Hb : b <= 1),
  0 <= eps ->
  (forall y, a <= y <= b -> Rabs (f y - f a) <= eps) ->
  Rabs (iv a b - (b - a) * f a) <= eps * (b - a).
Proof.
  intros a b eps Ha Hab Hb Heps Hmod.
  rewrite (iv_val a b Ha Hab Hb).
  set (pr := f_int a b Ha Hab Hb).
  set (prc := RiemannInt_P14 a b (f a)).
  set (prd := RiemannInt_P10 (-1) pr prc).
  set (prabs := RiemannInt_P16 prd).
  set (preps := RiemannInt_P14 a b eps).
  assert (Hdiff : RiemannInt pr - (b - a) * f a = RiemannInt prd).
  { rewrite (RiemannInt_P13 pr prc prd).
    rewrite (RiemannInt_P15 prc). ring. }
  rewrite Hdiff.
  eapply Rle_trans; [ apply (RiemannInt_P17 prd prabs Hab) | ].
  eapply Rle_trans.
  - apply (RiemannInt_P19 prabs preps Hab).
    intros x Hx. cbv beta. unfold fct_cte.
    replace (f x + -1 * f a) with (f x - f a) by ring.
    apply Hmod; lra.
  - rewrite (RiemannInt_P15 preps). apply Rle_refl.
Qed.

(* uniform continuity of f on [0,1] from Heine (compactness) *)
Lemma unif : forall eps, 0 < eps ->
  exists delta, 0 < delta /\
    forall x y, 0 <= x <= 1 -> 0 <= y <= 1 -> Rabs (x - y) < delta -> Rabs (f x - f y) < eps.
Proof.
  intros eps Heps.
  destruct (Heine f (fun c => 0 <= c <= 1) (compact_P3 0 1) Hc (mkposreal eps Heps))
    as [delta Hdelta].
  exists (pos delta). split; [ apply (cond_pos delta) | ].
  intros x y Hx Hy Hxy. exact (Hdelta x y Hx Hy Hxy).
Qed.

(* assembly: for a uniform partition of [0,1] into N = S m cells, if the modulus of
   continuity is <= eps on every cell, then |int_0^1 f - Rsum f N| <= eps. *)
Lemma riemann_sum_step : forall (m : nat) eps,
  0 <= eps ->
  (forall j, (j < S m)%nat -> forall y,
     INR j / INR (S m) <= y <= INR (S j) / INR (S m) ->
     Rabs (f y - f (INR j / INR (S m))) <= eps) ->
  Rabs (iv 0 1 - Rsum f (S m)) <= eps.
Proof.
  intros m eps Heps Hmod.
  set (N := S m) in *.
  assert (HNnat : (0 < N)%nat) by (unfold N; lia).
  assert (HN1 : (1 <= N)%nat) by lia.
  assert (HN0 : 0 < INR N) by (apply lt_0_INR; lia).
  assert (Hpart : iv 0 (INR N / INR N)
                  = psum (fun j => iv (INR j / INR N) (INR (S j) / INR N)) N)
    by (apply partition_additive; [ exact HN1 | apply Nat.le_refl ]).
  assert (HN_eq : INR N / INR N = 1) by (field; lra).
  rewrite HN_eq in Hpart.
  assert (HR : Rsum f N = psum (fun j => / INR N * f (INR j / INR N)) N).
  { unfold Rsum. assert (Hpred : pred N = m) by (unfold N; reflexivity).
    rewrite Hpred, sum_f_R0_psum, psum_scal. reflexivity. }
  rewrite Hpart, HR, psum_minus.
  eapply Rle_trans; [ apply psum_Rabs_triang | ].
  eapply Rle_trans.
  - apply (psum_le _ (fun _ => eps * / INR N)). intros j Hj.
    set (a := INR j / INR N). set (b := INR (S j) / INR N).
    assert (Hba : b - a = / INR N) by (unfold a, b; apply xk_diff; exact HNnat).
    rewrite <- Hba.
    apply cell_bound.
    + unfold a; apply xk_nonneg; exact HNnat.
    + unfold a, b; apply xk_mono; exact HNnat.
    + unfold b; apply xk_le1; [ exact HNnat | lia ].
    + exact Heps.
    + intros y Hy. unfold a, b in *. apply Hmod; [ exact Hj | exact Hy ].
  - rewrite psum_const.
    replace (INR N * (eps * / INR N)) with eps by (field; lra). apply Rle_refl.
Qed.

(* MAIN: the left Riemann sum over N=S m equal cells converges to int_0^1 f *)
Theorem riemann_sum_cv : Un_cv (fun m => Rsum f (S m)) (iv 0 1).
Proof.
  intros eps Heps.
  destruct (unif (eps / 2) ltac:(lra)) as [delta [Hd Hmod0]].
  destruct (archimed_cor1 delta Hd) as [M [HM HMpos]].
  exists M. intros n Hn.
  unfold R_dist. rewrite Rabs_minus_sym.
  apply Rle_lt_trans with (eps / 2); [ | lra ].
  apply (riemann_sum_step n (eps / 2)); [ lra | ].
  intros j Hj y Hy.
  assert (HSn : (0 < S n)%nat) by lia.
  assert (Ha0 : 0 <= INR j / INR (S n)) by (apply xk_nonneg; exact HSn).
  assert (Ha1 : INR j / INR (S n) <= 1) by (apply xk_le1; [ exact HSn | lia ]).
  assert (Hb1 : INR (S j) / INR (S n) <= 1) by (apply xk_le1; [ exact HSn | lia ]).
  assert (Hdiff : INR (S j) / INR (S n) - INR j / INR (S n) = / INR (S n))
    by (apply xk_diff; exact HSn).
  destruct Hy as [Hya Hyb].
  assert (Hy0 : 0 <= y) by lra.
  assert (Hy1 : y <= 1) by lra.
  apply Rlt_le. apply Hmod0.
  - split; [ exact Hy0 | exact Hy1 ].
  - split; [ exact Ha0 | exact Ha1 ].
  - rewrite Rabs_right by lra.
    apply Rle_lt_trans with (/ INR (S n)); [ lra | ].
    apply Rle_lt_trans with (/ INR M); [ | exact HM ].
    apply Rinv_le_contravar; [ apply lt_0_INR; lia | apply le_INR; lia ].
Qed.

(* corollary: convergence along the nat-valued primorial grid *)
Theorem riemann_grid_cv : forall (Q : nat -> nat) (HQ : forall i, (2 <= Q i)%nat),
  Un_cv (fun k => Rsum f (nprimorial Q k)) (iv 0 1).
Proof.
  intros Q HQ eps Heps.
  destruct (riemann_sum_cv eps Heps) as [M HM].
  destruct (nprimorial_cv_infty Q HQ (INR (S M))) as [K HK].
  exists K. intros k Hk.
  assert (Hgt : INR (S M) < INR (nprimorial Q k)) by (apply HK; exact Hk).
  apply INR_lt in Hgt.
  assert (Hsucc : nprimorial Q k = S (pred (nprimorial Q k))) by lia.
  rewrite Hsucc. apply HM. lia.
Qed.

End RS.

Print Assumptions partition_additive.
Print Assumptions riemann_sum_cv.
Print Assumptions riemann_grid_cv.
