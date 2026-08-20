(* ================================================================= *)
(*  XiHadamardUnif.v  —  Hadamard product, phase 2:                    *)
(*  pointwise convergence upgraded to LOCALLY UNIFORM on Cmod z <= Rr. *)
(*                                                                    *)
(*    hadamard_prod_unif : the partial products of                     *)
(*      Efac z (rho n) = (1 - z/rho_n) e^{z/rho_n}                     *)
(*      converge to their limit UNIFORMLY on every closed disk.        *)
(*                                                                    *)
(*  WHY IT WORKS.  The deviation bound already proved,                 *)
(*    Efac_dev_le : |Efac z rho - 1| <= KR (Cmod z) / |rho|^2,         *)
(*  depends on z only through KR (Cmod z), and KR is increasing.  So on *)
(*  Cmod z <= Rr every deviation is dominated by KR Rr * invsq (rho n)  *)
(*  -- a bound with NO z in it.  Feeding that through the Cauchy        *)
(*  estimate makes the whole tail bound uniform.                       *)
(*                                                                    *)
(*  The obstacle was that CInfProd.tail_bound is stated with T, the     *)
(*  EXACT limit of sum (dev f), in both slots -- and for a family f_z    *)
(*  both T and the partial sums move with z.  CInfProdUnif.             *)
(*  tail_bound_gen takes those two constants as hypotheses instead,     *)
(*  which is all that was needed.                                      *)
(*                                                                    *)
(*  The epsilon-chase avoids any continuity lemma: from Stdlib's        *)
(*  exp_ineq1_le (1 + x <= exp x) at x := -u one gets                   *)
(*      exp u - 1 <= u * exp u,   hence <= u * exp 1 for 0 <= u <= 1,   *)
(*  so exp 1 can be carried symbolically and no numeric bound on e is   *)
(*  ever required.  Axiom-clean.                                       *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia List.
Require Import ComplexField Cmodulus CSeries CInfProd CInfProdUnif
        CDyadicSum XiZeroEnum XiHgrow XiHadamardProd.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  A.  two elementary facts                                           *)
(* ----------------------------------------------------------------- *)
Lemma KR_mono : forall r1 r2, 0 <= r1 -> r1 <= r2 -> KR r1 <= KR r2.
Proof.
  intros r1 r2 H1 H12. unfold KR.
  assert (He : exp r1 <= exp r2) by (apply exp_le; lra).
  assert (Hp1 : 0 < exp r1) by apply exp_pos.
  assert (Hfac : (1 + r1) * exp r1 <= (1 + r2) * exp r2)
    by (apply Rmult_le_compat; lra).
  apply Rmult_le_compat.
  - apply pow_le; lra.
  - nra.
  - apply pow_incr; lra.
  - lra.
Qed.

Lemma exp_m1_le : forall u, 0 <= u -> exp u - 1 <= u * exp u.
Proof.
  intros u Hu.
  pose proof (exp_ineq1_le (- u)) as H.
  pose proof (exp_pos u) as Hp.
  assert (Hprod : exp u * exp (- u) = 1)
    by (rewrite <- exp_plus; replace (u + - u) with 0 by ring; apply exp_0).
  nra.
Qed.

Lemma Cmod_minus_sym : forall a b, Cmod (Cminus a b) = Cmod (Cminus b a).
Proof.
  intros a b. rewrite <- (Cmod_opp (Cminus a b)). f_equal. ring.
Qed.

Section Unif.

Variable rho : nat -> C.
Hypothesis Henum : ZeroEnum rho.
Hypothesis Hlow : forall n, 1 <= Cmod (rho n).
Variable Rr : R.
Hypothesis HR : 0 < Rr.

Lemma invsq_pos : forall n, 0 < invsq (rho n).
Proof.
  intro n. unfold invsq. apply Rinv_0_lt_compat. apply pow_lt.
  pose proof (Hlow n). lra.
Qed.

(* ----------------------------------------------------------------- *)
(*  B.  the invsq series and its limit                                 *)
(* ----------------------------------------------------------------- *)
Definition Ssum_cv : { S | Un_cv (sum_f_R0 (fun n => invsq (rho n))) S }.
Proof.
  set (Un := sum_f_R0 (fun n => invsq (rho n))).
  assert (Hgrow : Un_growing Un).
  { intro N. unfold Un. rewrite tech5. pose proof (invsq_pos (S N)). lra. }
  assert (Hub : has_ub Un).
  { exists (4 * agrow). intros v [N ->]. unfold Un.
    rewrite <- sumlist_takeN. apply enum_sum_bound; assumption. }
  destruct (growing_cv Un Hgrow Hub) as [l Hl]. exists l; exact Hl.
Defined.

Definition Ssum : R := proj1_sig Ssum_cv.

Lemma Ssum_spec : Un_cv (sum_f_R0 (fun n => invsq (rho n))) Ssum.
Proof. exact (proj2_sig Ssum_cv). Qed.

Lemma invsq_partial_le : forall N, sum_f_R0 (fun n => invsq (rho n)) N <= Ssum.
Proof.
  intro N. apply (growing_ineq (sum_f_R0 (fun n => invsq (rho n))));
    [ | apply Ssum_spec ].
  intro n. rewrite tech5. pose proof (invsq_pos (S n)). lra.
Qed.

(* ----------------------------------------------------------------- *)
(*  C.  THE UNIFORM DEVIATION BOUND -- no z on the right               *)
(* ----------------------------------------------------------------- *)
Lemma dev_unif : forall z, Cmod z <= Rr ->
  forall n, dev (fun k => Efac z (rho k)) n <= KR Rr * invsq (rho n).
Proof.
  intros z Hz n. unfold dev, invsq.
  eapply Rle_trans; [ apply Efac_dev_le; apply Hlow | ].
  apply Rmult_le_compat_r.
  - left. apply Rinv_0_lt_compat. apply pow_lt. pose proof (Hlow n). lra.
  - apply KR_mono; [ apply Cmod_nonneg | exact Hz ].
Qed.

Definition TU : R := KR Rr * (4 * agrow).

Lemma sumdev_le_TU : forall z, Cmod z <= Rr ->
  forall N, sum_f_R0 (dev (fun k => Efac z (rho k))) N <= TU.
Proof.
  intros z Hz N. unfold TU.
  apply Rle_trans with (sum_f_R0 (fun n => invsq (rho n) * KR Rr) N).
  - apply sumR0_le. intro i. rewrite Rmult_comm. apply dev_unif; exact Hz.
  - rewrite <- (scal_sum (fun n => invsq (rho n)) N (KR Rr)).
    apply Rmult_le_compat_l; [ apply KR_nonneg; lra | ].
    rewrite <- sumlist_takeN. apply enum_sum_bound; assumption.
Qed.

Definition dtail (M : nat) : R := Ssum - sum_f_R0 (fun n => invsq (rho n)) M.

Lemma dtail_nonneg : forall M, 0 <= dtail M.
Proof. intro M. unfold dtail. pose proof (invsq_partial_le M). lra. Qed.

Lemma tail_unif : forall z, Cmod z <= Rr -> forall M k,
  sum_f_R0 (dev (fun j => Efac z (rho j))) (S (M + k))
  - sum_f_R0 (dev (fun j => Efac z (rho j))) M
  <= KR Rr * dtail M.
Proof.
  intros z Hz M k.
  rewrite <- (sumtail_eq (dev (fun j => Efac z (rho j))) M k).
  apply Rle_trans with (sum_f_R0 (fun j => invsq (rho (S (M + j))) * KR Rr) k).
  - apply sumR0_le. intro i. rewrite Rmult_comm. apply dev_unif; exact Hz.
  - rewrite <- (scal_sum (fun j => invsq (rho (S (M + j)))) k (KR Rr)).
    apply Rmult_le_compat_l; [ apply KR_nonneg; lra | ].
    assert (Heq : sum_f_R0 (fun j => invsq (rho (S (M + j)))) k
                = sum_f_R0 (fun n => invsq (rho n)) (S (M + k))
                  - sum_f_R0 (fun n => invsq (rho n)) M)
      by (apply (sumtail_eq (fun n => invsq (rho n)) M k)).
    rewrite Heq.
    unfold dtail. pose proof (invsq_partial_le (S (M + k))). lra.
Qed.

(* ----------------------------------------------------------------- *)
(*  D.  the epsilon-chase: the uniform bound can be driven below eps   *)
(* ----------------------------------------------------------------- *)
Lemma small_M : forall eps, 0 < eps ->
  exists M, exp TU * (exp (KR Rr * dtail M) - 1) < eps.
Proof.
  intros eps Heps.
  set (K := KR Rr).
  assert (HK : 0 <= K) by (unfold K; apply KR_nonneg; lra).
  set (E := exp TU * exp 1).
  assert (HE : 0 < E) by (unfold E; apply Rmult_lt_0_compat; apply exp_pos).
  set (c := E * K + 1).
  assert (Hc : 0 < c) by (unfold c; nra).
  set (delta := Rmin (1 / (K + 1)) (eps / c)).
  assert (Hd : 0 < delta).
  { apply Rmin_glb_lt.
    - apply Rdiv_lt_0_compat; lra.
    - apply Rdiv_lt_0_compat; lra. }
  destruct (Ssum_spec delta Hd) as [M HM].
  exists M. specialize (HM M (le_n M)).
  (* dtail M < delta *)
  assert (Hdt : dtail M < delta).
  { unfold dtail. unfold R_dist in HM.
    pose proof (invsq_partial_le M). rewrite Rabs_left1 in HM by lra. lra. }
  assert (Hdt0 : 0 <= dtail M) by apply dtail_nonneg.
  set (u := K * dtail M).
  assert (Hu0 : 0 <= u) by (unfold u; nra).
  (* u <= 1, so exp u <= exp 1 *)
  assert (Hu1 : u <= 1).
  { unfold u. apply Rle_trans with (K * (1 / (K + 1))).
    - apply Rmult_le_compat_l; [ exact HK | ].
      left. eapply Rlt_le_trans; [ exact Hdt | apply Rmin_l ].
    - apply (Rmult_le_reg_r (K + 1)); [ lra | ].
      replace (K * (1 / (K + 1)) * (K + 1)) with K by (field; lra). lra. }
  assert (Hexpu : exp u <= exp 1) by (apply exp_le; exact Hu1).
  (* exp TU * (exp u - 1) <= E * u < eps *)
  assert (Hlin : exp u - 1 <= u * exp 1).
  { pose proof (exp_m1_le u Hu0). nra. }
  assert (Hstep : exp TU * (exp u - 1) <= E * u).
  { unfold E. pose proof (exp_pos TU). nra. }
  assert (Hfin : E * u < eps).
  { unfold u. apply Rle_lt_trans with (E * (K * (eps / c))).
    - apply Rmult_le_compat_l; [ lra | ].
      apply Rmult_le_compat_l; [ exact HK | ].
      left. eapply Rlt_le_trans; [ exact Hdt | apply Rmin_r ].
    - replace (E * (K * (eps / c))) with (eps * (E * K / c)) by (field; lra).
      assert (E * K / c < 1).
      { apply (Rmult_lt_reg_r c); [ lra | ].
        replace (E * K / c * c) with (E * K) by (field; lra). unfold c. lra. }
      nra. }
  unfold u in *. lra.
Qed.

(* ================================================================= *)
(*  E.  LOCALLY UNIFORM CONVERGENCE                                    *)
(* ================================================================= *)
Theorem hadamard_prod_unif : forall (P : C -> C),
  (forall z, CUn_cv (Pprod (fun k => Efac z (rho k))) (P z)) ->
  forall eps, 0 < eps ->
    exists N, forall n, (N <= n)%nat ->
      forall z, Cmod z <= Rr ->
        Cmod (Cminus (Pprod (fun k => Efac z (rho k)) n) (P z)) < eps.
Proof.
  intros P HP eps Heps.
  destruct (small_M (eps / 3) ltac:(lra)) as [M HM].
  exists M. intros n Hn z Hz.
  set (f := fun k => Efac z (rho k)).
  (* the UNIFORM half: any two indices beyond M are close *)
  assert (Hb : forall m, (M <= m)%nat -> Cmod (Cminus (Pprod f m) (Pprod f M)) < eps / 3).
  { intros m Hm. eapply Rle_lt_trans; [ | exact HM ].
    apply (tail_bound_gen f TU (KR Rr * dtail M) M).
    - apply sumdev_le_TU; exact Hz.
    - pose proof (dtail_nonneg M). pose proof (KR_nonneg Rr ltac:(lra)). nra.
    - intro k. apply tail_unif; exact Hz.
    - exact Hm. }
  (* the POINTWISE half: m may depend on z, since N and the bound do not *)
  destruct (HP z (eps / 3) ltac:(lra)) as [N0 HN0].
  set (m := Nat.max M N0).
  assert (HmM : (M <= m)%nat) by (unfold m; lia).
  pose proof (HN0 m ltac:(unfold m; lia)) as Hpt. fold f in Hpt.
  (* triangle through Pprod M and Pprod m *)
  assert (Hsplit : Cminus (Pprod f n) (P z)
    = Cadd (Cminus (Pprod f n) (Pprod f M))
           (Cadd (Cminus (Pprod f M) (Pprod f m)) (Cminus (Pprod f m) (P z))))
    by ring.
  rewrite Hsplit.
  eapply Rle_lt_trans; [ apply Cmod_triangle | ].
  assert (H2 : Cmod (Cadd (Cminus (Pprod f M) (Pprod f m)) (Cminus (Pprod f m) (P z)))
               <= Cmod (Cminus (Pprod f M) (Pprod f m)) + Cmod (Cminus (Pprod f m) (P z)))
    by apply Cmod_triangle.
  pose proof (Hb n Hn) as Hn'.
  pose proof (Hb m HmM) as Hm'.
  rewrite (Cmod_minus_sym (Pprod f M) (Pprod f m)) in H2.
  lra.
Qed.

End Unif.

(* ----------------------------------------------------------------- *)
(*  the same, instantiated at the limit function that phase 1 built.   *)
(*                                                                    *)
(*  hadamard_prod_cv returns a sig, so proj1_sig of it IS a function   *)
(*  C -> C -- data, obtained with no choice, because Pprod_cv is built  *)
(*  from R_complete.  Taking P as an input above and instantiating here *)
(*  keeps the main theorem free of proof-term dependence.              *)
(* ----------------------------------------------------------------- *)
Corollary hadamard_prod_unif_inst :
  forall (rho : nat -> C) (He : ZeroEnum rho) (Hl : forall n, 1 <= Cmod (rho n))
         (Rr : R), 0 < Rr ->
  forall eps, 0 < eps ->
    exists N, forall n, (N <= n)%nat ->
      forall z, Cmod z <= Rr ->
        Cmod (Cminus (Pprod (fun k => Efac z (rho k)) n)
                     (proj1_sig (hadamard_prod_cv rho He Hl z))) < eps.
Proof.
  intros rho He Hl Rr HR eps Heps.
  apply (hadamard_prod_unif rho He Hl Rr HR
           (fun z => proj1_sig (hadamard_prod_cv rho He Hl z))).
  - intro z. exact (proj2_sig (hadamard_prod_cv rho He Hl z)).
  - exact Heps.
Qed.

Print Assumptions hadamard_prod_unif.
Print Assumptions hadamard_prod_unif_inst.
