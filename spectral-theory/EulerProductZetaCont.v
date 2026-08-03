(* ================================================================= *)
(*  EulerProductZetaCont.v                                           *)
(*                                                                    *)
(*  THE EULER PRODUCT FORMULA for the operator zeta at general s>1:    *)
(*                                                                    *)
(*    prod_{p prime, p <= B} (1 - p^{-s})^{-1}  -->  zeta_cont s       *)
(*                                (euler_product_zeta)                *)
(*                                                                    *)
(*  the general-s analogue of EulerProductZeta.euler_product_zeta2     *)
(*  (which lands on zeta(2)).  It is the same squeeze, but the two      *)
(*  s=2-specific pieces are replaced:                                  *)
(*                                                                    *)
(*    - the Q reindex is replaced by EulerReindexR.euler_partial_-     *)
(*      reindex_Rs (a direct R distributive law);                     *)
(*    - the numeric zeta(2) bound recip_sq_nodup_bound is replaced by  *)
(*      recip_s_nodup_bound, which bounds any finite distinct sum of   *)
(*      n^{-s} by zeta_cont s using the operator trace's monotonicity  *)
(*      (dzeta_growing) and its limit (operator_zeta_eq_cont).         *)
(*                                                                    *)
(*  The squeeze: the operator trace diag_trace (z s) N (the partial    *)
(*  sum Sum_{n<=N} n^{-s}) is sandwiched between itself (converging to  *)
(*  zeta_cont s, operator_zeta_eq_cont) below the finite Euler product *)
(*  (dzeta_le_euler, factorization existence) and that product below   *)
(*  zeta_cont s (euler_factor_le_zeta_s).                             *)
(*                                                                    *)
(*  Uses the classical Reals axioms (quarantined), the same footprint  *)
(*  as operator_zeta_eq_cont.                                         *)
(* ================================================================= *)

Require Import PrimonGas PrimeFactorizationN PrimeFactorizationExists
        EulerReindex EulerReindexR EulerProductR EulerProductZeta
        EulerProductZetaBound RecipSquareBound EulerFactorR
        Ell2Zeta Ell2ZetaConverge Ell2ZetaCont.
From Stdlib Require Import ZArith Znumtheory Reals Rpower Lra Lia List Arith.
Import ListNotations.
Open Scope R_scope.

(* ================================================================= *)
(*  1.  BASIC POSITIVITY / BOUNDS OF THE OPERATOR SYMBOL AND FUGACITY *)
(* ================================================================= *)

Lemma z_nonneg : forall s m, 0 <= z s m.
Proof.
  intros s m; unfold z; destruct (Nat.eqb m 0);
    [ apply Rle_refl | apply Rlt_le; unfold Rpower; apply exp_pos ].
Qed.

(* the fugacity p^{-s} lies in [0,1) for s>0 and p prime *)
Lemma fug_lt1_s : forall s p, 0 < s -> prime p -> 0 <= Rpower (IZR p) (- s) < 1.
Proof.
  intros s p Hs Hp.
  assert (Hpp : (2 <= p)%Z) by (destruct Hp; lia).
  assert (Hp1 : (1 < IZR p)%R) by (apply IZR_lt; lia).
  assert (Hln : (0 < ln (IZR p))%R) by (rewrite <- ln_1; apply ln_increasing; lra).
  split.
  - apply Rlt_le; unfold Rpower; apply exp_pos.
  - unfold Rpower; rewrite <- exp_0; apply exp_increasing; nra.
Qed.

Lemma fug_abs_lt1_s : forall s p, 0 < s -> prime p -> Rabs (Rpower (IZR p) (- s)) < 1.
Proof.
  intros s p Hs Hp; pose proof (fug_lt1_s s p Hs Hp) as [Hlo Hhi].
  rewrite Rabs_pos_eq by exact Hlo; exact Hhi.
Qed.

(* ================================================================= *)
(*  2.  THE zeta_cont DOMINATION LEMMA (general-s replacement for      *)
(*      recip_sq_nodup_bound)                                         *)
(* ================================================================= *)

Theorem recip_s_nodup_bound : forall s (Hs0 : 0 < s) (Hs1 : s <> 1), 1 < s ->
  forall L, NoDup L -> (forall m, In m L -> (1 <= m)%nat) ->
    Rlsum (map (z s) L) <= zeta_cont s Hs0 Hs1.
Proof.
  intros s Hs0 Hs1 Hs L Hnd Hpos.
  assert (Hgrow : Un_growing (fun N => diag_trace (z s) N)).
  { intro n; rewrite !zeta_partition; apply dzeta_growing; lra. }
  assert (Hcv : Un_cv (fun N => diag_trace (z s) N) (zeta_cont s Hs0 Hs1))
    by (apply (operator_zeta_eq_cont s Hs0 Hs1 Hs)).
  destruct L as [|a L0].
  - assert (Hz0 : diag_trace (z s) 0 = 0) by (rewrite diag_trace_eq; reflexivity).
    pose proof (growing_ineq (fun N => diag_trace (z s) N)
                  (zeta_cont s Hs0 Hs1) Hgrow Hcv 0) as H0.
    cbv beta in H0; rewrite Hz0 in H0.
    unfold Rlsum; simpl; exact H0.
  - remember (list_max (a :: L0)) as M eqn:EM.
    assert (HM1 : (1 <= M)%nat).
    { subst M; pose proof (Hpos a (in_eq a L0));
        pose proof (in_le_list_max a (a :: L0) (in_eq a L0)); lia. }
    assert (Hincl : incl (a :: L0) (seq 1 M)).
    { intros x Hx; apply in_seq; split.
      - apply Hpos; exact Hx.
      - pose proof (in_le_list_max x (a :: L0) Hx); subst M; lia. }
    apply Rle_trans with (Rlsum (map (z s) (seq 1 M))).
    + apply (incl_sum_le (z s) (z_nonneg s) (seq 1 M) (a :: L0) Hnd Hincl).
    + unfold Rlsum; rewrite <- diag_trace_eq.
      apply (growing_ineq (fun N => diag_trace (z s) N)
               (zeta_cont s Hs0 Hs1) Hgrow Hcv M).
Qed.

(* ================================================================= *)
(*  3.  UPPER BOUND: the finite Euler product is <= zeta_cont s        *)
(* ================================================================= *)

Theorem euler_factor_le_zeta_s : forall s (Hs0 : 0 < s) (Hs1 : s <> 1), 1 < s ->
  forall ps, Forall prime ps -> NoDup ps ->
    Zfactor (map (fun p => Rpower (IZR p) (- s)) ps) <= zeta_cont s Hs0 Hs1.
Proof.
  intros s Hs0 Hs1 Hs ps Hpr Hnd.
  apply (lim_le (Zpartial (map (fun p => Rpower (IZR p) (- s)) ps))
                (Zfactor (map (fun p => Rpower (IZR p) (- s)) ps))
                (zeta_cont s Hs0 Hs1)).
  - apply euler_product_R.
    apply Forall_forall; intros y Hy; apply in_map_iff in Hy.
    destruct Hy as [p [Hpy Hp]]; subst y.
    apply fug_abs_lt1_s; [ lra | apply (proj1 (Forall_forall prime ps) Hpr p Hp) ].
  - intro N.
    rewrite (euler_partial_reindex_Rs s ps N Hpr).
    rewrite <- (map_map (fun ks : list nat => Z.to_nat (code ps ks)) (z s)).
    apply (recip_s_nodup_bound s Hs0 Hs1 Hs);
      [ apply (codes_nat_nodup ps Hpr Hnd) | apply (codes_nat_pos ps Hpr N) ].
Qed.

(* ================================================================= *)
(*  4.  LOWER BOUND: the operator trace is <= the finite Euler product *)
(* ================================================================= *)

Lemma dzeta_le_euler : forall s, 0 < s -> forall N,
  diag_trace (z s) N
  <= Zfactor (map (fun p => Rpower (IZR p) (- s)) (primes_upto (S N))).
Proof.
  intros s Hs N.
  set (ps := primes_upto (S N)).
  assert (Hpr : Forall prime ps) by apply primes_upto_Forall.
  assert (Hnd : NoDup ps) by apply primes_upto_nodup.
  assert (Hpr2 : Forall (fun p => (2 <= p)%Z) ps).
  { apply Forall_impl with (P := prime); [ intros p Hp; destruct Hp; lia | exact Hpr ]. }
  set (codes := map (fun ks => Z.to_nat (code ps ks)) (gstates (map fug ps) (S N))).
  assert (Hincl : incl (seq 1 N) codes).
  { intros m Hm. apply in_seq in Hm; destruct Hm as [Hm1 HmN].
    assert (Hsm : forall q, prime q -> (q | Z.of_nat m)%Z -> In q ps).
    { intros q Hq Hdvd; apply (small_smooth N m); [ lia | lia | exact Hq | exact Hdvd ]. }
    destruct (code_surj ps Hpr Hnd (Z.of_nat m) ltac:(lia) Hsm) as [ks [Hlen Hcode]].
    assert (Hb : Forall (fun e => (e < S N)%nat) ks).
    { apply Forall_forall; intros e He.
      pose proof (entry_pow_le_code ps ks Hpr2 Hlen e He) as Hpow.
      rewrite Hcode in Hpow.
      assert (Hpow2 : (2 ^ e <= m)%nat).
      { apply (proj2 (Nat2Z.inj_le (2 ^ e) m)); rewrite Nat2Z.inj_pow; exact Hpow. }
      pose proof (nat_lt_pow2 e); lia. }
    unfold codes; apply in_map_iff; exists ks; split.
    - rewrite Hcode, Nat2Z.id; reflexivity.
    - apply gstates_complete; [ rewrite length_map; symmetry; exact Hlen | exact Hb ]. }
  assert (Hsum : Rlsum (map (z s) (seq 1 N)) <= Rlsum (map (z s) codes)).
  { apply (incl_sum_le (z s) (z_nonneg s) codes (seq 1 N));
      [ apply seq_NoDup | exact Hincl ]. }
  assert (Hre : Rlsum (map (z s) codes)
                = Zpartial (map (fun p => Rpower (IZR p) (- s)) ps) N).
  { unfold codes; rewrite map_map, <- (euler_partial_reindex_Rs s ps N Hpr); reflexivity. }
  rewrite (diag_trace_eq (z s) N).
  eapply Rle_trans; [ exact Hsum | ].
  rewrite Hre; apply Zpartial_le_Zfactor.
  apply Forall_forall; intros y Hy; apply in_map_iff in Hy.
  destruct Hy as [p [Hpy Hp]]; subst y.
  apply fug_lt1_s; [ exact Hs | apply (proj1 (Forall_forall prime ps) Hpr p Hp) ].
Qed.

(* ================================================================= *)
(*  5.  THE EULER PRODUCT FORMULA for zeta_cont (general s>1)          *)
(* ================================================================= *)

Theorem euler_product_zeta : forall s (Hs0 : 0 < s) (Hs1 : s <> 1), 1 < s ->
  Un_cv (fun N => Zfactor (map (fun p => Rpower (IZR p) (- s)) (primes_upto (S N))))
        (zeta_cont s Hs0 Hs1).
Proof.
  intros s Hs0 Hs1 Hs.
  apply (squeeze_const_upper (fun N => diag_trace (z s) N) _ (zeta_cont s Hs0 Hs1)).
  - apply (operator_zeta_eq_cont s Hs0 Hs1 Hs).
  - intro N; apply dzeta_le_euler; lra.
  - intro N; apply (euler_factor_le_zeta_s s Hs0 Hs1 Hs (primes_upto (S N)));
      [ apply primes_upto_Forall | apply primes_upto_nodup ].
Qed.

Print Assumptions euler_product_zeta.

(* ================================================================= *)
(*  END EulerProductZetaCont.v                                        *)
(*  prod_{p prime, p <= B} (1 - p^{-s})^{-1} -> zeta_cont s as B -> oo   *)
(*  for every real s > 1: the operator zeta equals its prime Euler      *)
(*  product, generalizing the s=2 result to the whole half-line s>1.    *)
(*  Uses the classical Reals axioms (quarantined).                     *)
(* ================================================================= *)
