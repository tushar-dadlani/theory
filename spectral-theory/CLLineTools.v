(* ================================================================= *)
(*  CLLineTools.v  --  the three inputs for L(1+it,chi) <> 0.          *)
(*                                                                    *)
(*  ZetaLineNonzero derives zeta(1+it) <> 0 from three bounds and a    *)
(*  page of bookkeeping (INR_unbounded, Rmax, sigma = 1 + 1/n0).  The  *)
(*  bookkeeping is generic, so it is factored out here as a statement  *)
(*  about three real functions; only the three bounds are specific.    *)
(*                                                                    *)
(*  Also here: the pole bound for a twisted L-series.  For zeta the    *)
(*  first factor is bounded by the pole itself; for L(s,chi) we do not *)
(*  need the identity L(s,chi_0) = zeta(s)(1 - p^{-s}) (which would    *)
(*  need a reindexing of the series over multiples of p) -- the        *)
(*  triangle inequality against |chi| <= 1 already gives               *)
(*  |L(s,chi_a)| <= zeta_cont (Re s) for EVERY index a.                *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia ZArith Znumtheory List.
Require Import ComplexField Cmodulus CSeries RootsOfUnity ZmodOrder
        DirichletModP Ell2Zeta Ell2ZetaCont RecipSquareBound ZetaStripBound
        CEulerProductConv CEulerProductFull CharModulus CTwistedCoeff CLSeries
        CCharSumBound CTwistedSmooth CTwistPerPrime.
Import ListNotations.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  1.  the character index only matters mod (p-1)                     *)
(* ----------------------------------------------------------------- *)

Lemma dchar_index_mod : forall p g a n, (0 < p - 1)%nat ->
  dchar p g a n = dchar p g (a mod (p - 1)) n.
Proof.
  intros p g a n Hp1. unfold dchar.
  destruct (n mod p =? 0)%nat; [ reflexivity | ].
  rewrite (Cpow_w_mod (p - 1) (a * dlog p g (n mod p)) Hp1).
  rewrite (Cpow_w_mod (p - 1) (a mod (p - 1) * dlog p g (n mod p)) Hp1).
  f_equal.
  rewrite <- Nat.Div0.mul_mod_idemp_l. reflexivity.
Qed.

(* ----------------------------------------------------------------- *)
(*  2.  the pole bound: |L(s,chi_a)| <= zeta_cont (Re s)               *)
(* ----------------------------------------------------------------- *)

Theorem L_mod_le_zeta : forall p g A s L
  (Hg : (1 <= g <= p - 1)%nat) (Hord : ord p g = (p - 1)%nat)
  (H0 : 0 < Re s) (H1 : Re s <> 1),
  1 < Re s -> Cseries_cv (Lterm p g A s) L ->
  Cmod L <= zeta_cont (Re s) H0 H1.
Proof.
  intros p g A s L Hg Hord H0 H1 Hs HL.
  apply Rle_cv_lim
    with (Un := fun N => Cmod (Cpsum (Lterm p g A s) N))
         (Vn := fun N => diag_trace (z (Re s)) (S N)).
  - intro N. rewrite (Cpsum_Lterm_seq p g A s N).
    eapply Rle_trans; [ apply Cmod_Cwsum_le | ].
    rewrite map_map.
    assert (Hle : Rlsum (map (fun m => Cmod (Gchi p g A s m)) (seq 1 (S N)))
                  <= Rlsum (map (z (Re s)) (seq 1 (S N)))).
    { unfold Rlsum.
      assert (Hg2 : forall l : list nat,
        fold_right Rplus 0 (map (fun m => Cmod (Gchi p g A s m)) l)
        <= fold_right Rplus 0 (map (z (Re s)) l)).
      { induction l as [| x l IH]; cbn [map fold_right]; [ lra | ].
        pose proof (Gchi_mod_le p g A Hg Hord s x). lra. }
      apply Hg2. }
    eapply Rle_trans; [ exact Hle | ].
    unfold Rlsum. rewrite (diag_trace_eq (z (Re s)) (S N)). apply Rle_refl.
  - apply CUn_cv_Cmod. exact HL.
  - apply (Un_cv_S (fun N => diag_trace (z (Re s)) N)
             (zeta_cont (Re s) H0 H1)).
    apply (operator_zeta_eq_cont (Re s) H0 H1 Hs).
Qed.

(* ----------------------------------------------------------------- *)
(*  3.  the 3-4-1 contradiction, as a statement about real functions   *)
(* ----------------------------------------------------------------- *)

Theorem tfo_contradiction :
  forall (F G H : R -> R) (Cc Mm d : R),
  0 < d ->
  (forall sg, 1 < sg -> sg <= 2 -> sg - 1 < d ->
     1 <= (F sg) ^ 3 * (G sg) ^ 4 * (H sg)) ->
  (forall sg, 1 < sg -> sg <= 2 -> sg - 1 < d -> 0 <= F sg <= 2 / (sg - 1)) ->
  (forall sg, 1 < sg -> sg <= 2 -> sg - 1 < d -> 0 <= G sg <= Cc * (sg - 1)) ->
  (forall sg, 1 < sg -> sg <= 2 -> sg - 1 < d -> 0 <= H sg <= Mm) ->
  0 <= Cc -> 0 <= Mm -> False.
Proof.
  intros F G H Cc Mm d Hd Htfo HF HG HH HC0 HM0.
  (* choose sigma - 1 = e, small enough that 8 Cc^4 Mm e < 1 *)
  set (K := 8 * Cc ^ 4 * Mm + 1).
  assert (HK : 0 < K)
    by (unfold K; assert (0 <= 8 * Cc ^ 4 * Mm) by (apply Rmult_le_pos;
        [ apply Rmult_le_pos; [ lra | apply pow_le; exact HC0 ] | exact HM0 ]); lra).
  set (e := Rmin (Rmin (d / 2) 1) (/ (2 * K))).
  assert (He0 : 0 < e).
  { unfold e. apply Rmin_pos; [ apply Rmin_pos; lra | ].
    apply Rinv_0_lt_compat; lra. }
  assert (Hed : e < d)
    by (eapply Rle_lt_trans; [ eapply Rle_trans; [ apply Rmin_l | apply Rmin_l ] | lra ]).
  assert (He1 : e <= 1)
    by (eapply Rle_trans; [ eapply Rle_trans; [ apply Rmin_l | apply Rmin_r ] | lra ]).
  assert (HeK : e <= / (2 * K)) by apply Rmin_r.
  set (sg := 1 + e).
  assert (Hs1 : 1 < sg) by (unfold sg; lra).
  assert (Hs2 : sg <= 2) by (unfold sg; lra).
  assert (Hsd : sg - 1 < d) by (unfold sg; lra).
  assert (Hsm1 : sg - 1 = e) by (unfold sg; ring).
  pose proof (Htfo sg Hs1 Hs2 Hsd) as Ht.
  pose proof (HF sg Hs1 Hs2 Hsd) as [HF0 HFb].
  pose proof (HG sg Hs1 Hs2 Hsd) as [HG0 HGb].
  pose proof (HH sg Hs1 Hs2 Hsd) as [HH0 HHb].
  rewrite Hsm1 in HFb, HGb.
  (* F^3 <= 8/e^3, G^4 <= Cc^4 e^4, H <= Mm  ==>  product <= 8 Cc^4 Mm e *)
  assert (HF3 : (F sg) ^ 3 <= (2 / e) ^ 3)
    by (apply pow_incr; split; assumption).
  assert (HG4 : (G sg) ^ 4 <= (Cc * e) ^ 4)
    by (apply pow_incr; split; assumption).
  assert (HF30 : 0 <= (F sg) ^ 3) by (apply pow_le; exact HF0).
  assert (HG40 : 0 <= (G sg) ^ 4) by (apply pow_le; exact HG0).
  assert (HFe : 0 <= (2 / e) ^ 3)
    by (apply pow_le; apply Rlt_le, Rdiv_lt_0_compat; lra).
  assert (HGe : 0 <= (Cc * e) ^ 4) by (apply pow_le; nra).
  assert (Hchain : (F sg) ^ 3 * (G sg) ^ 4 * (H sg)
                   <= (2 / e) ^ 3 * (Cc * e) ^ 4 * Mm).
  { apply Rmult_le_compat; [ nra | exact HH0 | | exact HHb ].
    apply Rmult_le_compat; assumption. }
  assert (Hval : (2 / e) ^ 3 * (Cc * e) ^ 4 * Mm = 8 * Cc ^ 4 * Mm * e)
    by (field; lra).
  rewrite Hval in Hchain.
  (* but 8 Cc^4 Mm e <= (K-1) * / (2 K) < 1 *)
  assert (Hlt : 8 * Cc ^ 4 * Mm * e < 1).
  { assert (H0' : 0 <= 8 * Cc ^ 4 * Mm).
    { apply Rmult_le_pos;
        [ apply Rmult_le_pos; [ lra | apply pow_le; exact HC0 ] | exact HM0 ]. }
    assert (Hb : 8 * Cc ^ 4 * Mm <= K) by (unfold K; lra).
    apply Rle_lt_trans with (K * / (2 * K)).
    - apply Rmult_le_compat.
      + exact H0'.
      + lra.
      + exact Hb.
      + exact HeK.
    - replace (K * / (2 * K)) with (/ 2) by (field; lra). lra. }
  lra.
Qed.

Print Assumptions L_mod_le_zeta.
Print Assumptions tfo_contradiction.

(* ================================================================= *)
(*  END CLLineTools.v                                                 *)
(* ================================================================= *)
