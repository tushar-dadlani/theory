(* ================================================================= *)
(*  SelbergPin.v  —  rung 2b: the signed pin forces V = -v = alpha.    *)
(*                                                                    *)
(*  sum_upper (generic bulk/tail): for a bounded sequence u with       *)
(*  is_limsup u U,  sum_{d<=k}(Lam d/d) u(k/d) <= (U+eps) ln k + C.     *)
(*  Applied to Vsig (U=V) and to -Vsig (U=-v) it bounds the signed     *)
(*  Selberg average sum_{d}(Lam d/d)Vsig(k/d) both ways.  Combined      *)
(*  with selberg_average_signed (which pins that sum to -Vsig(k)ln k    *)
(*  + O(1)) at a spike (Vsig(k) ~ -+alpha), it forces V = -v = alpha.   *)
(*  Axiom-clean.                                                       *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia Arith Lists.List.
Import ListNotations.
Require Import Chebyshev ChebyshevBound ChebyshevPrime VonMangoldtGlobal
        RealMobius MobiusOverD SelbergEndgame SelbergAverage SelbergAverageSigned
        PsiAsymp LimSup LimInf SelbergSignedExtremes
        MertensVonMangoldt MertensTail SmoothingLemma SelbergDip.
Open Scope R_scope.

(* generic upper bound on the Lambda-weighted average by the limsup *)
Lemma sum_upper : forall (u : nat -> R) U B,
  is_limsup u U -> (forall n, Rabs (u n) <= B) ->
  forall eps, 0 < eps ->
  exists K C, forall k, (K <= k)%nat ->
    Rls (seq 1 k) (fun d => Lam d / INR d * u (k / d)%nat) <= (U + eps) * ln (INR k) + C.
Proof.
  intros u U B [HU_ub _] HB eps Heps.
  assert (HB0 : 0 <= B) by (pose proof (HB 0%nat); pose proof (Rabs_pos (u 0%nat)); lra).
  destruct (HU_ub eps Heps) as [N0' HN0'].
  set (N0 := Nat.max N0' 2).
  assert (HN0lo : (2 <= N0)%nat) by (unfold N0; lia).
  assert (HN0u : forall n, (N0 <= n)%nat -> u n < U + eps)
    by (intros n Hn; apply HN0'; unfold N0 in Hn; lia).
  set (D := Kup + ln (2 * INR N0)).
  set (Ctail := ln (2 * INR N0) + 2 * Kup).
  exists (Nat.max (2 * N0) 2), ((Rabs U + eps) * D + B * Ctail).
  intros k Hk.
  assert (HN2N0 : (2 * N0 <= k)%nat) by lia.
  set (q := (k / N0)%nat).
  assert (Hq1 : (1 <= q)%nat) by (unfold q; apply Nat.div_le_lower_bound; lia).
  assert (HqN : (q <= k)%nat)
    by (unfold q; pose proof (Nat.Div0.mul_div_le k N0) as Hm; nia).
  assert (Hseq : seq 1 k = seq 1 q ++ seq (S q) (k - q)).
  { replace k with (q + (k - q))%nat at 1 by lia.
    rewrite List.seq_app; f_equal; f_equal; lia. }
  set (g := fun d => Lam d / INR d).
  assert (Hgnn : forall d, (1 <= d)%nat -> 0 <= g d).
  { intros d Hd; unfold g, Rdiv; apply Rmult_le_pos;
      [ apply Lam_nonneg | apply inv_INR_nonneg ]. }
  assert (Htail_sum : Rls (seq (S q) (k - q)) g = msum k - msum q).
  { unfold g; rewrite (msum_Rls k), (msum_Rls q), Hseq, Rls_app; ring. }
  rewrite Hseq, Rls_app.
  (* BULK <= (U+eps) * msum q *)
  assert (Hbulk : Rls (seq 1 q) (fun d => Lam d / INR d * u (k / d)%nat)
                  <= (U + eps) * msum q).
  { apply Rle_trans with (Rls (seq 1 q) (fun d => (U + eps) * (Lam d / INR d))).
    - apply Rls_le; intros d Hd; apply in_seq in Hd.
      rewrite (Rmult_comm (U + eps)).
      apply Rmult_le_compat_l; [ apply Hgnn; lia | ].
      apply Rlt_le, HN0u, Ndiv_ge; unfold q in *; lia.
    - rewrite (Rls_scal' (seq 1 q) (U + eps)); rewrite <- (msum_Rls q); apply Rle_refl. }
  (* TAIL <= B * (msum k - msum q) *)
  assert (Htail : Rls (seq (S q) (k - q)) (fun d => Lam d / INR d * u (k / d)%nat)
                  <= B * (msum k - msum q)).
  { apply Rle_trans with (Rls (seq (S q) (k - q)) (fun d => B * (Lam d / INR d))).
    - apply Rls_le; intros d Hd; apply in_seq in Hd.
      rewrite (Rmult_comm B).
      apply Rmult_le_compat_l; [ apply Hgnn; lia | ].
      pose proof (HB (k / d)%nat); pose proof (Rle_abs (u (k / d)%nat)); lra.
    - rewrite (Rls_scal' (seq (S q) (k - q)) B); fold g; rewrite Htail_sum; apply Rle_refl. }
  (* |msum q - ln k| <= D *)
  assert (Ha2 : Rabs (msum q - ln (INR k)) <= D).
  { unfold D. pose proof (mertens_lam q ltac:(lia)) as Hml.
    pose proof (tail_ln k N0 ltac:(lia) HN2N0) as Htl.
    assert (Hlq : ln (INR q) <= ln (INR k))
      by (apply ln_le'; [ apply lt_0_INR; lia | apply le_INR; lia ]).
    pose proof (Rle_abs (msum q - ln (INR q))) as Hp1.
    pose proof (Rle_abs (- (msum q - ln (INR q)))) as Hp2; rewrite Rabs_Ropp in Hp2.
    apply Rabs_le; unfold q in *; lra. }
  (* bulk part: (U+eps) msum q <= (U+eps) ln k + (|U|+eps) D *)
  assert (Hbulk2 : (U + eps) * msum q <= (U + eps) * ln (INR k) + (Rabs U + eps) * D).
  { pose proof (Rle_abs ((U + eps) * (msum q - ln (INR k)))) as Hx.
    rewrite Rabs_mult in Hx.
    assert (Ha1 : Rabs (U + eps) <= Rabs U + eps).
    { pose proof (Rabs_triang U eps); rewrite (Rabs_pos_eq eps) in * by lra; lra. }
    assert (Hprod : Rabs (U + eps) * Rabs (msum q - ln (INR k)) <= (Rabs U + eps) * D)
      by (apply Rmult_le_compat; [ apply Rabs_pos | apply Rabs_pos | exact Ha1 | exact Ha2 ]).
    nra. }
  (* tail part: msum k - msum q <= Ctail *)
  assert (Htailb : msum k - msum q <= Ctail).
  { pose proof (mertens_tail q k ltac:(lia) ltac:(lia)) as Hmt.
    pose proof (tail_ln k N0 ltac:(lia) HN2N0) as Htl.
    unfold Ctail, q in *; lra. }
  assert (HBt : B * (msum k - msum q) <= B * Ctail)
    by (apply Rmult_le_compat_l; [ exact HB0 | exact Htailb ]).
  lra.
Qed.

Print Assumptions sum_upper.

(* ================================================================= *)
(*  END SelbergPin.v (part 1: sum_upper).  Pin theorem to follow.       *)
(* ================================================================= *)
