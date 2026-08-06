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
        PsiAsymp LimSup LimInf SelbergSignedExtremes LnLimits
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

Lemma Rls_opp : forall (l : list nat) (f : nat -> R), Rls l (fun d => - f d) = - Rls l f.
Proof.
  induction l as [|a l IH]; intros f;
    [ rewrite !Rls_nil2; ring | rewrite !Rls_cons, IH; ring ].
Qed.

(* ================================================================= *)
(*  THE PIN:  0 < alpha  ->  V = alpha  /\  v = - alpha.               *)
(* ================================================================= *)
Theorem signed_pin : forall V v alpha,
  is_limsup Vsig V -> is_liminf Vsig v -> is_limsup Vrem alpha -> 0 < alpha ->
  V = alpha /\ v = - alpha.
Proof.
  intros V v alpha HV Hv Halpha Hapos.
  pose proof (V_le_alpha V alpha HV Halpha) as HVa.
  pose proof (negalpha_le_v v alpha Hv Halpha) as Hva.
  pose proof (alpha_eq_max V v alpha HV Hv Halpha) as Hmax.
  set (Csig := (88 + 3 * Kup + 1) + (Kup - 1) * Kup).
  assert (Hbnd : forall n, Rabs (Vsig n) <= Kup - 1)
    by (intros n; rewrite <- Vrem_eq_absVsig; apply Vrem_bound_all).
  destruct (Rle_or_lt (- v) V) as [Hcase | Hcase].
  - (* -v <= V : alpha = V; prove v = -alpha via a +spike *)
    assert (HaV : Rmax V (- v) = V)
      by (apply Rle_antisym; [ apply Rmax_lub; [ lra | exact Hcase ] | apply Rmax_l ]).
    assert (HeV : alpha = V) by (rewrite Hmax; exact HaV).
    split; [ symmetry; exact HeV | ].
    apply Rle_antisym; [ | exact Hva ].
    destruct (Rle_or_lt v (- alpha)) as [Hg | Hb]; [ exact Hg | exfalso ].
    set (eps := (v + alpha) / 4).
    assert (Heps : 0 < eps) by (unfold eps; lra).
    assert (Hlimopp : is_limsup (fun n => - Vsig n) (- v))
      by (apply (proj1 (is_liminf_opp Vsig v)); exact Hv).
    assert (Hbndopp : forall n, Rabs (- Vsig n) <= Kup - 1)
      by (intros n; rewrite Rabs_Ropp; apply Hbnd).
    destruct (sum_upper (fun n => - Vsig n) (- v) (Kup - 1) Hlimopp Hbndopp eps Heps)
      as [K1 [C1 HC1]].
    destruct (cv_infty_ln (2 * (C1 + Csig) / (v + alpha))) as [Nln HNln].
    destruct HV as [_ HV_io].
    destruct (HV_io eps Heps (Nat.max (Nat.max K1 Nln) 2)) as [k [Hk Hspike]].
    assert (Hk1 : (1 <= k)%nat) by lia.
    assert (HlnN : 0 < ln (INR k)) by (apply ln_INR_pos; lia).
    pose proof (selberg_average_signed k Hk1) as Hpin. fold Csig in Hpin.
    set (S := Rls (seq 1 k) (fun d => Lam d / INR d * Vsig (k / d)%nat)) in *.
    pose proof (HC1 k ltac:(lia)) as HC1k; cbn beta in HC1k.
    assert (Hrls : Rls (seq 1 k) (fun d => Lam d / INR d * (- Vsig (k / d)%nat)) = - S)
      by (unfold S; rewrite <- Rls_opp; apply Rls_ext; intros d _; ring).
    rewrite Hrls in HC1k.
    assert (Hlnk : 2 * (C1 + Csig) / (v + alpha) < ln (INR k)) by (apply HNln; lia).
    pose proof (Rle_abs (Vsig k * ln (INR k) + S)) as Hup.
    assert (Hsp : alpha - eps < Vsig k) by (rewrite HeV; exact Hspike).
    assert (HVk : (alpha - eps) * ln (INR k) < Vsig k * ln (INR k))
      by (apply Rmult_lt_compat_r; [ exact HlnN | exact Hsp ]).
    assert (HPbound : (alpha - eps) * ln (INR k) < Csig - S)
      by (apply Rlt_le_trans with (Vsig k * ln (INR k)); [ exact HVk | lra ]).
    assert (Hcombine : (alpha - eps) * ln (INR k)
                       < Csig + (- v + eps) * ln (INR k) + C1) by lra.
    assert (Hderiv : (v + alpha) / 2 * ln (INR k) < C1 + Csig).
    { replace ((v + alpha) / 2 * ln (INR k))
        with ((alpha - eps) * ln (INR k) - (- v + eps) * ln (INR k))
        by (unfold eps; field).
      lra. }
    assert (HMeq : (v + alpha) / 2 * (2 * (C1 + Csig) / (v + alpha)) = C1 + Csig)
      by (field; lra).
    assert (Hcontra : C1 + Csig < (v + alpha) / 2 * ln (INR k))
      by (rewrite <- HMeq; apply Rmult_lt_compat_l; [ lra | exact Hlnk ]).
    lra.
  - (* V < -v : alpha = -v; prove V = alpha via a -spike *)
    assert (Hav0 : Rmax V (- v) = - v)
      by (apply Rle_antisym; [ apply Rmax_lub; [ lra | apply Rle_refl ] | apply Rmax_r ]).
    assert (Hev : alpha = - v) by (rewrite Hmax; exact Hav0).
    split; [ | lra ].
    apply Rle_antisym; [ exact HVa | ].
    destruct (Rle_or_lt alpha V) as [Hg | Hb]; [ exact Hg | exfalso ].
    set (eps := (alpha - V) / 4).
    assert (Heps : 0 < eps) by (unfold eps; lra).
    destruct (sum_upper Vsig V (Kup - 1) HV Hbnd eps Heps) as [K1 [C1 HC1]].
    destruct (cv_infty_ln (2 * (C1 + Csig) / (alpha - V))) as [Nln HNln].
    destruct Hv as [_ Hv_io].
    destruct (Hv_io eps Heps (Nat.max (Nat.max K1 Nln) 2)) as [k [Hk Hspike]].
    assert (Hk1 : (1 <= k)%nat) by lia.
    assert (HlnN : 0 < ln (INR k)) by (apply ln_INR_pos; lia).
    pose proof (selberg_average_signed k Hk1) as Hpin. fold Csig in Hpin.
    pose proof (HC1 k ltac:(lia)) as HC1k; cbn beta in HC1k.
    set (S := Rls (seq 1 k) (fun d => Lam d / INR d * Vsig (k / d)%nat)) in *.
    assert (Hlnk : 2 * (C1 + Csig) / (alpha - V) < ln (INR k)) by (apply HNln; lia).
    pose proof (Rle_abs (- (Vsig k * ln (INR k) + S))) as Hlo; rewrite Rabs_Ropp in Hlo.
    assert (Hsp : Vsig k < - alpha + eps) by (assert (v = - alpha) by lra; lra).
    assert (HVk : Vsig k * ln (INR k) < (- alpha + eps) * ln (INR k))
      by (apply Rmult_lt_compat_r; [ exact HlnN | exact Hsp ]).
    assert (HScombine : - ((V + eps) * ln (INR k) + (- alpha + eps) * ln (INR k))
                        < C1 + Csig) by lra.
    assert (Hderiv : (alpha - V) / 2 * ln (INR k) < C1 + Csig).
    { replace ((alpha - V) / 2 * ln (INR k))
        with (- ((V + eps) * ln (INR k) + (- alpha + eps) * ln (INR k)))
        by (unfold eps; field).
      exact HScombine. }
    assert (HMeq : (alpha - V) / 2 * (2 * (C1 + Csig) / (alpha - V)) = C1 + Csig)
      by (field; lra).
    assert (Hcontra : C1 + Csig < (alpha - V) / 2 * ln (INR k))
      by (rewrite <- HMeq; apply Rmult_lt_compat_l; [ lra | exact Hlnk ]).
    lra.
Qed.

Print Assumptions signed_pin.

(* ================================================================= *)
(*  END SelbergPin.v  —  V = -v = alpha (the signed symmetry the       *)
(*  dead-ended avg_below route could not see).  Next: the degree-2      *)
(*  self-improvement (star_inequality + smoothing) => alpha = 0.        *)
(* ================================================================= *)
