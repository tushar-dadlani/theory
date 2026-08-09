(* ================================================================= *)
(*  SelbergSelfImprove.v  —  the Erdős–Selberg self-improvement, stage  *)
(*  2a–2c:  reduce  self_improve  to the Λ₂-weighted dip via the         *)
(*  (already-proved) log² Selberg "star" inequality.                    *)
(*                                                                    *)
(*  With α := limsup Vrem > 0, the star inequality                       *)
(*    Vrem N · ln²N ≤ Σ_{n≤N} (Λ₂ n/n) Vrem(N/n) + O(ln N)              *)
(*  (StarInequality.star_inequality) plus Σ Λ₂/n = ln²N + O(ln N)        *)
(*  (SmoothingLemma.lam2_over_n_bound) turn a positive-Λ₂-density DIP     *)
(*  (Vrem(N/n) ≤ b < α on a set of Λ₂-mass ≥ θ ln²N) into the strict      *)
(*  improvement  Vrem N ≤ α − (α−b)θ + o(1),  contradicting limsup = α.  *)
(*                                                                    *)
(*    self_improve_of_dip :                                            *)
(*      forall L, is_limsup Vrem L -> 0 < L -> lambda2_dip L -> False.  *)
(*                                                                    *)
(*  This is the Λ₂/ln² analogue of SelbergDip.dip_avg_below; it isolates *)
(*  PNT to the single density fact  lambda2_dip.                         *)
(*                                                                    *)
(*  ⚠ CAVEAT (see docs/pnt_elementary_status.md): the theorems below are  *)
(*  VALID but on a DEAD BRANCH — lambda2_dip is FALSE for α>0.  At a peak *)
(*  N* (Vrem(N*)→α) the star inequality itself forces dipw2 b N* =        *)
(*  O(ε₀)·ln²N*, so no fixed θ works uniformly.  The unsigned |Vrem| log² *)
(*  route gives no improvement at peaks (|·| kills the ±α cancellation).  *)
(*  The correct closure is the SIGNED two-scale Erdős argument            *)
(*  (selberg_average_signed + signed_pin), not this dip.                 *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia Arith Lists.List.
Import ListNotations.
Require Import Chebyshev ChebyshevBound ChebyshevPrime VonMangoldtGlobal
        RealMobius MobiusOverD SelbergEndgame SelbergAverage SelbergSymmetry
        StarInequality SmoothingLemma SelbergDip LimSup PsiAsymp MertensVonMangoldt
        PNTUnconditional PNTConditional PrimePowerReindex.
Open Scope R_scope.

Lemma Rabs_le_inv : forall x M, Rabs x <= M -> - M <= x <= M.
Proof. intros x M H; unfold Rabs in H; destruct (Rcase_abs x); lra. Qed.

(* ---- Λ₂ ≥ 0 and Λ₂(n)/n ≥ 0 ---- *)
Lemma Rls_ge0 : forall (l : list nat) (f : nat -> R),
  (forall k, In k l -> 0 <= f k) -> 0 <= Rls l f.
Proof.
  induction l as [|a l IH]; intros f H.
  - rewrite Rls_nil2; lra.
  - rewrite Rls_cons; apply Rplus_le_le_0_compat;
      [ apply H; left; reflexivity
      | apply IH; intros k Hk; apply H; right; exact Hk ].
Qed.

Lemma Lam2_nonneg : forall n, (1 <= n)%nat -> 0 <= Lam2 n.
Proof.
  intros n Hn; unfold Lam2; apply Rplus_le_le_0_compat.
  - apply Rmult_le_pos; [ apply Lam_nonneg | ].
    rewrite <- ln_1; apply ln_le; [ lra | ].
    replace 1 with (INR 1) by (simpl; ring); apply le_INR; lia.
  - apply Rls_ge0; intros d _; apply Rmult_le_pos; apply Lam_nonneg.
Qed.

Lemma Lam2_over_n_nonneg : forall n, (1 <= n)%nat -> 0 <= Lam2 n / INR n.
Proof.
  intros n Hn; apply Rmult_le_pos;
    [ apply Lam2_nonneg; exact Hn
    | left; apply Rinv_0_lt_compat; apply lt_0_INR; lia ].
Qed.

(* ---- the Λ₂-weighted dip ---- *)
Definition ind2 (b : R) (N n : nat) : R :=
  if Rle_dec (Vrem (N / n)%nat) b then 1 else 0.

Definition dipw2 (b : R) (N : nat) : R :=
  Rls (seq 1 N) (fun n => Lam2 n / INR n * ind2 b N n).

Definition lambda2_dip (L : R) : Prop :=
  exists b theta, b < L /\ 0 < theta /\
    exists K, forall N, (K <= N)%nat -> theta * (ln (INR N) * ln (INR N)) <= dipw2 b N.

(* ---- the improved-bound accounting (Λ₂/ln² analogue of dip_avg_below) ---- *)
(* For all large N:  Vrem N · ln²N ≤ cmain·ln²N + C1·ln N + C0,  with       *)
(* cmain = (L+eps) − (L+eps−b)·theta.                                       *)
Theorem self_improve_of_dip :
  forall L, is_limsup Vrem L -> 0 < L -> lambda2_dip L -> False.
Proof.
  intros L Hlim Hpos Hdip.
  destruct Hdip as [b [theta [Hbl [Htheta [Kdip Hdw]]]]].
  assert (Hthle1 : theta <= 1 \/ 1 < theta) by lra.  (* theta is a density; either way fine *)
  destruct Hlim as [Hub Hreach].
  set (eps := (L - b) * theta / 8).
  assert (Heps : 0 < eps) by (unfold eps; nra).
  destruct (Hub eps Heps) as [N0' HN0'].
  set (N0 := Nat.max N0' 2).
  assert (HN0lo : (2 <= N0)%nat) by (unfold N0; lia).
  assert (HN0'2 : forall n, (N0 <= n)%nat -> Vrem n < L + eps)
    by (intros n Hn; apply HN0'; unfold N0 in Hn; lia).
  set (A := L + eps).
  assert (HAb : 0 <= A - b) by (unfold A, eps; nra).
  assert (HA : 0 <= A) by (unfold A, eps; nra).
  assert (HKupm : 0 <= Kup - 1) by (unfold Kup; pose proof ln2_pos; lra).
  assert (HKup0 : 0 <= Kup) by (unfold Kup; pose proof ln2_pos; lra).
  assert (HKup1 : 1 <= Kup) by (unfold Kup; pose proof ln2_pos; lra).
  assert (Hl2 : 0 <= ln 2) by (pose proof ln2_pos; lra).
  assert (Hln2 : 0 < ln 2) by (rewrite <- ln_1; apply ln_increasing; lra).
  set (cmain := A - (A - b) * theta).
  set (LN2 := ln (2 * INR N0)).
  assert (HLN2 : 0 <= LN2).
  { unfold LN2; rewrite <- ln_1; apply ln_le; [ lra | ].
    apply Rle_trans with (2 * 1); [ lra | apply Rmult_le_compat_l; [ lra | ] ].
    replace 1 with (INR 1) by (simpl; ring); apply le_INR; lia. }
  (* the O(ln N) constants of the remainder, made explicit *)
  set (C1 := A * (2 * Kup + ln 2)
             + (A - b + (Kup - 1)) * (2 * LN2 + 2 * (2 * Kup + ln 2))
             + (88 + 3 * Kup + 1)
             + ((88 + 3 * Kup + 1) + (Kup - 1) * ln 2)).
  set (C0 := A * ((Kup + ln 2) * Kup)
             + (A - b + (Kup - 1)) * (2 * ((Kup + ln 2) * Kup))
             + ((88 + 3 * Kup + 1) + (Kup - 1) * ln 2) * Kup).
  (* THE IMPROVED BOUND *)
  assert (Himp : forall N, (Nat.max (Nat.max Kdip (2 * N0)) 2 <= N)%nat ->
    Vrem N * (ln (INR N) * ln (INR N))
    <= cmain * (ln (INR N) * ln (INR N)) + C1 * ln (INR N) + C0).
  { intros N HN.
    assert (HNge2 : (2 <= N)%nat) by lia.
    assert (HN2N0 : (2 * N0 <= N)%nat) by lia.
    assert (HNKdip : (Kdip <= N)%nat) by lia.
    set (t := ln (INR N)).
    assert (Ht0 : 0 < t) by (unfold t; apply ln_INR_pos; lia).
    assert (Ht2 : ln 2 <= t)
      by (unfold t; apply ln_le'; [ lra | replace 2 with (INR 2) by (simpl; ring); apply le_INR; lia ]).
    set (q := (N / N0)%nat).
    assert (Hq1 : (1 <= q)%nat) by (unfold q; apply Nat.div_le_lower_bound; lia).
    assert (HqN : (q <= N)%nat)
      by (unfold q; pose proof (Nat.Div0.mul_div_le N N0) as Hm; nia).
    set (tq := ln (INR q)).
    assert (Htq0 : 0 <= tq)
      by (unfold tq; rewrite <- ln_1; apply ln_le; [ lra | replace 1 with (INR 1) by (simpl; ring); apply le_INR; lia ]).
    assert (Htqt : tq <= t)
      by (unfold tq, t; apply ln_le'; [ apply lt_0_INR; lia | apply le_INR; lia ]).
    (* seq split *)
    assert (Hseq : seq 1 N = seq 1 q ++ seq (S q) (N - q)).
    { replace N with (q + (N - q))%nat at 1 by lia.
      rewrite List.seq_app; f_equal; f_equal; lia. }
    set (g2 := fun n => Lam2 n / INR n).
    assert (Hg2nn : forall n, (1 <= n)%nat -> 0 <= g2 n) by (intros; apply Lam2_over_n_nonneg; lia).
    set (BN := Rls (seq 1 N) g2).
    set (Bq := Rls (seq 1 q) g2).
    set (Dq := Rls (seq 1 q) (fun n => Lam2 n / INR n * ind2 b N n)).
    (* the Λ₂ partial-sum bounds *)
    assert (HBNb : Rabs (BN - t * t) <= Kup * t + (Kup + ln 2) * (t + Kup)).
    { unfold BN, t; pose proof (lam2_over_n_bound N ltac:(lia)) as H.
      replace (Rls (seq 1 N) g2) with (Rls (seq 1 N) (fun n => Lam2 n / INR n)) by reflexivity.
      replace (ln (INR N) * ln (INR N)) with (ln (INR N) * ln (INR N)) by reflexivity; exact H. }
    assert (HBqb : Rabs (Bq - tq * tq) <= Kup * tq + (Kup + ln 2) * (tq + Kup)).
    { unfold Bq, tq; pose proof (lam2_over_n_bound q ltac:(lia)) as H; exact H. }
    (* BN = Bq + tail weight (nonneg) *)
    assert (Htailw : BN = Bq + Rls (seq (S q) (N - q)) g2)
      by (unfold BN, Bq; rewrite Hseq, Rls_app; reflexivity).
    assert (Htailnn : 0 <= Rls (seq (S q) (N - q)) g2)
      by (apply Rls_ge0; intros n Hn; apply in_seq in Hn; apply Hg2nn; lia).
    assert (HBqBN : Bq <= BN) by lra.
    (* tail log-gap:  t² − tq² ≤ 2·LN2·t *)
    assert (Hgap : t - tq <= LN2)
      by (unfold t, tq, LN2, q; apply tail_ln; lia).
    assert (Ht2tq2 : t * t - tq * tq <= 2 * LN2 * t).
    { apply Rle_trans with ((t - tq) * (t + tq)).
      - apply Req_le; ring.
      - apply Rle_trans with (LN2 * (2 * t)); [ | apply Req_le; ring ].
        apply Rmult_le_compat; lra. }
    (* BN − Bq bound *)
    assert (HBNBq : BN - Bq <= 2 * LN2 * t + (Kup * t + (Kup + ln 2) * (t + Kup))
                                            + (Kup * tq + (Kup + ln 2) * (tq + Kup))).
    { apply Rabs_le_inv in HBNb, HBqb. nra. }
    (* BULK *)
    assert (Hbulk : Rls (seq 1 q) (fun n => Lam2 n / INR n * Vrem (N / n)%nat)
                    <= A * Bq - (A - b) * Dq).
    { apply Rle_trans with (Rls (seq 1 q)
        (fun n => A * (Lam2 n / INR n) + (- (A - b)) * (Lam2 n / INR n * ind2 b N n))).
      - apply Rls_le; intros n Hn; apply in_seq in Hn.
        replace (A * (Lam2 n / INR n) + (- (A - b)) * (Lam2 n / INR n * ind2 b N n))
          with (Lam2 n / INR n * (A - (A - b) * ind2 b N n)) by ring.
        apply Rmult_le_compat_l; [ apply Hg2nn; lia | ].
        unfold ind2; destruct (Rle_dec (Vrem (N / n)%nat) b) as [Hd1 | Hd0]; [ lra | ].
        replace (A - (A - b) * 0) with A by ring.
        unfold A; apply Rlt_le, HN0'2, Ndiv_ge; unfold q in *; lia.
      - rewrite (Rls_lin (seq 1 q) A (- (A - b))).
        unfold Bq, Dq, g2; lra. }
    (* TAIL *)
    assert (Htail : Rls (seq (S q) (N - q)) (fun n => Lam2 n / INR n * Vrem (N / n)%nat)
                    <= (Kup - 1) * (BN - Bq)).
    { apply Rle_trans with (Rls (seq (S q) (N - q)) (fun n => (Kup - 1) * (Lam2 n / INR n))).
      - apply Rls_le; intros n Hn; apply in_seq in Hn.
        apply Rle_trans with (Lam2 n / INR n * (Kup - 1));
          [ apply Rmult_le_compat_l;
              [ apply Hg2nn; lia | apply Vrem_bound; apply Nat.div_le_lower_bound; lia ]
          | apply Req_le; ring ].
      - rewrite (Rls_scal' (seq (S q) (N - q)) (Kup - 1)).
        unfold g2 in Htailw; rewrite Htailw; lra. }
    (* dip credit:  Dq ≥ θ·t² − (BN − Bq) *)
    assert (Hdipsplit : dipw2 b N = Dq + Rls (seq (S q) (N - q)) (fun n => Lam2 n / INR n * ind2 b N n)).
    { unfold dipw2, Dq; rewrite Hseq, Rls_app; reflexivity. }
    assert (Htaildip : Rls (seq (S q) (N - q)) (fun n => Lam2 n / INR n * ind2 b N n) <= BN - Bq).
    { assert (Heqt : BN - Bq = Rls (seq (S q) (N - q)) (fun n => Lam2 n / INR n))
        by (rewrite Htailw; unfold g2; ring).
      rewrite Heqt; apply Rls_le; intros n Hn; apply in_seq in Hn.
      unfold ind2; destruct (Rle_dec (Vrem (N / n)%nat) b);
        [ rewrite Rmult_1_r; lra | rewrite Rmult_0_r; apply Lam2_over_n_nonneg; lia ]. }
    pose proof (Hdw N HNKdip) as Hdwn.
    assert (HDq : theta * (t * t) - (BN - Bq) <= Dq) by (unfold t; lra).
    (* star inequality + mertens; msum bound *)
    pose proof (star_inequality N ltac:(lia)) as Hstar; fold t in Hstar.
    pose proof (mertens_lam N ltac:(lia)) as Hmert; apply Rabs_le_inv in Hmert; fold t in Hmert.
    assert (Hmsum : msum N <= t + Kup) by lra.
    assert (HBqub : Bq <= t * t + (Kup * t + (Kup + ln 2) * (t + Kup)))
      by (apply Rabs_le_inv in HBqb; nra).
    (* RlsAll ≤ A·Bq − (A−b)·Dq + (Kup−1)·(BN−Bq) *)
    assert (Hrls : Rls (seq 1 N) (fun n => Lam2 n / INR n * Vrem (N / n)%nat)
                   <= A * Bq - (A - b) * Dq + (Kup - 1) * (BN - Bq))
      by (rewrite Hseq, Rls_app; lra).
    (* product bounds, kept as atoms for the final linear combine *)
    set (EN := Kup * t + (Kup + ln 2) * (t + Kup)).
    assert (HP1 : A * Bq <= A * (t * t) + A * EN)
      by (pose proof (Rmult_le_compat_l A Bq (t * t + EN) HA HBqub) as H; nra).
    assert (HP2e : (A - b) * theta * (t * t) - (A - b) * (BN - Bq) <= (A - b) * Dq).
    { replace ((A - b) * theta * (t * t) - (A - b) * (BN - Bq))
        with ((A - b) * (theta * (t * t) - (BN - Bq))) by ring.
      apply Rmult_le_compat_l; [ exact HAb | exact HDq ]. }
    (* BN − Bq ≤ 2·LN2·t + 2·EN  (tq ≤ t) *)
    assert (HBB : BN - Bq <= 2 * LN2 * t + 2 * EN) by (unfold EN; nra).
    assert (HP3a : (A - b) * (BN - Bq) <= (A - b) * (2 * LN2 * t + 2 * EN))
      by (apply Rmult_le_compat_l; [ exact HAb | exact HBB ]).
    assert (HP3b : (Kup - 1) * (BN - Bq) <= (Kup - 1) * (2 * LN2 * t + 2 * EN))
      by (apply Rmult_le_compat_l; [ exact HKupm | exact HBB ]).
    (* main-term cancellation and E1 bound (ring / mertens) *)
    assert (Ecm : A * (t * t) - (A - b) * theta * (t * t) = cmain * (t * t))
      by (unfold cmain; ring).
    assert (Hcoeff : 0 <= (88 + 3 * Kup + 1) + (Kup - 1) * ln 2) by nra.
    assert (HE1 : (88 + 3 * Kup + 1) * t + (88 + 3 * Kup + 1) * msum N + (Kup - 1) * ln 2 * msum N
                  <= (88 + 3 * Kup + 1) * t + ((88 + 3 * Kup + 1) + (Kup - 1) * ln 2) * (t + Kup)).
    { replace ((88 + 3 * Kup + 1) * t + (88 + 3 * Kup + 1) * msum N + (Kup - 1) * ln 2 * msum N)
        with ((88 + 3 * Kup + 1) * t + ((88 + 3 * Kup + 1) + (Kup - 1) * ln 2) * msum N) by ring.
      apply Rplus_le_compat_l, Rmult_le_compat_l; [ exact Hcoeff | exact Hmsum ]. }
    (* the O(ln N) remainder folds EXACTLY to C1·t + C0 (ring) *)
    assert (Hfinal :
      cmain * (t * t)
      + (A * EN + (A - b) * (2 * LN2 * t + 2 * EN) + (Kup - 1) * (2 * LN2 * t + 2 * EN))
      + ((88 + 3 * Kup + 1) * t + ((88 + 3 * Kup + 1) + (Kup - 1) * ln 2) * (t + Kup))
      = cmain * (t * t) + C1 * t + C0)
      by (unfold C1, C0, EN, LN2; ring).
    (* linear combine: all products are atoms *)
    lra. }
  (* ---- the contradiction ---- *)
  set (Kbase := Nat.max (Nat.max Kdip (2 * N0)) 2).
  set (pos := (A - b) * theta - 2 * eps).
  assert (Hpospos : 0 < pos).
  { unfold pos, A, eps.
    assert (H8 : (L - b) * theta / 8 = eps) by (unfold eps; reflexivity).
    nra. }
  set (Tsuff := 1 + (C1 + Rabs C0) / pos).
  destruct (INR_unbounded (exp Tsuff)) as [K2 HK2].
  set (Kfin := Nat.max (Nat.max Kbase K2) 2).
  destruct (Hreach eps Heps Kfin) as [k [Hk Hvk]].
  assert (Hk2 : (2 <= k)%nat) by (unfold Kfin in Hk; lia).
  assert (HkKbase : (Kbase <= k)%nat) by (unfold Kfin in Hk; lia).
  set (tk := ln (INR k)).
  assert (Htk0 : 0 < tk) by (unfold tk; apply ln_INR_pos; lia).
  (* tk is large *)
  assert (HtkT : Tsuff <= tk).
  { unfold tk.
    assert (Hexp : exp Tsuff <= INR k)
      by (apply Rle_trans with (INR K2); [ apply Rlt_le; exact HK2 | apply le_INR; unfold Kfin in Hk; lia ]).
    rewrite <- (ln_exp Tsuff); apply ln_le'; [ apply exp_pos | exact Hexp ]. }
  (* the improved bound at k *)
  pose proof (Himp k HkKbase) as Himpk.
  fold tk in Himpk.
  (* Vrem k > L − eps *)
  assert (Hlow : (L - eps) * (tk * tk) < Vrem k * (tk * tk))
    by (apply Rmult_lt_compat_r; [ nra | exact Hvk ]).
  (* so pos·tk² < C1·tk + C0, contradicting tk ≥ Tsuff *)
  assert (Hcontra : pos * (tk * tk) < C1 * tk + C0)
    by (unfold pos, cmain, A in *; nra).
  (* but tk ≥ Tsuff = 1 + (C1 + |C0|)/pos forces pos·tk² ≥ C1·tk + C0 *)
  assert (HC0 : C0 <= Rabs C0) by apply Rle_abs.
  assert (HRC0 : 0 <= Rabs C0) by apply Rabs_pos.
  assert (HC1pos : 0 <= C1) by (unfold C1; nra).
  assert (Hbig : C1 * tk + C0 <= pos * (tk * tk)).
  { assert (Htk1 : 1 <= tk).
    { apply Rle_trans with Tsuff; [ | exact HtkT ]. unfold Tsuff.
      assert (0 <= (C1 + Rabs C0) / pos)
        by (unfold Rdiv; apply Rmult_le_pos;
            [ lra | left; apply Rinv_0_lt_compat; exact Hpospos ]); lra. }
    assert (Hstep : (C1 + Rabs C0) / pos <= tk) by (unfold Tsuff in HtkT; lra).
    assert (Hkey : C1 + Rabs C0 <= pos * tk)
      by (apply Rmult_le_reg_l with (/ pos);
          [ apply Rinv_0_lt_compat; exact Hpospos
          | replace (/ pos * (pos * tk)) with tk by (field; lra);
            replace (/ pos * (C1 + Rabs C0)) with ((C1 + Rabs C0) / pos) by (field; lra);
            exact Hstep ]).
    nra. }
  lra.
Qed.

Print Assumptions self_improve_of_dip.

(* ---- PNT, reduced to the single Λ₂-dip density fact ---- *)
Theorem pnt_of_lambda2_dip :
  (forall L, is_limsup Vrem L -> 0 < L -> lambda2_dip L) ->
  Un_cv (fun N => pi_count N / (INR N / ln (INR N))) 1.
Proof.
  intro Hdip; apply pnt_of_self_improve.
  intros L Hlim Hpos; exact (self_improve_of_dip L Hlim Hpos (Hdip L Hlim Hpos)).
Qed.

Print Assumptions pnt_of_lambda2_dip.
