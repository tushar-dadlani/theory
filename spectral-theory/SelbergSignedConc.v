(* ================================================================= *)
(*  SelbergSignedConc.v  —  the peak-concentration lemma, foundation of  *)
(*  the SIGNED two-scale Erdős self-improvement.                        *)
(*                                                                    *)
(*  At a near-peak N (Vsig N ≥ α−η), the signed Selberg symmetry         *)
(*  (selberg_average_signed) forces the Λ(d)/d-weighted average of       *)
(*  Vsig(N/d) to be ≈ −α, hence — since Vsig(N/d) ≥ −α−ε (liminf) — MOST  *)
(*  of the Λ/d-mass concentrates at the TROUGH −α:                       *)
(*                                                                    *)
(*    δ · Σ_{d≤N/M0} (Λ d/d)·[Vsig(N/d) > −α+δ]                          *)
(*      ≤ (η+ε)·ln N + O(1).                                            *)
(*                                                                    *)
(*  i.e. the "not-a-trough" set has Λ/d-mass ≤ ((η+ε)ln N + O(1))/δ.      *)
(*  This is the input to the two-scale overlap (Selberg 1949).          *)
(*  Axiom-clean.  (The unsigned |Vrem| dip route is a dead branch — see  *)
(*  SelbergSelfImprove.v header / docs/pnt_elementary_status.md.)        *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia Arith Lists.List.
Import ListNotations.
Require Import Chebyshev ChebyshevBound VonMangoldtGlobal RealMobius MobiusOverD
        SelbergEndgame SelbergAverage SelbergAverageSigned SelbergSignedExtremes
        SelbergDip MertensTail MertensVonMangoldt SmoothingLemma LimSup LimInf.
Open Scope R_scope.

Lemma Rabs_le_inv : forall x M, Rabs x <= M -> - M <= x <= M.
Proof. intros x M H; unfold Rabs in H; destruct (Rcase_abs x); lra. Qed.

Definition Cs : R := 88 + 3 * Kup + 1 + (Kup - 1) * Kup.

Lemma Vsig_lb : forall n, (1 <= n)%nat -> - (Kup - 1) <= Vsig n.
Proof.
  intros n Hn; pose proof (Vrem_bound n Hn) as Hb; rewrite Vrem_eq_absVsig in Hb.
  apply Rabs_le_inv in Hb; lra.
Qed.

Lemma Vsig_ub : forall n, (1 <= n)%nat -> Vsig n <= Kup - 1.
Proof.
  intros n Hn; pose proof (Vrem_bound n Hn) as Hb; rewrite Vrem_eq_absVsig in Hb.
  apply Rabs_le_inv in Hb; lra.
Qed.

Section Conc.
Variable alpha : R.
Hypothesis Halpha0 : 0 <= alpha.

Definition ihi (delta : R) (N d : nat) : R :=
  if Rlt_dec (- alpha + delta) (Vsig (N / d)%nat) then 1 else 0.

Theorem peak_concentration : forall (N M0 : nat) (delta eps eta : R),
  0 < delta -> 0 <= eps -> 0 <= eta -> (1 <= M0)%nat -> (2 * M0 <= N)%nat ->
  (forall m, (M0 <= m)%nat -> - alpha - eps < Vsig m) ->
  alpha - eta <= Vsig N ->
  delta * Rls (seq 1 (N / M0)) (fun d => Lam d / INR d * ihi delta N d)
  <= (eta + eps) * ln (INR N)
     + (eps * Kup + (Kup - 1) * (ln (2 * INR M0) + 2 * Kup) + alpha * Kup + Cs).
Proof.
  intros N M0 delta eps eta Hd Heps Heta HM0 HN Hlim Hpeak.
  assert (HN1 : (1 <= N)%nat) by lia.
  assert (HlnN : 0 <= ln (INR N))
    by (rewrite <- ln_1; apply ln_le; [ lra | replace 1 with (INR 1) by (simpl; ring); apply le_INR; lia ]).
  assert (HKupm : 0 <= Kup - 1) by (unfold Kup; pose proof ln2_pos; lra).
  set (q := (N / M0)%nat).
  assert (Hq1 : (1 <= q)%nat) by (unfold q; apply Nat.div_le_lower_bound; lia).
  assert (HqN : (q <= N)%nat) by (unfold q; pose proof (Nat.Div0.mul_div_le N M0); nia).
  set (Q := Rls (seq 1 q) (fun d => Lam d / INR d * ihi delta N d)).
  set (P := Rls (seq 1 N) (fun d => Lam d / INR d * (Vsig (N / d)%nat + alpha))).
  set (g := fun d => Lam d / INR d).
  assert (Hgnn : forall d, (1 <= d)%nat -> 0 <= g d).
  { intros d Hd'; unfold g; apply Rmult_le_pos;
      [ apply Lam_nonneg | left; apply Rinv_0_lt_compat; apply lt_0_INR; lia ]. }
  (* P = S(N) + alpha·msum N *)
  assert (HPeq : P = Rls (seq 1 N) (fun d => Lam d / INR d * Vsig (N / d)%nat) + alpha * msum N).
  { unfold P.
    rewrite (Rls_ext nat
               (fun d => Lam d / INR d * (Vsig (N / d)%nat + alpha))
               (fun d => Lam d / INR d * Vsig (N / d)%nat + alpha * (Lam d / INR d))
               (seq 1 N))
      by (intros d _; ring).
    rewrite Rls_add', (Rls_scal' (seq 1 N) alpha), <- (msum_Rls N); reflexivity. }
  (* upper bound on P *)
  assert (Hmert : Rabs (msum N - ln (INR N)) <= Kup) by (apply mertens_lam; lia).
  apply Rabs_le_inv in Hmert.
  pose proof (selberg_average_signed N HN1) as Hsel; apply Rabs_le_inv in Hsel.
  assert (HPupper : P <= eta * ln (INR N) + (alpha * Kup + Cs)).
  { rewrite HPeq. unfold Cs in *. nra. }
  (* lower bound on P: seq split *)
  assert (Hseq : seq 1 N = seq 1 q ++ seq (S q) (N - q)).
  { replace N with (q + (N - q))%nat at 1 by lia.
    rewrite List.seq_app; f_equal; f_equal; lia. }
  assert (Hbulk : delta * Q - eps * msum q
                  <= Rls (seq 1 q) (fun d => Lam d / INR d * (Vsig (N / d)%nat + alpha))).
  { apply Rle_trans with (Rls (seq 1 q)
      (fun d => delta * (Lam d / INR d * ihi delta N d) + (- eps) * (Lam d / INR d))).
    - rewrite (Rls_lin (seq 1 q) delta (- eps)).
      unfold Q; rewrite <- (msum_Rls q); fold g; lra.
    - apply Rls_le; intros d Hd'; apply in_seq in Hd'.
      assert (HdM0 : (M0 <= N / d)%nat) by (apply Ndiv_ge; unfold q in *; lia).
      pose proof (Hlim (N / d)%nat HdM0) as Hvd.
      replace (delta * (Lam d / INR d * ihi delta N d) + - eps * (Lam d / INR d))
        with (Lam d / INR d * (delta * ihi delta N d - eps)) by ring.
      apply Rmult_le_compat_l; [ apply Hgnn; lia | ].
      unfold ihi; destruct (Rlt_dec (- alpha + delta) (Vsig (N / d)%nat)) as [Hlt | Hge];
        [ lra | lra ]. }
  set (Ctail := ln (2 * INR M0) + 2 * Kup).
  assert (Htail : - ((Kup - 1) * Ctail)
                  <= Rls (seq (S q) (N - q)) (fun d => Lam d / INR d * (Vsig (N / d)%nat + alpha))).
  { apply Rle_trans with (Rls (seq (S q) (N - q)) (fun d => (- (Kup - 1)) * (Lam d / INR d))).
    - rewrite (Rls_scal' (seq (S q) (N - q)) (- (Kup - 1))); fold g.
      assert (Htw : Rls (seq (S q) (N - q)) g = msum N - msum q)
        by (unfold g; rewrite (msum_Rls N), (msum_Rls q), Hseq, Rls_app; ring).
      rewrite Htw.
      pose proof (mertens_tail q N ltac:(lia) ltac:(lia)) as Hmt.
      pose proof (tail_ln N M0 ltac:(lia) ltac:(lia)) as Htl.
      unfold Ctail, q in *. nra.
    - apply Rls_le; intros d Hd'; apply in_seq in Hd'.
      assert (Hd1 : (1 <= N / d)%nat) by (apply Nat.div_le_lower_bound; lia).
      pose proof (Vsig_lb (N / d)%nat Hd1) as Hvd.
      replace (- (Kup - 1) * (Lam d / INR d)) with (Lam d / INR d * (- (Kup - 1))) by ring.
      apply Rmult_le_compat_l; [ apply Hgnn; lia | lra ]. }
  assert (HPlower : delta * Q - eps * msum q - (Kup - 1) * Ctail <= P).
  { unfold P; rewrite Hseq, Rls_app; lra. }
  (* combine *)
  assert (Hmsq : msum q <= ln (INR N) + Kup).
  { pose proof (mertens_lam q ltac:(lia)) as H; apply Rabs_le_inv in H.
    assert (ln (INR q) <= ln (INR N))
      by (apply ln_le'; [ apply lt_0_INR; lia | apply le_INR; lia ]); lra. }
  unfold Ctail in *. nra.
Qed.

Print Assumptions peak_concentration.

(* the mirror: at a near-trough N, MOST sub-scales are peaks (Vsig ≈ +α) *)
Definition ilo (delta : R) (N d : nat) : R :=
  if Rlt_dec (Vsig (N / d)%nat) (alpha - delta) then 1 else 0.

Theorem trough_concentration : forall (N M0 : nat) (delta eps eta : R),
  0 < delta -> 0 <= eps -> 0 <= eta -> (1 <= M0)%nat -> (2 * M0 <= N)%nat ->
  (forall m, (M0 <= m)%nat -> Vsig m < alpha + eps) ->
  Vsig N <= - alpha + eta ->
  delta * Rls (seq 1 (N / M0)) (fun d => Lam d / INR d * ilo delta N d)
  <= (eta + eps) * ln (INR N)
     + (eps * Kup + (Kup - 1) * (ln (2 * INR M0) + 2 * Kup) + alpha * Kup + Cs).
Proof.
  intros N M0 delta eps eta Hd Heps Heta HM0 HN Hlim Htrough.
  assert (HN1 : (1 <= N)%nat) by lia.
  assert (HlnN : 0 <= ln (INR N))
    by (rewrite <- ln_1; apply ln_le; [ lra | replace 1 with (INR 1) by (simpl; ring); apply le_INR; lia ]).
  assert (HKupm : 0 <= Kup - 1) by (unfold Kup; pose proof ln2_pos; lra).
  set (q := (N / M0)%nat).
  assert (Hq1 : (1 <= q)%nat) by (unfold q; apply Nat.div_le_lower_bound; lia).
  assert (HqN : (q <= N)%nat) by (unfold q; pose proof (Nat.Div0.mul_div_le N M0); nia).
  set (Q := Rls (seq 1 q) (fun d => Lam d / INR d * ilo delta N d)).
  set (P := Rls (seq 1 N) (fun d => Lam d / INR d * (alpha - Vsig (N / d)%nat))).
  set (g := fun d => Lam d / INR d).
  assert (Hgnn : forall d, (1 <= d)%nat -> 0 <= g d).
  { intros d Hd'; unfold g; apply Rmult_le_pos;
      [ apply Lam_nonneg | left; apply Rinv_0_lt_compat; apply lt_0_INR; lia ]. }
  assert (HPeq : P = alpha * msum N - Rls (seq 1 N) (fun d => Lam d / INR d * Vsig (N / d)%nat)).
  { unfold P.
    rewrite (Rls_ext nat
               (fun d => Lam d / INR d * (alpha - Vsig (N / d)%nat))
               (fun d => alpha * (Lam d / INR d) + (-1) * (Lam d / INR d * Vsig (N / d)%nat))
               (seq 1 N))
      by (intros d _; ring).
    rewrite Rls_add', (Rls_scal' (seq 1 N) alpha),
      (Rls_scal' (seq 1 N) (-1)), <- (msum_Rls N); ring. }
  assert (Hmert : Rabs (msum N - ln (INR N)) <= Kup) by (apply mertens_lam; lia).
  apply Rabs_le_inv in Hmert.
  pose proof (selberg_average_signed N HN1) as Hsel; apply Rabs_le_inv in Hsel.
  assert (HPupper : P <= eta * ln (INR N) + (alpha * Kup + Cs)).
  { rewrite HPeq. unfold Cs in *. nra. }
  assert (Hseq : seq 1 N = seq 1 q ++ seq (S q) (N - q)).
  { replace N with (q + (N - q))%nat at 1 by lia.
    rewrite List.seq_app; f_equal; f_equal; lia. }
  assert (Hbulk : delta * Q - eps * msum q
                  <= Rls (seq 1 q) (fun d => Lam d / INR d * (alpha - Vsig (N / d)%nat))).
  { apply Rle_trans with (Rls (seq 1 q)
      (fun d => delta * (Lam d / INR d * ilo delta N d) + (- eps) * (Lam d / INR d))).
    - rewrite (Rls_lin (seq 1 q) delta (- eps)).
      unfold Q; rewrite <- (msum_Rls q); fold g; lra.
    - apply Rls_le; intros d Hd'; apply in_seq in Hd'.
      assert (HdM0 : (M0 <= N / d)%nat) by (apply Ndiv_ge; unfold q in *; lia).
      pose proof (Hlim (N / d)%nat HdM0) as Hvd.
      replace (delta * (Lam d / INR d * ilo delta N d) + - eps * (Lam d / INR d))
        with (Lam d / INR d * (delta * ilo delta N d - eps)) by ring.
      apply Rmult_le_compat_l; [ apply Hgnn; lia | ].
      unfold ilo; destruct (Rlt_dec (Vsig (N / d)%nat) (alpha - delta)) as [Hlt | Hge];
        [ lra | lra ]. }
  set (Ctail := ln (2 * INR M0) + 2 * Kup).
  assert (Htail : - ((Kup - 1) * Ctail)
                  <= Rls (seq (S q) (N - q)) (fun d => Lam d / INR d * (alpha - Vsig (N / d)%nat))).
  { apply Rle_trans with (Rls (seq (S q) (N - q)) (fun d => (- (Kup - 1)) * (Lam d / INR d))).
    - rewrite (Rls_scal' (seq (S q) (N - q)) (- (Kup - 1))); fold g.
      assert (Htw : Rls (seq (S q) (N - q)) g = msum N - msum q)
        by (unfold g; rewrite (msum_Rls N), (msum_Rls q), Hseq, Rls_app; ring).
      rewrite Htw.
      pose proof (mertens_tail q N ltac:(lia) ltac:(lia)) as Hmt.
      pose proof (tail_ln N M0 ltac:(lia) ltac:(lia)) as Htl.
      unfold Ctail, q in *. nra.
    - apply Rls_le; intros d Hd'; apply in_seq in Hd'.
      assert (Hd1 : (1 <= N / d)%nat) by (apply Nat.div_le_lower_bound; lia).
      pose proof (Vsig_ub (N / d)%nat Hd1) as Hvd.
      replace (- (Kup - 1) * (Lam d / INR d)) with (Lam d / INR d * (- (Kup - 1))) by ring.
      apply Rmult_le_compat_l; [ apply Hgnn; lia | lra ]. }
  assert (HPlower : delta * Q - eps * msum q - (Kup - 1) * Ctail <= P).
  { unfold P; rewrite Hseq, Rls_app; lra. }
  assert (Hmsq : msum q <= ln (INR N) + Kup).
  { pose proof (mertens_lam q ltac:(lia)) as H; apply Rabs_le_inv in H.
    assert (ln (INR q) <= ln (INR N))
      by (apply ln_le'; [ apply lt_0_INR; lia | apply le_INR; lia ]); lra. }
  unfold Ctail in *. nra.
Qed.

Print Assumptions trough_concentration.

End Conc.

(* ================================================================= *)
(*  END SelbergSignedConc.v  —  peak-concentration in place; the deep    *)
(*  remaining step is the two-scale OVERLAP (apply this at a peak AND at  *)
(*  a trough sub-scale; the Fubini over the two indices produces the      *)
(*  Λ₂/contradiction) — Selberg's 1949 core.                             *)
(* ================================================================= *)
