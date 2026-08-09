(* ================================================================= *)
(*  SelbergDlogWeight.v  —  the SHARP total mass of the log-weight.      *)
(*                                                                    *)
(*  The signed log² Selberg identity (SelbergStarSigned.star_signed)     *)
(*  carries a surviving term  2·Dlog,  Dlog = Σ_{n≤N} Λ(n)ln n/n·Vsig.   *)
(*  To turn a concentration of Vsig on the sub-scales into a bound on     *)
(*  Dlog one needs the TOTAL log-weight mass — and, crucially, its SHARP  *)
(*  constant ½ (it is the ½ that pairs with the 2 to cancel α·ln²N).      *)
(*                                                                    *)
(*    | Σ_{n≤N} Λ(n)·ln n / n  −  ½·ln²N |  ≤  2·Kup·ln N + 1.            *)
(*                                                                    *)
(*  Proof: Abel summation of Mertens (msum n = ln n + O(Kup)) against     *)
(*  the weight ln n, plus the exact telescoping                          *)
(*     Σ ln n·(ln(n+1)−ln n) = ½ln²N − ½·Σ(ln(n+1)−ln n)²                 *)
(*  and  0 ≤ Σ(ln(n+1)−ln n)² ≤ 2  (from ln(1+1/n) ≤ 1/n, Σ1/n² ≤ 2).    *)
(*  The survey confirmed no standalone Σ Λ(n)ln n/n bound existed — it     *)
(*  only lived folded inside lam2_over_n_bound.  Axiom-clean.            *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia Arith Lists.List.
Import ListNotations.
Require Import Chebyshev ChebyshevBound VonMangoldtGlobal RealMobius MobiusOverD
        SelbergEndgame SelbergAverage SelbergAverageSigned SelbergSignedExtremes
        SelbergDip MertensTail MertensVonMangoldt SmoothingLemma.
Open Scope R_scope.

Lemma Rabs_le_inv : forall x M, Rabs x <= M -> - M <= x <= M.
Proof. intros x M H; unfold Rabs in H; destruct (Rcase_abs x); lra. Qed.

(* ----------------------------------------------------------------- *)
(*  0.  list-sum snoc + nonnegativity                                *)
(* ----------------------------------------------------------------- *)

Lemma Rls_snoc : forall (f : nat -> R) m,
  Rls (seq 1 (S m)) f = Rls (seq 1 m) f + f (S m).
Proof.
  intros f m. rewrite seq_S, Rls_app, Rls_cons, Rls_nil2.
  replace (1 + m)%nat with (S m) by lia. ring.
Qed.

Lemma Rls_nonneg : forall (f : nat -> R) l,
  (forall x, In x l -> 0 <= f x) -> 0 <= Rls l f.
Proof.
  intros f l; induction l as [|a l IH]; intros H.
  - rewrite Rls_nil2; lra.
  - rewrite Rls_cons. apply Rplus_le_le_0_compat.
    + apply H; left; reflexivity.
    + apply IH; intros x Hx; apply H; right; exact Hx.
Qed.

(* generic telescoping over the scale index *)
Lemma Rls_telescope : forall (u : nat -> R) N,
  Rls (seq 1 N) (fun n => u (S n) - u n) = u (S N) - u 1%nat.
Proof.
  intros u N; induction N as [|N IH].
  - assert (Hs : seq 1 0 = @nil nat) by reflexivity.
    rewrite Hs, Rls_nil2; ring.
  - rewrite Rls_snoc, IH; ring.
Qed.

(* ----------------------------------------------------------------- *)
(*  1.  the log-increment  dln n = ln(n+1) − ln n                     *)
(* ----------------------------------------------------------------- *)

Definition dln (n : nat) : R := ln (INR (S n)) - ln (INR n).

Lemma dln_nonneg : forall n, (1 <= n)%nat -> 0 <= dln n.
Proof.
  intros n Hn; unfold dln.
  assert (0 < INR n) by (apply lt_0_INR; lia).
  assert (INR n <= INR (S n)) by (apply le_INR; lia).
  pose proof (ln_le (INR n) (INR (S n)) ltac:(lra) ltac:(lra)); lra.
Qed.

Lemma dln_ub : forall n, (1 <= n)%nat -> dln n <= / INR n.
Proof.
  intros n Hn.
  assert (H0 : 0 < INR n) by (apply lt_0_INR; lia).
  assert (H1 : 0 < INR (S n)) by (apply lt_0_INR; lia).
  assert (Hrn : 0 < / INR n) by (apply Rinv_0_lt_compat; exact H0).
  assert (Hd : dln n = ln (INR (S n) / INR n)).
  { unfold dln, Rdiv.
    rewrite (ln_mult (INR (S n)) (/ INR n) H1 Hrn), (ln_Rinv (INR n) H0); ring. }
  rewrite Hd.
  apply Rle_trans with (INR (S n) / INR n - 1).
  - apply ln_self1, Rmult_lt_0_compat; [ exact H1 | exact Hrn ].
  - apply Req_le. rewrite S_INR. field. lra.
Qed.

(* ----------------------------------------------------------------- *)
(*  2.  Σ 1/n² ≤ 2  and  0 ≤ Σ (dln n)² ≤ 2                            *)
(* ----------------------------------------------------------------- *)

Lemma invsq_sum : forall N,
  Rls (seq 1 (S N)) (fun n => / INR n * / INR n) <= 2 - / INR (S N).
Proof.
  induction N as [|N IH].
  - assert (Hs : seq 1 1 = [1%nat]) by reflexivity.
    rewrite Hs, Rls_cons, Rls_nil2. simpl (INR 1). rewrite Rinv_1. lra.
  - rewrite Rls_snoc.
    assert (H1 : 0 < INR (S N)) by (apply lt_0_INR; lia).
    assert (H2 : 0 < INR (S (S N))) by (apply lt_0_INR; lia).
    assert (Ha : INR (S (S N)) = INR (S N) + 1) by (rewrite S_INR; reflexivity).
    (* the new top term is dominated by the telescoping gap *)
    assert (Hstep : / INR (S (S N)) * / INR (S (S N))
                    <= / INR (S N) - / INR (S (S N))).
    { assert (Hgap : / INR (S N) - / INR (S (S N))
                     = / (INR (S N) * INR (S (S N)))).
      { rewrite Ha; field; lra. }
      rewrite Hgap, <- Rinv_mult.
      apply Rinv_le_contravar.
      - apply Rmult_lt_0_compat; [ exact H1 | exact H2 ].
      - apply Rmult_le_compat_r; [ left; exact H2 | apply le_INR; lia ]. }
    lra.
Qed.

Lemma dlnsq_sum_bound : forall N,
  0 <= Rls (seq 1 N) (fun n => dln n * dln n) <= 2.
Proof.
  intro N; split.
  - apply Rls_nonneg; intros n Hn; nra.
  - destruct N as [|M].
    + assert (Hs : seq 1 0 = @nil nat) by reflexivity.
      rewrite Hs, Rls_nil2; lra.
    + apply Rle_trans with (Rls (seq 1 (S M)) (fun n => / INR n * / INR n)).
      * apply Rls_le; intros n Hn; apply in_seq in Hn.
        assert (Hn1 : (1 <= n)%nat) by lia.
        pose proof (dln_nonneg n Hn1) as Hp.
        pose proof (dln_ub n Hn1) as Hu.
        assert (0 < INR n) by (apply lt_0_INR; lia).
        assert (0 <= / INR n) by (left; apply Rinv_0_lt_compat; lra).
        nra.
      * pose proof (invsq_sum M) as H.
        assert (0 <= / INR (S M)) by (left; apply Rinv_0_lt_compat; apply lt_0_INR; lia).
        lra.
Qed.

(* ----------------------------------------------------------------- *)
(*  3.  Abel summation identity (bespoke, in the Rls / msum world)    *)
(* ----------------------------------------------------------------- *)

Lemma msum_snoc : forall m, msum (S m) = msum m + Lam (S m) / INR (S m).
Proof.
  intro m; rewrite (msum_Rls (S m)), (msum_Rls m), Rls_snoc; reflexivity.
Qed.

Lemma abel_id : forall N,
  Rls (seq 1 (S N)) (fun n => Lam n * ln (INR n) / INR n)
  = msum (S N) * ln (INR (S N))
    - Rls (seq 1 N) (fun n => msum n * dln n).
Proof.
  induction N as [|N IH].
  - assert (Hs1 : seq 1 1 = [1%nat]) by reflexivity.
    assert (Hs0 : seq 1 0 = @nil nat) by reflexivity.
    rewrite Hs1, Hs0, Rls_cons, Rls_nil2, Rls_nil2.
    rewrite Lam_1. simpl (INR 1). rewrite ln_1. lra.
  - rewrite (Rls_snoc (fun n => Lam n * ln (INR n) / INR n) (S N)), IH.
    rewrite (Rls_snoc (fun n => msum n * dln n) N).
    rewrite (msum_snoc (S N)).
    unfold dln.
    assert (Hi : INR (S (S N)) <> 0) by (apply not_0_INR; lia).
    field. exact Hi.
Qed.

(* Σ ln n·dln n = ½(ln²(N+1) − ln²1) − ½ Σ (dln n)²  *)
Lemma sum_lndln : forall N,
  Rls (seq 1 N) (fun n => ln (INR n) * dln n)
  = (ln (INR (S N)) * ln (INR (S N)) - ln (INR 1) * ln (INR 1)) / 2
    - Rls (seq 1 N) (fun n => dln n * dln n) / 2.
Proof.
  intro N.
  rewrite (Rls_ext nat
             (fun n => ln (INR n) * dln n)
             (fun n => / 2 * (ln (INR (S n)) * ln (INR (S n)) - ln (INR n) * ln (INR n))
                       + (- / 2) * (dln n * dln n))
             (seq 1 N))
    by (intros n _; unfold dln; field).
  rewrite Rls_add', Rls_scal', Rls_scal'.
  rewrite (Rls_telescope (fun n => ln (INR n) * ln (INR n)) N).
  field.
Qed.

(* ----------------------------------------------------------------- *)
(*  4.  the sharp total mass                                          *)
(* ----------------------------------------------------------------- *)

Theorem dlog_total_weight : forall N, (1 <= N)%nat ->
  Rabs (Rls (seq 1 N) (fun n => Lam n * ln (INR n) / INR n)
        - ln (INR N) * ln (INR N) / 2)
  <= 2 * Kup * ln (INR N) + 1.
Proof.
  intros N HN; destruct N as [|M]; [ lia | ].
  set (LN := ln (INR (S M))).
  assert (HLN0 : 0 <= LN).
  { unfold LN; rewrite <- ln_1; apply ln_le;
      [ lra | replace 1 with (INR 1) by (simpl; ring); apply le_INR; lia ]. }
  assert (Hln1 : ln (INR 1) = 0) by (replace (INR 1) with 1 by (simpl; ring); apply ln_1).
  set (DS := Rls (seq 1 M) (fun n => dln n * dln n)).
  set (SR := Rls (seq 1 M) (fun n => (msum n - ln (INR n)) * dln n)).
  (* split the Abel correction into telescoping mass + Mertens remainder *)
  assert (HAB : Rls (seq 1 M) (fun n => msum n * dln n)
                = (LN * LN - ln (INR 1) * ln (INR 1)) / 2 - DS / 2 + SR).
  { rewrite (Rls_ext nat
               (fun n => msum n * dln n)
               (fun n => ln (INR n) * dln n + (msum n - ln (INR n)) * dln n)
               (seq 1 M)) by (intros n _; ring).
    rewrite Rls_add'. fold SR. rewrite sum_lndln. unfold DS, LN. field. }
  (* the key equation *)
  assert (Heq : Rls (seq 1 (S M)) (fun n => Lam n * ln (INR n) / INR n)
                - LN * LN / 2
                = (msum (S M) - LN) * LN + DS / 2 - SR).
  { rewrite abel_id, HAB, Hln1. unfold LN; field. }
  (* the three bounds *)
  assert (Hrem : Rabs (msum (S M) - LN) <= Kup) by (unfold LN; apply mertens_lam; lia).
  apply Rabs_le_inv in Hrem.
  pose proof (dlnsq_sum_bound M) as [HDS0 HDS2]. fold DS in HDS0, HDS2.
  assert (HSR : Rabs SR <= Kup * LN).
  { unfold SR. eapply Rle_trans; [ apply Rls_abs | ].
    eapply Rle_trans with (Rls (seq 1 M) (fun n => Kup * dln n)).
    - apply Rls_le; intros n Hn; apply in_seq in Hn.
      assert (Hn1 : (1 <= n)%nat) by lia.
      pose proof (dln_nonneg n Hn1) as Hp.
      pose proof (mertens_lam n Hn1) as Hm; apply Rabs_le_inv in Hm.
      rewrite Rabs_mult, (Rabs_right (dln n)) by (apply Rle_ge; exact Hp).
      apply Rmult_le_compat_r; [ exact Hp | ].
      apply Rabs_le; lra.
    - rewrite Rls_scal'. unfold dln.
      rewrite (Rls_telescope (fun n => ln (INR n)) M).
      fold LN. rewrite Hln1. apply Req_le; ring. }
  apply Rabs_le_inv in HSR.
  (* combine *)
  apply Rabs_le; rewrite Heq; split; nra.
Qed.

Print Assumptions dlog_total_weight.

(* ================================================================= *)
(*  END SelbergDlogWeight.v  —  the sharp ½·ln²N total mass of the       *)
(*  log-weight Λ(n)ln n/n, the constant that pairs with the surviving    *)
(*  2·Dlog in the signed log² Selberg identity.  Axiom-clean.           *)
(* ================================================================= *)
