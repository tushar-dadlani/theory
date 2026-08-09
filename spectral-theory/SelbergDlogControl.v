(* ================================================================= *)
(*  SelbergDlogControl.v  —  bounding the surviving Dlog term.           *)
(*                                                                    *)
(*  star_signed (SelbergStarSigned) leaves an uncancelled                *)
(*    2·Dlog,   Dlog = Σ_{n≤N} Λ(n)ln n/n · Vsig(N/n)  =  Σ w(n)·Vsig,   *)
(*  with the NONNEGATIVE log-weight w(n) = Λ(n)ln n/n.                    *)
(*                                                                    *)
(*  The purely algebraic attack is circular (Λ(n)ln n = Λ2 − Λ∗Λ +       *)
(*  selberg2_reindex + selberg_average_signed regenerates star_signed).  *)
(*  So Dlog can only be controlled through the SIGN of Vsig.  We do the   *)
(*  clean, division-free half here:                                      *)
(*                                                                    *)
(*  1.  dlog_split_bound — the exact sign-split                          *)
(*        Dlog ≤ (−α+δ)·W  +  (Kup−1−(−α+δ))·Wc                          *)
(*      where  W = Σ w  (total mass)  and  Wc = Σ w·[Vsig(N/n) > −α+δ]    *)
(*      is the "not-a-deep-trough" mass.  (w≥0, |Vsig|≤Kup−1.)           *)
(*                                                                    *)
(*  2.  dlog_upper — feed in the SHARP total mass W = ½ln²N + O(ln N)     *)
(*      (SelbergDlogWeight.dlog_total_weight):                           *)
(*        Dlog ≤ (−α+δ)·½ln²N + (Kup−1+α−δ)·Wc + (α−δ)(2Kup ln N+1).      *)
(*                                                                    *)
(*  This isolates the SINGLE remaining density input Wc (the not-trough   *)
(*  log-mass) — the Stage-3 log-weighted concentration.  Axiom-clean.    *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia Arith Lists.List.
Import ListNotations.
Require Import Chebyshev ChebyshevBound VonMangoldtGlobal RealMobius MobiusOverD
        SelbergEndgame SelbergAverage SelbergAverageSigned SelbergSignedExtremes
        SelbergDip MertensTail MertensVonMangoldt SmoothingLemma
        SelbergSignedConc SelbergDlogWeight.
Open Scope R_scope.

(* the nonnegative log-weight and the Dlog functional *)
Definition w (n : nat) : R := Lam n * ln (INR n) / INR n.

Lemma w_nonneg : forall n, (1 <= n)%nat -> 0 <= w n.
Proof.
  intros n Hn; unfold w, Rdiv.
  apply Rmult_le_pos; [ apply Rmult_le_pos | left; apply Rinv_0_lt_compat; apply lt_0_INR; lia ].
  - apply Lam_nonneg.
  - rewrite <- ln_1; apply ln_le; [ lra | replace 1 with (INR 1) by (simpl; ring); apply le_INR; lia ].
Qed.

(* indicator "Vsig(N/n) is NOT a deep trough": Vsig(N/n) > −α+δ *)
Definition wnt (alpha delta : R) (N n : nat) : R :=
  if Rlt_dec (- alpha + delta) (Vsig (N / n)%nat) then 1 else 0.

Definition Dlogf (N : nat) : R := Rls (seq 1 N) (fun n => w n * Vsig (N / n)%nat).

(* ----------------------------------------------------------------- *)
(*  1.  the exact sign-split of Dlog                                  *)
(* ----------------------------------------------------------------- *)

Theorem dlog_split_bound : forall N alpha delta,
  Dlogf N
  <= (- alpha + delta) * Rls (seq 1 N) w
     + (Kup - 1 - (- alpha + delta))
       * Rls (seq 1 N) (fun n => w n * wnt alpha delta N n).
Proof.
  intros N alpha delta. unfold Dlogf.
  eapply Rle_trans with
    (Rls (seq 1 N)
       (fun n => (- alpha + delta) * w n
                 + (Kup - 1 - (- alpha + delta)) * (w n * wnt alpha delta N n))).
  - apply Rls_le; intros n Hn; apply in_seq in Hn.
    assert (Hn1 : (1 <= n)%nat) by lia.
    assert (Hq1 : (1 <= N / n)%nat) by (apply Nat.div_le_lower_bound; lia).
    pose proof (w_nonneg n Hn1) as Hw0.
    unfold wnt; destruct (Rlt_dec (- alpha + delta) (Vsig (N / n)%nat)) as [Hgt | Hle].
    + (* not a trough: bound Vsig(N/n) ≤ Kup−1 *)
      pose proof (Vsig_ub (N / n)%nat Hq1) as Hub.
      replace ((- alpha + delta) * w n + (Kup - 1 - (- alpha + delta)) * (w n * 1))
        with (w n * (Kup - 1)) by ring.
      apply Rmult_le_compat_l; [ exact Hw0 | exact Hub ].
    + (* deep trough: Vsig(N/n) ≤ −α+δ *)
      replace ((- alpha + delta) * w n + (Kup - 1 - (- alpha + delta)) * (w n * 0))
        with (w n * (- alpha + delta)) by ring.
      apply Rmult_le_compat_l; [ exact Hw0 | lra ].
  - rewrite Rls_add', Rls_scal', Rls_scal'. apply Req_le; ring.
Qed.

(* ----------------------------------------------------------------- *)
(*  2.  Dlog upper bound with the SHARP total mass ½ln²N              *)
(* ----------------------------------------------------------------- *)

Theorem dlog_upper : forall N alpha delta,
  0 <= alpha -> delta <= alpha -> (1 <= N)%nat ->
  Dlogf N
  <= (- alpha + delta) * (ln (INR N) * ln (INR N)) / 2
     + (Kup - 1 - (- alpha + delta))
       * Rls (seq 1 N) (fun n => w n * wnt alpha delta N n)
     + (alpha - delta) * (2 * Kup * ln (INR N) + 1).
Proof.
  intros N alpha delta Ha Hda HN.
  set (W := Rls (seq 1 N) w).
  set (Wc := Rls (seq 1 N) (fun n => w n * wnt alpha delta N n)).
  set (c := - alpha + delta).
  assert (Hc0 : c <= 0) by (unfold c; lra).
  (* the split *)
  pose proof (dlog_split_bound N alpha delta) as Hsplit. fold W Wc c in Hsplit.
  (* the sharp total mass: W ≥ ½ln²N − (2Kup ln N + 1) *)
  pose proof (dlog_total_weight N HN) as Htot.
  assert (HW : Rls (seq 1 N) (fun n => Lam n * ln (INR n) / INR n) = W)
    by (unfold W, w; reflexivity).
  rewrite HW in Htot. apply Rabs_le_inv in Htot.
  set (E := 2 * Kup * ln (INR N) + 1).
  assert (HWlo : ln (INR N) * ln (INR N) / 2 - E <= W) by (unfold E in *; lra).
  (* multiply W ≥ b by c ≤ 0 : c·W ≤ c·b *)
  assert (Hw : c * W <= c * (ln (INR N) * ln (INR N) / 2 - E))
    by (apply Rmult_le_compat_neg_l; [ exact Hc0 | exact HWlo ]).
  (* algebra of the boundary term *)
  assert (Hcb : c * (ln (INR N) * ln (INR N) / 2 - E)
                = c * (ln (INR N) * ln (INR N)) / 2 + (alpha - delta) * E)
    by (unfold c, E; field).
  unfold E in *. lra.
Qed.

Print Assumptions dlog_upper.

(* ================================================================= *)
(*  END SelbergDlogControl.v  —  Dlog is now pinned between the SHARP    *)
(*  total mass ½ln²N and the not-trough log-mass Wc.  The single         *)
(*  remaining input is a bound on Wc (the Stage-3 log-weighted           *)
(*  concentration); with Wc = o(ln²N) at a peak, star_signed forces       *)
(*  D2 = o(ln²N) there.  Full PNT closure still needs the two-scale       *)
(*  overlap on top.  Axiom-clean.                                        *)
(* ================================================================= *)
