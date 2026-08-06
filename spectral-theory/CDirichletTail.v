(* ================================================================= *)
(*  CDirichletTail.v  —  Milestone A / B3d: the corner sum -> 0.        *)
(*                                                                    *)
(*  The hardest brick.  Given two nonnegative sequences a, b whose      *)
(*  partial sums Rls(seq 1 N) converge to SA, SB, the "corner" sum      *)
(*      Rbound N = Sum_{d<=N} a_d * Sum_{N/d<m<=N} b_m                   *)
(*  tends to 0.  Split at K = sqrt N: for d<=K we have N/d>=K so the     *)
(*  inner sum lies in the B-tail beyond K; for d>K the outer sum lies    *)
(*  in the A-tail beyond K.  Hence Rbound N <= SA*(SB-PB K)+(SA-PA K)*SB *)
(*  = Gtail(sqrt N) -> 0.  This furnishes the ->0 majorant that squeezes *)
(*  the B3c estimate |P_N - H_N| <= Rbound N, closing the exhaustion.   *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia Arith List.
Require Import ComplexField RealMobius MobiusOverD GammaFunction.
Import ListNotations.
Open Scope R_scope.

(* ---- Rls partial-sum split at K ---- *)
Lemma Rls_split : forall (g : nat -> R) N K, (K <= N)%nat ->
  Rls (seq 1 N) g = Rls (seq 1 K) g + Rls (seq (S K) (N - K)) g.
Proof.
  intros g N K HK.
  rewrite <- Rls_app; f_equal.
  replace (S K) with (1 + K)%nat by lia.
  rewrite <- List.seq_app; f_equal; lia.
Qed.

(* ---- a nonnegative sum over any seq range is nonnegative ---- *)
Lemma Rls_seq_nonneg : forall (g : nat -> R) s n,
  (forall k, 0 <= g k) -> 0 <= Rls (seq s n) g.
Proof.
  intros g s n Hg; revert s; induction n as [|n IH]; intro s;
    [ simpl; rewrite Rls_nil2; lra | ].
  cbn [seq]; rewrite Rls_cons; pose proof (Hg s); pose proof (IH (S s)); lra.
Qed.

(* ---- monotonicity of partial sums of a nonnegative sequence ---- *)
Lemma PA_mono : forall (g : nat -> R) K M, (forall k, 0 <= g k) -> (K <= M)%nat ->
  Rls (seq 1 K) g <= Rls (seq 1 M) g.
Proof.
  intros g K M Hg HKM; rewrite (Rls_split g M K HKM).
  pose proof (Rls_seq_nonneg g (S K) (M - K) Hg); lra.
Qed.

(* ---- partial sums are bounded by the limit ---- *)
Lemma PA_le_lim : forall (g : nat -> R) S', (forall k, 0 <= g k) ->
  Un_cv (fun N => Rls (seq 1 N) g) S' -> forall N, Rls (seq 1 N) g <= S'.
Proof.
  intros g S' Hg Hcv N; apply (growing_ineq (fun N => Rls (seq 1 N) g)).
  - intro n; apply PA_mono; [ exact Hg | lia ].
  - exact Hcv.
Qed.

(* ---- composing a convergent sequence with sqrt still converges ---- *)
Lemma Un_cv_comp_sqrt : forall (u : nat -> R) l,
  Un_cv u l -> Un_cv (fun N => u (Nat.sqrt N)) l.
Proof.
  intros u l Hu eps Heps; destruct (Hu eps Heps) as [M HM].
  exists (M * M)%nat; intros N HN; apply HM.
  rewrite <- (Nat.sqrt_square M); apply Nat.sqrt_le_mono; lia.
Qed.

Section Tail.

Variable a b : nat -> R.
Hypothesis Ha : forall d, 0 <= a d.
Hypothesis Hb : forall m, 0 <= b m.
Variable SA SB : R.
Hypothesis HA : Un_cv (fun N => Rls (seq 1 N) a) SA.
Hypothesis HB : Un_cv (fun N => Rls (seq 1 N) b) SB.

Let PA (N : nat) := Rls (seq 1 N) a.
Let PB (N : nat) := Rls (seq 1 N) b.

Lemma SA_nonneg : 0 <= SA.
Proof.
  pose proof (PA_le_lim a SA Ha HA 0%nat) as HH; cbn [seq] in HH;
    rewrite Rls_nil2 in HH; exact HH.
Qed.

Lemma SB_nonneg : 0 <= SB.
Proof.
  pose proof (PA_le_lim b SB Hb HB 0%nat) as HH; cbn [seq] in HH;
    rewrite Rls_nil2 in HH; exact HH.
Qed.

Definition Gtail (K : nat) : R :=
  SA * (SB - Rls (seq 1 K) b) + (SA - Rls (seq 1 K) a) * SB.

Lemma Gtail_cv : Un_cv Gtail 0.
Proof.
  unfold Gtail.
  replace 0 with (SA * (SB - SB) + (SA - SA) * SB) by ring.
  apply CV_plus.
  - apply (CV_mult (fun _ => SA) (fun K => SB - Rls (seq 1 K) b));
      [ apply Un_cv_const | apply (CV_minus (fun _ => SB)); [ apply Un_cv_const | exact HB ] ].
  - apply (CV_mult (fun K => SA - Rls (seq 1 K) a) (fun _ => SB));
      [ apply (CV_minus (fun _ => SA)); [ apply Un_cv_const | exact HA ] | apply Un_cv_const ].
Qed.

Definition Rbound (N : nat) : R :=
  Rls (seq 1 N) (fun d => a d * Rls (seq (S (N / d)) (N - N / d)) b).

Lemma Rbound_le : forall N, Rbound N <= Gtail (Nat.sqrt N).
Proof.
  intro N; destruct (Nat.eq_dec N 0) as [->|Hn0].
  - unfold Rbound; cbn [seq]; rewrite Rls_nil2.
    replace (Nat.sqrt 0) with 0%nat by reflexivity.
    unfold Gtail; cbn [seq]; rewrite !Rls_nil2.
    pose proof SA_nonneg; pose proof SB_nonneg; nra.
  - set (K := Nat.sqrt N).
    assert (HKK : (K * K <= N)%nat) by (unfold K; apply Nat.sqrt_spec; lia).
    assert (HK1 : (1 <= K)%nat).
    { unfold K; rewrite <- Nat.sqrt_1; apply Nat.sqrt_le_mono; lia. }
    assert (HKN : (K <= N)%nat) by nia.
    unfold Rbound.
    rewrite (Rls_split (fun d => a d * Rls (seq (S (N / d)) (N - N / d)) b) N K HKN).
    unfold Gtail; apply Rplus_le_compat.
    + (* d <= K : inner sum lies beyond PB K *)
      apply Rle_trans with (Rls (seq 1 K) (fun d => a d * (SB - Rls (seq 1 K) b))).
      * apply Rls_le; intros d Hd.
        apply Rmult_le_compat_l; [ apply Ha | ].
        apply in_seq in Hd.
        assert (Hd1 : (1 <= d)%nat) by lia.
        assert (HdK : (d <= K)%nat) by lia.
        assert (HdN : (N / d <= N)%nat)
          by (apply Nat.div_le_upper_bound; [ lia | nia ]).
        assert (HKd : (K <= N / d)%nat)
          by (apply Nat.div_le_lower_bound; [ lia | nia ]).
        assert (HCor : Rls (seq (S (N / d)) (N - N / d)) b
                       = Rls (seq 1 N) b - Rls (seq 1 (N / d)) b)
          by (rewrite (Rls_split b N (N / d) HdN); ring).
        rewrite HCor.
        pose proof (PA_le_lim b SB Hb HB N) as HPBN.
        pose proof (PA_mono b K (N / d) Hb HKd) as HPBmono.
        lra.
      * rewrite (Rls_ext nat (fun d => a d * (SB - Rls (seq 1 K) b))
                   (fun d => (SB - Rls (seq 1 K) b) * a d) (seq 1 K)
                   ltac:(intros d _; cbv beta; ring)).
        rewrite <- Rls_scal.
        assert (HSBpos : 0 <= SB - Rls (seq 1 K) b)
          by (pose proof (PA_le_lim b SB Hb HB K); lra).
        pose proof (PA_le_lim a SA Ha HA K) as HPAK.
        rewrite (Rmult_comm SA (SB - Rls (seq 1 K) b)).
        apply Rmult_le_compat_l; [ exact HSBpos | exact HPAK ].
    + (* d > K : outer sum lies in the A-tail beyond K *)
      apply Rle_trans with (Rls (seq (S K) (N - K)) (fun d => a d * SB)).
      * apply Rls_le; intros d Hd.
        apply Rmult_le_compat_l; [ apply Ha | ].
        apply in_seq in Hd.
        assert (Hd1 : (1 <= d)%nat) by lia.
        assert (HdN : (N / d <= N)%nat)
          by (apply Nat.div_le_upper_bound; [ lia | nia ]).
        assert (HCor : Rls (seq (S (N / d)) (N - N / d)) b
                       = Rls (seq 1 N) b - Rls (seq 1 (N / d)) b)
          by (rewrite (Rls_split b N (N / d) HdN); ring).
        rewrite HCor.
        pose proof (PA_le_lim b SB Hb HB N) as HPBN.
        pose proof (Rls_seq_nonneg b 1 (N / d) Hb) as HPBd.
        lra.
      * rewrite (Rls_ext nat (fun d => a d * SB) (fun d => SB * a d)
                   (seq (S K) (N - K)) ltac:(intros d _; cbv beta; ring)).
        rewrite <- Rls_scal.
        assert (Htail : Rls (seq (S K) (N - K)) a = Rls (seq 1 N) a - Rls (seq 1 K) a)
          by (rewrite (Rls_split a N K HKN); ring).
        rewrite Htail.
        pose proof (PA_le_lim a SA Ha HA N) as HPAN.
        pose proof SB_nonneg as HSB0.
        rewrite (Rmult_comm (SA - Rls (seq 1 K) a) SB).
        apply Rmult_le_compat_l; [ exact HSB0 | lra ].
Qed.

Theorem corner_cv0 :
  Un_cv (fun N => Rls (seq 1 N) (fun d => a d * Rls (seq (S (N / d)) (N - N / d)) b)) 0.
Proof.
  apply (Un_cv_squeeze0 _ (fun N => Gtail (Nat.sqrt N))).
  - exists 0%nat; intros N _; split.
    + apply Rls_seq_nonneg; intro d.
      apply Rmult_le_pos; [ apply Ha | apply Rls_seq_nonneg; exact Hb ].
    + apply Rbound_le.
  - apply Un_cv_comp_sqrt; apply Gtail_cv.
Qed.

End Tail.

Print Assumptions corner_cv0.

(* ================================================================= *)
(*  END CDirichletTail.v  —  the corner remainder -> 0.                *)
(* ================================================================= *)
