(* ================================================================= *)
(*  PsiThetaTail.v  —  the prime-power tail  psi - theta = O(sqrt N ln N).*)
(*                                                                    *)
(*  psi(N) - theta(N) = Sum_{p^k<=N, k>=2} ln p  is the correction      *)
(*  between the two Chebyshev functions.  Reindexing psi over primes    *)
(*  (psi N <= Sum_{p<=N} inner N p, inner N p = ln p * #{k: p^k<=N}),    *)
(*  and theta N = Sum_{p<=N} ln p, gives                                *)
(*      psi N - theta N <= Sum_{p<=N} (inner N p - ln p),               *)
(*  where inner N p - ln p = 0 unless p^2 <= N (i.e. p <= sqrt N), and   *)
(*  is <= ln N there (inner_le).  Since #{primes p <= sqrt N} <= sqrt N: *)
(*      0 <= psi N - theta N <= sqrt N * ln N.                          *)
(*  Hence psi(N) ~ N  <=>  theta(N) ~ N  (Step 4a bridge).  Axiom-clean. *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia Arith List.
Require Import VonMangoldtGlobal Chebyshev ChebyshevBound MuLog
        PrimePowerReindex ChebyshevPrime.
Import ListNotations.
Open Scope R_scope.

Lemma Rlsum_map_minus : forall (A : Type) (f g : A -> R) (l : list A),
  Rlsum (map (fun x => f x - g x) l) = Rlsum (map f l) - Rlsum (map g l).
Proof.
  intros A f g l; induction l as [|a l IH]; [ simpl; ring | ].
  cbn [map]; rewrite !Rlsum_cons, IH; ring.
Qed.

(* inner N p = ln p * (number of exponents k with p^k <= N) *)
Lemma inner_count : forall N p,
  inner N p
  = ln (INR p) * INR (length (filter (fun k => Nat.leb (Nat.pow p k) N) (seq 1 (S N)))).
Proof.
  intros N p; unfold inner.
  change (Rlsum (map (gN N p) (seq 1 (S N)))) with (Rsum (gN N p) 1 (S N)).
  rewrite (Rsum_ext (gN N p)
             (fun k => ln (INR p) * (if Nat.leb (Nat.pow p k) N then 1%R else 0%R)) 1 (S N)).
  - rewrite <- Rsum_scale, Rsum_count; reflexivity.
  - intros k _; unfold gN; destruct (Nat.leb (Nat.pow p k) N); ring.
Qed.

Lemma inner_ge_lnp : forall N p, (2 <= p)%nat -> (p <= N)%nat -> ln (INR p) <= inner N p.
Proof.
  intros N p Hp HpN; rewrite inner_count.
  assert (Hin : In 1%nat (filter (fun k => Nat.leb (Nat.pow p k) N) (seq 1 (S N)))).
  { apply filter_In; split;
      [ apply in_seq; lia | apply Nat.leb_le; rewrite Nat.pow_1_r; exact HpN ]. }
  assert (HK1 : (1 <= length (filter (fun k => Nat.leb (Nat.pow p k) N) (seq 1 (S N))))%nat).
  { destruct (filter (fun k => Nat.leb (Nat.pow p k) N) (seq 1 (S N))) as [|x xs] eqn:E;
      [ simpl in Hin; contradiction | simpl; lia ]. }
  assert (0 <= ln (INR p)) by (apply ln_INR_nonneg; lia).
  assert (1 <= INR (length (filter (fun k => Nat.leb (Nat.pow p k) N) (seq 1 (S N)))))
    by (apply (le_INR 1); exact HK1).
  nra.
Qed.

(* for p > sqrt N (p^2 > N), only the k=1 term survives, so inner N p = ln p *)
Lemma inner_eq_lnp_large : forall N p,
  (2 <= p)%nat -> (p <= N)%nat -> (N < p * p)%nat -> inner N p = ln (INR p).
Proof.
  intros N p Hp HpN Hpp; rewrite inner_count.
  set (F := filter (fun k => Nat.leb (Nat.pow p k) N) (seq 1 (S N))).
  assert (Hincl : incl F [1%nat]).
  { intros k Hk; unfold F in Hk; apply filter_In in Hk; destruct Hk as [Hseq Hb].
    apply in_seq in Hseq; apply Nat.leb_le in Hb.
    destruct (Nat.eq_dec k 1) as [->|Hk1]; [ left; reflexivity | exfalso ].
    assert (p * p <= Nat.pow p k)%nat.
    { apply Nat.le_trans with (Nat.pow p 2); [ simpl; nia | apply Nat.pow_le_mono_r; lia ]. }
    lia. }
  assert (Hin1 : In 1%nat F).
  { unfold F; apply filter_In; split;
      [ apply in_seq; lia | apply Nat.leb_le; rewrite Nat.pow_1_r; exact HpN ]. }
  assert (HND : NoDup F) by (unfold F; apply NoDup_filter, seq_NoDup).
  assert (Hlen1 : (length F <= 1)%nat)
    by (pose proof (NoDup_incl_length HND Hincl) as HH; simpl in HH; exact HH).
  assert (Hlenge : (1 <= length F)%nat)
    by (destruct F as [|x xs]; [ simpl in Hin1; contradiction | simpl; lia ]).
  assert (Hlen : length F = 1%nat) by lia.
  rewrite Hlen, INR_1, Rmult_1_r; reflexivity.
Qed.

Lemma psi_le_sum_inner : forall N, (2 <= N)%nat -> psi N <= Rlsum (map (inner N) (primes N)).
Proof.
  intros N HN.
  set (h := fun pk : nat * nat => gN N (fst pk) (snd pk)).
  set (phi := fun n : nat => (spf n, expo n)).
  assert (Hpsi : psi N = Rlsum (map h (map phi (la N)))).
  { rewrite psi_Rsum; unfold Rsum.
    change (fold_right Rplus 0 (map Lam (seq 1 N))) with (Rlsum (map Lam (seq 1 N))).
    rewrite (Rlsum_map_filter_zero nat Lam is_pp' (seq 1 N))
      by (intros n Hn Hf; apply Lam_zero_off; [ apply in_seq in Hn; lia | exact Hf ]).
    change (filter is_pp' (seq 1 N)) with (la N).
    rewrite map_map.
    apply f_equal, map_ext_in; intros n Hn; apply Lam_eq_g; exact Hn. }
  rewrite Hpsi.
  apply Rle_trans with (Rlsum (map h (list_prod (primes N) (seq 1 (S N))))).
  - apply (incl_lsum_le _ pnat_eq_dec h).
    + apply NoDup_map_inj; [ | apply NoDup_filter, seq_NoDup ].
      intros m n Hm Hn Heq; unfold phi in Heq; injection Heq as Hs He.
      destruct (la_props N m Hm) as [Hm2 [_ Hpm]].
      destruct (la_props N n Hn) as [Hn2 [_ Hpn]].
      rewrite <- (expo_correct m Hm2 Hpm), <- (expo_correct n Hn2 Hpn), Hs, He; reflexivity.
    + intros pk Hpk; apply in_map_iff in Hpk; destruct Hpk as [n [Hpe Hn]].
      destruct (la_props N n Hn) as [Hn2 [HnN Hpow]].
      subst pk; unfold phi; apply in_prod.
      * unfold primes; apply filter_In; split;
          [ apply in_seq; pose proof (spf_ge2 n Hn2); pose proof (spf_le n Hn2); lia | ].
        apply primeb_true_iff; apply spf_nprime; exact Hn2.
      * apply in_seq; pose proof (expo_ge1 n Hn2); pose proof (expo_le n); lia.
    + intros pk Hpk; destruct pk as [pp kk]; apply in_prod_iff in Hpk; destruct Hpk as [Hfst _].
      unfold h, gN; cbn [fst snd]; destruct (Nat.leb (Nat.pow pp kk) N); [ | apply Rle_refl ].
      apply ln_INR_nonneg; unfold primes in Hfst; apply filter_In in Hfst.
      destruct Hfst as [Hs _]; apply in_seq in Hs; lia.
  - assert (HF : Rlsum (map h (list_prod (primes N) (seq 1 (S N))))
                 = Rlsum (map (inner N) (primes N)))
      by (unfold h, Rlsum, inner; apply (Fubini_list_prod (gN N) (primes N) (seq 1 (S N)))).
    rewrite HF; apply Rle_refl.
Qed.

Lemma theta_eq_sum_lnp : forall N,
  theta N = Rlsum (map (fun p => ln (INR p)) (primes N)).
Proof.
  intro N; unfold theta, Rsum.
  change (fold_right Rplus 0 (map tterm (seq 1 N))) with (Rlsum (map tterm (seq 1 N))).
  rewrite (Rlsum_map_filter_zero nat tterm primeb (seq 1 N))
    by (intros n Hn Hf; unfold tterm; rewrite Hf; reflexivity).
  change (filter primeb (seq 1 N)) with (primes N).
  f_equal; apply map_ext_in; intros p Hp; unfold tterm.
  unfold primes in Hp; apply filter_In in Hp; destruct Hp as [_ Hpb]; rewrite Hpb; reflexivity.
Qed.

Theorem psi_minus_theta_bound : forall N, (2 <= N)%nat ->
  0 <= psi N - theta N <= sqrt (INR N) * ln (INR N).
Proof.
  intros N HN; split; [ pose proof (theta_le_psi N); lra | ].
  pose proof (psi_le_sum_inner N HN) as Hpsi.
  rewrite (theta_eq_sum_lnp N).
  apply Rle_trans with
    (Rlsum (map (inner N) (primes N)) - Rlsum (map (fun p => ln (INR p)) (primes N)));
    [ lra | ].
  rewrite <- Rlsum_map_minus.
  assert (HlnN : 0 <= ln (INR N)) by (apply lpos; lia).
  apply Rle_trans with
    (Rlsum (map (fun p => if Nat.leb p (Nat.sqrt N) then ln (INR N) else 0) (primes N))).
  - apply Rlsum_map_le; intros p Hp.
    unfold primes in Hp; apply filter_In in Hp; destruct Hp as [Hseq Hpb].
    apply in_seq in Hseq; apply primeb_nprime in Hpb; assert (Hp2 : (2 <= p)%nat) by (destruct Hpb; lia).
    assert (Hlp : 0 <= ln (INR p)) by (apply ln_INR_nonneg; lia).
    destruct (Nat.leb p (Nat.sqrt N)) eqn:E.
    + change (if true then ln (INR N) else 0) with (ln (INR N)).
      pose proof (inner_le N p Hp2 HN); pose proof (inner_ge_lnp N p Hp2 ltac:(lia)); lra.
    + change (if false then ln (INR N) else 0) with (0%R).
      apply Nat.leb_gt in E.
      assert (Hpp : (N < p * p)%nat).
      { pose proof (Nat.sqrt_spec N ltac:(lia)) as [_ Hhi].
        assert (S (Nat.sqrt N) <= p)%nat by lia.
        assert (S (Nat.sqrt N) * S (Nat.sqrt N) <= p * p)%nat
          by (apply Nat.mul_le_mono; assumption).
        lia. }
      rewrite (inner_eq_lnp_large N p Hp2 ltac:(lia) Hpp); lra.
  - (* Sum of indicators = ln N * #{primes p <= sqrt N} <= ln N * sqrt N *)
    rewrite (Rlsum_map_filter_zero nat _ (fun p => Nat.leb p (Nat.sqrt N)) (primes N))
      by (intros p _ Hf; rewrite Hf; reflexivity).
    rewrite (map_ext_in (fun p => if Nat.leb p (Nat.sqrt N) then ln (INR N) else 0)
               (fun _ => ln (INR N)) (filter (fun p => Nat.leb p (Nat.sqrt N)) (primes N))).
    2:{ intros p Hp; apply filter_In in Hp; destruct Hp as [_ Hle]; rewrite Hle; reflexivity. }
    rewrite Rlsum_map_const.
    assert (Hlen : (length (filter (fun p => Nat.leb p (Nat.sqrt N)) (primes N))
                    <= Nat.sqrt N)%nat).
    { apply Nat.le_trans with (length (seq 1 (Nat.sqrt N))).
      - apply NoDup_incl_length.
        + apply NoDup_filter; unfold primes; apply NoDup_filter, seq_NoDup.
        + intros p Hp; apply filter_In in Hp; destruct Hp as [Hpr Hle]; apply Nat.leb_le in Hle.
          unfold primes in Hpr; apply filter_In in Hpr; destruct Hpr as [Hseq _]; apply in_seq in Hseq.
          apply in_seq; lia.
      - rewrite length_seq; apply Nat.le_refl. }
    apply Rle_trans with (ln (INR N) * INR (Nat.sqrt N)).
    + apply Rmult_le_compat_l; [ exact HlnN | apply le_INR; exact Hlen ].
    + rewrite (Rmult_comm (sqrt (INR N)) (ln (INR N)));
        apply Rmult_le_compat_l; [ exact HlnN | apply INR_sqrt_le ].
Qed.

Print Assumptions psi_minus_theta_bound.

(* ================================================================= *)
(*  END PsiThetaTail.v  —  0 <= psi N - theta N <= sqrt N * ln N.       *)
(* ================================================================= *)
