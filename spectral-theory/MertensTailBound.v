(* ================================================================= *)
(*  MertensTailBound.v                                                *)
(*                                                                    *)
(*  Closes HigherPPTailBounded (MertensPrime.v): the weighted         *)
(*  higher-prime-power tail                                           *)
(*     ppTail N = sum_{p^k<=N, k>=2} (ln p)/p^k                        *)
(*  is bounded by 8, uniformly in N.  Hence Mertens' first theorem    *)
(*  for primes becomes UNCONDITIONAL.                                 *)
(*                                                                    *)
(*  Method mirrors PsiThetaTail.psi_le_sum_inner (weighted, k>=2):    *)
(*   1. ppTail N = sum over proper prime powers d of (Lam d)/d;       *)
(*   2. map d -> (spf d, expo d), inject into primes(N) x [2..];      *)
(*   3. Fubini -> sum_p innerW N p;                                   *)
(*   4. innerW N p <= (ln p)/(p(p-1))      (geometric, k>=2);         *)
(*   5. sum_p (ln p)/(p(p-1)) <= sum_{m=2}^N (ln m)/(m(m-1)) <= 8.     *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia Arith List ZArith Znumtheory Bool.
Require Import ChebyshevBound Chebyshev VonMangoldtGlobal Ell2Primes
        PrimePowerReindex ChebyshevPrime MertensVonMangoldt
        MertensPrime MertensTailAnalytic.
Import ListNotations.
Open Scope R_scope.

Definition gW (N p k : nat) : R :=
  if Nat.leb (p ^ k) N then ln (INR p) / INR (p ^ k) else 0.
Definition innerW (N p : nat) : R := Rlsum (map (gW N p) (seq 2 (S N))).
Definition is_ppp (d : nat) : bool := andb (is_pp' d) (negb (primeb d)).
Definition lppp (N : nat) : list nat := filter is_ppp (seq 1 N).
Definition ph (d : nat) : nat * nat := (spf d, expo d).
Definition hW (N : nat) (pk : nat * nat) : R := gW N (fst pk) (snd pk).

(* ----------------------------------------------------------------- *)
(*  list-sum helpers                                                 *)
(* ----------------------------------------------------------------- *)

Lemma Rlsum_app : forall l1 l2, Rlsum (l1 ++ l2) = Rlsum l1 + Rlsum l2.
Proof.
  induction l1 as [|x l1 IH]; intro l2.
  - cbn [app]; replace (Rlsum (@nil R)) with 0 by reflexivity; ring.
  - cbn [app]; rewrite !Rlsum_cons, IH; ring.
Qed.

Lemma Rlsum_map_scal : forall c (f : nat -> R) l,
  Rlsum (map (fun k => c * f k) l) = c * Rlsum (map f l).
Proof.
  intros c f l; induction l as [|x l IH].
  - cbn [map]; replace (Rlsum (@nil R)) with 0 by reflexivity; ring.
  - cbn [map]; rewrite !Rlsum_cons, IH; ring.
Qed.

(* ----------------------------------------------------------------- *)
(*  geometric Rlsum bound                                            *)
(* ----------------------------------------------------------------- *)

Lemma geom_seq_eq : forall x n,
  Rlsum (map (fun k => x ^ k) (seq 2 n)) = sum_f_R0 (fun k => x ^ k) (S n) - 1 - x.
Proof.
  intros x n; induction n as [|n IH].
  - cbn [seq map sum_f_R0]; replace (Rlsum (@nil R)) with 0 by reflexivity; ring.
  - rewrite seq_S, map_app, Rlsum_app, IH. cbn [map].
    rewrite Rlsum_cons. replace (Rlsum (@nil R)) with 0 by reflexivity.
    change (sum_f_R0 (fun k => x ^ k) (S (S n)))
      with (sum_f_R0 (fun k => x ^ k) (S n) + x ^ (S (S n))).
    replace (2 + n)%nat with (S (S n)) by lia. ring.
Qed.

Lemma geom_seq_bound : forall x n, 0 <= x -> x < 1 ->
  Rlsum (map (fun k => x ^ k) (seq 2 n)) <= x ^ 2 / (1 - x).
Proof. intros x n Hx0 Hx1. rewrite geom_seq_eq. apply geom_tail_bound; assumption. Qed.

(* ----------------------------------------------------------------- *)
(*  Step 4: innerW N p <= (ln p)/(p(p-1))                            *)
(* ----------------------------------------------------------------- *)

Lemma innerW_le : forall N p, (2 <= p)%nat ->
  innerW N p <= ln (INR p) / (INR p * (INR p - 1)).
Proof.
  intros N p Hp. unfold innerW.
  assert (Hp1 : 1 < INR p) by (apply (lt_INR 1); lia).
  assert (Hlp : 0 <= ln (INR p)) by (rewrite <- ln_1; apply Rlt_le, ln_increasing; lra).
  apply Rle_trans with (Rlsum (map (fun k => ln (INR p) * (/ INR p) ^ k) (seq 2 (S N)))).
  - apply Rlsum_map_le. intros k Hk.
    assert (HINR : INR (p ^ k) = INR p ^ k) by (rewrite pow_INR; reflexivity).
    unfold gW. destruct (Nat.leb (p ^ k) N) eqn:E.
    + rewrite HINR, pow_inv. lra.
    + apply Rmult_le_pos; [ exact Hlp | apply pow_le; left; apply Rinv_0_lt_compat; lra ].
  - rewrite Rlsum_map_scal.
    apply Rle_trans with (ln (INR p) * ((/ INR p) ^ 2 / (1 - / INR p))).
    + apply Rmult_le_compat_l; [ exact Hlp | ].
      apply geom_seq_bound; [ left; apply Rinv_0_lt_compat; lra | ].
      rewrite <- Rinv_1. apply Rinv_lt_contravar; lra.
    + apply Req_le. field. split; lra.
Qed.

(* ----------------------------------------------------------------- *)
(*  proper-prime-power list facts and the summand rewrite            *)
(* ----------------------------------------------------------------- *)

Lemma lppp_props : forall N d, In d (lppp N) ->
  (2 <= d)%nat /\ (d <= N)%nat /\ is_pow d (spf d) d = true /\ primeb d = false.
Proof.
  intros N d Hd; unfold lppp in Hd; apply filter_In in Hd; destruct Hd as [Hseq Hppp].
  apply in_seq in Hseq; unfold is_ppp in Hppp; apply andb_true_iff in Hppp.
  destruct Hppp as [Hpp Hnp]; unfold is_pp' in Hpp; apply andb_true_iff in Hpp.
  destruct Hpp as [H2 Hpow]; apply Nat.leb_le in H2; apply negb_true_iff in Hnp.
  repeat split; try lia; assumption.
Qed.

(* a prime is a prime power: closes the primeb/is_pp' relation *)
Lemma prime_is_pp' : forall d, primeb d = true -> is_pp' d = true.
Proof.
  intros d Hpb. pose proof (primeb_nprime d Hpb) as Hnp.
  assert (Hd2 : (2 <= d)%nat) by (destruct Hnp; lia).
  assert (Hspf : spf d = d).
  { pose proof (spf_prime_pow d 1 Hnp ltac:(lia)) as Hs. rewrite Nat.pow_1_r in Hs. exact Hs. }
  unfold is_pp'. apply andb_true_iff; split; [ apply Nat.leb_le; exact Hd2 | ].
  rewrite Hspf. replace (is_pow d d d) with (is_pow d d (d ^ 1)) by (rewrite Nat.pow_1_r; reflexivity).
  apply is_pow_pow_true; lia.
Qed.

Lemma wterm_eq_gW : forall N d, In d (lppp N) ->
  (Lam d - tterm d) / INR d = hW N (ph d).
Proof.
  intros N d Hd. destruct (lppp_props N d Hd) as [Hd2 [HdN [Hpow Hnp]]].
  assert (Hpe : ((spf d) ^ (expo d))%nat = d) by (apply expo_correct; [ lia | exact Hpow ]).
  assert (HLam : Lam d = ln (INR (spf d))) by (unfold Lam; rewrite Hpow; reflexivity).
  assert (Htt : tterm d = 0) by (unfold tterm; rewrite Hnp; reflexivity).
  unfold hW, ph; cbn [fst snd]. unfold gW. rewrite Hpe.
  replace (Nat.leb d N) with true by (symmetry; apply Nat.leb_le; exact HdN).
  rewrite HLam, Htt. field. apply not_0_INR; lia.
Qed.

Lemma wterm_zero_off : forall N d, In d (seq 1 N) -> is_ppp d = false ->
  (Lam d - tterm d) / INR d = 0.
Proof.
  intros N d Hin Hf. apply in_seq in Hin.
  assert (HLt : Lam d = tterm d).
  { unfold is_ppp in Hf; apply andb_false_iff in Hf. destruct Hf as [Hpp | Hnp].
    - assert (Hnpb : primeb d = false).
      { destruct (primeb d) eqn:E; [ | reflexivity ]. rewrite (prime_is_pp' d E) in Hpp; discriminate. }
      assert (HL0 : Lam d = 0) by (apply Lam_zero_off; [ lia | exact Hpp ]).
      rewrite HL0; unfold tterm; rewrite Hnpb; reflexivity.
    - apply negb_false_iff in Hnp. pose proof (primeb_nprime d Hnp) as Hnpr.
      rewrite (Lam_prime d Hnpr); unfold tterm; rewrite Hnp; reflexivity. }
  rewrite HLt. unfold Rminus, Rdiv. rewrite Rplus_opp_r, Rmult_0_l; reflexivity.
Qed.

(* ----------------------------------------------------------------- *)
(*  Main theorem                                                     *)
(* ----------------------------------------------------------------- *)

Theorem HigherPPTailBounded_proof : HigherPPTailBounded.
Proof.
  exists 8. intros N HN.
  unfold ppTail, msum, mprime. rewrite Rsum_minus.
  change (Rsum (fun i => Lam i / INR i - tterm i / INR i) 1 N)
    with (Rlsum (map (fun i => Lam i / INR i - tterm i / INR i) (seq 1 N))).
  rewrite (map_ext_in (fun i => Lam i / INR i - tterm i / INR i)
                      (fun i => (Lam i - tterm i) / INR i) (seq 1 N))
    by (intros i _; unfold Rdiv; ring).
  rewrite (Rlsum_map_filter_zero nat (fun i => (Lam i - tterm i) / INR i) is_ppp (seq 1 N))
    by (intros d Hd Hf; apply (wterm_zero_off N); assumption).
  change (filter is_ppp (seq 1 N)) with (lppp N).
  rewrite (map_ext_in (fun i => (Lam i - tterm i) / INR i)
                      (fun d => hW N (ph d)) (lppp N))
    by (intros d Hd; apply wterm_eq_gW; exact Hd).
  replace (map (fun d => hW N (ph d)) (lppp N))
    with (map (hW N) (map ph (lppp N)))
    by (rewrite map_map; reflexivity).
  apply Rle_trans with (Rlsum (map (hW N) (list_prod (primes N) (seq 2 (S N))))).
  - apply (incl_lsum_le _ pnat_eq_dec (hW N)).
    + apply NoDup_map_inj; [ | apply NoDup_filter, seq_NoDup ].
      intros m n Hm Hn Heq; unfold ph in Heq; injection Heq as Hs He.
      destruct (lppp_props N m Hm) as [Hm2 [_ [Hpm _]]].
      destruct (lppp_props N n Hn) as [Hn2 [_ [Hpn _]]].
      rewrite <- (expo_correct m ltac:(lia) Hpm), <- (expo_correct n ltac:(lia) Hpn), Hs, He; reflexivity.
    + intros pk Hpk; apply in_map_iff in Hpk; destruct Hpk as [d [Hpe Hd]].
      destruct (lppp_props N d Hd) as [Hd2 [HdN [Hpow Hnp]]].
      subst pk; unfold ph; apply in_prod.
      * unfold primes; apply filter_In; split;
          [ apply in_seq; pose proof (spf_ge2 d ltac:(lia)); pose proof (spf_le d ltac:(lia)); lia | ].
        apply primeb_true_iff, spf_nprime; lia.
      * apply in_seq. pose proof (expo_le d) as Hel.
        assert (He2 : (2 <= expo d)%nat).
        { destruct (Nat.le_gt_cases 2 (expo d)) as [Hge | Hlt]; [ exact Hge | exfalso ].
          pose proof (expo_ge1 d ltac:(lia)) as He1.
          assert (Hexo1 : expo d = 1%nat) by lia.
          assert (Hpe : ((spf d) ^ (expo d))%nat = d) by (apply expo_correct; [ lia | exact Hpow ]).
          rewrite Hexo1, Nat.pow_1_r in Hpe.
          assert (Hnpr : nprime d) by (rewrite <- Hpe; apply spf_nprime; lia).
          apply primeb_true_iff in Hnpr; congruence. }
        lia.
    + intros pk Hpk; destruct pk as [pp kk]; unfold hW; cbn [fst snd].
      unfold gW; destruct (Nat.leb (pp ^ kk) N) eqn:E; [ | apply Rle_refl ].
      apply in_prod_iff in Hpk; destruct Hpk as [Hfst _].
      unfold primes in Hfst; apply filter_In in Hfst; destruct Hfst as [Hs Hpb].
      apply in_seq in Hs; apply primeb_nprime in Hpb.
      assert (Hpp2 : (2 <= pp)%nat) by (destruct Hpb; lia).
      apply Rmult_le_pos; [ apply ln_INR_nonneg; lia | ].
      apply Rlt_le, Rinv_0_lt_compat, lt_0_INR.
      assert (pp ^ kk <> 0)%nat by (apply Nat.pow_nonzero; lia). lia.
  - assert (HF : Rlsum (map (hW N) (list_prod (primes N) (seq 2 (S N))))
                 = Rlsum (map (innerW N) (primes N))).
    { unfold hW, innerW, Rlsum. apply (Fubini_list_prod (gW N) (primes N) (seq 2 (S N))). }
    rewrite HF.
    apply Rle_trans with (Rlsum (map (fun p => ln (INR p) / (INR p * (INR p - 1))) (primes N))).
    + apply Rlsum_map_le. intros p Hp.
      unfold primes in Hp; apply filter_In in Hp; destruct Hp as [Hs Hpb].
      apply in_seq in Hs; apply primeb_nprime in Hpb.
      apply innerW_le; destruct Hpb; lia.
    + apply Rle_trans with
        (Rlsum (map (fun m => ln (INR m) / (INR m * (INR m - 1))) (seq 2 (N - 1)))).
      * apply (incl_lsum_le _ Nat.eq_dec).
        -- unfold primes; apply NoDup_filter, seq_NoDup.
        -- intros p Hp; unfold primes in Hp; apply filter_In in Hp; destruct Hp as [Hs Hpb].
           apply in_seq in Hs; apply primeb_nprime in Hpb.
           apply in_seq. destruct Hpb; lia.
        -- intros m Hm; apply in_seq in Hm.
           apply Rmult_le_pos; [ apply ln_INR_nonneg; lia | ].
           apply Rlt_le, Rinv_0_lt_compat, Rmult_lt_0_compat;
             assert (2 <= INR m) by (apply (le_INR 2); lia); lra.
      * apply series_sum_bound.
Qed.

(* ----------------------------------------------------------------- *)
(*  Consequence: Mertens' first theorem for primes, UNCONDITIONAL.    *)
(*    exists C, forall N>=1,  | sum_{p<=N}(ln p)/p  -  ln N | <= C.    *)
(* ----------------------------------------------------------------- *)

Theorem mertens_first_prime :
  exists C, forall N, (1 <= N)%nat -> Rabs (mprime N - ln (INR N)) <= C.
Proof. apply mertens_prime_of_tail, HigherPPTailBounded_proof. Qed.
