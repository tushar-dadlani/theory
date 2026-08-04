(* ================================================================= *)
(*  PrimePowerReindex.v  —  the crux of Chebyshev's theorem.           *)
(*                                                                    *)
(*  psi N <= pi_count N * ln N  for N >= 2, where pi_count counts       *)
(*  primes <= N.  Proved by regrouping psi = sum_{n<=N} Lam n (a sum    *)
(*  over PRIME POWERS) by (prime p, exponent k): every prime power      *)
(*  n = p^k contributes ln p, and for a fixed prime p the powers        *)
(*  p^1,...,p^Kp <= N contribute Kp*ln p = ln(p^Kp) <= ln N, so the     *)
(*  total is <= (#primes<=N)*ln N.  The reindexing uses a computable     *)
(*  p-adic exponent `expo` and an injection-domination lemma.           *)
(*  Axiom-clean (classical Reals only, inherited from psi).            *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia ZArith Znumtheory Arith List Bool.
Require Import VonMangoldtGlobal Ell2Primes Chebyshev ChebyshevBound
        EuclidPrimes DirichletAP.
Import ListNotations.
Open Scope R_scope.

(* ================================================================= *)
(*  0.  nat primality  <->  Z primality                               *)
(* ================================================================= *)

Lemma nprime_iff_Zprime : forall p, nprime p <-> prime (Z.of_nat p).
Proof.
  intro p; split.
  - intros [Hp2 Hdiv]; apply prime_alt; split.
    + lia.
    + intros n [Hn1 Hnp] Hn.
      assert (Hn0 : (0 < n)%Z) by lia.
      set (m := Z.to_nat n).
      assert (Hmn : n = Z.of_nat m) by (unfold m; rewrite Z2Nat.id; lia).
      rewrite Hmn in Hn, Hn1, Hnp.
      apply Zdiv_nat in Hn.
      destruct (Hdiv m Hn) as [-> | ->]; lia.
  - intros Hp; split.
    + pose proof (prime_ge_2 _ Hp); lia.
    + intros d Hd.
      apply dvd_nat_Z in Hd.
      destruct (prime_divisors _ Hp _ Hd) as [H | [H | [H | H]]].
      * lia.
      * left; lia.
      * right; lia.
      * assert (0 <= Z.of_nat d)%Z by lia; assert (0 < Z.of_nat p)%Z
          by (pose proof (prime_ge_2 _ Hp); lia); lia.
Qed.

Definition primeb (n : nat) : bool :=
  if prime_dec (Z.of_nat n) then true else false.

Lemma primeb_true_iff : forall n, primeb n = true <-> nprime n.
Proof.
  intro n; unfold primeb; destruct (prime_dec (Z.of_nat n)) as [Hp | Hnp]; split;
    try discriminate; try reflexivity.
  - intros _; apply nprime_iff_Zprime; exact Hp.
  - intro Hn; apply nprime_iff_Zprime in Hn; contradiction.
Qed.

Lemma primeb_nprime : forall n, primeb n = true -> nprime n.
Proof. intros n H; apply primeb_true_iff; exact H. Qed.

(* ================================================================= *)
(*  1.  prime counting                                                *)
(* ================================================================= *)

Definition pi_count (N : nat) : R :=
  Rsum (fun n => if primeb n then 1%R else 0%R) 1 N.

Definition pin (N : nat) : nat := length (filter primeb (seq 1 N)).

(* ================================================================= *)
(*  2.  list-sum helpers                                              *)
(* ================================================================= *)

Definition Rlsum (l : list R) : R := fold_right Rplus 0%R l.

Lemma Rsum_one : forall a n, Rsum (fun _ => 1%R) a n = INR n.
Proof.
  intros a n; revert a; induction n as [|n IH]; intro a.
  - reflexivity.
  - replace (Rsum (fun _ => 1%R) a (S n)) with (1%R + Rsum (fun _ => 1%R) (S a) n)
      by (unfold Rsum; reflexivity).
    rewrite IH, S_INR; ring.
Qed.

Lemma Rsum_count : forall (b : nat -> bool) a n,
  Rsum (fun i => if b i then 1%R else 0%R) a n = INR (length (filter b (seq a n))).
Proof.
  intros b a n; revert a; induction n as [|n IH]; intro a.
  - reflexivity.
  - replace (Rsum (fun i => if b i then 1%R else 0%R) a (S n))
      with ((if b a then 1%R else 0%R)
            + Rsum (fun i => if b i then 1%R else 0%R) (S a) n)
      by (unfold Rsum; reflexivity).
    replace (filter b (seq a (S n)))
      with (if b a then a :: filter b (seq (S a) n) else filter b (seq (S a) n))
      by reflexivity.
    rewrite IH; destruct (b a); [ simpl length; rewrite S_INR; ring | ring ].
Qed.

Lemma pi_count_pin : forall N, pi_count N = INR (pin N).
Proof. intro N; unfold pi_count, pin; apply Rsum_count. Qed.

(* ================================================================= *)
(*  3.  a computable p-adic exponent                                  *)
(* ================================================================= *)

Local Open Scope nat_scope.

Fixpoint vp (fuel p n : nat) : nat :=
  match fuel with
  | O => O
  | S f => if Nat.eqb n 1 then O
           else if Nat.eqb (n mod p) 0 then S (vp f p (n / p)) else O
  end.

Definition expo (n : nat) : nat := vp n (spf n) n.

Lemma vp_le : forall fuel p n, vp fuel p n <= fuel.
Proof.
  induction fuel as [|f IH]; intros p n; cbn [vp]; [ lia | ].
  destruct (Nat.eqb n 1); [ lia | ].
  destruct (Nat.eqb (n mod p) 0); [ specialize (IH p (n / p)); lia | lia ].
Qed.

Lemma expo_le : forall n, expo n <= n.
Proof. intro n; unfold expo; apply vp_le. Qed.

Lemma vp_correct : forall fuel p n,
  2 <= p -> is_pow fuel p n = true -> n = p ^ (vp fuel p n).
Proof.
  induction fuel as [|f IH]; intros p n Hp Hpow.
  - cbn [is_pow] in Hpow; discriminate.
  - cbn [is_pow] in Hpow; cbn [vp].
    destruct (Nat.eqb n 1) eqn:E1.
    + apply Nat.eqb_eq in E1; subst n; reflexivity.
    + destruct (Nat.eqb (n mod p) 0) eqn:E0.
      * apply Nat.eqb_eq in E0.
        assert (Hne : n = p * (n / p)) by (apply (Nat.div_exact n p ltac:(lia)); exact E0).
        specialize (IH p (n / p) Hp Hpow).
        rewrite Nat.pow_succ_r', <- IH; exact Hne.
      * discriminate.
Qed.

Lemma expo_correct : forall n, 2 <= n -> is_pow n (spf n) n = true ->
  (spf n) ^ (expo n) = n.
Proof.
  intros n Hn Hpow; unfold expo; symmetry.
  apply vp_correct; [ apply spf_ge2; exact Hn | exact Hpow ].
Qed.

Lemma expo_ge1 : forall n, 2 <= n -> 1 <= expo n.
Proof.
  intros n Hn; unfold expo.
  assert (Hmod : n mod spf n = 0)
    by (apply Nat.mod_divide; [ pose proof (spf_ge2 n Hn); lia | apply spf_divides; exact Hn ]).
  destruct n as [|n']; [ lia | ]; cbn [vp].
  replace (Nat.eqb (S n') 1) with false by (symmetry; apply Nat.eqb_neq; lia).
  rewrite Hmod; cbn [Nat.eqb]; lia.
Qed.

Lemma spf_le : forall n, 2 <= n -> spf n <= n.
Proof.
  intros n Hn; apply Nat.divide_pos_le; [ lia | apply spf_divides; exact Hn ].
Qed.

Local Close Scope nat_scope.

(* ================================================================= *)
(*  4.  generic list-sum machinery                                    *)
(* ================================================================= *)

Lemma Rlsum_cons : forall x l, Rlsum (x :: l) = x + Rlsum l.
Proof. intros; reflexivity. Qed.

Lemma Rlsum_map_le : forall (A : Type) (f g : A -> R) (l : list A),
  (forall x, In x l -> f x <= g x) -> Rlsum (map f l) <= Rlsum (map g l).
Proof.
  intros A f g l; induction l as [|a l IH]; intro H.
  - cbn; lra.
  - cbn [map]; rewrite !Rlsum_cons.
    apply Rplus_le_compat;
      [ apply H; left; reflexivity | apply IH; intros x Hx; apply H; right; exact Hx ].
Qed.

Lemma Rlsum_map_nonneg : forall (A : Type) (f : A -> R) (l : list A),
  (forall x, In x l -> 0 <= f x) -> 0 <= Rlsum (map f l).
Proof.
  intros A f l; induction l as [|a l IH]; intro H.
  - cbn; lra.
  - cbn [map]; rewrite Rlsum_cons.
    apply Rplus_le_le_0_compat;
      [ apply H; left; reflexivity | apply IH; intros x Hx; apply H; right; exact Hx ].
Qed.

Lemma NoDup_map_inj : forall (A B : Type) (f : A -> B) (l : list A),
  (forall x y, In x l -> In y l -> f x = f y -> x = y) -> NoDup l -> NoDup (map f l).
Proof.
  intros A B f l Hinj Hnd; induction Hnd as [| x l Hx Hnd IH]; cbn [map]; constructor.
  - intro Hin; apply in_map_iff in Hin; destruct Hin as [y [Hfy Hy]].
    assert (x = y) by (apply Hinj; [ left; reflexivity | right; exact Hy | symmetry; exact Hfy ]).
    subst y; contradiction.
  - apply IH; intros a b Ha Hb Hab; apply Hinj; [ right; exact Ha | right; exact Hb | exact Hab ].
Qed.

Lemma NoDup_remove_A : forall (A : Type) (eqd : forall x y : A, {x = y} + {x <> y})
  (r : A) (l : list A), NoDup l -> NoDup (remove eqd r l).
Proof.
  intros A eqd r l; induction l as [|a l IH]; intro Hnd; cbn [remove]; [ constructor | ].
  inversion Hnd as [| ? ? Hna Hnd']; subst.
  destruct (eqd r a) as [He | Hne]; [ apply IH; exact Hnd' | ].
  constructor.
  - intro Hin; apply in_remove in Hin; destruct Hin as [Hin _]; contradiction.
  - apply IH; exact Hnd'.
Qed.

Lemma sum_remove_A : forall (A : Type) (eqd : forall x y : A, {x = y} + {x <> y})
  (h : A -> R) (r : A) (l : list A), In r l -> NoDup l ->
  Rlsum (map h l) = h r + Rlsum (map h (remove eqd r l)).
Proof.
  intros A eqd h r l; induction l as [|a l IH]; intros Hin Hnd; [ destruct Hin | ].
  inversion Hnd as [| ? ? Hna Hnd']; subst.
  cbn [map remove]; rewrite Rlsum_cons.
  destruct (eqd r a) as [He | Hne].
  - subst a; rewrite (notin_remove eqd l r Hna); reflexivity.
  - destruct Hin as [Ha | Hin]; [ symmetry in Ha; contradiction | ].
    cbn [map]; rewrite Rlsum_cons, (IH Hin Hnd'); ring.
Qed.

Lemma incl_lsum_le : forall (A : Type) (eqd : forall x y : A, {x = y} + {x <> y})
  (h : A -> R) (l2 l1 : list A),
  NoDup l1 -> incl l1 l2 -> (forall y, In y l2 -> 0 <= h y) ->
  Rlsum (map h l1) <= Rlsum (map h l2).
Proof.
  intros A eqd h l2; induction l2 as [|r l2 IH]; intros l1 Hnd Hincl Hpos.
  - assert (l1 = []).
    { destruct l1 as [|a l0]; [ reflexivity | destruct (Hincl a (in_eq a l0)) ]. }
    subst; cbn [map Rlsum]; lra.
  - cbn [map]; rewrite Rlsum_cons.
    destruct (in_dec eqd r l1) as [Hin | Hnin].
    + rewrite (sum_remove_A A eqd h r l1 Hin Hnd).
      apply Rplus_le_compat_l.
      apply IH; [ apply NoDup_remove_A; exact Hnd | | intros y Hy; apply Hpos; right; exact Hy ].
      intros x Hx; apply in_remove in Hx; destruct Hx as [Hx1 Hx2].
      destruct (Hincl x Hx1) as [He | Hin']; [ subst; contradiction | exact Hin' ].
    + apply Rle_trans with (Rlsum (map h l2)).
      * apply IH; [ exact Hnd | | intros y Hy; apply Hpos; right; exact Hy ].
        intros x Hx; destruct (Hincl x Hx) as [He | Hin']; [ subst; contradiction | exact Hin' ].
      * pose proof (Hpos r (in_eq r l2)); lra.
Qed.

Lemma Rlsum_map_const : forall (A : Type) (c : R) (l : list A),
  Rlsum (map (fun _ => c) l) = c * INR (length l).
Proof.
  intros A c l; induction l as [|a l IH]; cbn [map length].
  - simpl; ring.
  - rewrite Rlsum_cons, IH, S_INR; ring.
Qed.

Lemma Rlsum_map_filter_zero : forall (A : Type) (f : A -> R) (b : A -> bool) (l : list A),
  (forall x, In x l -> b x = false -> f x = 0) ->
  Rlsum (map f l) = Rlsum (map f (filter b l)).
Proof.
  intros A f b l; induction l as [|a l IH]; intro H; [ reflexivity | ].
  cbn [filter]; destruct (b a) eqn:E.
  - cbn [map]; rewrite !Rlsum_cons, IH; [ reflexivity | ].
    intros x Hx Hf; apply H; [ right; exact Hx | exact Hf ].
  - cbn [map]; rewrite Rlsum_cons.
    rewrite (H a (in_eq a l) E), IH.
    + ring.
    + intros x Hx Hf; apply H; [ right; exact Hx | exact Hf ].
Qed.

(* ================================================================= *)
(*  5.  the prime-counting building blocks                            *)
(* ================================================================= *)

Definition primes (N : nat) : list nat := filter primeb (seq 1 N).
Definition is_pp' (n : nat) : bool := andb (Nat.leb 2 n) (is_pow n (spf n) n).
Definition la (N : nat) : list nat := filter is_pp' (seq 1 N).
Definition gN (N p k : nat) : R := if Nat.leb (Nat.pow p k) N then ln (INR p) else 0%R.
Definition inner (N p : nat) : R := Rlsum (map (gN N p) (seq 1 (S N))).

Lemma ln_INR_nonneg : forall p, (1 <= p)%nat -> 0 <= ln (INR p).
Proof.
  intros p Hp; rewrite <- ln_1; apply ln_le; [ lra | ].
  replace 1 with (INR 1) by (simpl; ring); apply le_INR; exact Hp.
Qed.

Lemma Lam_zero_off : forall n, (1 <= n)%nat -> is_pp' n = false -> Lam n = 0.
Proof.
  intros n Hn Hf; unfold is_pp' in Hf; apply andb_false_iff in Hf.
  destruct Hf as [H2 | Hpow].
  - apply Nat.leb_gt in H2; assert (n = 1)%nat by lia; subst; apply Lam_1.
  - unfold Lam; rewrite Hpow; reflexivity.
Qed.

Lemma la_props : forall N n, In n (la N) ->
  (2 <= n)%nat /\ (n <= N)%nat /\ is_pow n (spf n) n = true.
Proof.
  intros N n Hn; unfold la in Hn; apply filter_In in Hn; destruct Hn as [Hseq Hpp].
  apply in_seq in Hseq; unfold is_pp' in Hpp; apply andb_true_iff in Hpp.
  destruct Hpp as [H2 Hpow]; apply Nat.leb_le in H2; repeat split; try lia; exact Hpow.
Qed.

Lemma Lam_eq_g : forall N n, In n (la N) -> Lam n = gN N (spf n) (expo n).
Proof.
  intros N n Hn; destruct (la_props N n Hn) as [Hn2 [HnN Hpow]].
  assert (HLam : Lam n = ln (INR (spf n))) by (unfold Lam; rewrite Hpow; reflexivity).
  assert (Hpe : ((spf n) ^ (expo n))%nat = n) by (apply expo_correct; assumption).
  unfold gN; rewrite Hpe.
  replace (Nat.leb n N) with true by (symmetry; apply Nat.leb_le; exact HnN).
  exact HLam.
Qed.

Lemma list_max_in : forall l, l <> nil -> In (list_max l) l.
Proof.
  induction l as [|a l IH]; intro Hne; [ contradiction | clear Hne ].
  destruct l as [|b l'].
  - unfold list_max; cbn [fold_right]; rewrite Nat.max_0_r; left; reflexivity.
  - change (list_max (a :: b :: l')) with (Nat.max a (list_max (b :: l'))).
    destruct (Nat.max_dec a (list_max (b :: l'))) as [E | E]; rewrite E;
      [ left; reflexivity | right; apply IH; discriminate ].
Qed.

Lemma pow_count_le : forall p N, (2 <= p)%nat -> (1 <= N)%nat ->
  (Nat.pow p (length (filter (fun k => Nat.leb (Nat.pow p k) N) (seq 1 (S N)))) <= N)%nat.
Proof.
  intros p N Hp HN.
  set (L := filter (fun k => Nat.leb (Nat.pow p k) N) (seq 1 (S N))).
  set (K := length L).
  destruct (Nat.eq_dec K 0) as [HK0 | HKpos].
  - rewrite HK0; cbn [Nat.pow]; lia.
  - assert (HLne : L <> nil) by (intro He; apply HKpos; unfold K; rewrite He; reflexivity).
    set (km := list_max L).
    assert (Hin : In km L) by (apply list_max_in; exact HLne).
    assert (Hval : (Nat.pow p km <= N)%nat).
    { unfold L in Hin; apply filter_In in Hin; destruct Hin as [_ Hb]; apply Nat.leb_le in Hb; exact Hb. }
    assert (Hall : Forall (fun k => (k <= km)%nat) L)
      by (apply (proj1 (list_max_le L km)); unfold km; apply Nat.le_refl).
    assert (Hincl : incl L (seq 1 km)).
    { intros k Hk; apply in_seq.
      assert (Hk1 : In k (seq 1 (S N))) by (unfold L in Hk; apply filter_In in Hk; tauto).
      apply in_seq in Hk1; rewrite Forall_forall in Hall; specialize (Hall k Hk); lia. }
    assert (HKkm : (K <= km)%nat).
    { unfold K; rewrite <- (length_seq km 1);
        apply NoDup_incl_length; [ apply NoDup_filter, seq_NoDup | exact Hincl ]. }
    apply Nat.le_trans with (Nat.pow p km);
      [ apply Nat.pow_le_mono_r; [ lia | exact HKkm ] | exact Hval ].
Qed.

Lemma inner_le : forall N p, (2 <= p)%nat -> (2 <= N)%nat -> inner N p <= ln (INR N).
Proof.
  intros N p Hp HN; unfold inner.
  set (K := length (filter (fun k => Nat.leb (Nat.pow p k) N) (seq 1 (S N)))).
  assert (Heq : Rlsum (map (gN N p) (seq 1 (S N))) = ln (INR p) * INR K).
  { change (Rlsum (map (gN N p) (seq 1 (S N)))) with (Rsum (gN N p) 1 (S N)).
    rewrite (Rsum_ext (gN N p)
               (fun k => ln (INR p) * (if Nat.leb (Nat.pow p k) N then 1%R else 0%R)) 1 (S N)).
    - rewrite <- Rsum_scale, Rsum_count; reflexivity.
    - intros k _; unfold gN; destruct (Nat.leb (Nat.pow p k) N); ring. }
  rewrite Heq.
  assert (HpK : (Nat.pow p K <= N)%nat) by (unfold K; apply pow_count_le; lia).
  assert (HposK : (0 < Nat.pow p K)%nat)
    by (assert (Nat.pow p K <> 0)%nat by (apply Nat.pow_nonzero; lia); lia).
  rewrite Rmult_comm, <- ln_pow by (apply lt_0_INR; lia).
  rewrite <- pow_INR; apply ln_le; [ apply lt_0_INR; exact HposK | apply le_INR; exact HpK ].
Qed.

(* ================================================================= *)
(*  6.  the reindexing theorem                                        *)
(* ================================================================= *)

Definition pnat_eq_dec : forall x y : nat * nat, {x = y} + {x <> y}.
Proof. decide equality; apply Nat.eq_dec. Defined.

Theorem psi_le_picount_lnN : forall N, (2 <= N)%nat -> psi N <= pi_count N * ln (INR N).
Proof.
  intros N HN.
  set (h := fun pk : nat * nat => gN N (fst pk) (snd pk)).
  set (phi := fun n : nat => (spf n, expo n)).
  (* psi = sum of Lam over prime powers = sum of h over their (p,k) codes *)
  assert (Hpsi : psi N = Rlsum (map h (map phi (la N)))).
  { rewrite psi_Rsum; unfold Rsum.
    change (fold_right Rplus 0 (map Lam (seq 1 N))) with (Rlsum (map Lam (seq 1 N))).
    rewrite (Rlsum_map_filter_zero nat Lam is_pp' (seq 1 N))
      by (intros n Hn Hf; apply Lam_zero_off; [ apply in_seq in Hn; lia | exact Hf ]).
    change (filter is_pp' (seq 1 N)) with (la N).
    rewrite map_map.
    apply f_equal, map_ext_in; intros n Hn; apply Lam_eq_g; exact Hn. }
  rewrite Hpsi.
  (* dominate by the full pair-product, then Fubini + per-prime bound *)
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
                 = Rlsum (map (inner N) (primes N))).
    { unfold h, Rlsum, inner; apply (Fubini_list_prod (gN N) (primes N) (seq 1 (S N))). }
    rewrite HF.
    apply Rle_trans with (Rlsum (map (fun _ : nat => ln (INR N)) (primes N))).
    + apply Rlsum_map_le; intros p Hp; apply inner_le; [ | lia ].
      unfold primes in Hp; apply filter_In in Hp; destruct Hp as [Hseq Hpb].
      apply primeb_nprime in Hpb; destruct Hpb; lia.
    + rewrite Rlsum_map_const, pi_count_pin.
      unfold pin, primes; rewrite Rmult_comm; apply Rle_refl.
Qed.

Print Assumptions psi_le_picount_lnN.

(* ================================================================= *)
(*  END PrimePowerReindex.v                                           *)
(* ================================================================= *)
