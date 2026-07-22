(* ================================================================= *)
(*  EulerProductZeta.v                                               *)
(*                                                                    *)
(*  THE EULER PRODUCT FORMULA FOR zeta(2):                            *)
(*                                                                    *)
(*     prod_{p prime, p <= B} (1 - p^-2)^-1  -->  zeta(2)   as B -> oo *)
(*                                (euler_product_zeta2)               *)
(*                                                                    *)
(*  This is the unconditional capstone: the finite Euler product over   *)
(*  all primes up to B converges to zeta(2) as B grows.  It closes the  *)
(*  arc primon gas -> reindex -> factorization bijection -> squeeze.    *)
(*                                                                    *)
(*  The two sides of the squeeze:                                     *)
(*    - UPPER (Hupper): EulerProductZetaBound.euler_factor_le_zeta      *)
(*        gives  prod_{p<=B} (1-p^-2)^-1 <= zeta(2)  (the coded numbers  *)
(*        are DISTINCT so RecipSquareBound dominates);                 *)
(*    - LOWER (Hlower, proved here): zpart N <= prod_{p<=N+1}...        *)
(*        because every m in {1..N+1} is {primes<=N+1}-smooth, so its   *)
(*        1/m^2 appears among the coded terms (factorization EXISTENCE, *)
(*        PrimeFactorizationExists.code_surj, with bounded exponents).  *)
(*  Since the upper bound is the constant zeta(2) and zpart N -> zeta(2),*)
(*  a squeeze finishes it.                                             *)
(*                                                                    *)
(*  This is the honest form of  zeta = prod_p (1-p^-s)^-1  at s = 2      *)
(*  (existence of the product as a limit equal to zeta(2); the value     *)
(*  pi^2/6 and general s remain out of scope).                         *)
(*                                                                    *)
(*  Uses the classical Reals axioms (quarantined).                    *)
(* ================================================================= *)

Require Import PrimonGas PrimeFactorizationN PrimeFactorizationExists
        EulerReindex RecipSquareBound EulerProductR EulerProductZetaBound ZetaConverge.
From Stdlib Require Import QArith Qreals Reals Lra ZArith Znumtheory List Lia Arith.
Import ListNotations.

(* ================================================================= *)
(*  1.  ENUMERATION OF PRIMES UP TO A BOUND                          *)
(* ================================================================= *)

Definition primes_upto (B : nat) : list Z :=
  filter (fun z => if prime_dec z then true else false)
         (map Z.of_nat (seq 0 (S B))).

Lemma primes_upto_prime : forall B q, In q (primes_upto B) -> prime q.
Proof.
  intros B q Hin; unfold primes_upto in Hin; apply filter_In in Hin.
  destruct Hin as [_ Hf]; destruct (prime_dec q) as [Hp | _]; [ exact Hp | discriminate ].
Qed.

Lemma primes_upto_Forall : forall B, Forall prime (primes_upto B).
Proof.
  intro B; apply Forall_forall; intros q Hq; apply (primes_upto_prime B q Hq).
Qed.

Lemma primes_upto_nodup : forall B, NoDup (primes_upto B).
Proof.
  intro B; unfold primes_upto; apply NoDup_filter.
  apply NoDup_map_inj; [ intros x y _ _ H; apply Nat2Z.inj; exact H | apply seq_NoDup ].
Qed.

Lemma primes_upto_complete : forall B q,
  prime q -> (q <= Z.of_nat B)%Z -> In q (primes_upto B).
Proof.
  intros B q Hp Hq; unfold primes_upto; apply filter_In.
  assert (Hq2 : (2 <= q)%Z) by (destruct Hp; lia).
  split.
  - apply in_map_iff; exists (Z.to_nat q); split.
    + apply Z2Nat.id; lia.
    + apply in_seq; split; [ lia | ].
      assert (Z.to_nat q <= B)%nat by (apply (proj2 (Nat2Z.inj_le (Z.to_nat q) B));
        rewrite Z2Nat.id by lia; exact Hq); lia.
  - destruct (prime_dec q) as [_ | Hnp]; [ reflexivity | contradiction ].
Qed.

(* ================================================================= *)
(*  2.  gstates CONTAINS EVERY BOUNDED OCCUPATION VECTOR             *)
(* ================================================================= *)

Lemma gstates_complete : forall xs K ks,
  length ks = length xs -> Forall (fun e => (e < K)%nat) ks -> In ks (gstates xs K).
Proof.
  induction xs as [|x xs IH]; intros K ks Hlen Hall.
  - destruct ks; [ left; reflexivity | simpl in Hlen; discriminate ].
  - destruct ks as [|k ks']; [ simpl in Hlen; discriminate | ].
    inversion Hall as [| ? ? Hk Hall']; subst.
    cbn [gstates]; apply in_flat_map; exists k; split.
    + apply in_seq; lia.
    + apply in_map_iff; exists ks'; split; [ reflexivity | ].
      apply IH; [ simpl in Hlen; lia | exact Hall' ].
Qed.

(* ================================================================= *)
(*  3.  EXPONENTS OF A CODED NUMBER ARE SMALL                        *)
(* ================================================================= *)

Lemma pow_le_base : forall (p : Z) e, (2 <= p)%Z -> (2 ^ Z.of_nat e <= p ^ Z.of_nat e)%Z.
Proof. intros p e Hp; apply Z.pow_le_mono_l; lia. Qed.

Lemma code_ge_1 : forall ps ks, Forall (fun p => (1 <= p)%Z) ps -> (1 <= code ps ks)%Z.
Proof.
  induction ps as [|p ps' IH]; intros ks Hpr.
  - destruct ks; simpl; lia.
  - inversion Hpr as [| ? ? Hp Hpr']; subst.
    destruct ks as [|k ks']; simpl; [ lia | ].
    pose proof (zpow_ge_1 p k Hp) as Hpk.
    pose proof (IH ks' Hpr') as Hc; nia.
Qed.

(* every entry e of ks satisfies 2^e <= code ps ks *)
Lemma entry_pow_le_code : forall ps ks,
  Forall (fun p => (2 <= p)%Z) ps -> length ps = length ks ->
  forall e, In e ks -> (2 ^ Z.of_nat e <= code ps ks)%Z.
Proof.
  induction ps as [|p ps' IH]; intros ks Hpr Hlen e Hin.
  - destruct ks; [ destruct Hin | simpl in Hlen; discriminate ].
  - destruct ks as [|k ks']; [ simpl in Hlen; discriminate | ].
    inversion Hpr as [| ? ? Hp Hpr']; subst.
    assert (Hcode' : (1 <= code ps' ks')%Z).
    { apply code_ge_1; apply Forall_impl with (P := fun p => (2 <= p)%Z);
        [ intros a Ha; lia | exact Hpr' ]. }
    pose proof (zpow_ge_1 p k ltac:(lia)) as Hpk1.
    cbn [code]; destruct Hin as [He | He].
    + subst e. pose proof (pow_le_base p k ltac:(lia)) as Hpb; nia.
    + pose proof (IH ks' Hpr' ltac:(simpl in Hlen; lia) e He) as Hle; nia.
Qed.

Lemma nat_lt_pow2 : forall e, (e < 2 ^ e)%nat.
Proof. induction e as [|e IH]; simpl; lia. Qed.

(* ================================================================= *)
(*  4.  SMALL NUMBERS ARE SMOOTH OVER primes_upto                    *)
(* ================================================================= *)

Lemma small_smooth : forall N m,
  (1 <= m)%nat -> (m <= S N)%nat ->
  forall q, prime q -> (q | Z.of_nat m)%Z -> In q (primes_upto (S N)).
Proof.
  intros N m Hm1 HmN q Hq Hdvd.
  apply primes_upto_complete; [ exact Hq | ].
  assert (q <= Z.of_nat m)%Z by (apply Z.divide_pos_le; [ lia | exact Hdvd ]).
  lia.
Qed.

(* ================================================================= *)
(*  5.  PARTIAL EULER PRODUCT <= EULER FACTOR (product of geoms)     *)
(* ================================================================= *)

Lemma sumf_nonneg : forall (f : nat -> R) N,
  (forall k, (0 <= f k)%R) -> (0 <= sum_f_R0 f N)%R.
Proof.
  intros f N Hf; induction N as [|N IH]; simpl; [ apply Hf | ].
  pose proof (Hf (S N)); lra.
Qed.

Lemma Zpartial_nonneg : forall xs, Forall (fun x => (0 <= x < 1)%R) xs ->
  forall K, (0 <= Zpartial xs K)%R.
Proof.
  induction xs as [|x xs IH]; intros Hall K; unfold Zpartial in *; simpl; [ lra | ].
  inversion Hall as [| ? ? Hx Hxs]; subst.
  apply Rmult_le_pos.
  - apply sumf_nonneg; intro k; apply pow_le; lra.
  - apply (IH Hxs K).
Qed.

Lemma Zpartial_le_Zfactor : forall xs, Forall (fun x => (0 <= x < 1)%R) xs ->
  forall K, (Zpartial xs K <= Zfactor xs)%R.
Proof.
  induction xs as [|x xs IH]; intros Hall K; unfold Zpartial, Zfactor in *; simpl; [ lra | ].
  inversion Hall as [| ? ? Hx Hxs]; subst.
  apply Rmult_le_compat.
  - apply sumf_nonneg; intro k; apply pow_le; lra.
  - apply (Zpartial_nonneg xs Hxs K).
  - rewrite tech3 by lra.
    assert (Hxp : (0 <= x ^ S K)%R) by (apply pow_le; lra).
    assert (Hinv : (0 <= / (1 - x))%R) by (apply Rlt_le, Rinv_0_lt_compat; lra).
    unfold Rdiv.
    apply Rle_trans with (1 * / (1 - x))%R;
      [ apply Rmult_le_compat_r; [ exact Hinv | lra ]
      | rewrite Rmult_1_l; apply Rle_refl ].
  - apply (IH Hxs K).
Qed.

(* ================================================================= *)
(*  6.  THE SQUEEZE (constant upper bound)                           *)
(* ================================================================= *)

Lemma squeeze_const_upper : forall (a u : nat -> R) L,
  Un_cv a L -> (forall N, (a N <= u N)%R) -> (forall N, (u N <= L)%R) -> Un_cv u L.
Proof.
  intros a u L Ha Hau HuL eps Heps.
  destruct (Ha eps Heps) as [M HM]; exists M; intros n Hn.
  specialize (HM n Hn); specialize (Hau n); specialize (HuL n).
  unfold R_dist in *; apply Rabs_def2 in HM; destruct HM as [_ H2].
  rewrite Rabs_left1 by lra; lra.
Qed.

(* ================================================================= *)
(*  7.  LOWER BOUND (Hlower): zpart N <= Euler product over p<=N+1    *)
(* ================================================================= *)

Lemma zpart_le_euler : forall N,
  (zpart N <= Zfactor (map (fun p => (/ (IZR p) ^ 2)%R) (primes_upto (S N))))%R.
Proof.
  intro N.
  set (ps := primes_upto (S N)).
  assert (Hpr : Forall prime ps) by apply primes_upto_Forall.
  assert (Hnd : NoDup ps) by apply primes_upto_nodup.
  assert (Hpr2 : Forall (fun p => (2 <= p)%Z) ps).
  { apply Forall_impl with (P := prime); [ intros p Hp; destruct Hp; lia | exact Hpr ]. }
  (* the coded-number list at truncation K = S N *)
  set (codes := map (fun ks => Z.to_nat (code ps ks)) (gstates (map fug ps) (S N))).
  (* every m in [1..S N] appears among codes *)
  assert (Hincl : incl (seq 1 (S N)) codes).
  { intros m Hm. apply in_seq in Hm; destruct Hm as [Hm1 HmN].
    (* m is {ps}-smooth *)
    assert (Hsm : forall q, prime q -> (q | Z.of_nat m)%Z -> In q ps).
    { intros q Hq Hdvd; apply (small_smooth N m); [ lia | lia | exact Hq | exact Hdvd ]. }
    destruct (code_surj ps Hpr Hnd (Z.of_nat m) ltac:(lia) Hsm) as [ks [Hlen Hcode]].
    (* ks has bounded exponents, so it is in gstates *)
    assert (Hb : Forall (fun e => (e < S N)%nat) ks).
    { apply Forall_forall; intros e He.
      pose proof (entry_pow_le_code ps ks Hpr2 Hlen e He) as Hpow.
      rewrite Hcode in Hpow.
      assert (Hpow2 : (2 ^ e <= m)%nat).
      { apply (proj2 (Nat2Z.inj_le (2 ^ e) m)); rewrite Nat2Z.inj_pow; exact Hpow. }
      pose proof (nat_lt_pow2 e); lia. }
    unfold codes; apply in_map_iff; exists ks; split.
    - rewrite Hcode, Nat2Z.id; reflexivity.
    - apply gstates_complete; [ rewrite length_map; symmetry; exact Hlen | exact Hb ]. }
  (* sum over [1..S N] <= sum over codes = Zpartial ps N *)
  assert (Hsum : (Rlsum (map rr (seq 1 (S N))) <= Rlsum (map rr codes))%R).
  { apply (incl_sum_le rr rr_nonneg codes (seq 1 (S N))); [ apply seq_NoDup | exact Hincl ]. }
  rewrite seqsum_zpart in Hsum.
  (* Rlsum (map rr codes) = Zpartial ps N *)
  assert (Hre : Rlsum (map rr codes) = Zpartial (map (fun p => (/ (IZR p) ^ 2)%R) ps) N).
  { unfold codes; symmetry; apply euler_partial_reindex_R; assumption. }
  rewrite Hre in Hsum.
  (* Zpartial <= Zfactor *)
  eapply Rle_trans; [ exact Hsum | ].
  apply Zpartial_le_Zfactor.
  apply Forall_forall; intros y Hy; apply in_map_iff in Hy.
  destruct Hy as [p [Hpy Hp]]; subst y.
  pose proof (proj1 (Forall_forall prime ps) Hpr p Hp) as Hpp.
  assert (H2 : (2 <= IZR p)%R) by (apply IZR_le; destruct Hpp; lia).
  split.
  - apply Rlt_le, Rinv_0_lt_compat, pow_lt; lra.
  - apply Rle_lt_trans with (/ 4)%R; [ apply Rinv_le_contravar; [ lra | nra ] | lra ].
Qed.

(* ================================================================= *)
(*  8.  THE EULER PRODUCT FORMULA FOR zeta(2)                        *)
(* ================================================================= *)

Theorem euler_product_zeta2 :
  Un_cv (fun N => Zfactor (map (fun p => (/ (IZR p) ^ 2)%R) (primes_upto (S N))))
        (proj1_sig zeta2_converges).
Proof.
  apply (squeeze_const_upper zpart _ (proj1_sig zeta2_converges)).
  - exact (proj2_sig zeta2_converges).
  - exact zpart_le_euler.
  - intro N; apply euler_factor_le_zeta; [ apply primes_upto_Forall | apply primes_upto_nodup ].
Qed.

Print Assumptions euler_product_zeta2.

(* ================================================================= *)
(*  END EulerProductZeta.v                                           *)
(*  prod_{p prime, p <= B} (1 - p^-2)^-1 -> zeta(2) as B -> oo: the      *)
(*  Euler product formula for zeta(2), unconditional, squeezed between   *)
(*  the zeta partial sums (Hlower, via factorization existence) and       *)
(*  zeta(2) (Hupper).  Uses the classical Reals axioms (quarantined).   *)
(* ================================================================= *)
