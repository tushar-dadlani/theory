(* ================================================================= *)
(*  EulerProductZetaBound.v                                          *)
(*                                                                    *)
(*  THE ANALYTIC BRIDGE (part 2): the finite Euler product over any    *)
(*  distinct primes is <= zeta(2).                                    *)
(*                                                                    *)
(*  Transports EulerReindex.euler_reindex (a Q identity) through Q2R    *)
(*  into RecipSquareBound.recip_sq_nodup_bound (the R-side domination): *)
(*                                                                    *)
(*    euler_partial_reindex_R : the R finite Euler partial product      *)
(*      Zpartial (map (p |-> 1/p^2) ps) N  equals the sum of 1/m^2      *)
(*      over the coded numbers m = code ps ks (as reals);              *)
(*                                                                    *)
(*    Zpartial_le_zeta : hence each partial product <= zeta(2)          *)
(*      (the coded numbers are DISTINCT positive integers, so           *)
(*       recip_sq_nodup_bound applies);                                *)
(*                                                                    *)
(*    euler_factor_le_zeta : and so the FINITE EULER PRODUCT            *)
(*      Zfactor (map (p |-> 1/p^2) ps) = prod_p (1 - p^-2)^-1 <= zeta(2)*)
(*      (taking N -> oo via euler_product_R + lim_le).                  *)
(*                                                                    *)
(*  This is exactly Hupper (the upper half of PrimorialZeta) for the    *)
(*  concrete prime enumeration: EP n <= zeta(2), tighter than the       *)
(*  telescoping EP n <= 2 (needed since zeta(2) < 2).                   *)
(*                                                                    *)
(*  Uses the classical Reals axioms (quarantined).                    *)
(* ================================================================= *)

Require Import PrimonGas PrimeFactorizationN EulerReindex RecipSquareBound EulerProductR ZetaConverge.
From Stdlib Require Import QArith Qreals Reals Lra ZArith Znumtheory List Lia.
Import ListNotations.

(* ----------------------------------------------------------------- *)
(*  Q2R homomorphism helpers                                         *)
(* ----------------------------------------------------------------- *)

Lemma Q2R_0' : Q2R 0 = 0%R.
Proof. unfold Q2R; simpl; lra. Qed.

Lemma Q2R_1' : Q2R 1 = 1%R.
Proof. unfold Q2R; simpl; rewrite Rinv_1, Rmult_1_r; reflexivity. Qed.

Lemma Q2R_inject_Z : forall z, Q2R (inject_Z z) = IZR z.
Proof. intro z; unfold Q2R, inject_Z; simpl; rewrite Rinv_1, Rmult_1_r; reflexivity. Qed.

Lemma Q2R_qpow : forall x k, Q2R (qpow x k) = ((Q2R x) ^ k)%R.
Proof.
  intros x k; induction k as [|k IH]; simpl.
  - apply Q2R_1'.
  - rewrite Q2R_mult, IH; reflexivity.
Qed.

Lemma Q2R_qprod : forall l, Q2R (qprod l) = fold_right Rmult 1%R (map Q2R l).
Proof.
  induction l as [|a l IH]; simpl; [ apply Q2R_1' | rewrite Q2R_mult, IH; reflexivity ].
Qed.

Lemma Q2R_qsum : forall l, Q2R (qsum l) = Rlsum (map Q2R l).
Proof.
  induction l as [|a l IH]; simpl; unfold Rlsum in *; simpl;
    [ apply Q2R_0' | rewrite Q2R_plus, IH; reflexivity ].
Qed.

Lemma Rlsum_seq_sumf : forall (f : nat -> R) N,
  Rlsum (map f (seq 0 (S N))) = sum_f_R0 f N.
Proof.
  intros f N; induction N as [|N IH].
  - unfold Rlsum; simpl; ring.
  - rewrite seq_S, map_app, Rlsum_app, IH; simpl.
    replace (0 + S N)%nat with (S N) by lia.
    unfold Rlsum; simpl; ring.
Qed.

Lemma inject_Z_nonzero : forall z, (z <> 0)%Z -> ~ inject_Z z == 0.
Proof. intros z Hz Heq; apply Hz; unfold Qeq in Heq; simpl in Heq; lia. Qed.

Lemma qpow2_nonzero : forall x, ~ x == 0 -> ~ qpow x 2 == 0.
Proof.
  intros x Hx H; apply Hx; simpl in H; rewrite Qmult_1_r in H.
  destruct (Qmult_integral x x H); assumption.
Qed.

Lemma Q2R_recip_qpow2 : forall z, (z <> 0)%Z -> Q2R (/ qpow (inject_Z z) 2) = (/ (IZR z) ^ 2)%R.
Proof.
  intros z Hz.
  rewrite Q2R_inv by (apply qpow2_nonzero, inject_Z_nonzero; exact Hz).
  rewrite Q2R_qpow, Q2R_inject_Z; reflexivity.
Qed.

Lemma Q2R_psum_sumf : forall x N,
  Q2R (psum x (S N)) = sum_f_R0 (fun k => ((Q2R x) ^ k)%R) N.
Proof.
  intros x N; unfold psum; rewrite Q2R_qsum, map_map.
  rewrite (map_ext (fun k => Q2R (qpow x k)) (fun k => ((Q2R x) ^ k)%R))
    by (intro k; apply Q2R_qpow).
  apply Rlsum_seq_sumf.
Qed.

(* ----------------------------------------------------------------- *)
(*  NoDup of the occupation-state enumeration                        *)
(* ----------------------------------------------------------------- *)

Lemma NoDup_map_inj : forall (A B : Type) (f : A -> B) (l : list A),
  (forall x y, In x l -> In y l -> f x = f y -> x = y) -> NoDup l -> NoDup (map f l).
Proof.
  intros A B f l; induction l as [|a l IH]; intros Hinj Hnd; simpl; [ constructor | ].
  rewrite NoDup_cons_iff in Hnd; destruct Hnd as [Hna Hnd].
  rewrite NoDup_cons_iff; split.
  - intro Hin; apply in_map_iff in Hin; destruct Hin as [y [Hfy Hy]].
    assert (a = y) by (apply Hinj; [ left; reflexivity | right; exact Hy | symmetry; exact Hfy ]).
    subst y; contradiction.
  - apply IH; [ intros x y Hx Hy; apply Hinj; right; assumption | exact Hnd ].
Qed.

Lemma nodup_flatmap_cons : forall (L : list (list nat)) ks,
  NoDup ks -> NoDup L -> NoDup (flat_map (fun k => map (cons k) L) ks).
Proof.
  intros L ks; induction ks as [|k ks IH]; intros Hks HL; simpl; [ constructor | ].
  rewrite NoDup_cons_iff in Hks; destruct Hks as [Hnk Hks].
  apply NoDup_app.
  - apply NoDup_map_inj; [ intros x y _ _ Heq; injection Heq; auto | exact HL ].
  - apply IH; [ exact Hks | exact HL ].
  - intros a Hin1 Hin2.
    apply in_map_iff in Hin1; destruct Hin1 as [t1 [Ht1 _]].
    apply in_flat_map in Hin2; destruct Hin2 as [k' [Hk' Hin2']].
    apply in_map_iff in Hin2'; destruct Hin2' as [t2 [Ht2 _]].
    assert (Heq : k :: t1 = k' :: t2) by (transitivity a; [ exact Ht1 | symmetry; exact Ht2 ]).
    injection Heq as Hkeq _; rewrite <- Hkeq in Hk'; contradiction.
Qed.

Lemma gstates_nodup : forall xs K, NoDup (gstates xs K).
Proof.
  induction xs as [|x xs IH]; intro K; simpl.
  - constructor; [ destruct 1 | constructor ].
  - apply nodup_flatmap_cons; [ apply seq_NoDup | apply IH ].
Qed.

(* ----------------------------------------------------------------- *)
(*  positivity of the coded numbers, and the rr/Z.to_nat bridge      *)
(* ----------------------------------------------------------------- *)

Lemma zpow_ge_1 : forall (p : Z) k, (1 <= p)%Z -> (1 <= p ^ Z.of_nat k)%Z.
Proof.
  intros p k Hp; induction k as [|k IH]; [ simpl; lia | ].
  rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia; nia.
Qed.

Lemma code_pos : forall ps ks, Forall prime ps -> (1 <= code ps ks)%Z.
Proof.
  induction ps as [|p ps' IH]; intros ks Hpr.
  - destruct ks; simpl; lia.
  - inversion Hpr as [| ? ? Hp Hpr']; subst.
    destruct ks as [|k ks']; simpl; [ lia | ].
    assert (Hp2 : (2 <= p)%Z) by (destruct Hp; lia).
    pose proof (zpow_ge_1 p k ltac:(lia)) as Hpk.
    pose proof (IH ks' Hpr') as Hc; nia.
Qed.

Lemma rr_Z2Nat : forall c, (0 <= c)%Z -> rr (Z.to_nat c) = (/ (IZR c) ^ 2)%R.
Proof.
  intros c Hc; unfold rr; rewrite INR_IZR_INZ, Z2Nat.id by exact Hc; reflexivity.
Qed.

(* a convergent sequence bounded above by c has limit <= c *)
Lemma lim_le : forall (Un : nat -> R) l c,
  Un_cv Un l -> (forall n, (Un n <= c)%R) -> (l <= c)%R.
Proof.
  intros Un l c Hcv Hb.
  destruct (Rle_or_lt l c) as [Hle | Hlt]; [ exact Hle | exfalso ].
  set (eps := ((l - c) / 2)%R).
  assert (Heps : (0 < eps)%R) by (unfold eps; lra).
  destruct (Hcv eps Heps) as [N HN]; specialize (HN N (Nat.le_refl N)).
  unfold R_dist in HN; apply Rabs_def2 in HN; destruct HN as [_ Hlo].
  specialize (Hb N); unfold eps in *; lra.
Qed.

(* ----------------------------------------------------------------- *)
(*  the bridge, for a fixed list ps of distinct primes               *)
(* ----------------------------------------------------------------- *)

Section Bridge.
Variable ps : list Z.
Hypothesis Hpr : Forall prime ps.
Hypothesis Hnd : NoDup ps.

(* the R finite Euler partial product = Q2R of the Q finite Euler product *)
Lemma Lpart : forall N,
  Zpartial (map (fun p => (/ (IZR p) ^ 2)%R) ps) N
  = Q2R (qprod (map (fun p => psum (fug p) (S N)) ps)).
Proof.
  intro N; unfold Zpartial; rewrite map_map, Q2R_qprod, map_map.
  f_equal; apply map_ext_in; intros p Hp.
  pose proof (proj1 (Forall_forall prime ps) Hpr p Hp) as Hpp.
  symmetry; rewrite Q2R_psum_sumf.
  apply sum_eq; intros k _; unfold fug; rewrite Q2R_recip_qpow2; [ reflexivity | destruct Hpp; lia ].
Qed.

(* Q2R of the reindexed Q sum = the R sum of 1/m^2 over the coded numbers *)
Lemma Rpart : forall N,
  Q2R (qsum (map (fun ks => / qpow (inject_Z (code ps ks)) 2)
                 (gstates (map fug ps) (S N))))
  = Rlsum (map rr (map (fun ks => Z.to_nat (code ps ks)) (gstates (map fug ps) (S N)))).
Proof.
  intro N; rewrite Q2R_qsum, map_map, map_map.
  f_equal; apply map_ext_in; intros ks _.
  pose proof (code_pos ps ks Hpr) as Hc.
  rewrite Q2R_recip_qpow2 by lia.
  rewrite rr_Z2Nat by lia; reflexivity.
Qed.

Theorem euler_partial_reindex_R : forall N,
  Zpartial (map (fun p => (/ (IZR p) ^ 2)%R) ps) N
  = Rlsum (map rr (map (fun ks => Z.to_nat (code ps ks)) (gstates (map fug ps) (S N)))).
Proof.
  intro N; rewrite Lpart, (Qeq_eqR _ _ (euler_reindex ps (S N))); apply Rpart.
Qed.

(* the coded numbers are distinct positive integers *)
Lemma codes_nat_nodup : forall N,
  NoDup (map (fun ks => Z.to_nat (code ps ks)) (gstates (map fug ps) (S N))).
Proof.
  intro N; apply NoDup_map_inj; [ | apply gstates_nodup ].
  intros ks ks' Hks Hks' Heq.
  assert (Hc : code ps ks = code ps ks').
  { apply Z2Nat.inj;
      [ pose proof (code_pos ps ks Hpr); lia
      | pose proof (code_pos ps ks' Hpr); lia
      | exact Heq ]. }
  apply (codes_distinct ps (S N) Hpr Hnd ks ks' Hks Hks' Hc).
Qed.

Lemma codes_nat_pos : forall N m,
  In m (map (fun ks => Z.to_nat (code ps ks)) (gstates (map fug ps) (S N))) -> (1 <= m)%nat.
Proof.
  intros N m Hin; apply in_map_iff in Hin; destruct Hin as [ks [Hm _]]; subst m.
  pose proof (code_pos ps ks Hpr) as Hc.
  destruct (Z.to_nat (code ps ks)) as [|q] eqn:E; [ exfalso | lia ].
  pose proof (Z2Nat.id (code ps ks) ltac:(lia)) as Hid.
  rewrite E in Hid; simpl in Hid; lia.
Qed.

(* each partial Euler product is <= zeta(2) *)
Theorem Zpartial_le_zeta : forall N,
  (Zpartial (map (fun p => (/ (IZR p) ^ 2)%R) ps) N <= proj1_sig zeta2_converges)%R.
Proof.
  intro N; rewrite euler_partial_reindex_R.
  apply recip_sq_nodup_bound; [ apply codes_nat_nodup | apply codes_nat_pos ].
Qed.

(* HUPPER (list form): the finite Euler product prod_p (1-p^-2)^-1 <= zeta(2) *)
Theorem euler_factor_le_zeta :
  (Zfactor (map (fun p => (/ (IZR p) ^ 2)%R) ps) <= proj1_sig zeta2_converges)%R.
Proof.
  apply (lim_le (Zpartial (map (fun p => (/ (IZR p) ^ 2)%R) ps))
                (Zfactor (map (fun p => (/ (IZR p) ^ 2)%R) ps))
                (proj1_sig zeta2_converges)).
  - apply euler_product_R.
    apply Forall_forall; intros y Hy; apply in_map_iff in Hy.
    destruct Hy as [p [Hpy Hp]]; subst y.
    pose proof (proj1 (Forall_forall prime ps) Hpr p Hp) as Hpp.
    assert (H2 : (2 <= IZR p)%R) by (apply IZR_le; destruct Hpp; lia).
    assert (Hpos : (0 < / (IZR p) ^ 2)%R) by (apply Rinv_0_lt_compat, pow_lt; lra).
    rewrite Rabs_pos_eq by lra.
    apply Rle_lt_trans with (/ 4)%R; [ apply Rinv_le_contravar; [ lra | nra ] | lra ].
  - apply Zpartial_le_zeta.
Qed.

End Bridge.

Print Assumptions euler_factor_le_zeta.

(* ================================================================= *)
(*  END EulerProductZetaBound.v                                      *)
(*  For any list ps of distinct primes, the finite Euler product        *)
(*  prod_{p in ps} (1 - p^-2)^-1 <= zeta(2).  This is Hupper for the     *)
(*  concrete prime enumeration: it reindexes the product (Q2R of         *)
(*  EulerReindex) as a sum of 1/m^2 over distinct smooth numbers, then   *)
(*  dominates by RecipSquareBound.  Uses the classical Reals axioms.    *)
(* ================================================================= *)
