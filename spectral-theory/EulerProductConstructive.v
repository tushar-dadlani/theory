(* ================================================================= *)
(*  EulerProductConstructive.v                                      *)
(*                                                                    *)
(*  THE EULER PRODUCT, AXIOM-FREE over the constructive real:         *)
(*     ∏_{p prime ≤ N} 1/(1 − p⁻²)  →  ζ(2)   as N → ∞               *)
(*  i.e. `cvQ (fun N => ZfactorQ (primes_upto (S N))) zeta2c`.        *)
(*  Movement III of the ζ arc, ported to Rocq's axiom-free `CReal`.   *)
(* ================================================================= *)

From Stdlib Require Import Reals.Cauchy.ConstructiveCauchyReals
        Reals.Cauchy.ConstructiveCauchyRealsMult
        Reals.Cauchy.ConstructiveCauchyAbs
        Reals.Cauchy.ConstructiveRcomplete.
From Stdlib Require Import ZArith QArith Qabs Qround Lqa Lia List Arith Znumtheory.
Import ListNotations.
Require Import PrimonGas EulerReindex PrimeFactorizationN PrimeFactorizationExists
        MobiusReciprocal EulerProductZeta EulerProductZetaBound
        CRealCv ZetaConstructive ZetaSquareConstructive ZetaMasterConstructive Totient.
Local Open Scope Q_scope.

(* ----------------------------------------------------------------- *)
(*  a couple of missing ℚ list helpers                               *)
(* ----------------------------------------------------------------- *)
Lemma qprod_map_ext_in : forall {A} (f g : A -> Q) (l : list A),
  (forall a, In a l -> f a == g a) -> qprod (map f l) == qprod (map g l).
Proof.
  intros A f g l; induction l as [|a l IH]; intro H; [ reflexivity | ].
  cbn [map qprod]; rewrite (H a (or_introl eq_refl)), IH; [ reflexivity | ].
  intros x Hx; apply H; right; exact Hx.
Qed.

Lemma qprod_nonneg : forall (l : list Q), (forall x, In x l -> 0 <= x) -> 0 <= qprod l.
Proof.
  induction l as [|a l IH]; intro H; [ cbn; lra | ].
  cbn [qprod]; apply Qmult_le_0_compat;
    [ apply H; left; reflexivity | apply IH; intros x Hx; apply H; right; exact Hx ].
Qed.

Lemma qprod_le_1 : forall (l : list Q), (forall x, In x l -> 0 <= x <= 1) -> qprod l <= 1.
Proof.
  induction l as [|a l IH]; intro H; [ cbn; lra | ].
  cbn [qprod].
  assert (Ha : 0 <= a <= 1) by (apply H; left; reflexivity).
  assert (Hl : qprod l <= 1) by (apply IH; intros x Hx; apply H; right; exact Hx).
  assert (Hl0 : 0 <= qprod l) by (apply qprod_nonneg; intros x Hx; apply (H x); right; exact Hx).
  nra.
Qed.

Lemma qpow_bounds : forall x K, 0 <= x <= 1 -> 0 <= qpow x K <= 1.
Proof. intros x K Hx; induction K as [|K IH]; [ cbn; lra | cbn [qpow]; nra ]. Qed.

(* ================================================================= *)
(*  Part A — the ℚ Euler-factor algebra                              *)
(* ================================================================= *)
Definition efacQ (p : Z) : Q := / (1 - fug p).
Definition ZfactorQ (ps : list Z) : Q := qprod (map efacQ ps).
Definition ZpartialQ (ps : list Z) (K : nat) : Q := qprod (map (fun p => psum (fug p) K) ps).

Lemma fug_pos : forall p, prime p -> 0 < fug p.
Proof.
  intros p Hp; pose proof (prime_ge_2 _ Hp) as H2.
  assert (Hp0 : 0 < inject_Z p) by (unfold Qlt; simpl; lia).
  unfold fug; apply Qinv_lt_0_compat.
  change (qpow (inject_Z p) 2) with (inject_Z p * (inject_Z p * 1)); nra.
Qed.

Lemma fug_le : forall p, prime p -> fug p <= 1 # 4.
Proof.
  intros p Hp; pose proof (prime_ge_2 _ Hp) as H2.
  assert (Hp2 : 2 <= inject_Z p) by (unfold Qle; simpl; lia).
  assert (E : (1 # 4) == / inject_Z 4) by reflexivity.
  rewrite E; unfold fug; apply Qinv_le.
  - unfold Qlt; simpl; lia.
  - change (qpow (inject_Z p) 2) with (inject_Z p * (inject_Z p * 1)).
    assert (E4 : inject_Z 4 == 4) by reflexivity; rewrite E4; nra.
Qed.

Lemma fug_lt1 : forall p, prime p -> fug p < 1.
Proof. intros p Hp; apply Qle_lt_trans with (1 # 4); [ apply fug_le; auto | reflexivity ]. Qed.

Lemma efacQ_pos : forall p, prime p -> 0 < efacQ p.
Proof. intros p Hp; unfold efacQ; apply Qinv_lt_0_compat; pose proof (fug_lt1 p Hp); lra. Qed.

Lemma efacQ_le2 : forall p, prime p -> efacQ p <= 2.
Proof.
  intros p Hp; unfold efacQ.
  pose proof (fug_le p Hp) as Hle; pose proof (fug_pos p Hp) as Hpos.
  apply Qle_shift_inv_r; [ lra | ].
  assert (fug p <= 1#4) by exact Hle; lra.
Qed.

(* psum as the closed Euler factor times the geometric remainder *)
Lemma psum_efac : forall p K, prime p ->
  psum (fug p) K == efacQ p * (1 - qpow (fug p) K).
Proof.
  intros p K Hp; pose proof (fug_lt1 p Hp) as H1.
  unfold efacQ; rewrite <- geom_closed; field; lra.
Qed.

(* ZpartialQ ps K == ZfactorQ ps · ∏ (1 − fug p ^K) *)
Lemma Zpartial_factored : forall ps K, Forall prime ps ->
  ZpartialQ ps K == ZfactorQ ps * qprod (map (fun p => 1 - qpow (fug p) K) ps).
Proof.
  intros ps K Hps; unfold ZpartialQ, ZfactorQ.
  rewrite (qprod_map_ext_in (fun p => psum (fug p) K)
             (fun p => efacQ p * (1 - qpow (fug p) K)) ps).
  - rewrite <- qprod_mult; reflexivity.
  - intros a Ha; apply psum_efac; rewrite Forall_forall in Hps; apply Hps; exact Ha.
Qed.

Lemma ZfactorQ_nonneg : forall ps, Forall prime ps -> 0 <= ZfactorQ ps.
Proof.
  intros ps Hps; unfold ZfactorQ; apply qprod_nonneg.
  intros x Hx; apply in_map_iff in Hx; destruct Hx as [p [Hp Hin]]; subst x.
  apply Qlt_le_weak, efacQ_pos; rewrite Forall_forall in Hps; apply Hps; exact Hin.
Qed.

Lemma ZpartialQ_le_ZfactorQ : forall ps K, Forall prime ps -> ZpartialQ ps K <= ZfactorQ ps.
Proof.
  intros ps K Hps; rewrite (Zpartial_factored ps K Hps).
  pose proof (ZfactorQ_nonneg ps Hps) as Hzf.
  assert (Hb : forall p, In p ps -> 0 <= 1 - qpow (fug p) K <= 1).
  { intros p Hin; rewrite Forall_forall in Hps; pose proof (Hps p Hin) as Hprime.
    assert (0 <= fug p <= 1) by (pose proof (fug_pos p Hprime); pose proof (fug_le p Hprime); lra).
    pose proof (qpow_bounds (fug p) K H); lra. }
  assert (Hprod1 : qprod (map (fun p => 1 - qpow (fug p) K) ps) <= 1).
  { apply qprod_le_1; intros x Hx; apply in_map_iff in Hx; destruct Hx as [p [Hp Hin]]; subst x; apply Hb; exact Hin. }
  assert (Hprod0 : 0 <= qprod (map (fun p => 1 - qpow (fug p) K) ps)).
  { apply qprod_nonneg; intros x Hx; apply in_map_iff in Hx; destruct Hx as [p [Hp Hin]]; subst x;
      apply (Hb p Hin). }
  nra.
Qed.

(* ================================================================= *)
(*  Part B — reindex the finite product to a qw-sum over codes        *)
(* ================================================================= *)
Definition codenats (ps : list Z) (K : nat) : list nat :=
  map (fun ks => Z.to_nat (code ps ks)) (gstates (map fug ps) K).

Lemma prime_Forall_1 : forall ps, Forall prime ps -> Forall (fun p => (1 <= p)%Z) ps.
Proof.
  intros ps Hp; rewrite Forall_forall in *; intros x Hx; pose proof (prime_ge_2 _ (Hp x Hx)); lia.
Qed.

Lemma qw_code : forall ps ks, Forall prime ps ->
  / qpow (inject_Z (code ps ks)) 2 == qw (Z.to_nat (code ps ks)).
Proof.
  intros ps ks Hp.
  assert (Hge : (1 <= code ps ks)%Z) by (apply code_ge_1, prime_Forall_1; exact Hp).
  unfold qw, qN; rewrite Z2Nat.id by lia.
  change (qpow (inject_Z (code ps ks)) 2)
    with (inject_Z (code ps ks) * (inject_Z (code ps ks) * 1)).
  assert (E : inject_Z (code ps ks) * (inject_Z (code ps ks) * 1)
              == inject_Z (code ps ks) * inject_Z (code ps ks)) by ring.
  rewrite E; reflexivity.
Qed.

Lemma ZpartialQ_as_codes : forall ps K, Forall prime ps ->
  ZpartialQ ps K == qsum (map qw (codenats ps K)).
Proof.
  intros ps K Hp; unfold ZpartialQ, codenats.
  rewrite (euler_reindex ps K), map_map.
  apply qsum_map_ext; intros ks; apply qw_code; exact Hp.
Qed.

Lemma codenats_nodup : forall ps K, Forall prime ps -> NoDup ps -> NoDup (codenats ps K).
Proof.
  intros ps K Hp Hnd; unfold codenats; apply NoDup_map_inj; [ | apply gstates_nodup ].
  intros ks ks' Hin Hin' Heq.
  apply (codes_distinct ps K Hp Hnd ks ks' Hin Hin').
  assert (1 <= code ps ks)%Z by (apply code_ge_1, prime_Forall_1; exact Hp).
  assert (1 <= code ps ks')%Z by (apply code_ge_1, prime_Forall_1; exact Hp).
  apply Z2Nat.inj; lia.
Qed.

Lemma codenats_pos : forall ps K m, Forall prime ps -> In m (codenats ps K) -> (1 <= m)%nat.
Proof.
  intros ps K m Hp Hin; unfold codenats in Hin; apply in_map_iff in Hin.
  destruct Hin as [ks [Hm _]]; subst m.
  assert (1 <= code ps ks)%Z by (apply code_ge_1, prime_Forall_1; exact Hp); lia.
Qed.

(* ================================================================= *)
(*  Part C — the two bounds (truncated Euler product)                 *)
(* ================================================================= *)

(* UPPER: every finite truncated Euler product ≤ ζ(2) *)
Theorem Ptrunc_le_zeta2c : forall ps K, Forall prime ps -> NoDup ps ->
  (inject_Q (ZpartialQ ps K) <= zeta2c)%CReal.
Proof.
  intros ps K Hp Hnd.
  assert (E : (inject_Q (ZpartialQ ps K) == inject_Q (qsum (map qw (codenats ps K))))%CReal)
    by (apply inject_Q_morph, ZpartialQ_as_codes; exact Hp).
  rewrite E; apply recip_sq_le_zeta2c;
    [ apply codenats_nodup; assumption
    | intros m Hm; apply codenats_pos with (ps := ps) (K := K); assumption ].
Qed.

(* LOWER: the ζ(2) partial sum is covered by the smooth codes ≤ N *)
Lemma smooth_incl : forall N, incl (seq 1 (S N)) (codenats (primes_upto (S N)) (S N)).
Proof.
  intros N m Hm; apply in_seq in Hm.
  set (ps := primes_upto (S N)).
  assert (Hpr : Forall prime ps) by apply primes_upto_Forall.
  assert (Hnd : NoDup ps) by apply primes_upto_nodup.
  assert (Hsm : forall q, prime q -> (q | Z.of_nat m) -> In q ps)
    by (intros q Hq Hqd; apply small_smooth with (m := m); [ lia | lia | exact Hq | exact Hqd ]).
  destruct (code_surj ps Hpr Hnd (Z.of_nat m) ltac:(lia) Hsm) as [ks [Hlen Hcode]].
  assert (H2p : Forall (fun p => (2 <= p)%Z) ps).
  { rewrite Forall_forall; intros x Hx;
      pose proof (prime_ge_2 _ ((proj1 (Forall_forall _ _)) Hpr x Hx)); lia. }
  assert (Hexp : Forall (fun e => (e < S N)%nat) ks).
  { rewrite Forall_forall; intros e He.
    pose proof (entry_pow_le_code ps ks H2p Hlen e He) as Hpow.
    rewrite Hcode in Hpow.
    assert (Hle : (2 ^ e <= m)%nat)
      by (apply Nat2Z.inj_le; rewrite Nat2Z.inj_pow; change (Z.of_nat 2) with 2%Z; exact Hpow).
    pose proof (nat_lt_pow2 e); lia. }
  assert (Hin : In ks (gstates (map fug ps) (S N)))
    by (apply gstates_complete; [ rewrite length_map; symmetry; exact Hlen | exact Hexp ]).
  unfold codenats; apply in_map_iff; exists ks; split; [ | exact Hin ].
  rewrite Hcode, Nat2Z.id; reflexivity.
Qed.

Lemma zpartQ_le_Zpartial : forall N,
  zpartQ N <= ZpartialQ (primes_upto (S N)) (S N).
Proof.
  intro N.
  assert (Hz : zpartQ N == qsum (map qw (seq 1 (S N))))
    by (rewrite <- SMQ_eq_zpartQ; unfold SMQ; reflexivity).
  rewrite Hz, (ZpartialQ_as_codes (primes_upto (S N)) (S N) (primes_upto_Forall _)).
  apply qsum_incl_le_qw; [ apply seq_NoDup | apply smooth_incl ].
Qed.

(* ================================================================= *)
(*  Part D — the Euler product converges to ζ(2)                     *)
(* ================================================================= *)
Theorem euler_product_trunc :
  cvQ (fun N => ZpartialQ (primes_upto (S N)) (S N)) zeta2c.
Proof.
  apply (cvQ_squeeze_const_upper zpartQ
           (fun N => ZpartialQ (primes_upto (S N)) (S N)) zeta2c).
  - apply zeta2c_cv.
  - intro N; apply zpartQ_le_Zpartial.
  - intro N; apply Ptrunc_le_zeta2c; [ apply primes_upto_Forall | apply primes_upto_nodup ].
Qed.

(* ================================================================= *)
(*  Part E — the FULL Euler factor ∏ 1/(1−p⁻²)                       *)
(* ================================================================= *)
Lemma qpow_nonneg : forall x K, 0 <= x -> 0 <= qpow x K.
Proof. intros x K Hx; induction K; [ cbn; lra | cbn [qpow]; nra ]. Qed.

Lemma qpow_le_base : forall x y K, 0 <= x -> x <= y -> qpow x K <= qpow y K.
Proof.
  intros x y K Hx Hxy; induction K as [|K IH]; [ cbn; lra | cbn [qpow] ].
  assert (Hy : 0 <= y) by lra.
  pose proof (qpow_nonneg x K Hx) as Hpx; pose proof (qpow_nonneg y K Hy) as Hpy; nra.
Qed.

Lemma qsum_map_le : forall {A} (f g : A -> Q) l,
  (forall a, In a l -> f a <= g a) -> qsum (map f l) <= qsum (map g l).
Proof.
  intros A f g l; induction l as [|a l IH]; intro H; [ cbn; lra | ].
  cbn [map qsum]; pose proof (H a (or_introl eq_refl)).
  assert (qsum (map f l) <= qsum (map g l)) by (apply IH; intros x Hx; apply H; right; exact Hx); lra.
Qed.

Lemma one_minus_prod_le_sum : forall (l : list Q),
  (forall x, In x l -> 0 <= x <= 1) -> 0 <= 1 - qprod (map (fun x => 1 - x) l) <= qsum l.
Proof.
  induction l as [|a l IH]; intro H; [ cbn; lra | ].
  cbn [map qprod qsum].
  assert (Ha : 0 <= a <= 1) by (apply H; left; auto).
  assert (Hrec : 0 <= 1 - qprod (map (fun x => 1 - x) l) <= qsum l)
    by (apply IH; intros x Hx; apply H; right; auto).
  assert (Hp0 : 0 <= qprod (map (fun x => 1 - x) l)).
  { apply qprod_nonneg; intros y Hy; apply in_map_iff in Hy; destruct Hy as [z [Hz Hin]]; subst y.
    assert (0 <= z <= 1) by (apply H; right; auto); lra. }
  assert (Hp1 : qprod (map (fun x => 1 - x) l) <= 1).
  { apply qprod_le_1; intros y Hy; apply in_map_iff in Hy; destruct Hy as [z [Hz Hin]]; subst y.
    assert (0 <= z <= 1) by (apply H; right; auto); lra. }
  nra.
Qed.

Lemma quarter_pow_le : forall K, qpow (1 # 4) K <= / inject_Z (Z.of_nat (S K)).
Proof.
  intro K.
  assert (Hq : qpow (1 # 4) K == / qpow (inject_Z 4) K).
  { assert (H : (1 # 4) == / inject_Z 4) by reflexivity; rewrite H, qpow_inv; reflexivity. }
  rewrite Hq; apply Qinv_le.
  - unfold Qlt; simpl; lia.
  - rewrite <- (inj_pow 4 K), <- Zle_Qle.
    assert (HSK : (S K <= 4 ^ K)%nat).
    { pose proof (nat_lt_pow2 K); assert (2 ^ K <= 4 ^ K)%nat by (apply Nat.pow_le_mono_l; lia); lia. }
    replace (4 ^ Z.of_nat K)%Z with (Z.of_nat (4 ^ K)) by (rewrite Nat2Z.inj_pow; reflexivity); lia.
Qed.

Lemma qN_mult : forall a b, qN (a * b)%nat == qN a * qN b.
Proof. intros a b; unfold qN; rewrite Nat2Z.inj_mul, inject_Z_mult; reflexivity. Qed.

Lemma ZfactorQ_bound : forall ps, Forall prime ps -> ZfactorQ ps <= qN (2 ^ length ps).
Proof.
  induction ps as [|p ps IH]; intro Hps.
  - unfold ZfactorQ; cbn [map qprod length].
    assert (E : qN (2 ^ 0)%nat == 1) by (unfold qN; reflexivity); rewrite E; apply Qle_refl.
  - inversion Hps as [|? ? Hp Hps']; subst.
    unfold ZfactorQ in *; cbn [map qprod length].
    assert (Hef : 0 <= efacQ p <= 2)
      by (split; [ apply Qlt_le_weak, efacQ_pos | apply efacQ_le2 ]; exact Hp).
    assert (Hzf0 : 0 <= qprod (map efacQ ps)) by (apply ZfactorQ_nonneg; exact Hps').
    pose proof (IH Hps') as HI.
    apply Qle_trans with (2 * qN (2 ^ length ps)); [ nra | ].
    change (2 ^ S (length ps))%nat with (2 * 2 ^ length ps)%nat.
    rewrite qN_mult; assert (E2 : qN 2 == 2) by (unfold qN; reflexivity); rewrite E2; apply Qle_refl.
Qed.

Lemma modulus_bound : forall Cn K p, (Cn * Pos.to_nat p <= K)%nat ->
  qN Cn * / inject_Z (Z.of_nat (S K)) <= 1 # p.
Proof.
  intros Cn K p HK.
  assert (HB : 0 < inject_Z (Z.of_nat (S K))) by (unfold Qlt; simpl; lia).
  assert (Bne : ~ inject_Z (Z.of_nat (S K)) == 0)
    by (intro C; rewrite C in HB; exact (Qlt_irrefl 0 HB)).
  apply (proj1 (Qmult_le_r _ (1 # p) _ HB)).
  assert (E1 : qN Cn * / inject_Z (Z.of_nat (S K)) * inject_Z (Z.of_nat (S K)) == qN Cn)
    by (field; exact Bne).
  rewrite E1.
  assert (Hpp : 0 < inject_Z (Z.pos p)) by (unfold Qlt; simpl; lia).
  assert (E2 : (1 # p) * inject_Z (Z.of_nat (S K)) == inject_Z (Z.of_nat (S K)) * / inject_Z (Z.pos p))
    by (assert (Hpe : (1 # p) == / inject_Z (Z.pos p)) by reflexivity; rewrite Hpe; ring).
  rewrite E2; apply (proj1 (Qmult_le_r _ _ (inject_Z (Z.pos p)) Hpp)).
  assert (E3 : inject_Z (Z.of_nat (S K)) * / inject_Z (Z.pos p) * inject_Z (Z.pos p)
               == inject_Z (Z.of_nat (S K)))
    by (field; intro C; rewrite C in Hpp; exact (Qlt_irrefl 0 Hpp)).
  rewrite E3; unfold qN; rewrite <- inject_Z_mult, <- Zle_Qle, <- positive_nat_Z, <- Nat2Z.inj_mul.
  apply Nat2Z.inj_le; lia.
Qed.

Lemma Zpartial_cv_Zfactor : forall ps, Forall prime ps ->
  cvQ (fun K => ZpartialQ ps K) (inject_Q (ZfactorQ ps)).
Proof.
  intros ps Hps p.
  exists (2 ^ length ps * length ps * Pos.to_nat p)%nat; intros K HK.
  assert (Hle : ZpartialQ ps K <= ZfactorQ ps) by (apply ZpartialQ_le_ZfactorQ; exact Hps).
  assert (Hdiff : ZfactorQ ps - ZpartialQ ps K <= 1 # p).
  { rewrite (Zpartial_factored ps K Hps).
    set (P := qprod (map (fun q => 1 - qpow (fug q) K) ps)).
    assert (EG : ZfactorQ ps - ZfactorQ ps * P == ZfactorQ ps * (1 - P)) by ring; rewrite EG.
    set (t := / inject_Z (Z.of_nat (S K))).
    assert (Ht0 : 0 <= t) by (unfold t; apply Qinv_le_0_compat; unfold Qle; simpl; lia).
    assert (Hlen0 : 0 <= qN (length ps)) by (apply qN_nonneg).
    assert (Hzf0 : 0 <= ZfactorQ ps) by (apply ZfactorQ_nonneg; exact Hps).
    (* 1 - P <= qN (length ps) * t *)
    assert (Heps : forall x, In x (map (fun q => qpow (fug q) K) ps) -> 0 <= x <= 1).
    { intros x Hx; apply in_map_iff in Hx; destruct Hx as [q [Hq Hin]]; subst x.
      rewrite Forall_forall in Hps; pose proof (Hps q Hin) as Hpr.
      assert (0 <= fug q <= 1) by (pose proof (fug_pos q Hpr); pose proof (fug_le q Hpr); lra).
      apply (qpow_bounds (fug q) K H). }
    pose proof (one_minus_prod_le_sum (map (fun q => qpow (fug q) K) ps) Heps) as [_ HG1].
    rewrite map_map in HG1; fold P in HG1.
    assert (Hsum : qsum (map (fun q => qpow (fug q) K) ps) <= qN (length ps) * t).
    { eapply Qle_trans.
      - apply (qsum_map_le (fun q => qpow (fug q) K) (fun _ => qpow (1 # 4) K) ps).
        intros q Hin; rewrite Forall_forall in Hps; pose proof (Hps q Hin) as Hpr.
        apply qpow_le_base; [ apply Qlt_le_weak, fug_pos; exact Hpr | apply fug_le; exact Hpr ].
      - rewrite (qsum_const (fun _ => qpow (1 # 4) K) ps (qpow (1 # 4) K)) by (intros; reflexivity).
        pose proof (quarter_pow_le K) as Hq14; unfold t; nra. }
    assert (H1P : 1 - P <= qN (length ps) * t) by lra.
    assert (HzfB : ZfactorQ ps <= qN (2 ^ length ps)) by (apply ZfactorQ_bound; exact Hps).
    assert (Hmod : qN (2 ^ length ps) * qN (length ps) * t <= 1 # p).
    { rewrite <- qN_mult; unfold t; apply modulus_bound; exact HK. }
    assert (HCD : 0 <= qN (length ps) * t) by nra.
    apply Qle_trans with (ZfactorQ ps * (qN (length ps) * t)); [ nra | ].
    apply Qle_trans with (qN (2 ^ length ps) * (qN (length ps) * t)); [ nra | ].
    rewrite Qmult_assoc; exact Hmod. }
  assert (Eq : (inject_Q (ZpartialQ ps K) - inject_Q (ZfactorQ ps)
               == inject_Q (ZpartialQ ps K - ZfactorQ ps))%CReal)
    by (rewrite inject_Q_diff; unfold CReal_minus; reflexivity).
  rewrite Eq; apply inj_abs_le; apply Qabs_Qle_condition; split; lra.
Qed.

(* the full Euler factor product over any prime set is ≤ ζ(2) *)
Theorem ZfactorQ_le_zeta2c : forall ps, Forall prime ps -> NoDup ps ->
  (inject_Q (ZfactorQ ps) <= zeta2c)%CReal.
Proof.
  intros ps Hp Hnd; apply (cvQ_le_const (fun K => ZpartialQ ps K));
    [ apply Zpartial_cv_Zfactor; exact Hp
    | intro K; apply Ptrunc_le_zeta2c; assumption ].
Qed.

(* the ζ(2) partial sum is dominated by the Euler factor product over primes ≤ N *)
Theorem zpartQ_le_ZfactorQ_primes : forall N,
  zpartQ N <= ZfactorQ (primes_upto (S N)).
Proof.
  intro N; apply Qle_trans with (ZpartialQ (primes_upto (S N)) (S N));
    [ apply zpartQ_le_Zpartial | apply ZpartialQ_le_ZfactorQ; apply primes_upto_Forall ].
Qed.

Theorem euler_product_constructive :
  cvQ (fun N => ZfactorQ (primes_upto (S N))) zeta2c.
Proof.
  apply (cvQ_squeeze_const_upper zpartQ (fun N => ZfactorQ (primes_upto (S N))) zeta2c).
  - apply zeta2c_cv.
  - intro N; apply Qle_trans with (ZpartialQ (primes_upto (S N)) (S N));
      [ apply zpartQ_le_Zpartial | apply ZpartialQ_le_ZfactorQ; apply primes_upto_Forall ].
  - intro N; apply (cvQ_le_const (fun K => ZpartialQ (primes_upto (S N)) K));
      [ apply Zpartial_cv_Zfactor; apply primes_upto_Forall
      | intro K; apply Ptrunc_le_zeta2c; [ apply primes_upto_Forall | apply primes_upto_nodup ] ].
Qed.

Print Assumptions euler_product_trunc.
Print Assumptions euler_product_constructive.

(* ================================================================= *)
(*  END EulerProductConstructive.v                                  *)
(*  The FULL Euler product ∏_{p≤N} 1/(1−p⁻²) → ζ(2), axiom-free      *)
(*  (euler_product_constructive), plus the truncated-factor form.    *)
(*  Closed under the global context.                                 *)
(* ================================================================= *)
