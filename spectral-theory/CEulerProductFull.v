(* ================================================================= *)
(*  CEulerProductFull.v  —  the FULL complex Euler product converges.  *)
(*                                                                    *)
(*  EF s N := prod_{p <= S N} (1 - p^{-s})^{-1}  (the true Euler        *)
(*  factors, not the truncated geometric sums of cEF).  For Re s > 1,  *)
(*  EF s N -> zetaC s, proved via a product-difference bound against    *)
(*  the truncated product cEF (CEulerProductConv, already -> zetaC):    *)
(*  each factor differs by the geometric tail p^{-s(N+1)}/(1-p^{-s}),   *)
(*  all factors are bounded by M = 1/(1-2^{-σ}) >= 1, so                *)
(*    Cmod(EF - cEF) <= len * M^len * d,  d = (2^{-σ})^{S N} * M,       *)
(*  and len * M^len * d <= C * n * q^n -> 0 with q = M*2^{-σ} < 1       *)
(*  (Mertens: 2^{-σ} < 1/2 for σ > 1).  Axiom-clean.                    *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia ZArith Znumtheory List.
Require Import ComplexField Cmodulus CexpFull RootsOfUnity CDeriv CSeries
        DirichletLEuler EulerProductZeta CEulerProductZeta CEulerProductConv
        CDirichlet CZeta LogGeomSeries.
Import ListNotations.
Open Scope R_scope.

(* ================================================================= *)
(*  0.  n q^n -> 0                                                    *)
(* ================================================================= *)

Lemma nqn_cv0 : forall q, 0 <= q < 1 -> Un_cv (fun n => INR n * q ^ n) 0.
Proof.
  intros q [Hq0 Hq1].
  destruct (Rle_lt_or_eq_dec 0 q Hq0) as [Hqpos | Hqzero]; [ | ].
  - set (rho := (1 + q) / 2).
    assert (Hrho1 : rho < 1) by (unfold rho; lra).
    assert (Hrhoq : q < rho) by (unfold rho; lra).
    assert (Hrho0 : 0 < rho) by (unfold rho; lra).
    destruct (INR_unbounded (q / (rho - q))) as [N1 HN1].
    assert (Hstep : forall n, (N1 <= n)%nat ->
              INR (S n) * q ^ (S n) <= rho * (INR n * q ^ n)).
    { intros n Hn.
      assert (Hn1 : q / (rho - q) < INR n)
        by (apply Rlt_le_trans with (INR N1); [ exact HN1 | apply le_INR; exact Hn ]).
      assert (Hqlt : q < (rho - q) * INR n).
      { apply (Rmult_lt_reg_l (/ (rho - q))); [ apply Rinv_0_lt_compat; lra | ].
        rewrite <- Rmult_assoc, Rinv_l by lra; rewrite Rmult_1_l.
        replace (/ (rho - q) * q) with (q / (rho - q)) by (unfold Rdiv; ring); exact Hn1. }
      assert (Hqn : q * INR (S n) <= rho * INR n) by (rewrite S_INR; nra).
      assert (Hqnn : 0 <= q ^ n) by (apply pow_le; lra).
      change (q ^ S n) with (q * q ^ n); nra. }
    assert (Hgeo : forall m, INR (N1 + m) * q ^ (N1 + m) <= INR N1 * q ^ N1 * rho ^ m).
    { induction m as [|m IH].
      - rewrite Nat.add_0_r; replace (rho ^ 0) with 1 by (simpl; ring); lra.
      - replace (N1 + S m)%nat with (S (N1 + m)) by lia.
        eapply Rle_trans; [ apply Hstep; lia | ].
        replace (INR N1 * q ^ N1 * rho ^ S m) with (rho * (INR N1 * q ^ N1 * rho ^ m))
          by (simpl; ring).
        apply Rmult_le_compat_l; [ lra | exact IH ]. }
    intros eps Heps.
    assert (Hgcv : Un_cv (fun m => INR N1 * q ^ N1 * rho ^ m) 0).
    { replace 0 with (INR N1 * q ^ N1 * 0) by ring.
      apply CV_mult; [ apply Un_cv_const | apply pow_cv0; rewrite Rabs_pos_eq; lra ]. }
    destruct (Hgcv eps Heps) as [M2 HM2]; exists (N1 + M2)%nat; intros n Hn.
    assert (Hun0 : 0 <= INR n * q ^ n)
      by (apply Rmult_le_pos; [ apply pos_INR | apply pow_le; lra ]).
    unfold R_dist; rewrite Rminus_0_r, Rabs_right by (apply Rle_ge; exact Hun0).
    replace n with (N1 + (n - N1))%nat by lia.
    eapply Rle_lt_trans; [ apply Hgeo | ].
    specialize (HM2 (n - N1)%nat ltac:(lia)); unfold R_dist in HM2; rewrite Rminus_0_r in HM2.
    rewrite Rabs_right in HM2
      by (apply Rle_ge, Rmult_le_pos;
          [ apply Rmult_le_pos; [ apply pos_INR | apply pow_le; lra ] | apply pow_le; lra ]).
    exact HM2.
  - intros eps Heps; exists 0%nat; intros n _.
    unfold R_dist; rewrite Rminus_0_r.
    replace (INR n * q ^ n) with 0 by (rewrite <- Hqzero; destruct n; simpl; ring).
    rewrite Rabs_R0; exact Heps.
Qed.

(* ================================================================= *)
(*  1.  complex finite-product/sum modulus bounds                    *)
(* ================================================================= *)

Lemma Cmod_Csum_le : forall (f : nat -> C) N,
  Cmod (Csum f (S N)) <= sum_f_R0 (fun k => Cmod (f k)) N.
Proof.
  intros f N; induction N as [|N IH].
  - cbn [Csum]; replace (Cadd C0 (f 0%nat)) with (f 0%nat) by ring; cbn [sum_f_R0]; apply Rle_refl.
  - change (Csum f (S (S N))) with (Cadd (Csum f (S N)) (f (S N))); rewrite tech5.
    eapply Rle_trans; [ apply Cmod_triangle | apply Rplus_le_compat_r; exact IH ].
Qed.

Lemma Cwprod_nil : Cwprod [] = C1.
Proof. reflexivity. Qed.
Lemma Cwprod_cons : forall a l, Cwprod (a :: l) = Cmul a (Cwprod l).
Proof. reflexivity. Qed.

Lemma Cmod_Cwprod_le : forall l M, 0 <= M ->
  (forall x, In x l -> Cmod x <= M) -> Cmod (Cwprod l) <= M ^ (length l).
Proof.
  intros l M HM; induction l as [|a l IH]; intro Hall; cbn [length].
  - rewrite Cwprod_nil, Cmod_C1; simpl; lra.
  - rewrite Cwprod_cons, Cmod_mul; simpl (M ^ S (length l)).
    apply Rmult_le_compat.
    + apply Cmod_nonneg.
    + apply Cmod_nonneg.
    + apply Hall; left; reflexivity.
    + apply IH; intros x Hx; apply Hall; right; exact Hx.
Qed.

(* telescoping product-difference bound *)
Lemma Cwprod_diff_bound : forall (fa fb : Z -> C) ps M d,
  1 <= M -> 0 <= d ->
  (forall p, In p ps -> Cmod (fa p) <= M) ->
  (forall p, In p ps -> Cmod (fb p) <= M) ->
  (forall p, In p ps -> Cmod (Cminus (fa p) (fb p)) <= d) ->
  Cmod (Cminus (Cwprod (map fa ps)) (Cwprod (map fb ps)))
  <= INR (length ps) * M ^ (length ps) * d.
Proof.
  intros fa fb ps M d HM Hd; induction ps as [|p ps IH]; intros Ha Hb Hab.
  - cbn [map length]; rewrite !Cwprod_nil; replace (Cminus C1 C1) with C0 by ring.
    rewrite Cmod_C0; simpl; lra.
  - cbn [map length]; rewrite !Cwprod_cons.
    (* a A - b B = a (A - B) + (a - b) B *)
    replace (Cminus (Cmul (fa p) (Cwprod (map fa ps))) (Cmul (fb p) (Cwprod (map fb ps))))
      with (Cadd (Cmul (fa p) (Cminus (Cwprod (map fa ps)) (Cwprod (map fb ps))))
                 (Cmul (Cminus (fa p) (fb p)) (Cwprod (map fb ps)))) by ring.
    eapply Rle_trans; [ apply Cmod_triangle | ].
    rewrite !Cmod_mul.
    (* bound each piece *)
    assert (HAB : Cmod (Cminus (Cwprod (map fa ps)) (Cwprod (map fb ps)))
                  <= INR (length ps) * M ^ (length ps) * d)
      by (apply IH; intros q Hq; [ apply Ha | apply Hb | apply Hab ]; right; exact Hq).
    assert (HBb : Cmod (Cwprod (map fb ps)) <= M ^ (length ps)).
    { rewrite <- (length_map fb ps); apply Cmod_Cwprod_le; [ lra | ].
      intros x Hx; apply in_map_iff in Hx; destruct Hx as [q [Hq Hqin]]; subst x;
        apply Hb; right; exact Hqin. }
    assert (HMpos : 0 <= M ^ (length ps)) by (apply pow_le; lra).
    assert (Hfa : Cmod (fa p) <= M) by (apply Ha; left; reflexivity).
    assert (Hfab : Cmod (Cminus (fa p) (fb p)) <= d) by (apply Hab; left; reflexivity).
    (* INR(S len) * M^(S len) * d = (INR len + 1) * (M * M^len) * d *)
    rewrite S_INR; simpl (M ^ S (length ps)).
    apply Rle_trans with
      (M * (INR (length ps) * M ^ (length ps) * d) + d * M ^ (length ps)).
    + apply Rplus_le_compat.
      * apply Rmult_le_compat; [ apply Cmod_nonneg | apply Cmod_nonneg | exact Hfa | exact HAB ].
      * apply Rmult_le_compat; [ apply Cmod_nonneg | apply Cmod_nonneg | exact Hfab | exact HBb ].
    + (* M*(len*M^len*d) + d*M^len <= (len+1)*(M*M^len)*d, given 1<=M *)
      assert (Hle0 : 0 <= INR (length ps)) by apply pos_INR.
      assert (Haux : 0 <= d * M ^ (length ps) * (M - 1))
        by (apply Rmult_le_pos; [ apply Rmult_le_pos; [ exact Hd | exact HMpos ] | lra ]).
      nra.
Qed.

(* filter never lengthens *)
Lemma filter_len_le : forall (A : Type) (f : A -> bool) (l : list A),
  (length (filter f l) <= length l)%nat.
Proof.
  intros A f l; induction l as [|a l IH]; simpl; [ lia | ].
  destruct (f a); simpl; lia.
Qed.

Lemma primes_upto_len : forall B, (length (primes_upto B) <= S B)%nat.
Proof.
  intro B; unfold primes_upto.
  eapply Nat.le_trans; [ apply filter_len_le | ].
  rewrite length_map, length_seq; lia.
Qed.

(* ================================================================= *)
(*  2.  real-analysis helpers                                         *)
(* ================================================================= *)

Lemma exp_le : forall x y, x <= y -> exp x <= exp y.
Proof.
  intros x y H; destruct (Rle_lt_or_eq_dec x y H) as [Hlt | Heq];
    [ apply Rlt_le, exp_increasing; exact Hlt | subst; apply Rle_refl ].
Qed.

(* Rpower is decreasing in the base for a nonpositive exponent *)
Lemma Rpower_base_le : forall a b e, 0 < a -> a <= b -> e <= 0 ->
  Rpower b e <= Rpower a e.
Proof.
  intros a b e Ha Hab He; unfold Rpower; apply exp_le.
  assert (Hln : ln a <= ln b).
  { destruct (Rle_lt_or_eq_dec a b Hab) as [Hlt | Heq];
      [ apply Rlt_le, ln_increasing; lra | subst; apply Rle_refl ]. }
  nra.
Qed.

Lemma Un_cv_S : forall f l, Un_cv f l -> Un_cv (fun n => f (S n)) l.
Proof.
  intros f l H eps Heps; destruct (H eps Heps) as [N HN]; exists N; intros n Hn.
  apply HN; lia.
Qed.

Lemma CUn_cv_mod0 : forall u l, CUn_cv u l -> Un_cv (fun n => Cmod (Cminus (u n) l)) 0.
Proof.
  intros u l H eps Heps; destruct (H eps Heps) as [N HN]; exists N; intros n Hn.
  unfold R_dist; rewrite Rminus_0_r, Rabs_right by (apply Rle_ge, Cmod_nonneg).
  apply HN; exact Hn.
Qed.

(* the geometric tail identity: (1-x)^{-1} - Σ_{k<S N} x^k = x^{S N} (1-x)^{-1} *)
Lemma geom_tail_id : forall x N, Cminus C1 x <> C0 ->
  Cminus (Cinv (Cminus C1 x)) (Csum (fun k => Cpow x k) (S N))
  = Cmul (Cpow x (S N)) (Cinv (Cminus C1 x)).
Proof.
  intros x N Hne.
  assert (HxC1 : x <> C1).
  { intro He; apply Hne; subst x; replace (Cminus C1 C1) with C0 by ring; reflexivity. }
  assert (HB : Cminus x C1 <> C0).
  { intro He; apply Hne.
    replace (Cminus C1 x) with (Copp (Cminus x C1)) by ring; rewrite He; ring. }
  rewrite (geom_sum_value x (S N) HxC1); unfold Cdiv.
  field; split; assumption.
Qed.

(* ================================================================= *)
(*  3.  the s-dependent argument                                      *)
(* ================================================================= *)

Section Full.
Variable s : C.
Hypothesis Hgt : 1 < Re s.

Let sig := Re s.
Let q0 := Rpower 2 (- sig).
Let M := / (1 - q0).

Definition xp (p : Z) : C := Cpw (IZR p) (Copp s).
Definition efac (p : Z) : C := Cinv (Cminus C1 (xp p)).
Definition cfac (N : nat) (p : Z) : C := Csum (fun k => Cpow (xp p) k) (S N).
Definition EF (N : nat) : C := Cwprod (map efac (primes_upto (S N))).

(* --- constants: 0 < q0 < 1/2,  1 <= M < 2,  q := M q0 < 1 --- *)

Lemma q0_pos : 0 < q0.
Proof. unfold q0, Rpower; apply exp_pos. Qed.

Lemma q0_half : q0 < / 2.
Proof.
  unfold q0.
  apply Rlt_le_trans with (Rpower 2 (- (1))).
  - apply Rpower_lt; [ lra | unfold sig; lra ].
  - rewrite Rpower_Ropp, Rpower_1 by lra; apply Rle_refl.
Qed.

Lemma Mpos : 0 < M.
Proof. unfold M; apply Rinv_0_lt_compat; pose proof q0_half; lra. Qed.

Lemma M_def : M * (1 - q0) = 1.
Proof. unfold M; rewrite Rinv_l; [ reflexivity | pose proof q0_half; lra ]. Qed.

Lemma M_ge1 : 1 <= M.
Proof. pose proof M_def; pose proof Mpos; pose proof q0_pos; nra. Qed.

Let q := M * q0.

Lemma q_pos : 0 < q.
Proof. unfold q; apply Rmult_lt_0_compat; [ apply Mpos | apply q0_pos ]. Qed.

Lemma q_lt1 : q < 1.
Proof.
  unfold q; pose proof M_def; pose proof q0_half; pose proof Mpos; nra.
Qed.

(* --- per-factor estimates (for primes p >= 2) --- *)

Lemma xp_mod_le : forall p, (2 <= IZR p) -> Cmod (xp p) <= q0.
Proof.
  intros p Hp; unfold xp; rewrite Cpw_mod.
  replace (Re (Copp s)) with (- sig) by (unfold sig, Copp; cbn [Re]; ring).
  unfold q0; apply Rpower_base_le; [ lra | exact Hp | ].
  unfold sig; lra.
Qed.

Lemma den_low : forall p, (2 <= IZR p) -> 1 - q0 <= Cmod (Cminus C1 (xp p)).
Proof.
  intros p Hp; pose proof (Cmod_diff_le C1 (xp p)) as HD; rewrite Cmod_C1 in HD.
  pose proof (Cmod_nonneg (xp p)) as Hn; pose proof (xp_mod_le p Hp) as Hxq.
  pose proof q0_half.
  rewrite Rabs_right in HD by lra; lra.
Qed.

Lemma den_ne0 : forall p, (2 <= IZR p) -> Cminus C1 (xp p) <> C0.
Proof.
  intros p Hp He; pose proof (den_low p Hp) as Hl; pose proof q0_half.
  rewrite He, Cmod_C0 in Hl; lra.
Qed.

Lemma efac_mod_le : forall p, (2 <= IZR p) -> Cmod (efac p) <= M.
Proof.
  intros p Hp; unfold efac; rewrite Cmod_inv by (apply den_ne0; exact Hp).
  unfold M; apply Rinv_le_contravar; [ pose proof q0_half; lra | apply den_low; exact Hp ].
Qed.

Lemma cfac_mod_le : forall N p, (2 <= IZR p) -> Cmod (cfac N p) <= M.
Proof.
  intros N p Hp; unfold cfac.
  set (t := Cmod (xp p)).
  assert (Ht0 : 0 <= t) by (unfold t; apply Cmod_nonneg).
  assert (Htq : t <= q0) by (unfold t; apply xp_mod_le; exact Hp).
  pose proof q0_half as Hh.
  assert (Ht1 : t <> 1) by lra.
  eapply Rle_trans; [ apply Cmod_Csum_le | ].
  rewrite (sum_eq (fun k => Cmod (Cpow (xp p) k)) (fun k => t ^ k))
    by (intros i _; unfold t; apply Cmod_Cpow).
  rewrite tech3 by exact Ht1.
  (* (1 - t^{S N})/(1 - t) <= /(1-t) <= /(1-q0) = M *)
  assert (Htsn : 0 <= t ^ (S N)) by (apply pow_le; exact Ht0).
  apply Rle_trans with (/ (1 - t)).
  - unfold Rdiv; rewrite <- (Rmult_1_l (/ (1 - t))) at 2.
    apply Rmult_le_compat_r; [ apply Rlt_le, Rinv_0_lt_compat; lra | lra ].
  - unfold M; apply Rinv_le_contravar; [ lra | lra ].
Qed.

(* the per-factor difference is bounded by  d := q0^{S N} * M *)
Lemma factor_diff_le : forall N p, (2 <= IZR p) ->
  Cmod (Cminus (efac p) (cfac N p)) <= q0 ^ (S N) * M.
Proof.
  intros N p Hp; unfold efac, cfac.
  rewrite geom_tail_id by (apply den_ne0; exact Hp).
  rewrite Cmod_mul, Cmod_Cpow, Cmod_inv by (apply den_ne0; exact Hp).
  apply Rmult_le_compat.
  - apply pow_le, Cmod_nonneg.
  - apply Rlt_le, Rinv_0_lt_compat, Cmod_pos_ne0; apply den_ne0; exact Hp.
  - apply pow_incr; split; [ apply Cmod_nonneg | apply xp_mod_le; exact Hp ].
  - unfold M; apply Rinv_le_contravar; [ pose proof q0_half; lra | apply den_low; exact Hp ].
Qed.

(* --- the truncated product cEF, as a product of the cfac's --- *)
Lemma cEF_eq : forall N, cEF s N = Cwprod (map (cfac N) (primes_upto (S N))).
Proof. intro N; reflexivity. Qed.

(* the whole-product difference bound *)
Lemma EF_cEF_diff : forall N,
  Cmod (Cminus (EF N) (cEF s N))
  <= INR (length (primes_upto (S N))) * M ^ (length (primes_upto (S N)))
     * (q0 ^ (S N) * M).
Proof.
  intro N; unfold EF; rewrite cEF_eq.
  assert (Hp2 : forall p, In p (primes_upto (S N)) -> (2 <= IZR p)).
  { intros p Hin; apply IZR_le.
    pose proof (primes_upto_prime (S N) p Hin) as Hpr; destruct Hpr; lia. }
  apply Cwprod_diff_bound.
  - apply M_ge1.
  - apply Rmult_le_pos; [ apply pow_le, Rlt_le, q0_pos | apply Rlt_le, Mpos ].
  - intros p Hin; apply efac_mod_le, Hp2; exact Hin.
  - intros p Hin; apply cfac_mod_le, Hp2; exact Hin.
  - intros p Hin; apply factor_diff_le, Hp2; exact Hin.
Qed.

(* --- the difference majorant converges to 0 --- *)

Lemma maj_cv0 : Un_cv (fun N => M ^ 2 * (INR (S (S N)) * q ^ (S N))) 0.
Proof.
  replace 0 with (M ^ 2 * 0) by ring.
  apply CV_mult; [ apply Un_cv_const | ].
  apply (Un_cv_ext (fun N => INR (S N) * q ^ (S N) + q ^ (S N))).
  - intro n; rewrite (S_INR (S n)); ring.
  - replace 0 with (0 + 0) by ring; apply CV_plus.
    + apply (Un_cv_S (fun n => INR n * q ^ n) 0); apply nqn_cv0; split;
        [ apply Rlt_le, q_pos | apply q_lt1 ].
    + apply (Un_cv_S (fun n => q ^ n) 0); apply pow_cv0;
        rewrite Rabs_right by (apply Rle_ge, Rlt_le, q_pos); apply q_lt1.
Qed.

(* the whole-product difference is dominated by the majorant *)
Lemma EF_cEF_maj : forall N,
  Cmod (Cminus (EF N) (cEF s N)) <= M ^ 2 * (INR (S (S N)) * q ^ (S N)).
Proof.
  intro N; eapply Rle_trans; [ apply EF_cEF_diff | ].
  set (len := length (primes_upto (S N))).
  assert (Hlen : (len <= S (S N))%nat) by (unfold len; apply primes_upto_len).
  assert (HM1 : 1 <= M) by apply M_ge1.
  assert (Hq00 : 0 <= q0) by (apply Rlt_le, q0_pos).
  assert (HM0 : 0 <= M) by (apply Rlt_le, Mpos).
  (* M^len <= M^(S N) * M *)
  assert (HMpow : M ^ (S (S N)) = M ^ (S N) * M)
    by (replace (S (S N)) with (S N + 1)%nat by lia; rewrite pow_add; simpl; ring).
  assert (HpowB : M ^ len <= M ^ (S N) * M)
    by (rewrite <- HMpow; apply Rle_pow; [ exact HM1 | exact Hlen ]).
  assert (HpowN : 0 <= M ^ (S N)) by (apply pow_le; exact HM0).
  assert (Hq0N : 0 <= q0 ^ (S N)) by (apply pow_le; exact Hq00).
  assert (HlenN : INR len <= INR (S (S N))) by (apply le_INR; exact Hlen).
  assert (Hlen0 : 0 <= INR len) by apply pos_INR.
  assert (Hpl0 : 0 <= M ^ len) by (apply pow_le; exact HM0).
  (* q^(S N) = M^(S N) * q0^(S N) *)
  assert (HqB : q ^ (S N) = M ^ (S N) * q0 ^ (S N))
    by (unfold q; rewrite Rpow_mult_distr; reflexivity).
  (* chain *)
  apply Rle_trans with ((INR (S (S N)) * (M ^ (S N) * M)) * (q0 ^ (S N) * M)).
  - apply Rmult_le_compat_r.
    + apply Rmult_le_pos; [ exact Hq0N | exact HM0 ].
    + apply Rmult_le_compat; [ exact Hlen0 | exact Hpl0 | exact HlenN | exact HpowB ].
  - apply Req_le; rewrite HqB; ring.
Qed.

(* --- assembly: EF -> zetaC --- *)
Theorem EF_cv : forall (H0 : 0 < Re s) (H1 : Cminus C1 s <> C0),
  CUn_cv EF (zetaC s H0 H1).
Proof.
  intros H0 H1.
  apply (CUn_cv_bound EF (zetaC s H0 H1)
           (fun N => M ^ 2 * (INR (S (S N)) * q ^ (S N))
                     + Cmod (Cminus (cEF s N) (zetaC s H0 H1)))).
  - intro N.
    replace (Cminus (EF N) (zetaC s H0 H1))
      with (Cadd (Cminus (EF N) (cEF s N)) (Cminus (cEF s N) (zetaC s H0 H1))) by ring.
    eapply Rle_trans; [ apply Cmod_triangle | ].
    apply Rplus_le_compat; [ apply EF_cEF_maj | apply Rle_refl ].
  - replace 0 with (0 + 0) by ring; apply CV_plus;
      [ apply maj_cv0 | apply CUn_cv_mod0, cEF_cv; exact Hgt ].
Qed.

End Full.

Print Assumptions EF_cv.

(* ================================================================= *)
(*  END CEulerProductFull.v                                          *)
(*  EF s N = ∏_{p<=S N} (1-p^{-s})^{-1}  ->  zetaC s   for Re s > 1.   *)
(* ================================================================= *)
