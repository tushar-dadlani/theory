(* ================================================================= *)
(*  CEulerProductZeta.v  —  MILESTONE 1: zetaC(s) <> 0 for Re s > 1.    *)
(*                                                                    *)
(*  The truncated complex Euler product cEF s N converges to zetaC s   *)
(*  (CEulerProductConv.cEF_cv) and is bounded below in modulus by a    *)
(*  positive constant independent of N:                               *)
(*                                                                    *)
(*    |cEF s N| = ∏_{p≤S N} |Σ_{k≤N} (p^{-s})^k|                       *)
(*             ≥ ∏_{p≤S N} (1 - p^{-σ})²  =  (∏ (1 - p^{-σ}))²         *)
(*             = (1 / Zfactor)²  ≥  (1 / zeta_cont σ)²  > 0,           *)
(*                                                                    *)
(*  using the per-factor geometric bound |Σ_{k≤N} x^k| ≥ (1-|x|)²      *)
(*  (geom_sum_value) and the real Euler bound Zfactor ≤ zeta_cont σ    *)
(*  (EulerProductZetaCont.euler_factor_le_zeta_s).  Passing to the     *)
(*  limit (Rle_cv_lim) gives |zetaC s| ≥ (1/zeta_cont σ)² > 0, hence   *)
(*  zetaC s <> 0.  Axiom-clean.                                        *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia ZArith Znumtheory List QArith Arith.
Require Import ComplexField Cmodulus CexpFull CPowMul RootsOfUnity DirichletLEuler
        CSeries CDeriv CZeta CDirichlet CEulerFactorSmooth CEulerProductConv
        PrimeFactorizationN EulerReindex EulerProductR EulerProductZeta
        EulerProductZetaBound RecipSquareBound EulerProductZetaCont
        Ell2Zeta Ell2ZetaConverge Ell2ZetaCont ZetaContinuation.
Import ListNotations.
Open Scope R_scope.

(* ================================================================= *)
(*  0.  complex product modulus + small real-product helpers          *)
(* ================================================================= *)

Lemma Cmod_Cpow : forall a k, Cmod (Cpow a k) = (Cmod a) ^ k.
Proof.
  intros a k; induction k as [|k IH]; cbn [Cpow pow].
  - apply Cmod_C1.
  - rewrite Cmod_mul, IH; reflexivity.
Qed.

Lemma Cmod_Cwprod : forall l, Cmod (Cwprod l) = fold_right Rmult 1 (map Cmod l).
Proof.
  intro l; unfold Cwprod; induction l as [|a l IH]; cbn [fold_right map].
  - apply Cmod_C1.
  - rewrite Cmod_mul, IH; reflexivity.
Qed.

Lemma pow_le1 : forall t n, 0 <= t -> t <= 1 -> t ^ n <= 1.
Proof.
  intros t n Ht Ht1; induction n as [|n IH]; cbn [pow]; [ lra | nra ].
Qed.

Lemma Rprod_nonneg : forall (f : Z -> R) ps,
  (forall p, In p ps -> 0 <= f p) -> 0 <= fold_right Rmult 1 (map f ps).
Proof.
  intros f ps; induction ps as [|p ps IH]; intro H; cbn [map fold_right]; [ lra | ].
  apply Rmult_le_pos; [ apply H; left; reflexivity | apply IH; intros q Hq; apply H; right; exact Hq ].
Qed.

Lemma Rprod_map_le : forall (f g : Z -> R) ps,
  (forall p, In p ps -> 0 <= f p <= g p) ->
  fold_right Rmult 1 (map f ps) <= fold_right Rmult 1 (map g ps).
Proof.
  intros f g ps; induction ps as [|p ps IH]; intro H; cbn [map fold_right]; [ lra | ].
  apply Rmult_le_compat.
  - apply (proj1 (H p (in_eq p ps))).
  - apply Rprod_nonneg; intros q Hq; apply (proj1 (H q (in_cons p q ps Hq))).
  - apply (proj2 (H p (in_eq p ps))).
  - apply IH; intros q Hq; apply H; right; exact Hq.
Qed.

Lemma Rprod_sq : forall (f : Z -> R) ps,
  fold_right Rmult 1 (map (fun p => (f p) ^ 2) ps)
  = (fold_right Rmult 1 (map f ps)) ^ 2.
Proof.
  intros f ps; induction ps as [|p ps IH]; cbn [map fold_right]; [ ring | rewrite IH; ring ].
Qed.

Lemma Zfactor_pos : forall xs, (forall x, In x xs -> x < 1) -> 0 < Zfactor xs.
Proof.
  intros xs; induction xs as [|x xs IH]; intro H; unfold Zfactor in *; cbn [map fold_right]; [ lra | ].
  apply Rmult_lt_0_compat.
  - apply Rinv_0_lt_compat; pose proof (H x (in_eq x xs)); lra.
  - apply IH; intros y Hy; apply H; right; exact Hy.
Qed.

Lemma Rprod_one_minus_inv_Zfactor : forall xs, (forall x, In x xs -> x < 1) ->
  fold_right Rmult 1 (map (fun x => 1 - x) xs) = / Zfactor xs.
Proof.
  induction xs as [|x xs IH]; intro H; cbn [map fold_right].
  - unfold Zfactor; cbn [map fold_right]; rewrite Rinv_1; reflexivity.
  - rewrite (IH (fun y Hy => H y (or_intror Hy))).
    assert (Hx1 : 1 - x <> 0) by (pose proof (H x (in_eq x xs)); lra).
    assert (HZ : Zfactor xs <> 0)
      by (apply Rgt_not_eq, Zfactor_pos; intros y Hy; apply H; right; exact Hy).
    change (Zfactor (x :: xs)) with (/ (1 - x) * Zfactor xs); field; split; assumption.
Qed.

(* ================================================================= *)
(*  1.  the per-factor geometric lower bound |Σ_{k≤N} x^k| ≥ (1-|x|)²  *)
(* ================================================================= *)

Lemma cgeom_lower : forall x N, Cmod x < 1 ->
  (1 - Cmod x) ^ 2 <= Cmod (Csum (fun k => Cpow x k) (S N)).
Proof.
  intros x N Hx.
  assert (HxC1 : x <> C1) by (intro He; subst x; rewrite Cmod_C1 in Hx; lra).
  assert (HB : Cminus x C1 <> C0).
  { intro He; apply HxC1; replace x with (Cadd (Cminus x C1) C1) by ring; rewrite He; ring. }
  rewrite (geom_sum_value x (S N) HxC1); unfold Cdiv.
  rewrite Cmod_mul, Cmod_inv by exact HB.
  set (t := Cmod x) in *; assert (Ht0 : 0 <= t) by (unfold t; apply Cmod_nonneg).
  assert (Htsn1 : t ^ (S N) <= 1) by (apply pow_le1; lra).
  assert (Htsnt : t ^ (S N) <= t).
  { cbn [pow]; apply Rle_trans with (t * 1);
      [ apply Rmult_le_compat_l; [ exact Ht0 | apply pow_le1; lra ] | lra ]. }
  assert (HA : 1 - t <= Cmod (Cminus (Cpow x (S N)) C1)).
  { pose proof (Cmod_diff_le (Cpow x (S N)) C1) as HD.
    rewrite Cmod_C1, Cmod_Cpow in HD; fold t in HD.
    rewrite (Rabs_left1 (t ^ (S N) - 1)) in HD by lra; lra. }
  assert (HBle : Cmod (Cminus x C1) <= 1 + t).
  { pose proof (Cmod_triangle x (Copp C1)) as HT.
    replace (Cadd x (Copp C1)) with (Cminus x C1) in HT by ring.
    rewrite Cmod_opp, Cmod_C1 in HT; unfold t; lra. }
  assert (HBpos : 0 < Cmod (Cminus x C1)) by (apply Cmod_pos_ne0; exact HB).
  apply (Rmult_le_reg_r (Cmod (Cminus x C1)) _ _ HBpos).
  rewrite Rmult_assoc.
  rewrite Rinv_l by (apply Rgt_not_eq; exact HBpos).
  rewrite Rmult_1_r.
  apply Rle_trans with (1 - t); [ | exact HA ].
  replace ((1 - t) ^ 2) with ((1 - t) * (1 - t)) by ring.
  apply Rle_trans with ((1 - t) * (1 - t) * (1 + t)).
  - apply Rmult_le_compat_l; [ nra | exact HBle ].
  - nra.
Qed.

(* ================================================================= *)
(*  2.  positivity of zeta_cont on Re > 1                             *)
(* ================================================================= *)

Lemma zeta_cont_ge1 : forall sg (Hs0 : 0 < sg) (Hs1 : sg <> 1), 1 < sg ->
  1 <= zeta_cont sg Hs0 Hs1.
Proof.
  intros sg Hs0 Hs1 Hs.
  assert (Hg : Un_growing (fun N => diag_trace (z sg) N))
    by (intro n; rewrite !zeta_partition; apply dzeta_growing; lra).
  pose proof (growing_ineq (fun N => diag_trace (z sg) N) (zeta_cont sg Hs0 Hs1)
                Hg (operator_zeta_eq_cont sg Hs0 Hs1 Hs) 1) as Hle.
  cbv beta in Hle.
  assert (Hd1 : diag_trace (z sg) 1 = 1).
  { rewrite diag_trace_eq; cbn [seq map fold_right]; unfold z; cbn [Nat.eqb].
    rewrite INR_1, Rpower_base1; ring. }
  rewrite Hd1 in Hle; exact Hle.
Qed.

(* complex limit ⇒ modulus limit *)
Lemma CUn_cv_Cmod : forall u l, CUn_cv u l -> Un_cv (fun n => Cmod (u n)) (Cmod l).
Proof.
  intros u l H eps Heps; destruct (H eps Heps) as [N HN]; exists N; intros n Hn.
  specialize (HN n Hn); unfold R_dist.
  eapply Rle_lt_trans; [ apply Cmod_diff_le | exact HN ].
Qed.

(* ================================================================= *)
(*  3.  the modulus lower bound on the truncated Euler product         *)
(* ================================================================= *)

Section NonVanish.
Variable s : C.
Hypothesis Hgt : 1 < Re s.

Let sig := Re s.
Lemma Hg0 : 0 < sig. Proof. unfold sig; lra. Qed.
Lemma Hg1 : sig <> 1. Proof. unfold sig; lra. Qed.
Lemma Hggt : 1 < sig. Proof. unfold sig; exact Hgt. Qed.

Lemma Cmod_fug : forall p, Cmod (Cpw (IZR p) (Copp s)) = Rpower (IZR p) (- sig).
Proof.
  intro p; rewrite Cpw_mod; f_equal; unfold sig, Copp; cbn [Re]; ring.
Qed.

Lemma fug_lt1 : forall p, prime p -> Rpower (IZR p) (- sig) < 1.
Proof. intros p Hp; apply (fug_lt1_s sig p Hg0 Hp). Qed.

Lemma cEF_lower : forall N, (/ zeta_cont sig Hg0 Hg1) ^ 2 <= Cmod (cEF s N).
Proof.
  intro N; set (ps := primes_upto (S N)).
  assert (Hpr : Forall prime ps) by apply primes_upto_Forall.
  assert (Hnd : NoDup ps) by apply primes_upto_nodup.
  assert (Hlt1 : forall p, In p ps -> Rpower (IZR p) (- sig) < 1)
    by (intros p Hp; apply fug_lt1, (proj1 (Forall_forall prime ps) Hpr p Hp)).
  unfold cEF; fold ps; rewrite Cmod_Cwprod, map_map.
  apply Rle_trans with
    (fold_right Rmult 1 (map (fun p => (1 - Rpower (IZR p) (- sig)) ^ 2) ps)).
  - (* (/zeta_cont)^2 <= ∏ (1 - p^{-σ})² *)
    rewrite Rprod_sq.
    assert (Hpe : fold_right Rmult 1 (map (fun p => 1 - Rpower (IZR p) (- sig)) ps)
                = / Zfactor (map (fun p => Rpower (IZR p) (- sig)) ps)).
    { rewrite <- (map_map (fun p => Rpower (IZR p) (- sig)) (fun x => 1 - x)).
      apply Rprod_one_minus_inv_Zfactor.
      intros x Hx; apply in_map_iff in Hx; destruct Hx as [p [Hp Hpin]]; subst x; apply Hlt1; exact Hpin. }
    rewrite Hpe.
    assert (HZle : Zfactor (map (fun p => Rpower (IZR p) (- sig)) ps) <= zeta_cont sig Hg0 Hg1)
      by (apply (euler_factor_le_zeta_s sig Hg0 Hg1 Hggt ps Hpr Hnd)).
    assert (HZpos : 0 < Zfactor (map (fun p => Rpower (IZR p) (- sig)) ps))
      by (apply Zfactor_pos; intros x Hx; apply in_map_iff in Hx;
          destruct Hx as [p [Hp Hpin]]; subst x; apply Hlt1; exact Hpin).
    assert (Hzc : 0 < zeta_cont sig Hg0 Hg1)
      by (pose proof (zeta_cont_ge1 sig Hg0 Hg1 Hggt); lra).
    apply pow_incr; split.
    + apply Rlt_le, Rinv_0_lt_compat; exact Hzc.
    + apply Rinv_le_contravar; [ exact HZpos | exact HZle ].
  - (* ∏ (1 - p^{-σ})² <= ∏ |Σ_{k≤N} (p^{-s})^k| *)
    apply Rprod_map_le; intros p Hp; split.
    + apply pow2_ge_0.
    + rewrite <- Cmod_fug.
      apply cgeom_lower; rewrite Cmod_fug; apply Hlt1; exact Hp.
Qed.

(* ================================================================= *)
(*  4.  MILESTONE 1: zetaC(s) <> 0 for Re s > 1                        *)
(* ================================================================= *)

Theorem zetaC_nonzero : forall (H0 : 0 < Re s) (H1 : Cminus C1 s <> C0),
  zetaC s H0 H1 <> C0.
Proof.
  intros H0 H1.
  assert (Hzc : 0 < zeta_cont sig Hg0 Hg1)
    by (pose proof (zeta_cont_ge1 sig Hg0 Hg1 Hggt); lra).
  assert (Hclb : (/ zeta_cont sig Hg0 Hg1) ^ 2 <= Cmod (zetaC s H0 H1)).
  { apply Rle_cv_lim with (Un := fun _ : nat => (/ zeta_cont sig Hg0 Hg1) ^ 2)
                          (Vn := fun N : nat => Cmod (cEF s N)).
    - intro N; apply cEF_lower.
    - apply Un_cv_const.
    - apply CUn_cv_Cmod, (cEF_cv s Hgt H0 H1). }
  assert (Hpos : 0 < (/ zeta_cont sig Hg0 Hg1) ^ 2).
  { apply pow_lt, Rinv_0_lt_compat; exact Hzc. }
  intro Hc; rewrite Hc, Cmod_C0 in Hclb; lra.
Qed.

End NonVanish.

Print Assumptions zetaC_nonzero.

(* ================================================================= *)
(*  END CEulerProductZeta.v                                           *)
(*  zetaC(s) <> 0 for every complex s with Re s > 1 — the nontrivial   *)
(*  zeros of the operator zeta lie to the LEFT of Re s = 1 (the        *)
(*  boundary of the critical strip).  Uses the classical Reals axioms. *)
(* ================================================================= *)
