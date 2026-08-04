(* ================================================================= *)
(*  ThreeFourOne.v  —  the Mertens 3-4-1 product inequality.          *)
(*                                                                    *)
(*  For sigma > 1 and any tau:                                        *)
(*    |zeta(sigma)|^3 |zeta(sigma+i tau)|^4 |zeta(sigma+2 i tau)| >= 1.*)
(*                                                                    *)
(*  Route: per prime p the Euler factors satisfy                       *)
(*    |1-p^{-sigma}|^{-3} |1-p^{-(sigma+i tau)}|^{-4}                   *)
(*        |1-p^{-(sigma+2 i tau)}|^{-1} >= 1,                          *)
(*  the logarithmic form of which is exactly per_prime_log             *)
(*  (EulerFactorLog) with r = p^{-sigma}, phi = tau ln p.  Taking the  *)
(*  product over primes <= S N gives the same inequality for the finite*)
(*  complex Euler products EF, and EF -> zetaC (CEulerProductFull)      *)
(*  passes it to the limit.  Axiom-clean.                              *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia ZArith Znumtheory List.
Require Import ComplexField Cmodulus CexpFull CPowBase RootsOfUnity CDeriv
        CSeries EulerProductZeta CEulerProductZeta CEulerProductConv CZeta
        EulerFactorLog LogGeomSeries CEulerProductFull.
Import ListNotations.
Open Scope R_scope.

(* ================================================================= *)
(*  0.  small real-analysis helpers                                   *)
(* ================================================================= *)

Lemma exp_le' : forall x y, x <= y -> exp x <= exp y.
Proof.
  intros x y H; destruct (Rle_lt_or_eq_dec x y H) as [Hlt | Heq];
    [ apply Rlt_le, exp_increasing; exact Hlt | subst; apply Rle_refl ].
Qed.

Lemma ln_sqrt' : forall x, 0 < x -> ln (sqrt x) = / 2 * ln x.
Proof.
  intros x Hx; assert (Hs : 0 < sqrt x) by (apply sqrt_lt_R0; exact Hx).
  assert (H : ln x = ln (sqrt x) + ln (sqrt x)).
  { rewrite <- ln_mult by exact Hs; rewrite sqrt_sqrt by lra; reflexivity. }
  lra.
Qed.

Lemma ln_powS : forall x n, 0 < x -> ln (x ^ n) = INR n * ln x.
Proof.
  intros x n Hx; induction n as [|n IH]; cbn [pow].
  - rewrite ln_1; simpl (INR 0); ring.
  - rewrite ln_mult by (try lra; apply pow_lt; exact Hx).
    rewrite IH, S_INR; ring.
Qed.

Lemma Un_cv_pow : forall u a n, Un_cv u a -> Un_cv (fun N => (u N) ^ n) (a ^ n).
Proof.
  intros u a n H; induction n as [|n IH]; cbn [pow].
  - apply Un_cv_const.
  - apply CV_mult; [ exact H | exact IH ].
Qed.

(* ================================================================= *)
(*  1.  list-product homomorphisms                                    *)
(* ================================================================= *)

Lemma Rprod_ones : forall ps : list Z, fold_right Rmult 1 (map (fun _ => 1) ps) = 1.
Proof.
  intro ps; induction ps as [|p ps IH]; cbn [map fold_right]; [ reflexivity | rewrite IH; ring ].
Qed.

Lemma Rprod_mult : forall (f g : Z -> R) ps,
  fold_right Rmult 1 (map (fun p => f p * g p) ps)
  = (fold_right Rmult 1 (map f ps)) * (fold_right Rmult 1 (map g ps)).
Proof.
  intros f g ps; induction ps as [|p ps IH]; cbn [map fold_right]; [ ring | rewrite IH; ring ].
Qed.

Lemma Rprod_pow : forall (f : Z -> R) k ps,
  fold_right Rmult 1 (map (fun p => (f p) ^ k) ps)
  = (fold_right Rmult 1 (map f ps)) ^ k.
Proof.
  intros f k ps; induction ps as [|p ps IH]; cbn [map fold_right].
  - rewrite pow1; reflexivity.
  - rewrite IH, <- Rpow_mult_distr; reflexivity.
Qed.

(* ================================================================= *)
(*  2.  the per-prime Euler factor as a real quantity                 *)
(* ================================================================= *)

(* Qfac a b p = |1 - p^{-(a + i b)}|^{-1} *)
Definition Qfac (a b : R) (p : Z) : R :=
  / Cmod (Cminus C1 (Cpw (IZR p) (Copp (mkC a b)))).

(* the squared modulus D = 1 - 2 r cos(b ln p) + r^2,  r = p^{-a} *)
Lemma Dexpr : forall a b p,
  Cnorm2 (Cminus C1 (Cpw (IZR p) (Copp (mkC a b))))
  = 1 - 2 * Rpower (IZR p) (- a) * cos (b * ln (IZR p)) + (Rpower (IZR p) (- a)) ^ 2.
Proof.
  intros a b p.
  unfold Cnorm2, Cminus, C1; cbn [Re Im].
  rewrite Re_Cpw, Im_Cpw.
  replace (Re (Copp (mkC a b))) with (- a) by (unfold Copp; cbn [Re]; ring).
  replace (Im (Copp (mkC a b))) with (- b) by (unfold Copp; cbn [Im]; ring).
  replace (- b * ln (IZR p)) with (- (b * ln (IZR p))) by ring.
  rewrite cos_neg, sin_neg.
  set (r := Rpower (IZR p) (- a)).
  set (c := cos (b * ln (IZR p))).
  set (sn := sin (b * ln (IZR p))).
  pose proof (sin2_cos2 (b * ln (IZR p))) as Hpy; unfold Rsqr in Hpy; fold c sn in Hpy.
  nra.
Qed.

Lemma r_bounds : forall a p, 2 <= IZR p -> 1 < a -> 0 < Rpower (IZR p) (- a) < 1.
Proof.
  intros a p Hp Ha; split.
  - unfold Rpower; apply exp_pos.
  - apply Rlt_le_trans with (Rpower (IZR p) 0).
    + apply Rpower_lt; [ lra | lra ].
    + rewrite Rpower_O by lra; apply Rle_refl.
Qed.

Lemma Dpos : forall a b p, 2 <= IZR p -> 1 < a ->
  0 < 1 - 2 * Rpower (IZR p) (- a) * cos (b * ln (IZR p)) + (Rpower (IZR p) (- a)) ^ 2.
Proof.
  intros a b p Hp Ha; pose proof (r_bounds a p Hp Ha) as [Hr0 Hr1].
  pose proof (COS_bound (b * ln (IZR p))) as [Hc0 Hc1].
  set (r := Rpower (IZR p) (- a)) in *; set (c := cos (b * ln (IZR p))) in *.
  nra.
Qed.

Lemma den_ne0' : forall a b p, 2 <= IZR p -> 1 < a ->
  Cminus C1 (Cpw (IZR p) (Copp (mkC a b))) <> C0.
Proof.
  intros a b p Hp Ha He.
  pose proof (Dpos a b p Hp Ha) as HD; rewrite <- Dexpr in HD.
  rewrite He in HD; unfold Cnorm2, C0 in HD; cbn [Re Im] in HD; lra.
Qed.

Lemma Cmod_den_pos : forall a b p, 2 <= IZR p -> 1 < a ->
  0 < Cmod (Cminus C1 (Cpw (IZR p) (Copp (mkC a b)))).
Proof.
  intros a b p Hp Ha; apply Cmod_pos_ne0; apply den_ne0'; assumption.
Qed.

Lemma Qfac_pos : forall a b p, 2 <= IZR p -> 1 < a -> 0 < Qfac a b p.
Proof.
  intros a b p Hp Ha; unfold Qfac; apply Rinv_0_lt_compat, Cmod_den_pos; assumption.
Qed.

(* the bridge: ln(Qfac) is the log-series limit L *)
Lemma Qfac_L : forall a b p, 2 <= IZR p -> 1 < a ->
  ln (Qfac a b p) = L (b * ln (IZR p)) (Rpower (IZR p) (- a)).
Proof.
  intros a b p Hp Ha; unfold Qfac, Cmod.
  rewrite Dexpr.
  rewrite ln_Rinv by (apply sqrt_lt_R0, Dpos; assumption).
  rewrite ln_sqrt' by (apply Dpos; assumption).
  unfold L; ring.
Qed.

(* ================================================================= *)
(*  3.  the per-prime product inequality                              *)
(* ================================================================= *)

Lemma per_prime_prod : forall a b p, 2 <= IZR p -> 1 < a ->
  1 <= (Qfac a 0 p) ^ 3 * (Qfac a b p) ^ 4 * (Qfac a (2 * b) p).
Proof.
  intros a b p Hp Ha.
  set (A := Qfac a 0 p); set (B := Qfac a b p); set (C := Qfac a (2 * b) p).
  assert (HA : 0 < A) by (unfold A; apply Qfac_pos; assumption).
  assert (HB : 0 < B) by (unfold B; apply Qfac_pos; assumption).
  assert (HC : 0 < C) by (unfold C; apply Qfac_pos; assumption).
  set (y := A ^ 3 * B ^ 4 * C).
  assert (Hy : 0 < y).
  { unfold y; apply Rmult_lt_0_compat; [ apply Rmult_lt_0_compat | ].
    - apply pow_lt; exact HA.
    - apply pow_lt; exact HB.
    - exact HC. }
  (* 0 <= ln y = 3 ln A + 4 ln B + ln C = per_prime_log >= 0 *)
  assert (HA3 : 0 < A ^ 3) by (apply pow_lt; exact HA).
  assert (HB4 : 0 < B ^ 4) by (apply pow_lt; exact HB).
  assert (HAB : 0 < A ^ 3 * B ^ 4) by (apply Rmult_lt_0_compat; assumption).
  assert (Hlny : ln y = INR 3 * ln A + INR 4 * ln B + ln C).
  { unfold y.
    rewrite (ln_mult (A ^ 3 * B ^ 4) C) by assumption.
    rewrite (ln_mult (A ^ 3) (B ^ 4)) by assumption.
    rewrite (ln_powS A 3) by exact HA; rewrite (ln_powS B 4) by exact HB; reflexivity. }
  assert (Hpp : 0 <= 3 * ln A + 4 * ln B + ln C).
  { unfold A, B, C; rewrite !Qfac_L by assumption.
    replace (0 * ln (IZR p)) with 0 by ring.
    replace (2 * b * ln (IZR p)) with (2 * (b * ln (IZR p))) by ring.
    apply per_prime_log; pose proof (r_bounds a p Hp Ha); lra. }
  assert (Hlny0 : 0 <= ln y) by (rewrite Hlny; simpl (INR 3); simpl (INR 4); lra).
  (* 1 = exp 0 <= exp (ln y) = y *)
  rewrite <- exp_0.
  apply Rle_trans with (exp (ln y)); [ apply exp_le'; exact Hlny0 | ].
  rewrite exp_ln by exact Hy; apply Rle_refl.
Qed.

(* ================================================================= *)
(*  4.  the finite Euler products                                     *)
(* ================================================================= *)

Definition EFmod (a b : R) (N : nat) : R :=
  fold_right Rmult 1 (map (Qfac a b) (primes_upto (S N))).

Lemma EFmod_eq : forall a b N, 1 < a -> EFmod a b N = Cmod (EF (mkC a b) N).
Proof.
  intros a b N Ha; unfold EFmod, EF.
  rewrite Cmod_Cwprod, map_map.
  apply f_equal, map_ext_in; intros p Hp.
  assert (Hp2 : 2 <= IZR p)
    by (apply IZR_le; pose proof (primes_upto_prime (S N) p Hp) as Hpr; destruct Hpr; lia).
  unfold Qfac, efac, xp.
  rewrite Cmod_inv by (apply den_ne0'; assumption); reflexivity.
Qed.

Lemma finite_ineq : forall a b N, 1 < a ->
  1 <= (EFmod a 0 N) ^ 3 * (EFmod a b N) ^ 4 * (EFmod a (2 * b) N).
Proof.
  intros a b N Ha.
  (* product of per-prime factors >= 1 *)
  assert (Hprod :
    1 <= fold_right Rmult 1
           (map (fun p => (Qfac a 0 p) ^ 3 * (Qfac a b p) ^ 4 * (Qfac a (2 * b) p))
                (primes_upto (S N)))).
  { apply Rle_trans with
      (fold_right Rmult 1 (map (fun _ : Z => 1) (primes_upto (S N)))).
    - rewrite Rprod_ones; apply Rle_refl.
    - apply Rprod_map_le; intros p Hp; split; [ lra | ].
      apply per_prime_prod; [ | exact Ha ].
      apply IZR_le; pose proof (primes_upto_prime (S N) p Hp) as Hpr; destruct Hpr; lia. }
  (* decompose the product *)
  rewrite (Rprod_mult (fun p => (Qfac a 0 p) ^ 3 * (Qfac a b p) ^ 4) (Qfac a (2 * b))) in Hprod.
  rewrite (Rprod_mult (fun p => (Qfac a 0 p) ^ 3) (fun p => (Qfac a b p) ^ 4)) in Hprod.
  rewrite (Rprod_pow (Qfac a 0) 3), (Rprod_pow (Qfac a b) 4) in Hprod.
  unfold EFmod; exact Hprod.
Qed.

(* ================================================================= *)
(*  5.  pass to the limit: the product inequality for zetaC           *)
(* ================================================================= *)

Theorem tfo_zeta : forall a b (Ha : 1 < a)
  (H00 : 0 < Re (mkC a 0)) (H01 : Cminus C1 (mkC a 0) <> C0)
  (H10 : 0 < Re (mkC a b)) (H11 : Cminus C1 (mkC a b) <> C0)
  (H20 : 0 < Re (mkC a (2 * b))) (H21 : Cminus C1 (mkC a (2 * b)) <> C0),
  1 <= (Cmod (zetaC (mkC a 0) H00 H01)) ^ 3
       * (Cmod (zetaC (mkC a b) H10 H11)) ^ 4
       * (Cmod (zetaC (mkC a (2 * b)) H20 H21)).
Proof.
  intros a b Ha H00 H01 H10 H11 H20 H21.
  set (a0 := Cmod (zetaC (mkC a 0) H00 H01)).
  set (a1 := Cmod (zetaC (mkC a b) H10 H11)).
  set (a2 := Cmod (zetaC (mkC a (2 * b)) H20 H21)).
  apply Rle_cv_lim with
    (Un := fun _ : nat => 1)
    (Vn := fun N => (EFmod a 0 N) ^ 3 * (EFmod a b N) ^ 4 * (EFmod a (2 * b) N)).
  - intro N; apply finite_ineq; exact Ha.
  - apply Un_cv_const.
  - (* Vn -> a0^3 * a1^4 * a2 *)
    apply (Un_cv_ext
             (fun N => (Cmod (EF (mkC a 0) N)) ^ 3
                       * (Cmod (EF (mkC a b) N)) ^ 4
                       * (Cmod (EF (mkC a (2 * b)) N)))).
    + intro N; rewrite !EFmod_eq by exact Ha; reflexivity.
    + apply CV_mult; [ apply CV_mult | ].
      * apply Un_cv_pow, CUn_cv_Cmod, EF_cv; exact Ha.
      * apply Un_cv_pow, CUn_cv_Cmod, EF_cv; exact Ha.
      * apply CUn_cv_Cmod, EF_cv; exact Ha.
Qed.

Print Assumptions tfo_zeta.

(* ================================================================= *)
(*  END ThreeFourOne.v                                               *)
(*  |zeta(s)|^3 |zeta(s+it)|^4 |zeta(s+2it)| >= 1 for Re s > 1.        *)
(* ================================================================= *)
