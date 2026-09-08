(* ================================================================= *)
(*  CTwistedEuler.v  --  THE ANALYTIC EULER PRODUCT FOR L(s,chi).      *)
(*                                                                    *)
(*      L(s,chi)  =  prod_{q prime} (1 - chi(q) q^{-s})^{-1}           *)
(*                                                          (Re s > 1)*)
(*                                                                    *)
(*  One such series for each of the p-1 characters mod each prime p,   *)
(*  hence infinitely many genuine prime series.  This is the object    *)
(*  DirichletLEuler stops short of: its Llocal is a truncated sum in a *)
(*  formal variable never set to q^{-s}, and its header concedes that  *)
(*  assembling the infinite product "stays prose".                     *)
(*                                                                    *)
(*  Mirror of CEulerProductFull's Section Full.  The whole quantitative*)
(*  scaffolding q0 = 2^{-Re s}, M = 1/(1-q0), q = M q0 < 1 carries over *)
(*  UNCHANGED, because |chi(q) q^{-s}| <= |q^{-s}| <= q0 -- the twist   *)
(*  never enlarges a modulus.  In the original, the coefficient is     *)
(*  unfolded in exactly one lemma (xp_mod_le); here Fchi_mod_q0 plays   *)
(*  that role and nothing else changes.                               *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia ZArith Znumtheory List QArith.
Require Import ComplexField Cmodulus CexpFull CPowMul CPowBase CSeries
        RootsOfUnity DirichletLEuler PrimonGas PrimeFactorizationN
        EulerReindex EulerProductR EulerProductZeta EulerProductZetaBound
        EulerProductZetaCont RecipSquareBound Ell2Zeta Ell2ZetaCont
        ZmodOrder DirichletModP CharModulus CEulerReindexGen CTwistedCoeff
        CLSeries CEulerFactorSmooth CEulerProductConv CEulerProductFull
        CTwistedSmooth CCauchyCont CDeriv LogGeomSeries.
Import ListNotations.
Open Scope R_scope.

Lemma Un_cv_ext_loc : forall (u v : nat -> R) l,
  (forall n, u n = v n) -> Un_cv u l -> Un_cv v l.
Proof.
  intros u v l He Hu eps Heps. destruct (Hu eps Heps) as [N HN].
  exists N. intros n Hn. rewrite <- He. apply HN; exact Hn.
Qed.

Section TwFull.

Variable p g a : nat.
Hypothesis Hp : prime (Z.of_nat p).
Hypothesis Hg : (1 <= g <= p - 1)%nat.
Hypothesis Hord : ord p g = (p - 1)%nat.

Variable s : C.
Hypothesis Hgt : 1 < Re s.

Let q0 := Rpower 2 (- Re s).
Let M := / (1 - q0).

Definition efchi (q : Z) : C := Cinv (Cminus C1 (Fchi p g a s q)).
Definition cfchi (N : nat) (q : Z) : C :=
  Csum (fun k => Cpow (Fchi p g a s q) k) (S N).
Definition LF (N : nat) : C := Cwprod (map efchi (primes_upto (S N))).

(* --- the constants, verbatim from Section Full --- *)

Lemma tq0_pos : 0 < q0.
Proof. unfold q0, Rpower; apply exp_pos. Qed.

Lemma tq0_half : q0 < / 2.
Proof.
  unfold q0. apply Rlt_le_trans with (Rpower 2 (- (1))).
  - apply Rpower_lt; lra.
  - rewrite Rpower_Ropp, Rpower_1 by lra; apply Rle_refl.
Qed.

Lemma tMpos : 0 < M.
Proof. unfold M; apply Rinv_0_lt_compat; pose proof tq0_half; lra. Qed.

Lemma tM_def : M * (1 - q0) = 1.
Proof. unfold M; rewrite Rinv_l; [ reflexivity | pose proof tq0_half; lra ]. Qed.

Lemma tM_ge1 : 1 <= M.
Proof. pose proof tM_def; pose proof tMpos; pose proof tq0_pos; nra. Qed.

Let q := M * q0.

Lemma tq_pos : 0 < q.
Proof. unfold q; apply Rmult_lt_0_compat; [ apply tMpos | apply tq0_pos ]. Qed.

Lemma tq_lt1 : q < 1.
Proof. unfold q; pose proof tM_def; pose proof tq0_half; pose proof tMpos; nra. Qed.

(* --- per-factor estimates: the ONLY place the coefficient is opened --- *)

Lemma Fchi_q0 : forall q1, (2 <= IZR q1) -> Cmod (Fchi p g a s q1) <= q0.
Proof. intros q1 Hq1; apply (Fchi_mod_q0 p g a s ltac:(lra) q1 Hq1). Qed.

Lemma tden_low : forall q1, (2 <= IZR q1) ->
  1 - q0 <= Cmod (Cminus C1 (Fchi p g a s q1)).
Proof.
  intros q1 Hq1; pose proof (Cmod_diff_le C1 (Fchi p g a s q1)) as HD.
  rewrite Cmod_C1_loc in HD.
  pose proof (Cmod_nonneg (Fchi p g a s q1)) as Hn.
  pose proof (Fchi_q0 q1 Hq1) as Hxq. pose proof tq0_half.
  rewrite Rabs_right in HD by lra; lra.
Qed.

Lemma tden_ne0 : forall q1, (2 <= IZR q1) -> Cminus C1 (Fchi p g a s q1) <> C0.
Proof.
  intros q1 Hq1 He; pose proof (tden_low q1 Hq1) as Hl; pose proof tq0_half.
  rewrite He, (proj2 (Cmod0 C0) eq_refl) in Hl; lra.
Qed.

Lemma tefac_mod_le : forall q1, (2 <= IZR q1) -> Cmod (efchi q1) <= M.
Proof.
  intros q1 Hq1; unfold efchi.
  rewrite Cmod_inv by (apply tden_ne0; exact Hq1).
  unfold M; apply Rinv_le_contravar;
    [ pose proof tq0_half; lra | apply tden_low; exact Hq1 ].
Qed.

Lemma tcfac_mod_le : forall N q1, (2 <= IZR q1) -> Cmod (cfchi N q1) <= M.
Proof.
  intros N q1 Hq1; unfold cfchi.
  set (t := Cmod (Fchi p g a s q1)).
  assert (Ht0 : 0 <= t) by (unfold t; apply Cmod_nonneg).
  assert (Htq : t <= q0) by (unfold t; apply Fchi_q0; exact Hq1).
  pose proof tq0_half as Hh.
  assert (Ht1 : t <> 1) by lra.
  eapply Rle_trans; [ apply Cmod_Csum_le | ].
  rewrite (sum_eq (fun k => Cmod (Cpow (Fchi p g a s q1) k)) (fun k => t ^ k))
    by (intros i _; unfold t; apply Cmod_Cpow).
  rewrite tech3 by exact Ht1.
  assert (Htsn : 0 <= t ^ (S N)) by (apply pow_le; exact Ht0).
  apply Rle_trans with (/ (1 - t)).
  - unfold Rdiv; rewrite <- (Rmult_1_l (/ (1 - t))) at 2.
    apply Rmult_le_compat_r; [ apply Rlt_le, Rinv_0_lt_compat; lra | lra ].
  - unfold M; apply Rinv_le_contravar; lra.
Qed.

Lemma tfactor_diff_le : forall N q1, (2 <= IZR q1) ->
  Cmod (Cminus (efchi q1) (cfchi N q1)) <= q0 ^ (S N) * M.
Proof.
  intros N q1 Hq1; unfold efchi, cfchi.
  rewrite geom_tail_id by (apply tden_ne0; exact Hq1).
  rewrite Cmod_mul, Cmod_Cpow, Cmod_inv by (apply tden_ne0; exact Hq1).
  apply Rmult_le_compat.
  - apply pow_le, Cmod_nonneg.
  - apply Rlt_le, Rinv_0_lt_compat, Cmod_pos_ne0; apply tden_ne0; exact Hq1.
  - apply pow_incr; split; [ apply Cmod_nonneg | apply Fchi_q0; exact Hq1 ].
  - unfold M; apply Rinv_le_contravar;
      [ pose proof tq0_half; lra | apply tden_low; exact Hq1 ].
Qed.

Lemma cLF_eq : forall N,
  cLF p g a s N = Cwprod (map (cfchi N) (primes_upto (S N))).
Proof. intro N; reflexivity. Qed.

Lemma LF_cLF_diff : forall N,
  Cmod (Cminus (LF N) (cLF p g a s N))
  <= INR (length (primes_upto (S N))) * M ^ (length (primes_upto (S N)))
     * (q0 ^ (S N) * M).
Proof.
  intro N; unfold LF; rewrite cLF_eq.
  assert (Hp2 : forall q1, In q1 (primes_upto (S N)) -> (2 <= IZR q1)).
  { intros q1 Hin; apply IZR_le.
    pose proof (primes_upto_prime (S N) q1 Hin) as Hpr; destruct Hpr; lia. }
  apply Cwprod_diff_bound.
  - apply tM_ge1.
  - apply Rmult_le_pos; [ apply pow_le, Rlt_le, tq0_pos | apply Rlt_le, tMpos ].
  - intros q1 Hin; apply tefac_mod_le, Hp2; exact Hin.
  - intros q1 Hin; apply tcfac_mod_le, Hp2; exact Hin.
  - intros q1 Hin; apply tfactor_diff_le, Hp2; exact Hin.
Qed.

Lemma tmaj_cv0 : Un_cv (fun N => M ^ 2 * (INR (S (S N)) * q ^ (S N))) 0.
Proof.
  replace 0 with (M ^ 2 * 0) by ring.
  apply CV_mult; [ apply Un_cv_const | ].
  apply (Un_cv_ext_loc (fun N => INR (S N) * q ^ (S N) + q ^ (S N))).
  - intro n; rewrite (S_INR (S n)); ring.
  - replace 0 with (0 + 0) by ring; apply CV_plus.
    + apply (Un_cv_S (fun n => INR n * q ^ n) 0); apply nqn_cv0; split;
        [ apply Rlt_le, tq_pos | apply tq_lt1 ].
    + apply (Un_cv_S (fun n => q ^ n) 0); apply pow_cv0;
        rewrite Rabs_right by (apply Rle_ge, Rlt_le, tq_pos); apply tq_lt1.
Qed.

Lemma LF_cLF_maj : forall N,
  Cmod (Cminus (LF N) (cLF p g a s N)) <= M ^ 2 * (INR (S (S N)) * q ^ (S N)).
Proof.
  intro N; eapply Rle_trans; [ apply LF_cLF_diff | ].
  set (len := length (primes_upto (S N))).
  assert (Hlen : (len <= S (S N))%nat) by (unfold len; apply primes_upto_len).
  assert (HM1 : 1 <= M) by apply tM_ge1.
  assert (Hq00 : 0 <= q0) by (apply Rlt_le, tq0_pos).
  assert (HM0 : 0 <= M) by (apply Rlt_le, tMpos).
  assert (HMpow : M ^ (S (S N)) = M ^ (S N) * M)
    by (replace (S (S N)) with (S N + 1)%nat by lia; rewrite pow_add; simpl; ring).
  assert (HpowB : M ^ len <= M ^ (S N) * M)
    by (rewrite <- HMpow; apply Rle_pow; [ exact HM1 | exact Hlen ]).
  assert (HpowN : 0 <= M ^ (S N)) by (apply pow_le; exact HM0).
  assert (Hq0N : 0 <= q0 ^ (S N)) by (apply pow_le; exact Hq00).
  assert (HlenN : INR len <= INR (S (S N))) by (apply le_INR; exact Hlen).
  assert (Hlen0 : 0 <= INR len) by apply pos_INR.
  assert (Hpl0 : 0 <= M ^ len) by (apply pow_le; exact HM0).
  assert (HqB : q ^ (S N) = M ^ (S N) * q0 ^ (S N))
    by (unfold q; rewrite Rpow_mult_distr; reflexivity).
  apply Rle_trans with ((INR (S (S N)) * (M ^ (S N) * M)) * (q0 ^ (S N) * M)).
  - apply Rmult_le_compat_r.
    + apply Rmult_le_pos; [ exact Hq0N | exact HM0 ].
    + apply Rmult_le_compat; [ exact Hlen0 | exact Hpl0 | exact HlenN | exact HpowB ].
  - apply Req_le; rewrite HqB; ring.
Qed.

(* ================================================================= *)
(*  THE EULER PRODUCT                                                 *)
(* ================================================================= *)
Theorem dirichlet_L_euler_product : forall Lval,
  Cseries_cv (Lterm p g a s) Lval -> CUn_cv LF Lval.
Proof.
  intros Lval HL.
  apply (CUn_cv_bound LF Lval
           (fun N => M ^ 2 * (INR (S (S N)) * q ^ (S N))
                     + Cmod (Cminus (cLF p g a s N) Lval))).
  - intro N.
    replace (Cminus (LF N) Lval)
      with (Cadd (Cminus (LF N) (cLF p g a s N)) (Cminus (cLF p g a s N) Lval))
      by ring.
    eapply Rle_trans; [ apply Cmod_triangle | ].
    apply Rplus_le_compat; [ apply LF_cLF_maj | apply Rle_refl ].
  - replace 0 with (0 + 0) by ring; apply CV_plus;
      [ apply tmaj_cv0
      | apply CUn_cv_mod0, (cLF_cv p g a Hp Hg Hord s Hgt Lval HL) ].
Qed.

(* NOTE.  L(s,chi) <> 0 on Re s > 1 does NOT follow from the above without
   a lower bound on the infinite product (the partial products' trivial
   lower bound (1/(1+q0))^len tends to 0).  The honest route is
   convergence of prod (1 - chi(q) q^{-s}) to a nonzero limit, which needs
   infinite-product machinery beyond this file.  Left out rather than
   admitted. *)

End TwFull.

Print Assumptions dirichlet_L_euler_product.

(* ================================================================= *)
(*  END CTwistedEuler.v                                               *)
(* ================================================================= *)
