(* ================================================================= *)
(*  XiHDiskBound.v  —  steps 3 and 4 of the SubQuadLog chain:          *)
(*  ln |H| bounded on a DISK, via a circle that misses the zeros.      *)
(*                                                                    *)
(*    xi_H_disk_bound : for every r >= 8 there is a circle radius      *)
(*      rr in [2r, 4r] with                                            *)
(*                                                                    *)
(*        ln |Hglob z|  <=  ln 4 + Lxi rr - LBexp rr del K             *)
(*                                                                    *)
(*      for EVERY z with |z| <= r.                                     *)
(*                                                                    *)
(*  THE WHOLE POINT is that the bound holds on a DISK while the        *)
(*  estimate is only available on a CIRCLE.  |H| = |xi|/|P| is         *)
(*  worthless at a zero -- P vanishes there and the quotient bound     *)
(*  blows up even though H itself is entire and zero-free.  So the     *)
(*  estimate is made on the zero-avoiding circle of XiGoodRadius and   *)
(*  then carried inward by CCauchyEstimate.disk_value_bound, which     *)
(*  stands in for the maximum-modulus principle this development does  *)
(*  not have.  The band [2r, 4r] is exactly what makes rr/2 >= r, so   *)
(*  the half-disk the Cauchy estimate controls covers |z| <= r.        *)
(*                                                                    *)
(*  The circle step is multiplicative and short:                       *)
(*      |H w| . exp(LBexp)  <=  |H w| . |P w|  =  |xi w|  <=  XiM rr,  *)
(*  the outer bounds being XiProdLower.xi_prod_lower_circle and        *)
(*  XiGrowthBound.XiC_growth.  Logarithms are taken only at the very   *)
(*  end, where Hglob_ne0 guarantees the argument is positive.          *)
(*                                                                    *)
(*  What remains for SubQuadLog is arithmetic: that                    *)
(*  ln 4 + Lxi rr - LBexp is o(r^2), and packaging it as a monotone    *)
(*  majorant.  Axiom-clean.                                            *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia List.
Require Import ComplexField Cmodulus Holomorphic CDeriv CHoloCcontC CSegInt
        CPathIntegral CSeries CInfProd CCauchyEstimate PerronRemovable
        JensenMultiZero CZeroListFactor RiemannXiEntire XiGrowthBound
        XiZeroCount XiHgrow XiZeroEnum XiHadamardProd XiHcof XiProdLimit
        XiHadamardLocal XiHadamardGlue XiProdLower XiLnBound.
Open Scope R_scope.

Section HBound.

Variable rho : nat -> C.
Variable Gseq : nat -> C -> C.
Hypothesis HZ : ZeroEnumG rho Gseq.
Hypothesis Hlow : forall n, 1 <= Cmod (rho n).

Notation En := (HE rho Gseq HZ).
Notation Hg := (Hglob rho Gseq HZ Hlow).
Notation Pf := (Pinf rho Gseq HZ Hlow).

Lemma Hg_ptcont : ptcont Hg.
Proof. exact (holo_ptcont Hg (Hglob_holo rho Gseq HZ Hlow)). Qed.

Theorem xi_H_disk_bound : forall r, 8 <= r ->
  exists (rr del : R) (K : nat),
    2 * r <= rr /\ rr <= 4 * r /\
    forall z, Cmod z <= r ->
      ln (Cmod (Hg z)) <= ln 4 + Lxi rr - LBexp rr del K.
Proof.
  intros r Hr.
  destruct (xi_prod_lower_circle rho En Hlow r ltac:(lra))
    as [rr [del [K [Hlo [Hhi [Hd0 [Hdr [Hdb [HK1 [HK2 Hlb]]]]]]]]]].
  exists rr, del, K.
  assert (HRr : 0 < rr) by lra.
  assert (Hrr8 : 8 <= rr) by lra.
  pose proof (XiM_pos rr) as HXM.
  set (B := XiM rr * exp (- LBexp rr del K)).
  assert (HB : 0 < B)
    by (unfold B; apply Rmult_lt_0_compat; [ exact HXM | apply exp_pos ]).
  (* ---- the circle bound ---- *)
  assert (Hcirc : forall w, Cmod w = rr -> Cmod (Hg w) <= B).
  { intros w Hw.
    pose proof (Hlb w Hw (Pf w) (Pinf_spec rho Gseq HZ Hlow w)) as HPge.
    pose proof (XiC_growth w) as Hxi. rewrite Hw in Hxi.
    assert (Hfac : Cmod (XiC w) = Cmod (Hg w) * Cmod (Pf w))
      by (rewrite (Hglob_id rho Gseq HZ Hlow w); apply Cmod_mul).
    assert (Hgn : 0 <= Cmod (Hg w)) by apply Cmod_nonneg.
    assert (Hstep : Cmod (Hg w) * exp (LBexp rr del K) <= XiM rr).
    { apply Rle_trans with (Cmod (Hg w) * Cmod (Pf w));
        [ apply Rmult_le_compat_l; assumption | ].
      rewrite <- Hfac. unfold XiM. exact Hxi. }
    assert (Hcancel : exp (- LBexp rr del K) * exp (LBexp rr del K) = 1).
    { rewrite <- exp_plus.
      replace (- LBexp rr del K + LBexp rr del K) with 0 by ring.
      apply exp_0. }
    unfold B.
    apply (Rmult_le_reg_r (exp (LBexp rr del K))); [ apply exp_pos | ].
    replace (XiM rr * exp (- LBexp rr del K) * exp (LBexp rr del K))
      with (XiM rr * (exp (- LBexp rr del K) * exp (LBexp rr del K))) by ring.
    rewrite Hcancel, Rmult_1_r. exact Hstep. }
  (* ---- carried inward ---- *)
  split; [ exact Hlo | ]. split; [ exact Hhi | ].
  intros z Hz.
  assert (HzR : Cmod z <= rr / 2) by lra.
  assert (Hdisk : Cmod (Hg z) <= 4 * B).
  { apply (disk_value_bound Hg rr B z HRr Hg_ptcont
             (fun u => Hcirc (arc rr u) (Cmod_arc rr u ltac:(lra))) HzR).
    intros w _. apply (Hglob_holo rho Gseq HZ Hlow). }
  (* ---- take logs ---- *)
  assert (Hne : Cmod (Hg z) > 0).
  { destruct (Cmod_nonneg (Hg z)) as [Hlt | Heq]; [ exact Hlt | exfalso ].
    apply (Hglob_ne0 rho Gseq HZ Hlow z). apply (proj1 (Cmod0 _)). lra. }
  apply Rle_trans with (ln (4 * B)); [ apply ln_le_mono; lra | ].
  rewrite ln_mult by lra. unfold B.
  rewrite ln_mult by (try lra; apply exp_pos).
  rewrite ln_exp.
  pose proof (XiM_ln_bound rr Hrr8). lra.
Qed.

End HBound.

Print Assumptions xi_H_disk_bound.
