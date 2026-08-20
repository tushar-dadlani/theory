(* ================================================================= *)
(*  XiLogDerivZeros.v  —  xi'/xi as a SUM OVER ZEROS.                  *)
(*                                                                    *)
(*    Pinf_logderiv : the partial traces converge to P'/P,             *)
(*        SUM_n [ 1/(z-rho n) + 1/rho n ]  =  P'(z)/P(z);              *)
(*    xi_logderiv_zeros :                                              *)
(*        xi'/xi (z)  =  Hglob'/Hglob (z)  +  SUM_rho [...]            *)
(*                                                                    *)
(*  This is the last Stage-C input of the explicit formula.  Both      *)
(*  ExplicitFormulaXiLogDeriv and ExplicitFormulaDigamma name it as    *)
(*  the one remaining term, the archimedean half of the bridge being   *)
(*  already proved (XiC_logderiv).                                     *)
(*                                                                    *)
(*  IT DOES NOT NEED SubQuadLog.  xi = Hglob . P is unconditional      *)
(*  (XiHadamardGlue.Hglob_id), so the identity above holds with an     *)
(*  entire correction term Hglob'/Hglob.  SubQuadLog is needed only    *)
(*  afterwards, to collapse that term to the constant b.  So the       *)
(*  explicit formula no longer waits on the minimum-modulus estimate.  *)
(*                                                                    *)
(*  CONVERGENCE COMES FROM THE IDENTITY, not from a comparison test.   *)
(*  Splitting P = Pprod_M . T_M at every M and differentiating,        *)
(*      P'/P  =  (partial trace through M)  +  T_M'/T_M,               *)
(*  so the partial traces converge as soon as T_M'/T_M -> 0.  A        *)
(*  majorant argument would have needed 2|z|/|rho|^2, valid only once  *)
(*  |rho| >= 2|z| -- finitely many exceptions, which is not            *)
(*  structural.  This way value and convergence arrive together.       *)
(*                                                                    *)
(*  T_M'/T_M -> 0 is where the Cauchy derivative estimate earns its    *)
(*  keep, and the subtlety is WHICH function to apply it to: T_M is    *)
(*  near 1, not near 0, so bounding it gives nothing.  It is the       *)
(*  DEVIATION T_M - 1 that is uniformly small (tail_prod_near1), and   *)
(*  it has the same derivative.  Below, tail_prod_ge keeps |T_M| above *)
(*  1/2 so the quotient is controlled.  Axiom-clean.                   *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia List FunctionalExtensionality.
Require Import ComplexField Cmodulus Holomorphic CDeriv CHoloCalculus CHoloCcontC
        CexpFull CSegInt CPathIntegral CSeries CInfProd CDerivUnique CDerivGlobal
        CCauchyEstimate
        PerronRemovable CSpecDet
        JensenMultiZero CZeroListFactor RiemannXiEntire
        XiZeroEnum XiHadamardProd XiHadamardUnif XiHcof XiProdLimit
        XiTailProd XiTMHolo XiTMSelect XiHadamardLocal XiHadamardGlue.
Open Scope R_scope.

(* the limit of a sequence bounded in modulus is bounded *)
Lemma CUn_cv_mod_le : forall (u : nat -> C) (l : C) (c : R) (N0 : nat),
  CUn_cv u l -> (forall n, (N0 <= n)%nat -> Cmod (u n) <= c) -> Cmod l <= c.
Proof.
  intros u l c N0 Hcv Hb.
  destruct (Rle_or_lt (Cmod l) c) as [H | H]; [ exact H | exfalso ].
  destruct (Hcv (Cmod l - c) ltac:(lra)) as [N HN].
  pose proof (HN (Nat.max N N0) ltac:(lia)) as H1.
  pose proof (Hb (Nat.max N N0) ltac:(lia)) as H2.
  pose proof (Cmod_diff_le l (u (Nat.max N N0))) as H3.
  pose proof (Rle_abs (Cmod l - Cmod (u (Nat.max N N0)))) as H4.
  assert (Hsym : Cmod (Cminus l (u (Nat.max N N0)))
                 = Cmod (Cminus (u (Nat.max N N0)) l)).
  { rewrite <- (Cmod_opp (Cminus l (u (Nat.max N N0)))). f_equal. ring. }
  lra.
Qed.

Section LogDeriv.

Variable rho : nat -> C.
Variable Gseq : nat -> C -> C.
Hypothesis HZ : ZeroEnumG rho Gseq.
Hypothesis Hlow : forall n, 1 <= Cmod (rho n).

Notation En := (HE rho Gseq HZ).
Notation Pf := (Pinf rho Gseq HZ Hlow).
Notation Tf M := (TM rho En Hlow M).
Notation Tptc M := (TM_ptcont rho En Hlow M).
Notation Td M := (Fderiv (Tf M) (Tptc M)).

Lemma Tf_holo : forall M z, exists d, is_Cderiv (Tf M) z d.
Proof. intros M z. apply TM_holo. Qed.

Lemma Td_spec : forall M z, is_Cderiv (Tf M) z (Td M z).
Proof. intros M z. apply (Fderiv_spec (Tf M) (Tptc M) (Tf_holo M) z). Qed.

Lemma Td_holo : forall M z, exists d, is_Cderiv (Td M) z d.
Proof. intros M z. apply (Fderiv_holo (Tf M) (Tptc M) (Tf_holo M) z). Qed.

Lemma Td_cc : forall M, CcontC (Td M).
Proof.
  intro M. apply ptcont_CcontC, holo_ptcont. apply Td_holo.
Qed.

(* the tail's DEVIATION from 1 is uniformly small -- that is the
   function the Cauchy estimate must see *)
Lemma Tdev_le : forall (Rr : R), 0 < Rr -> forall M z, Cmod z <= Rr ->
  Cmod (Cminus (Tf M z) C1) <= exp (KR Rr * Ttl rho En Hlow M) - 1.
Proof.
  intros Rr HR M z Hz.
  apply (CUn_cv_mod_le
           (fun k => Cminus (Pprod (fun j => Efac z (rsh rho M j)) k) C1)
           (Cminus (Tf M z) C1) _ 0%nat).
  - intros eps Heps.
    destruct (TM_spec rho En Hlow M z eps Heps) as [N HN].
    exists N. intros n Hn.
    replace (Cminus (Cminus (Pprod (fun j => Efac z (rsh rho M j)) n) C1)
                    (Cminus (Tf M z) C1))
      with (Cminus (Pprod (fun j => Efac z (rsh rho M j)) n) (Tf M z)) by ring.
    apply HN; exact Hn.
  - intros n _. apply (tail_prod_near1 rho En Hlow Rr HR M z Hz n).
Qed.

(* the derivative bound: apply the Cauchy estimate to T_M - 1 *)
Lemma Td_bound : forall (Rr : R), 0 < Rr -> forall M z, Cmod z <= Rr / 2 ->
  Cmod (Td M z) <= 8 * (exp (KR Rr * Ttl rho En Hlow M) - 1) / Rr.
Proof.
  intros Rr HR M z Hz.
  assert (HGptc : ptcont (fun w => Cminus (Tf M w) C1)).
  { intros w eps Heps. destruct (Tptc M w eps Heps) as [del [Hd Hb]].
    exists del. split; [ exact Hd | ]. intros w' Hw'.
    replace (Cminus (Cminus (Tf M w') C1) (Cminus (Tf M w) C1))
      with (Cminus (Tf M w') (Tf M w)) by ring.
    apply Hb; exact Hw'. }
  assert (HGd : forall w, is_Cderiv (fun w' => Cminus (Tf M w') C1) w (Td M w)).
  { intro w.
    apply (isd_val _ _ (Cminus (Td M w) C0));
      [ apply (Cderiv_minus (Tf M) (fun _ => C1) w (Td M w) C0);
          [ apply Td_spec | apply Cderiv_const ]
      | ring ]. }
  assert (Hbd : forall u, Cmod (Cminus (Tf M (arc Rr u)) C1)
                          <= exp (KR Rr * Ttl rho En Hlow M) - 1).
  { intro u. apply (Tdev_le Rr HR M).
    rewrite (Cmod_arc Rr u ltac:(lra)). lra. }
  exact (disk_deriv_bound (fun w => Cminus (Tf M w) C1) Rr
           (exp (KR Rr * Ttl rho En Hlow M) - 1) z HR HGptc Hbd Hz
           (Td M) HGd (Td_holo M) (Td_cc M)).
Qed.

(* ----------------------------------------------------------------- *)
(*  THE TRACE                                                          *)
(* ----------------------------------------------------------------- *)
Theorem Pinf_logderiv : forall z, (forall n, z <> rho n) ->
  exists d, is_Cderiv Pf z d
         /\ CUn_cv (Cpsum (lterm rho z)) (Cmul d (Cinv (Pf z))).
Proof.
  intros z Hz.
  assert (Hne : forall k, rho k <> C0).
  { intros k Hc. pose proof (Hlow k) as H.
    rewrite Hc, (proj2 (Cmod0 C0) eq_refl) in H. lra. }
  assert (HPne : Pf z <> C0)
    by (apply (hadamard_prod_ne0 rho En Hlow z Hz);
        apply (Pinf_spec rho Gseq HZ Hlow)).
  set (Rr := 2 * (Cmod z + 1)).
  assert (HR : 0 < Rr) by (unfold Rr; pose proof (Cmod_nonneg z); lra).
  assert (HzR : Cmod z <= Rr / 2) by (unfold Rr; lra).
  (* the split, as an identity of FUNCTIONS *)
  assert (Hfe : forall M, Pf = fun w => Cmul (Pprod (fun k => Efac w (rho k)) M)
                                             (Tf M w))
    by (intro M; apply functional_extensionality; intro w;
        apply (Pinf_split rho Gseq HZ Hlow M w)).
  (* each truncation gives a derivative of Pf at z *)
  assert (Hder : forall M, is_Cderiv Pf z
            (Cadd (Cmul (Cmul (Pprod (fun k => Efac z (rho k)) M)
                              (Cpsum (lterm rho z) M)) (Tf M z))
                  (Cmul (Pprod (fun k => Efac z (rho k)) M) (Td M z)))).
  { intro M. rewrite (Hfe M).
    apply (Cderiv_mul (fun w => Pprod (fun k => Efac w (rho k)) M) (Tf M) z
             (Cmul (Pprod (fun k => Efac z (rho k)) M) (Cpsum (lterm rho z) M))
             (Td M z));
      [ apply Pprod_logderiv; assumption | apply Td_spec ]. }
  set (d := Cadd (Cmul (Cmul (Pprod (fun k => Efac z (rho k)) 0)
                             (Cpsum (lterm rho z) 0)) (Tf 0 z))
                 (Cmul (Pprod (fun k => Efac z (rho k)) 0) (Td 0 z))).
  exists d. split; [ exact (Hder 0%nat) | ].
  (* every truncation computes the same derivative *)
  assert (Hsame : forall M,
            d = Cadd (Cmul (Cmul (Pprod (fun k => Efac z (rho k)) M)
                                 (Cpsum (lterm rho z) M)) (Tf M z))
                     (Cmul (Pprod (fun k => Efac z (rho k)) M) (Td M z)))
    by (intro M; exact (is_Cderiv_unique Pf z _ _ (Hder 0%nat) (Hder M))).
  (* the head product and the tail are both nonzero at z *)
  assert (Hsplitz : forall M, Pf z = Cmul (Pprod (fun k => Efac z (rho k)) M) (Tf M z))
    by (intro M; apply (Pinf_split rho Gseq HZ Hlow M z)).
  assert (HPPne : forall M, Pprod (fun k => Efac z (rho k)) M <> C0).
  { intros M Hc. apply HPne. rewrite (Hsplitz M), Hc. ring. }
  assert (HTne : forall M, Tf M z <> C0).
  { intros M Hc. apply HPne. rewrite (Hsplitz M), Hc. ring. }
  (* the residual is exactly Td / Tf *)
  assert (Hres : forall M,
            Cminus (Cpsum (lterm rho z) M) (Cmul d (Cinv (Pf z)))
            = Copp (Cmul (Td M z) (Cinv (Tf M z)))).
  { intro M. rewrite (Hsplitz M), (Hsame M). field.
    split; [ apply HTne | apply HPPne ]. }
  (* ...and it tends to 0 *)
  intros eps Heps.
  pose proof (exp_pos 1) as He1.
  pose proof (exp_ineq1_le 1) as He1'.
  pose proof (KR_pos Rr HR) as HKR.
  set (bnd := Rmin (/ (2 * exp 1)) (eps * Rr / (16 * exp 1))).
  assert (Hbnd : 0 < bnd)
    by (apply Rmin_glb_lt;
        [ apply Rinv_0_lt_compat; lra | repeat apply Rdiv_lt_0_compat; nra ]).
  destruct (Ttl_small rho En Hlow (bnd / KR Rr)
              ltac:(apply Rdiv_lt_0_compat; lra)) as [N0 HN0].
  exists N0. intros M HM.
  rewrite (Hres M), Cmod_opp.
  (* the tail sum only shrinks *)
  assert (Htt : KR Rr * Ttl rho En Hlow M < bnd).
  { pose proof (Ttl_decr rho En Hlow N0 M HM) as Hd'.
    apply (Rmult_lt_reg_r (/ KR Rr)); [ apply Rinv_0_lt_compat; lra | ].
    replace (KR Rr * Ttl rho En Hlow M * / KR Rr) with (Ttl rho En Hlow M)
      by (field; lra).
    replace (bnd * / KR Rr) with (bnd / KR Rr) by (unfold Rdiv; ring). lra. }
  assert (Htt0 : 0 <= KR Rr * Ttl rho En Hlow M).
  { pose proof (Ttl_nonneg rho En Hlow M). nra. }
  (* deviation bound, hence |Tf| >= 1/2 and |Td| small *)
  assert (Hb1 : bnd <= / (2 * exp 1)) by apply Rmin_l.
  assert (Hb2 : bnd <= eps * Rr / (16 * exp 1)) by apply Rmin_r.
  assert (Hu1 : KR Rr * Ttl rho En Hlow M <= 1).
  { assert (Hi : / (2 * exp 1) <= 1)
      by (rewrite <- Rinv_1 at 2; apply Rinv_le_contravar; lra).
    lra. }
  assert (Heps1 : exp (KR Rr * Ttl rho En Hlow M) - 1
                  <= KR Rr * Ttl rho En Hlow M * exp 1).
  { pose proof (exp_m1_le _ Htt0) as H.
    assert (Hex : exp (KR Rr * Ttl rho En Hlow M) <= exp 1) by (apply exp_le; lra).
    assert (Hs : KR Rr * Ttl rho En Hlow M * exp (KR Rr * Ttl rho En Hlow M)
                 <= KR Rr * Ttl rho En Hlow M * exp 1)
      by (apply Rmult_le_compat_l; lra).
    lra. }
  assert (Hhalf : exp (KR Rr * Ttl rho En Hlow M) - 1 <= / 2).
  { assert (Hkey : / (2 * exp 1) * exp 1 = / 2) by (field; lra).
    assert (Hs1 : KR Rr * Ttl rho En Hlow M * exp 1 <= bnd * exp 1)
      by (apply Rmult_le_compat_r; lra).
    assert (Hs2 : bnd * exp 1 <= / (2 * exp 1) * exp 1)
      by (apply Rmult_le_compat_r; lra).
    lra. }
  assert (HTge : / 2 <= Cmod (Tf M z)).
  { apply (CUn_cv_mod_ge _ _ (/ 2) 0%nat (TM_spec rho En Hlow M z)).
    intros n _. apply (tail_prod_ge rho En Hlow Rr HR M Hhalf z ltac:(lra) n). }
  assert (HTdb : Cmod (Td M z) <= 8 * (exp (KR Rr * Ttl rho En Hlow M) - 1) / Rr)
    by (apply Td_bound; [ exact HR | exact HzR ]).
  (* assemble *)
  rewrite Cmod_mul, (Cmod_inv (Tf M z) (HTne M)).
  assert (Hinv : / Cmod (Tf M z) <= 2).
  { apply Rle_trans with (/ (/ 2));
      [ apply Rinv_le_contravar; lra | right; field ]. }
  assert (Hnn : 0 <= Cmod (Td M z)) by apply Cmod_nonneg.
  assert (Hprod : Cmod (Td M z) * / Cmod (Tf M z)
                  <= (8 * (exp (KR Rr * Ttl rho En Hlow M) - 1) / Rr) * 2).
  { apply Rmult_le_compat; [ exact Hnn | | exact HTdb | exact Hinv ].
    left; apply Rinv_0_lt_compat; lra. }
  assert (Hfin : (8 * (exp (KR Rr * Ttl rho En Hlow M) - 1) / Rr) * 2 < eps).
  { assert (Hs1 : KR Rr * Ttl rho En Hlow M * exp 1 < bnd * exp 1)
      by (apply Rmult_lt_compat_r; lra).
    assert (Hchain : exp (KR Rr * Ttl rho En Hlow M) - 1 < bnd * exp 1) by lra.
    assert (Hkey2 : eps * Rr / (16 * exp 1) * exp 1 = eps * Rr / 16)
      by (field; lra).
    assert (Hs2 : bnd * exp 1 <= eps * Rr / (16 * exp 1) * exp 1)
      by (apply Rmult_le_compat_r; lra).
    assert (Hb3 : bnd * exp 1 <= eps * Rr / 16) by lra.
    apply (Rmult_lt_reg_r (Rr / 16)); [ lra | ].
    replace (8 * (exp (KR Rr * Ttl rho En Hlow M) - 1) / Rr * 2 * (Rr / 16))
      with (exp (KR Rr * Ttl rho En Hlow M) - 1) by (field; lra).
    lra. }
  lra.
Qed.

(* ----------------------------------------------------------------- *)
(*  THE PAYOFF: xi'/xi as a sum over zeros, with NO SubQuadLog          *)
(* ----------------------------------------------------------------- *)
Lemma Hg_holo : forall z, exists d, is_Cderiv (Hglob rho Gseq HZ Hlow) z d.
Proof. apply Hglob_holo. Qed.

Lemma Hg_ptc : ptcont (Hglob rho Gseq HZ Hlow).
Proof. exact (holo_ptcont (Hglob rho Gseq HZ Hlow) Hg_holo). Qed.

Notation Hgd := (Fderiv (Hglob rho Gseq HZ Hlow) Hg_ptc).

Theorem xi_logderiv_zeros : forall z, (forall n, z <> rho n) ->
  exists dxi,
    is_Cderiv XiC z dxi
    /\ CUn_cv (Cpsum (lterm rho z))
         (Cminus (Cmul dxi (Cinv (XiC z)))
                 (Cmul (Hgd z) (Cinv (Hglob rho Gseq HZ Hlow z)))).
Proof.
  intros z Hz.
  destruct (Pinf_logderiv z Hz) as [dP [HdP Hcv]].
  assert (HHne : Hglob rho Gseq HZ Hlow z <> C0) by apply Hglob_ne0.
  assert (Hne : forall k, rho k <> C0).
  { intros k Hc. pose proof (Hlow k) as H.
    rewrite Hc, (proj2 (Cmod0 C0) eq_refl) in H. lra. }
  assert (HPne : Pf z <> C0)
    by (apply (hadamard_prod_ne0 rho En Hlow z Hz);
        apply (Pinf_spec rho Gseq HZ Hlow)).
  assert (Hxi : XiC = fun w => Cmul (Hglob rho Gseq HZ Hlow w) (Pf w))
    by (apply functional_extensionality; intro w;
        apply (Hglob_id rho Gseq HZ Hlow w)).
  exists (Cadd (Cmul (Hgd z) (Pf z))
               (Cmul (Hglob rho Gseq HZ Hlow z) dP)).
  split.
  - rewrite Hxi.
    apply (Cderiv_mul (Hglob rho Gseq HZ Hlow) Pf z (Hgd z) dP);
      [ apply (Fderiv_spec (Hglob rho Gseq HZ Hlow) Hg_ptc Hg_holo) | exact HdP ].
  - assert (Heq :
      Cminus (Cmul (Cadd (Cmul (Hgd z) (Pf z))
                         (Cmul (Hglob rho Gseq HZ Hlow z) dP)) (Cinv (XiC z)))
             (Cmul (Hgd z) (Cinv (Hglob rho Gseq HZ Hlow z)))
      = Cmul dP (Cinv (Pf z))).
    { rewrite (Hglob_id rho Gseq HZ Hlow z). field. split; assumption. }
    rewrite Heq. exact Hcv.
Qed.

Print Assumptions Tdev_le.
Print Assumptions Pinf_logderiv.
Print Assumptions xi_logderiv_zeros.

End LogDeriv.
