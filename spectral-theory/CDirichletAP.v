(* ================================================================= *)
(*  CDirichletAP.v  --  DIRICHLET'S THEOREM ON ARITHMETIC PROGRESSIONS*)
(*                                                                    *)
(*    p prime, g a primitive root mod p, m coprime to p               *)
(*      ==>  for every B there is a PRIME q > B with q m = 1 mod p     *)
(*                                                                    *)
(*  i.e. the residue class of m^{-1} mod p contains infinitely many    *)
(*  primes.                                                           *)
(*                                                                    *)
(*  This discharges the divergence hypothesis of                       *)
(*  CDirichletClass.class_has_large_prime from                         *)
(*    CClassLimit.class_lower          (p-1) Cinf >= Phi(chi_0)-(p-2)K*)
(*    CLPhi0Lower.chi0part_unbounded   Phi(chi_0) exceeds any bound    *)
(*    CLPhiUniform.Phi_bounded_uniform one K for every a <> 0          *)
(*    CClassLimit.class_cv             the class partial sums converge *)
(*                                                                    *)
(*  ONE MOVE IS NOT BOOKKEEPING.  The hypothesis has to hold at        *)
(*  sigma = 1, where none of the L-function machinery is defined -- L  *)
(*  and Phi only exist for Re s > 1.  It does hold, because every      *)
(*  class term Lambda(n) n^{-sigma} DECREASES in sigma: prove the      *)
(*  bound at a sigma_0 strictly above 1, where all the analysis lives, *)
(*  and it propagates down to sigma = 1 for free (Ares_anti).          *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia List ZArith Znumtheory.
Require Import ComplexField Cmodulus CexpFull CSeries CListSum CDirichlet
        CZetaTerm RootsOfUnity ZmodOrder DirichletModP CTwistedCoeff CLSeries
        VonMangoldtGlobal CVonMangoldtChi CharSelectorSeries CDirichletClass
        CClassPartial CLPhiBounded CLPhiUniform CLPrincipal CLPhi0Lower
        CClassLimit CPPowTail CLWeightAnti CPhiZetaLower LFunOne CAbelTail
        Chebyshev PrimePowerReindex.
Import ListNotations.
Open Scope R_scope.

Section AP.

Variable p g m : nat.
Hypothesis Hp : prime (Z.of_nat p).
Hypothesis Hg : (1 <= g <= p - 1)%nat.
Hypothesis Hord : ord p g = (p - 1)%nat.
Hypothesis Hm : (m mod p <> 0)%nat.

Lemma Hp2' : (2 <= p)%nat.
Proof. pose proof (prime_ge_2 _ Hp); lia. Qed.

Notation SC := (CClassPartial.sc).

(* ---- the principal term is RtoC of the real chi_0 series ---- *)

Lemma pchi0_bridge : forall sig k,
  pchi p g 0 (SC sig) k = RtoC (chi0part p sig k).
Proof.
  intros sig k. unfold pchi, chi0part, Lterm, Gchi.
  rewrite dchar0_val.
  replace (Copp (SC sig)) with (RtoC (- sig))
    by (apply Ceq; unfold Copp, RtoC, CClassPartial.sc; cbn [Re Im]; ring).
  rewrite Cpw_RtoC.
  destruct (S k mod p =? 0)%nat.
  - apply Ceq; unfold Cmul, C0, RtoC; cbn [Re Im]; ring.
  - apply Ceq; unfold Cmul, C1, RtoC; cbn [Re Im]; ring.
Qed.

Lemma chi0part_nonneg : forall sig k, 0 <= chi0part p sig k.
Proof.
  intros sig k. unfold chi0part.
  destruct (S k mod p =? 0)%nat; [ apply Rle_refl | ].
  apply Rmult_le_pos; [ apply Lam_nonneg | ].
  apply Rlt_le; unfold Rpower; apply exp_pos.
Qed.

Lemma chi0part_le_Phi : forall sig (Hs : 1 < Re (SC sig)) N,
  sum_f_R0 (chi0part p sig) N <= Re (Phichi p g 0 Hg Hord (SC sig) Hs).
Proof.
  intros sig Hs N.
  assert (Hcv : Un_cv (fun M => sum_f_R0 (chi0part p sig) M)
                      (Re (Phichi p g 0 Hg Hord (SC sig) Hs))).
  { pose proof (Phichi_spec p g 0 Hg Hord (SC sig) Hs) as HS.
    unfold Cseries_cv in HS.
    assert (HS' : CUn_cv (fun M => RtoC (sum_f_R0 (chi0part p sig) M))
                         (Phichi p g 0 Hg Hord (SC sig) Hs)).
    { apply (CUn_cv_ext (Cpsum (pchi p g 0 (SC sig)))); [ | exact HS ].
      intro M. rewrite <- Cpsum_RtoC. apply Cpsum_ext. intro k.
      apply pchi0_bridge. }
    rewrite CUn_cv_comp in HS'. destruct HS' as [HRe _].
    apply (Un_cv_ext (fun M => Re (RtoC (sum_f_R0 (chi0part p sig) M))));
      [ intro M; unfold RtoC; cbn [Re]; reflexivity | exact HRe ]. }
  apply (growing_ineq (fun M => sum_f_R0 (chi0part p sig) M)); [ | exact Hcv ].
  intro M. rewrite tech5. pose proof (chi0part_nonneg sig (S M)). lra.
Qed.

(* ---- the class terms decrease in sigma ---- *)

Lemma Ares_anti : forall sig1 sig2 k, 1 <= sig1 -> sig1 <= sig2 ->
  CDirichletClass.Ares p m sig2 k <= CDirichletClass.Ares p m sig1 k.
Proof.
  intros sig1 sig2 k Hs1 Hs12.
  unfold CDirichletClass.Ares.
  destruct (CDirichletClass.inclass p m (S k)); [ | apply Rle_refl ].
  assert (Hx1 : 1 <= INR (S k)) by (rewrite <- INR_1; apply le_INR; lia).
  assert (Hstep : Rpower (INR (S k)) (- sig2) <= Rpower (INR (S k)) (- sig1))
    by (apply Rpower_exp_anti; lra).
  pose proof (Lam_nonneg (S k)).
  apply Rmult_le_compat_l; assumption.
Qed.

(* ---- THE divergence ---- *)

Theorem class_sum_diverges : forall M, exists N del, 0 < del /\
  forall sig, 1 <= sig -> sig <= 1 + del ->
    M <= sum_f_R0 (CDirichletClass.Ares p m sig) N.
Proof.
  intro M.
  destruct (Phi_bounded_uniform p g Hp Hg Hord) as [K0 [del1 [Hd1 HK0]]].
  set (K := Rmax K0 0).
  assert (HKnn : 0 <= K) by apply Rmax_r.
  pose proof Hp2' as H2.
  assert (Hp1R : 0 < INR (p - 1)) by (apply lt_0_INR; lia).
  assert (Hp2R : 0 <= INR (p - 2)) by apply pos_INR.
  destruct (chi0part_unbounded p Hp (INR (p - 1) * (M + 1) + INR (p - 2) * K))
    as [N0 [del2 [Hd2 HN0]]].
  set (del := Rmin del1 del2 / 2).
  assert (Hdel : 0 < del)
    by (unfold del; apply Rdiv_lt_0_compat; [ apply Rmin_pos; assumption | lra ]).
  set (sig0 := 1 + del).
  assert (Hs0R : 1 < sig0) by (unfold sig0; lra).
  assert (Hs0 : 1 < Re (SC sig0)) by (unfold CClassPartial.sc; cbn [Re]; lra).
  assert (Hlt1 : sig0 < 1 + del1)
    by (unfold sig0, del; pose proof (Rmin_l del1 del2); lra).
  assert (Hle2 : sig0 <= 1 + del2)
    by (unfold sig0, del; pose proof (Rmin_r del1 del2); lra).
  (* principal character large at sigma0 *)
  assert (HPhi0 : INR (p - 1) * (M + 1) + INR (p - 2) * K
                  <= Re (Phichi p g 0 Hg Hord (SC sig0) Hs0)).
  { eapply Rle_trans; [ apply (HN0 sig0 ltac:(lra) Hle2) | ].
    apply chi0part_le_Phi. }
  (* the other characters are capped at sigma0 *)
  assert (HB : forall A, (0 < A < p - 1)%nat ->
                 Cmod (Phichi p g A Hg Hord (SC sig0) Hs0) <= K).
  { intros A HA.
    eapply Rle_trans; [ apply (HK0 A HA sig0 Hs0 Hlt1) | apply Rmax_l ]. }
  pose proof (class_lower p g m Hp Hg Hord Hm K HKnn sig0 Hs0 HB) as Hlow.
  (* hence the class limit exceeds M + 1 *)
  assert (HCinf : M + 1 <= Cinf p g m Hg Hord sig0 Hs0).
  { apply (Rmult_le_reg_l (INR (p - 1))); [ exact Hp1R | ]. lra. }
  (* so some partial sum exceeds M *)
  destruct (class_cv p g m Hp Hg Hord Hm sig0 Hs0 1 Rlt_0_1) as [N1 HN1].
  exists N1, del. split; [ exact Hdel | ].
  intros sig Hs1 Hs2.
  assert (Hat0 : M <= sum_f_R0 (CDirichletClass.Ares p m sig0) N1).
  { pose proof (HN1 N1 (Nat.le_refl N1)) as H. unfold R_dist in H.
    destruct (Rabs_def2 _ _ H) as [_ Hlow2]. lra. }
  eapply Rle_trans; [ exact Hat0 | ].
  apply sum_Rle. intros k _. apply Ares_anti; [ lra | unfold sig0; lra ].
Qed.

(* ================================================================= *)
(*  DIRICHLET'S THEOREM                                               *)
(* ================================================================= *)

Theorem dirichlet_arithmetic_progression : forall B,
  exists q, (B < q)%nat /\ primeb q = true /\ (q * m) mod p = 1%nat.
Proof.
  intro B.
  destruct (class_has_large_prime p m Hp2' class_sum_diverges B)
    as [q [Hq1 [Hq2 Hq3]]].
  exists q. split; [ exact Hq1 | split; [ exact Hq2 | ] ].
  unfold CDirichletClass.inclass in Hq3. apply Nat.eqb_eq. exact Hq3.
Qed.

End AP.

Print Assumptions dirichlet_arithmetic_progression.

(* ================================================================= *)
(*  END CDirichletAP.v                                                *)
(* ================================================================= *)
