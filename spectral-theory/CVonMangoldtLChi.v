(* ================================================================= *)
(*  CVonMangoldtLChi.v  --  Phi(s,chi) * L(s,chi) = sum chi(n) ln n   *)
(*  n^{-s}  on Re s > 1.                                              *)
(*                                                                    *)
(*  The twisted analogue of CVonMangoldtZeta.phi_zeta_eq_neg_zeta',    *)
(*  written to mirror that file step for step.  Only two things are    *)
(*  genuinely different:                                              *)
(*                                                                    *)
(*  (1) Gchi is completely multiplicative for a DIFFERENT reason than  *)
(*      gC: gC needs only Cpw_base_mul, while Gchi needs that AND      *)
(*      dchar_mul.  That is conv_term_chi's Hgmul.                     *)
(*                                                                    *)
(*  (2) |Gchi m| is <= n^{-Re s}, not = n^{-Re s} as for gC.  So       *)
(*      bchi_abs_cv cannot be the sum_eq argument bterm_abs_cv uses;   *)
(*      it goes through Rseries_abs_cv against the p-series instead.   *)
(*                                                                    *)
(*  Everything else -- the reindexing between Cpsum and Cls (seq 1 N), *)
(*  the divisor-sum collapse, and the appeal to cdirichlet_product --  *)
(*  is the zeta proof with chi carried along.                          *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia List ZArith Znumtheory
     FunctionalExtensionality.
Require Import ComplexField Cmodulus CexpFull CPowMul CSeries CListSum
        CDirichletProduct CDirichlet CZetaTerm Ell2Zeta RealMobius
        VonMangoldtGlobal Chebyshev CVonMangoldtSeries CVonMangoldtZeta
        RootsOfUnity ZmodOrder DirichletModP DirichletLEuler CTwistedCoeff CLSeries
        CVonMangoldtChi.
Import ListNotations.
Open Scope R_scope.

Section LChi.

Variable p g A : nat.
Hypothesis Hp : prime (Z.of_nat p).
Hypothesis Hg : (1 <= g <= p - 1)%nat.
Hypothesis Hord : ord p g = (p - 1)%nat.
Variable s : C.
Hypothesis Hs : 1 < Re s.

Notation PH := (Phichi p g A Hg Hord s Hs).

Definition bchi (n : nat) : C := Gchi p g A s n.

Lemma bchi_S : forall k, bchi (S k) = Lterm p g A s k.
Proof. intro k. unfold bchi, Lterm. reflexivity. Qed.

(* ---- partial sums converge to Phi(s,chi) and L(s,chi) ---- *)

Lemma achi_cv : CUn_cv (fun N => Cls (seq 1 N) (achi p g A s)) PH.
Proof.
  apply CUn_cv_pred_S.
  apply (CUn_cv_ext (fun N => Cpsum (pchi p g A s) N));
    [ | exact (Phichi_spec p g A Hg Hord s Hs) ].
  intro N. rewrite <- (Cpsum_shift_eq_Cls (achi p g A s) N).
  assert (Hf : pchi p g A s = (fun k => achi p g A s (S k)))
    by (apply functional_extensionality; intro k; symmetry; apply achi_S).
  rewrite Hf; reflexivity.
Qed.

Lemma bchi_cv : forall L, Cseries_cv (Lterm p g A s) L ->
  CUn_cv (fun N => Cls (seq 1 N) bchi) L.
Proof.
  intros L HL. apply CUn_cv_pred_S.
  apply (CUn_cv_ext (fun N => Cpsum (Lterm p g A s) N)); [ | exact HL ].
  intro N. rewrite <- (Cpsum_shift_eq_Cls bchi N).
  assert (Hf : Lterm p g A s = (fun k => bchi (S k)))
    by (apply functional_extensionality; intro k; symmetry; apply bchi_S).
  rewrite Hf; reflexivity.
Qed.

(* ---- absolute convergence of the L-side (INEQUALITY, unlike zeta) ---- *)

Lemma bchi_abs_cv :
  { T | Un_cv (fun N => Rls (seq 1 N) (fun m => Cmod (bchi m))) T }.
Proof.
  assert (Hmaj : forall n, Rabs (Cmod (bchi (S n))) <= Rpower (INR (S n)) (- Re s)).
  { intro n. rewrite Rabs_pos_eq by apply Cmod_nonneg.
    pose proof (Gchi_mod_le p g A Hg Hord s (S n)) as H.
    replace (z (Re s) (S n)) with (Rpower (INR (S n)) (- Re s)) in H by reflexivity.
    exact H. }
  destruct (Rseries_abs_cv (fun n => Cmod (bchi (S n)))
              (fun n => Rpower (INR (S n)) (- Re s)) Hmaj
              (pseries_cv (Re s) Hs)) as [Tb HTb].
  exists Tb. apply Un_cv_pred_S.
  apply (Un_cv_ext (sum_f_R0 (fun k => Cmod (bchi (S k))))); [ | exact HTb ].
  intro N. symmetry. apply Rls_seq_S_eq_sumf.
Qed.

(* ---- the convolution coefficient collapses ---- *)

Lemma conv_term_chi : forall n, (1 <= n)%nat ->
  Cls (divisors n) (fun d => Cmul (achi p g A s d) (bchi (n / d)%nat))
  = Cmul (RtoC (ln (INR n))) (Gchi p g A s n).
Proof.
  intros n Hn.
  rewrite (Cls_ext nat
             (fun d => Cmul (achi p g A s d) (bchi (n / d)%nat))
             (fun d => Cmul (RtoC (Lam d)) (Gchi p g A s n))
             (divisors n)).
  2:{ intros d Hd; apply in_divisors in Hd; destruct Hd as [[Hd1 Hdn] Hdvd].
      assert (Hqe : (n / d >= 1)%nat) by (apply Nat.div_le_lower_bound; lia).
      assert (Hdd : (d * (n / d))%nat = n)
        by (destruct Hdvd as [q Hq]; rewrite Hq, Nat.div_mul by lia; lia).
      assert (Hgmul : Cmul (Gchi p g A s d) (Gchi p g A s (n / d)%nat)
                      = Gchi p g A s n).
      { unfold Gchi.
        replace (dchar p g A n) with (Cmul (dchar p g A d) (dchar p g A (n / d)%nat)).
        2:{ rewrite <- (dchar_mul p g A d (n / d)%nat Hp Hg Hord).
            f_equal. exact Hdd. }
        replace (Cpw (INR n) (Copp s))
          with (Cmul (Cpw (INR d) (Copp s)) (Cpw (INR (n / d)%nat) (Copp s))).
        2:{ rewrite <- Cpw_base_mul by (apply lt_0_INR; lia).
            rewrite <- mult_INR. f_equal. f_equal. exact Hdd. }
        apply Ceq; unfold Cmul; cbn [Re Im]; ring. }
      unfold achi, bchi; rewrite <- Hgmul; ring. }
  rewrite Cls_scal_r, Cls_RtoC.
  replace (Rls (divisors n) Lam) with (dsum Lam n) by reflexivity.
  rewrite (vonmangoldt_identity n Hn); reflexivity.
Qed.

(* ---- THE product identity ---- *)

Theorem phi_L_eq : forall L, Cseries_cv (Lterm p g A s) L ->
  CUn_cv (fun N => Cls (seq 1 N)
            (fun n => Cmul (RtoC (ln (INR n))) (Gchi p g A s n))) (Cmul PH L).
Proof.
  intros L HL.
  destruct (achi_abs_cv p g A Hg Hord s Hs) as [TA HTA].
  destruct bchi_abs_cv as [TB HTB].
  pose proof (cdirichlet_product (achi p g A s) bchi PH L TA TB
                achi_cv (bchi_cv L HL) HTA HTB) as Hcp.
  apply (CUn_cv_ext (fun N => Cls (seq 1 N)
           (fun n => Cls (divisors n)
              (fun d => Cmul (achi p g A s d) (bchi (n / d)%nat)))));
    [ | exact Hcp ].
  intro N. apply Cls_ext. intros n Hn. apply in_seq in Hn.
  apply conv_term_chi. lia.
Qed.

End LChi.

Print Assumptions phi_L_eq.

(* ================================================================= *)
(*  END CVonMangoldtLChi.v                                            *)
(* ================================================================= *)
