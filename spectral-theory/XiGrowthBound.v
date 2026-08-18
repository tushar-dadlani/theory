(* ================================================================= *)
(*  XiGrowthBound.v  —  Hadamard Stage A: the order-1 growth bound.      *)
(*                                                                    *)
(*  Toward the Hadamard product xi(s) = e^{A+Bs} prod_rho (1-s/rho)      *)
(*  e^{s/rho}, the first analytic keystone is that XiC has order 1:      *)
(*                                                                    *)
(*    XiC_order1_bound : Cmod (XiC z) <= exp (Kxi.(Cmod z+2).ln(Cmod z+2)). *)
(*                                                                    *)
(*  Route (reusing the Stage-2 CImp machinery):                         *)
(*   - XiC z = 1/2 + 1/2.z.(z-1).(TC z + TC(1-z))  (XiC_factored);       *)
(*   - Cmod (XiC z) <= 1/2 + 1/2 (|z|+1)^2 (|TC z| + |TC(1-z)|);         *)
(*   - |TC z| <= T(Re z)  (CImp_triangle + Cmod_wkerC + T_spec) --       *)
(*     independent of Im z;                                             *)
(*   - T(sigma) <= exp(O(sigma ln sigma))  (Stirling-type, this file);   *)
(*   - fold Re z < 1/2 onto Re(1-z) >= 1/2 via XiC_symmetric.            *)
(*                                                                    *)
(*  This file: the clean pieces (XiC_factored, modulus reduction, the    *)
(*  Im-independent TC modulus bound).  Axiom-clean.                     *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra.
Require Import ComplexField Cmodulus RiemannXiEntire ThetaTailEntire MellinTail
        ImproperCv1 CImproperIntegral PerronEdge.
Open Scope R_scope.

(* XiC in factored form: 1/2 + 1/2.z.(z-1).(TC z + TC(1-z)) *)
Lemma XiC_factored : forall z,
  XiC z = Cadd (RtoC (/ 2))
    (Cmul (RtoC (/ 2)) (Cmul z (Cmul (Cminus z C1) (Cadd (TC z) (TC (Cminus C1 z)))))).
Proof.
  intro z. unfold XiC.
  assert (HA : Cadd (Cmul C0 z) (RtoC (/ 2)) = RtoC (/ 2))
    by (apply Ceq; cbn [Re Im Cadd Cmul Cminus Copp C0 C1 RtoC]; ring).
  assert (HB : Cadd (Cmul C1 z) C0 = z)
    by (apply Ceq; cbn [Re Im Cadd Cmul Cminus Copp C0 C1 RtoC]; ring).
  assert (HD : Cadd (Cmul C1 z) (Copp C1) = Cminus z C1)
    by (apply Ceq; cbn [Re Im Cadd Cmul Cminus Copp C0 C1 RtoC]; ring).
  assert (HE : Cadd (Cmul (Copp C1) z) C1 = Cminus C1 z)
    by (apply Ceq; cbn [Re Im Cadd Cmul Cminus Copp C0 C1 RtoC]; ring).
  rewrite HA, HB, HD, HE. reflexivity.
Qed.

Lemma Cmod_C1_eq1 : Cmod C1 = 1.
Proof. change C1 with (RtoC 1). rewrite Cmod_RtoC. apply Rabs_R1. Qed.

(* the modulus reduction *)
Lemma XiC_mod_reduction : forall z,
  Cmod (XiC z)
  <= / 2 + / 2 * (Cmod z + 1) ^ 2 * (Cmod (TC z) + Cmod (TC (Cminus C1 z))).
Proof.
  intro z. rewrite XiC_factored.
  set (S := Cmod (TC z) + Cmod (TC (Cminus C1 z))).
  assert (HS : 0 <= S) by (unfold S; pose proof (Cmod_nonneg (TC z));
                           pose proof (Cmod_nonneg (TC (Cminus C1 z))); lra).
  assert (Hz : 0 <= Cmod z) by apply Cmod_nonneg.
  eapply Rle_trans; [ apply Cmod_triangle | ].
  assert (H12 : Cmod (RtoC (/ 2)) = / 2) by (rewrite Cmod_RtoC, Rabs_right; lra).
  rewrite H12. apply Rplus_le_compat_l.
  rewrite Cmod_mul, H12.
  replace (/ 2 * (Cmod z + 1) ^ 2 * S) with (/ 2 * ((Cmod z + 1) ^ 2 * S)) by ring.
  apply Rmult_le_compat_l; [ lra | ].
  (* Cmod (z.((z-1).W)) <= (|z|+1)^2 . S *)
  rewrite !Cmod_mul.
  assert (Hzc1 : Cmod (Cminus z C1) <= Cmod z + 1).
  { replace (Cminus z C1) with (Cadd z (Copp C1))
      by (apply Ceq; cbn [Re Im Cadd Copp Cminus]; ring).
    eapply Rle_trans; [ apply Cmod_triangle | ].
    rewrite Cmod_opp, Cmod_C1_eq1. lra. }
  assert (HW : Cmod (Cadd (TC z) (TC (Cminus C1 z))) <= S) by (apply Cmod_triangle).
  apply Rle_trans with (Cmod z * ((Cmod z + 1) * S)).
  - apply Rmult_le_compat_l; [ exact Hz | ].
    apply Rmult_le_compat;
      [ apply Cmod_nonneg | apply Cmod_nonneg | exact Hzc1 | exact HW ].
  - simpl. nra.
Qed.

(* |TC z| <= T(Re z), independent of Im z (reuse of the Stage-2 chain) *)
Lemma TC_mod_le : forall z, Cmod (TC z) <= T (Re z).
Proof.
  intro z.
  apply (CImp_triangle (wkerC z) (cont_RI _ (cont_wkerC_re z))
           (cont_RI _ (cont_wkerC_im z)) (TC z)
           (cont_RI _ (Ccont_Cmod (wkerC z) (Ccont_wkerC z))) (T (Re z))).
  - exact (TC_spec z).
  - apply (improper_ext (wker (Re z)) (fun u => Cmod (wkerC z u))
             (wker_int (Re z)) (cont_RI _ (Ccont_Cmod (wkerC z) (Ccont_wkerC z)))
             (T (Re z))).
    + intros x _. symmetry. apply Cmod_wkerC.
    + exact (T_spec (Re z)).
Qed.

Print Assumptions XiC_mod_reduction.
Print Assumptions TC_mod_le.
