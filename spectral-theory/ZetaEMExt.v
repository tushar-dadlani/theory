(* ================================================================= *)
(*  ZetaEMExt.v  --  (s-1) zeta(s) carried to the half-plane Re s > -1.*)
(*                                                                    *)
(*  WHY.  To count zeta zeros in a disk about c = 1.1 + i t by the     *)
(*  peel/Jensen method, the bound circle must have radius > 2(a - 1/2) *)
(*  where a = Re c (CPeelBound's own header: the per-factor ratio is   *)
(*  alpha/(1-alpha), which is < 1 only for alpha < 1/2).  So the disk  *)
(*  necessarily reaches Re s < 0.  Every |zeta| bound in the repo      *)
(*  (ZetaStripBound.zetaC_bound) dies at Re s = 0.                     *)
(*                                                                    *)
(*  THE OBSERVATION.  No functional equation is needed.  The trapezoid *)
(*  Euler-Maclaurin representation                                     *)
(*                                                                    *)
(*     zeta(s) = 1/(s-1) + 1/2 + Sum_n htermC s n     (ZetaEM)         *)
(*                                                                    *)
(*  converges for Re s > -1, because ZetaTrap.Cmod_htermC_bound        *)
(*  majorises the n-th term by (n+1)^{-Re s - 2}, summable as soon as  *)
(*  Re s + 2 > 1.  That lemma is STATED with 0 <= Re s, but inspecting *)
(*  its proof the hypothesis is discharged in exactly one place -- the *)
(*  third argument of Rpow_negexp_anti inside Hmax, whose goal is      *)
(*  0 <= Re s + 2.  So it holds verbatim for -2 <= Re s.               *)
(*  Cmod_htermC_bound_ext below is that proof with the hypothesis      *)
(*  weakened and nothing else changed.                                 *)
(*                                                                    *)
(*  (ZetaEM.hmaj_step, by contrast, genuinely needs 0 <= Re s -- it    *)
(*  uses antitonicity of x |-> x^{-Re s}, which reverses below 0.  We  *)
(*  do not use it: the tail-after-M estimate is for the certified      *)
(*  evaluator, not for a circle bound.)                                *)
(*                                                                    *)
(*  THE OBJECT.  Rather than divide out the pole we write it away:     *)
(*                                                                    *)
(*     Bfn1 s := 1 + (s-1) * (1/2 + HsumT s)                           *)
(*                                                                    *)
(*  which EQUALS (s-1) zeta(s) on Re s > 0 (Bfn1_eq) but is manifestly *)
(*  regular at s = 1, with Bfn1 1 = 1 <> 0.  No removable-singularity  *)
(*  argument is needed anywhere.                                       *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia FunctionalExtensionality.
Require Import ComplexField Cmodulus CexpFull CPowBase CSeries CZetaTerm
        CDeriv CZeta ZetaTrap ZetaEM ZetaStripBound ZetaFn.
Open Scope R_scope.

(* ================================================================= *)
(*  1.  the per-term bound, on Re s >= -2                             *)
(* ================================================================= *)

Theorem Cmod_htermC_bound_ext : forall s n, -2 <= Re s -> Cminus C1 s <> C0 ->
  Cmod (htermC s n)
  <= / 6 * (Cmod s * Cmod (Cadd s C1) * Rpower (INR (S n)) (- Re s - 2)).
Proof.
  intros s n Hs Hs1.
  assert (Ha : 0 < INR (S n)) by (apply lt_0_INR; lia).
  set (a := INR (S n)) in *.
  set (M0 := Cmod s * Cmod (Cadd s C1) * Rpower a (- Re s - 2)).
  assert (HM0 : 0 <= M0).
  { unfold M0. apply Rmult_le_pos.
    - apply Rmult_le_pos; apply Cmod_nonneg.
    - unfold Rpower. left; apply exp_pos. }
  assert (Hb : INR (S (S n)) = a + 1) by (unfold a; rewrite S_INR; reflexivity).
  assert (Hmax : forall x, a <= x <= a + 1 -> Cmod (gd2C s x) <= M0).
  { intros x Hx. rewrite Cmod_gd2C. unfold M0.
    apply Rmult_le_compat_l; [ apply Rmult_le_pos; apply Cmod_nonneg | ].
    replace (- Re s - 2) with (- (Re s + 2)) by ring.
    apply Rpow_negexp_anti; [ exact Ha | lra | lra ]. }
  assert (HR : Rabs (Re (GC s (a + 1)) - Re (GC s a)
                     - 1 / 2 * (Re (gC s a) + Re (gC s (a + 1)))) <= M0 / 12).
  { apply (trap_bound (fun x => Re (gC s x)) (fun x => Re (gderivC s x))
             (fun x => Re (gd2C s x)) (fun x => Re (GC s x)) a M0).
    - intros x Hx. apply ReGC_deriv; [ lra | exact Hs1 ].
    - intros x Hx. apply RegC_deriv; lra.
    - intros x Hx. apply Regd_deriv; lra.
    - intros x Hx. eapply Rle_trans; [ apply Rabs_Re_le | apply Hmax; exact Hx ]. }
  assert (HI : Rabs (Im (GC s (a + 1)) - Im (GC s a)
                     - 1 / 2 * (Im (gC s a) + Im (gC s (a + 1)))) <= M0 / 12).
  { apply (trap_bound (fun x => Im (gC s x)) (fun x => Im (gderivC s x))
             (fun x => Im (gd2C s x)) (fun x => Im (GC s x)) a M0).
    - intros x Hx. apply ImGC_deriv; [ lra | exact Hs1 ].
    - intros x Hx. apply ImgC_deriv; lra.
    - intros x Hx. apply Imgd_deriv; lra.
    - intros x Hx. eapply Rle_trans; [ apply Rabs_Im_le | apply Hmax; exact Hx ]. }
  assert (ER : Re (htermC s n)
               = / 2 * (Re (gC s a) + Re (gC s (a + 1)))
                 - (Re (GC s (a + 1)) - Re (GC s a))).
  { unfold htermC. rewrite Hb, !Re_Cminus, Re_scal, Re_Cadd'. reflexivity. }
  assert (EI : Im (htermC s n)
               = / 2 * (Im (gC s a) + Im (gC s (a + 1)))
                 - (Im (GC s (a + 1)) - Im (GC s a))).
  { unfold htermC. rewrite Hb, !Im_Cminus, Im_scal, Im_Cadd'. reflexivity. }
  assert (HR2 : Rabs (Re (htermC s n)) <= M0 / 12).
  { rewrite ER.
    replace (/ 2 * (Re (gC s a) + Re (gC s (a + 1)))
             - (Re (GC s (a + 1)) - Re (GC s a)))
      with (- (Re (GC s (a + 1)) - Re (GC s a)
               - 1 / 2 * (Re (gC s a) + Re (gC s (a + 1))))) by field.
    rewrite Rabs_Ropp. exact HR. }
  assert (HI2 : Rabs (Im (htermC s n)) <= M0 / 12).
  { rewrite EI.
    replace (/ 2 * (Im (gC s a) + Im (gC s (a + 1)))
             - (Im (GC s (a + 1)) - Im (GC s a)))
      with (- (Im (GC s (a + 1)) - Im (GC s a)
               - 1 / 2 * (Im (gC s a) + Im (gC s (a + 1))))) by field.
    rewrite Rabs_Ropp. exact HI. }
  eapply Rle_trans; [ apply Cmod_le_comp | ].
  unfold M0 in *. lra.
Qed.

Lemma Kh_htermC_bound : forall s n, -2 <= Re s -> Cminus C1 s <> C0 ->
  Cmod (htermC s n) <= Kh s * Rpower (INR (S n)) (- (Re s + 2)).
Proof.
  intros s n Hs Hs1.
  pose proof (Cmod_htermC_bound_ext s n Hs Hs1) as H.
  unfold Kh. replace (- (Re s + 2)) with (- Re s - 2) by ring. lra.
Qed.

(* ================================================================= *)
(*  2.  convergence on Re s > -1                                      *)
(* ================================================================= *)

Lemma htermC_cv_ext : forall s, -1 < Re s -> Cminus C1 s <> C0 ->
  { Z | Cseries_cv (htermC s) Z }.
Proof.
  intros s Hs0 Hs1.
  apply (Cseries_abs_cv (htermC s)
           (fun n => Kh s * Rpower (INR (S n)) (- (Re s + 2)))).
  - intro n; apply Kh_htermC_bound; [ lra | exact Hs1 ].
  - destruct (pseries_cv (Re s + 2) ltac:(lra)) as [T HT].
    exists (Kh s * T).
    replace (sum_f_R0 (fun n => Kh s * Rpower (INR (S n)) (- (Re s + 2))))
      with (fun N => Kh s
             * sum_f_R0 (fun n => Rpower (INR (S n)) (- (Re s + 2))) N).
    + apply (CV_mult (fun _ => Kh s)
               (sum_f_R0 (fun n => Rpower (INR (S n)) (- (Re s + 2)))) (Kh s) T);
        [ apply Un_cv_const | exact HT ].
    + apply functional_extensionality; intro N.
      rewrite (scal_sum (fun n => Rpower (INR (S n)) (- (Re s + 2))) N (Kh s)).
      apply sum_eq; intros i _; ring.
Qed.

(* ---- the total wrapper, exactly ZetaFn's pattern ---- *)
Definition HsumT (s : C) : C :=
  match Rlt_dec (-1) (Re s) with
  | left h0 => match Ceq_dec2 (Cminus C1 s) C0 with
               | left _ => C0
               | right h1 => proj1_sig (htermC_cv_ext s h0 h1)
               end
  | right _ => C0
  end.

Lemma HsumT_cv : forall s (H0 : -1 < Re s) (H1 : Cminus C1 s <> C0),
  Cseries_cv (htermC s) (HsumT s).
Proof.
  intros s H0 H1. unfold HsumT.
  destruct (Rlt_dec (-1) (Re s)) as [h0 | h0]; [ | exfalso; lra ].
  destruct (Ceq_dec2 (Cminus C1 s) C0) as [Hc | h1];
    [ exfalso; apply H1; exact Hc | exact (proj2_sig (htermC_cv_ext s h0 h1)) ].
Qed.

(* ---- on Re s > 0 it is ZetaEM's Hsum ---- *)
Lemma HsumT_eq_Hsum : forall s (H0 : 0 < Re s) (H1 : Cminus C1 s <> C0),
  HsumT s = Hsum s H0 H1.
Proof.
  intros s H0 H1.
  apply (CUn_cv_unique (Cpsum (htermC s)));
    [ exact (HsumT_cv s ltac:(lra) H1) | exact (htermC_cv s H0 H1) ].
Qed.

(* ================================================================= *)
(*  3.  Bfn1 = (s-1) zeta(s), with the pole written away              *)
(* ================================================================= *)

Definition Bfn1 (s : C) : C :=
  Cadd C1 (Cmul (Cminus s C1) (Cadd (RtoC (/ 2)) (HsumT s))).

Lemma Bfn1_at_one : Bfn1 C1 = C1.
Proof. unfold Bfn1. ring. Qed.

Lemma Bfn1_ne0_at_one : Bfn1 C1 <> C0.
Proof. rewrite Bfn1_at_one. exact C1_neq_C0. Qed.

Lemma sub1_ne0 : forall s, Cminus C1 s <> C0 -> Cminus s C1 <> C0.
Proof.
  intros s H Hc. apply H.
  replace (Cminus C1 s) with (Copp (Cminus s C1)) by ring.
  rewrite Hc. apply Ceq; cbn; ring.
Qed.

Theorem Bfn1_eq : forall s (H0 : 0 < Re s) (H1 : Cminus C1 s <> C0),
  Bfn1 s = Cmul (Cminus s C1) (zetaC s H0 H1).
Proof.
  intros s H0 H1.
  pose proof (sub1_ne0 s H1) as Hne.
  unfold Bfn1.
  rewrite (HsumT_eq_Hsum s H0 H1), (zetaC_trapezoid s H0 H1).
  field. exact Hne.
Qed.

Theorem Bfn1_zero_iff : forall s, 0 < Re s -> Cminus C1 s <> C0 ->
  (Bfn1 s = C0 <-> zF s = C0).
Proof.
  intros s H0 H1. pose proof (sub1_ne0 s H1) as Hne.
  rewrite (Bfn1_eq s H0 H1), <- (zF_eq s H0 H1). split.
  - intro Hz. destruct (Ceq_dec2 (zF s) C0) as [Hy | Hn]; [ exact Hy | ].
    exfalso. exact (Cmul_ne0 _ _ Hne Hn Hz).
  - intro Hz. rewrite Hz. ring.
Qed.

(* ================================================================= *)
(*  4.  the bound: cubic in |s|, uniform in the height                *)
(* ================================================================= *)

Theorem HsumT_bound : forall s, -1 < Re s -> Cminus C1 s <> C0 ->
  Cmod (HsumT s) <= Kh s * (1 + / (Re s + 1)).
Proof.
  intros s H0 H1.
  assert (HK : 0 <= Kh s) by apply Kh_nonneg.
  assert (Hpb : forall N, Cmod (Cpsum (htermC s) N) <= Kh s * (1 + / (Re s + 1))).
  { intro N. eapply Rle_trans; [ apply Cmod_Cpsum_le | ].
    eapply Rle_trans.
    - apply sum_Rle. intros n _. apply Kh_htermC_bound; [ lra | exact H1 ].
    - assert (Heq : sum_f_R0 (fun n => Kh s * Rpower (INR (S n)) (- (Re s + 2))) N
                  = Kh s * sum_f_R0 (fun n => Rpower (INR (S n)) (- (Re s + 2))) N).
      { rewrite (scal_sum (fun n => Rpower (INR (S n)) (- (Re s + 2))) N (Kh s)).
        apply sum_eq; intros i _; ring. }
      rewrite Heq.
      pose proof (pseries_partial_ub (Re s + 2) ltac:(lra) N) as Hub.
      replace (Re s + 2 - 1) with (Re s + 1) in Hub by ring.
      nra. }
  eapply Rle_cv_lim.
  - exact Hpb.
  - apply CUn_cv_Cmod. exact (HsumT_cv s H0 H1).
  - apply Un_cv_const.
Qed.

Theorem Bfn1_bound : forall s, -1 < Re s -> Cminus C1 s <> C0 ->
  Cmod (Bfn1 s)
  <= 1 + Cmod (Cminus s C1) * (/ 2 + Kh s * (1 + / (Re s + 1))).
Proof.
  intros s H0 H1.
  pose proof (HsumT_bound s H0 H1) as HS.
  pose proof (Cmod_nonneg (Cminus s C1)) as Hm0.
  unfold Bfn1.
  eapply Rle_trans; [ apply Cmod_triangle | ].
  rewrite Cmod_one.
  apply Rplus_le_compat_l.
  rewrite Cmod_mul.
  apply Rmult_le_compat_l; [ exact Hm0 | ].
  eapply Rle_trans; [ apply Cmod_triangle | ].
  rewrite Cmod_RtoC, Rabs_pos_eq by lra.
  lra.
Qed.

Print Assumptions Bfn1_eq.
Print Assumptions Bfn1_bound.

(* ================================================================= *)
(*  END ZetaEMExt.v                                                   *)
(* ================================================================= *)
