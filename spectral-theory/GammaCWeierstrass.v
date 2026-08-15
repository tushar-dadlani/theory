(* ================================================================= *)
(*  GammaCWeierstrass.v   (complex Weierstrass product, part 1)          *)
(*                                                                    *)
(*  The complex reciprocal product                                      *)
(*     Pc z = z * e^{gamma z} * prod_{k>=1} (1 + z/k) e^{-z/k}           *)
(*  converges pointwise (CInfProd.Pprod_cv, dev = O(1/k^2)) and agrees   *)
(*  on the real axis with the real  Pval  of GammaWeierstrass:           *)
(*     Pc (RtoC s) = RtoC (Pval s Hs).                                   *)
(*  This is the anchor for the identity  GammaC z * Pc z = 1  on {Re>0}. *)
(*                                                                    *)
(*  Axioms: standard classical-Reals only.                            *)
(* ================================================================= *)

From Stdlib Require Import Reals Rpower Lra Lia Factorial.
Require Import ComplexField Cmodulus CexpFull CSeries CInfProd CexpRemainder
        GammaWeierstrass EulerMascheroni.
Open Scope R_scope.

(* ------------------------------------------------------------------ *)
(*  small Cmod helpers (proved locally to avoid import hunting)        *)
(* ------------------------------------------------------------------ *)

Lemma cmodC1 : Cmod C1 = 1.
Proof. replace C1 with (RtoC 1) by reflexivity. rewrite Cmod_RtoC. apply Rabs_R1. Qed.

Lemma cmodC0 : Cmod C0 = 0.
Proof. replace C0 with (RtoC 0) by reflexivity. rewrite Cmod_RtoC, Rabs_R0. reflexivity. Qed.

Lemma cmodInv : forall c, c <> C0 -> Cmod (Cinv c) = / Cmod c.
Proof.
  intros c Hc. assert (Hm : Cmod c <> 0) by (intro H; apply Hc, (proj1 (Cmod0 c)); exact H).
  apply (Rmult_eq_reg_l (Cmod c)); [ | exact Hm ].
  rewrite <- Cmod_mul. replace (Cmul c (Cinv c)) with (Cmul (Cinv c) c) by ring.
  rewrite Cinv_l by exact Hc. rewrite cmodC1, Rinv_r by exact Hm. reflexivity.
Qed.

Lemma rtocOpp : forall r, Copp (RtoC r) = RtoC (- r).
Proof. intro r. unfold Copp, RtoC. apply Ceq; cbn [Re Im]; ring. Qed.

Lemma cinvRtoC : forall r, r <> 0 -> Cinv (RtoC r) = RtoC (/ r).
Proof.
  intros r Hr.
  assert (Hne : RtoC r <> C0).
  { intro H. apply Hr. apply (f_equal Re) in H. unfold RtoC, C0 in H; cbn [Re] in H. exact H. }
  assert (Hml : Cmul (RtoC (/ r)) (RtoC r) = C1)
    by (rewrite <- RtoC_mul, Rinv_l by exact Hr; reflexivity).
  transitivity (Cmul (Cinv (RtoC r)) (Cmul (RtoC (/ r)) (RtoC r))).
  - rewrite Hml; ring.
  - replace (Cmul (Cinv (RtoC r)) (Cmul (RtoC (/ r)) (RtoC r)))
       with (Cmul (Cmul (Cinv (RtoC r)) (RtoC r)) (RtoC (/ r))) by ring.
    rewrite Cinv_l by exact Hne. ring.
Qed.

Lemma sumR0_le : forall (A B : nat -> R) N,
  (forall i, A i <= B i) -> sum_f_R0 A N <= sum_f_R0 B N.
Proof.
  intros A B N H; induction N; cbn [sum_f_R0]; [ apply H | pose proof (H (S N)); lra ].
Qed.

Lemma Snpos' : forall n, 0 < INR (S n).
Proof. intro n; apply lt_0_INR; lia. Qed.

(* sum of 1/k^2 is bounded by 2 *)
Lemma invsq_aux : forall N, (1 <= N)%nat ->
  sum_f_R0 (fun k => / (INR k) ^ 2) N <= 2 - / INR N.
Proof.
  induction N as [| N IH]; [ lia | intros _ ].
  destruct (Nat.eq_dec N 0) as [-> | Hne].
  - cbn [sum_f_R0]. replace (INR 0) with 0 by reflexivity.
    replace (/ 0 ^ 2) with 0 by (simpl; rewrite Rmult_0_l, Rinv_0; reflexivity).
    replace (INR 1) with 1 by (simpl; ring). lra.
  - rewrite tech5. specialize (IH ltac:(lia)).
    set (a := INR (S N)) in *.
    assert (Ha2 : 2 <= a) by (unfold a; replace 2 with (INR 2) by (simpl; ring);
                              apply le_INR; lia).
    assert (Ha0 : 0 < a) by lra.
    assert (HaN : INR N = a - 1) by (unfold a; rewrite S_INR; ring).
    assert (Hstep : / a ^ 2 <= / INR N - / a).
    { rewrite HaN.
      replace (/ a ^ 2) with (/ (a * a)) by (simpl; rewrite Rmult_1_r; reflexivity).
      replace (/ (a - 1) - / a) with (/ ((a - 1) * a))
        by (field; repeat split; apply Rgt_not_eq; lra).
      apply Rinv_le_contravar; [ apply Rmult_lt_0_compat; lra | ].
      apply Rmult_le_compat_r; lra. }
    lra.
Qed.

Lemma invsq_bound : forall N, sum_f_R0 (fun k => / (INR k) ^ 2) N <= 2.
Proof.
  intro N. destruct N as [| N].
  - cbn [sum_f_R0]. replace (INR 0) with 0 by reflexivity.
    replace (/ 0 ^ 2) with 0 by (simpl; rewrite Rmult_0_l, Rinv_0; reflexivity). lra.
  - pose proof (invsq_aux (S N) ltac:(lia)) as H.
    assert (0 <= / INR (S N)) by (left; apply Rinv_0_lt_compat, Snpos'). lra.
Qed.

(* ------------------------------------------------------------------ *)
(*  the complex product factor  (1 + z/k) e^{-z/k}                     *)
(* ------------------------------------------------------------------ *)

Definition wcf (z : C) (k : nat) : C :=
  match k with
  | O => C1
  | S m => Cmul (Cadd C1 (Cdiv z (RtoC (INR (S m)))))
                (Cexpf (Copp (Cdiv z (RtoC (INR (S m))))))
  end.

Lemma wcf_RtoC : forall s k, wcf (RtoC s) k = RtoC (wq s k).
Proof.
  intros s k. destruct k as [| m].
  - simpl. assert (Hw0 : wq s 0 = 1).
    { unfold wq. replace (INR 0) with 0 by reflexivity.
      unfold Rdiv. rewrite Rinv_0, Rmult_0_r, Ropp_0, exp_0. ring. }
    rewrite Hw0. reflexivity.
  - cbn [wcf]. unfold wq.
    assert (Hn : INR (S m) <> 0) by (apply Rgt_not_eq, Snpos').
    assert (Hd : Cdiv (RtoC s) (RtoC (INR (S m))) = RtoC (s / INR (S m))).
    { unfold Cdiv. rewrite (cinvRtoC (INR (S m)) Hn), <- RtoC_mul. reflexivity. }
    rewrite Hd, rtocOpp, Cexpf_RtoC.
    replace (Cadd C1 (RtoC (s / INR (S m)))) with (RtoC (1 + s / INR (S m)))
      by (change C1 with (RtoC 1); rewrite <- RtoC_add; reflexivity).
    rewrite <- RtoC_mul. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  the deviation  |wcf z k - 1| = O(1/k^2)                            *)
(* ------------------------------------------------------------------ *)

Definition Kz (z : C) : R := Cmod z ^ 2 * (1 + 3 * (1 + Cmod z) * exp (Cmod z)).

Lemma Kz_nonneg : forall z, 0 <= Kz z.
Proof.
  intro z. unfold Kz. apply Rmult_le_pos; [ apply pow_le, Cmod_nonneg | ].
  pose proof (Cmod_nonneg z). pose proof (exp_pos (Cmod z)).
  apply Rplus_le_le_0_compat; [ lra | repeat apply Rmult_le_pos; lra ].
Qed.

Lemma wcf_dev_le : forall z k, dev (wcf z) k <= Kz z * / (INR k) ^ 2.
Proof.
  intros z k. destruct k as [| m].
  - unfold dev. simpl wcf. replace (Cminus C1 C1) with C0 by ring. rewrite cmodC0.
    assert (H0 : (INR 0) ^ 2 = 0) by (simpl; ring).
    rewrite H0, Rinv_0, Rmult_0_r. apply Rle_refl.
  - unfold dev. cbn [wcf].
    set (w := Cdiv z (RtoC (INR (S m)))).
    set (Rem := Cminus (Cminus (Cexpf (Copp w)) C1) (Copp w)).
    assert (Hexp : Cexpf (Copp w) = Cadd (Cadd C1 (Copp w)) Rem) by (unfold Rem; ring).
    assert (Hid : Cminus (Cmul (Cadd C1 w) (Cexpf (Copp w))) C1
                  = Cadd (Copp (Cmul w w)) (Cmul (Cadd C1 w) Rem))
      by (rewrite Hexp; ring).
    rewrite Hid.
    assert (Hmw0 : 0 <= Cmod w) by apply Cmod_nonneg.
    assert (HRem : Cmod Rem <= 3 * Cmod w ^ 2 * exp (Cmod w)).
    { unfold Rem. pose proof (Cexpf_remainder (Copp w)) as H. rewrite Cmod_opp in H. exact H. }
    assert (H1w : Cmod (Cadd C1 w) <= 1 + Cmod w).
    { eapply Rle_trans; [ apply Cmod_triangle | ]. rewrite cmodC1. apply Rle_refl. }
    assert (Hmw_eq : Cmod w = Cmod z / INR (S m)).
    { unfold w, Cdiv. rewrite Cmod_mul, cmodInv, Cmod_RtoC.
      - rewrite (Rabs_right (INR (S m))) by (apply Rle_ge, Rlt_le, Snpos'). reflexivity.
      - intro Hc; apply (f_equal Re) in Hc; unfold RtoC, C0 in Hc; cbn [Re] in Hc;
          pose proof (Snpos' m); lra. }
    assert (HmwZ : Cmod w <= Cmod z).
    { rewrite Hmw_eq. unfold Rdiv. rewrite <- (Rmult_1_r (Cmod z)) at 2.
      apply Rmult_le_compat_l; [ apply Cmod_nonneg | ].
      rewrite <- Rinv_1. apply Rinv_le_contravar; [ lra | rewrite <- INR_1; apply le_INR; lia ]. }
    assert (HmwSq : Cmod w ^ 2 = Cmod z ^ 2 * / INR (S m) ^ 2).
    { rewrite Hmw_eq. unfold Rdiv. rewrite Rpow_mult_distr, pow_inv. reflexivity. }
    assert (Hfac : (1 + Cmod w) * exp (Cmod w) <= (1 + Cmod z) * exp (Cmod z)).
    { apply Rmult_le_compat; [ lra | left; apply exp_pos | lra | ].
      destruct (Rle_lt_or_eq_dec (Cmod w) (Cmod z) HmwZ) as [Hlt | Heq];
        [ left; apply exp_increasing; exact Hlt | rewrite Heq; apply Rle_refl ]. }
    assert (Hmono : 1 + 3 * (1 + Cmod w) * exp (Cmod w) <= 1 + 3 * (1 + Cmod z) * exp (Cmod z)).
    { assert (3 * (1 + Cmod w) * exp (Cmod w) <= 3 * (1 + Cmod z) * exp (Cmod z)).
      { replace (3 * (1 + Cmod w) * exp (Cmod w)) with (3 * ((1 + Cmod w) * exp (Cmod w))) by ring.
        replace (3 * (1 + Cmod z) * exp (Cmod z)) with (3 * ((1 + Cmod z) * exp (Cmod z))) by ring.
        apply Rmult_le_compat_l; [ lra | exact Hfac ]. }
      lra. }
    (* triangle + factor bound *)
    eapply Rle_trans; [ apply Cmod_triangle | ].
    rewrite Cmod_opp, Cmod_mul, Cmod_mul.
    apply Rle_trans with (Cmod w * Cmod w + (1 + Cmod w) * (3 * Cmod w ^ 2 * exp (Cmod w))).
    + apply Rplus_le_compat_l. apply Rmult_le_compat;
        [ apply Cmod_nonneg | apply Cmod_nonneg | exact H1w | exact HRem ].
    + assert (Heq1 : Cmod w * Cmod w + (1 + Cmod w) * (3 * Cmod w ^ 2 * exp (Cmod w))
               = Cmod w ^ 2 * (1 + 3 * (1 + Cmod w) * exp (Cmod w))) by ring.
      rewrite Heq1, HmwSq.
      apply Rle_trans with
        (Cmod z ^ 2 * / INR (S m) ^ 2 * (1 + 3 * (1 + Cmod z) * exp (Cmod z))).
      * apply Rmult_le_compat_l; [ | exact Hmono ].
        apply Rmult_le_pos; [ apply pow_le, Cmod_nonneg
                            | left; apply Rinv_0_lt_compat, pow_lt, Snpos' ].
      * unfold Kz. apply Req_le. ring.
Qed.

(* ------------------------------------------------------------------ *)
(*  summability, hence pointwise convergence of the complex product   *)
(* ------------------------------------------------------------------ *)

Definition devsum_cv (z : C) : { T | Un_cv (sum_f_R0 (dev (wcf z))) T }.
Proof.
  set (Un := sum_f_R0 (dev (wcf z))).
  assert (Hgrow : Un_growing Un).
  { intro N. unfold Un. rewrite tech5. pose proof (Cmod_nonneg (Cminus (wcf z (S N)) C1)).
    unfold dev; lra. }
  assert (Hub : has_ub Un).
  { exists (Kz z * 2). intros v [N ->]. unfold Un.
    eapply Rle_trans.
    - apply (sumR0_le (dev (wcf z)) (fun k => / (INR k) ^ 2 * Kz z)).
      intro i. rewrite Rmult_comm. apply wcf_dev_le.
    - rewrite <- (scal_sum (fun k => / (INR k) ^ 2) N (Kz z)).
      apply Rmult_le_compat_l; [ apply Kz_nonneg | apply invsq_bound ]. }
  destruct (growing_cv Un Hgrow Hub) as [l Hl]. exists l; exact Hl.
Defined.

Definition Wc (z : C) : C :=
  proj1_sig (Pprod_cv (wcf z) (proj1_sig (devsum_cv z)) (proj2_sig (devsum_cv z))).

Lemma Wc_spec : forall z, CUn_cv (Pprod (wcf z)) (Wc z).
Proof.
  intro z. unfold Wc.
  exact (proj2_sig (Pprod_cv (wcf z) (proj1_sig (devsum_cv z)) (proj2_sig (devsum_cv z)))).
Qed.

(* ------------------------------------------------------------------ *)
(*  the complex product  Pc  and its real-axis agreement              *)
(* ------------------------------------------------------------------ *)

Definition Pc (z : C) : C := Cmul (Cmul z (Cexpf (Cmul (RtoC gamma) z))) (Wc z).

Lemma Pprod_wcf_RtoC : forall s N, Pprod (wcf (RtoC s)) N = RtoC (Wprod s N).
Proof.
  intros s N. induction N as [| N IH].
  - cbn [Pprod wcf Wprod]. reflexivity.
  - rewrite Pprod_S, IH, (wcf_RtoC s (S N)), <- RtoC_mul. reflexivity.
Qed.

Lemma Wc_RtoC : forall s (Hs : 0 < s), Wc (RtoC s) = RtoC (exp (Winf s Hs)).
Proof.
  intros s Hs.
  pose proof (proj1 (CUn_cv_comp (Pprod (wcf (RtoC s))) (Wc (RtoC s))) (Wc_spec (RtoC s)))
    as [HRe HIm].
  (* Re (Pprod ... N) = Wprod s N,  Im = 0 *)
  assert (HReW : Un_cv (Wprod s) (Re (Wc (RtoC s)))).
  { apply (Un_cv_ext (fun N => Re (Pprod (wcf (RtoC s)) N))); [ | exact HRe ].
    intro N. rewrite Pprod_wcf_RtoC. reflexivity. }
  assert (HImW : Im (Wc (RtoC s)) = 0).
  { apply (UL_sequence (fun N => Im (Pprod (wcf (RtoC s)) N))); [ exact HIm | ].
    apply (Un_cv_ext (fun _ => 0)); [ intro N; rewrite Pprod_wcf_RtoC; reflexivity | ].
    intros eps He; exists 0%nat; intros n _; unfold R_dist; rewrite Rminus_0_r, Rabs_R0; exact He. }
  assert (HReW2 : Re (Wc (RtoC s)) = exp (Winf s Hs))
    by (apply (UL_sequence (Wprod s)); [ exact HReW | apply Wprod_cv ]).
  apply Ceq; [ rewrite HReW2; reflexivity | rewrite HImW; reflexivity ].
Qed.

Theorem Pc_agree : forall s (Hs : 0 < s), Pc (RtoC s) = RtoC (Pval s Hs).
Proof.
  intros s Hs. unfold Pc.
  rewrite (Wc_RtoC s Hs).
  replace (Cmul (RtoC gamma) (RtoC s)) with (RtoC (gamma * s)) by (rewrite <- RtoC_mul; reflexivity).
  rewrite Cexpf_RtoC.
  rewrite <- RtoC_mul, <- RtoC_mul.
  unfold Pval.
  replace (s * exp (gamma * s) * exp (Winf s Hs)) with (s * exp (Winf s Hs) * exp (s * gamma))
    by (rewrite (Rmult_comm gamma s); ring).
  reflexivity.
Qed.

Print Assumptions Pc_agree.
