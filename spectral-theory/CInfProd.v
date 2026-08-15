(* ================================================================= *)
(*  CInfProd.v   (complex infinite products)                           *)
(*                                                                    *)
(*  If  sum_n Cmod(f n - 1)  converges, then the partial products      *)
(*    Pprod f N = f 0 * f 1 * ... * f N                                 *)
(*  converge (CUn_cv).  Standard proof: |Pprod| <= prod(1+|dev|) <=     *)
(*  exp(sum|dev|) is bounded, and the tail telescopes to a Cauchy        *)
(*  bound  exp(T)*(exp(T - partial) - 1) -> 0, so (Re,Im) are real       *)
(*  Cauchy sequences (R_complete).                                      *)
(*                                                                    *)
(*  Convergence infrastructure for the Weierstrass product              *)
(*  1/Gamma(z) = z e^{gamma z} prod (1+z/n) e^{-z/n}.                   *)
(*                                                                    *)
(*  Axioms: standard classical-Reals only.                            *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import ComplexField Cmodulus CSeries.
Open Scope R_scope.

Lemma exp_le : forall x y, x <= y -> exp x <= exp y.
Proof.
  intros x y H. destruct (Rle_lt_or_eq_dec x y H) as [Hlt | Heq].
  - left; apply exp_increasing; exact Hlt.
  - rewrite Heq; apply Rle_refl.
Qed.

Lemma Cmod_C1_eq1 : Cmod C1 = 1.
Proof. replace C1 with (RtoC 1) by reflexivity; rewrite Cmod_RtoC; apply Rabs_R1. Qed.

Lemma CV_const : forall a : R, Un_cv (fun _ => a) a.
Proof.
  intros a eps Heps. exists 0%nat. intros n _. unfold R_dist.
  replace (a - a) with 0 by ring. rewrite Rabs_R0. exact Heps.
Qed.

(* ----------------------------------------------------------------- *)
(*  partial products and the real modulus-product majorant           *)
(* ----------------------------------------------------------------- *)
Fixpoint Pprod (f : nat -> C) (N : nat) : C :=
  match N with O => f O | S M => Cmul (Pprod f M) (f (S M)) end.

Fixpoint RPdev (b : nat -> R) (N : nat) : R :=
  match N with O => 1 + b O | S M => RPdev b M * (1 + b (S M)) end.

Definition dev (f : nat -> C) (n : nat) : R := Cmod (Cminus (f n) C1).

Lemma dev_nonneg : forall f n, 0 <= dev f n.
Proof. intros f n; apply Cmod_nonneg. Qed.

Lemma RPdev_ge1 : forall (b : nat -> R), (forall n, 0 <= b n) ->
  forall N, 1 <= RPdev b N.
Proof.
  intros b Hb N. induction N as [| N IH]; simpl.
  - pose proof (Hb 0%nat); lra.
  - pose proof (Hb (S N)). rewrite <- (Rmult_1_r 1). apply Rmult_le_compat; lra.
Qed.

Lemma RPdev_le_exp : forall (b : nat -> R), (forall n, 0 <= b n) ->
  forall N, RPdev b N <= exp (sum_f_R0 b N).
Proof.
  intros b Hb N. induction N as [| N IH]; simpl.
  - apply exp_ineq1_le.
  - eapply Rle_trans.
    + apply Rmult_le_compat.
      * pose proof (RPdev_ge1 b Hb N); lra.
      * pose proof (Hb (S N)); lra.
      * exact IH.
      * apply (exp_ineq1_le (b (S N))).
    + rewrite <- exp_plus. apply Rle_refl.
Qed.

Lemma Cmod_shift1 : forall c, Cmod c <= 1 + Cmod (Cminus c C1).
Proof.
  intro c. apply Rle_trans with (Cmod C1 + Cmod (Cminus c C1)).
  - replace c with (Cadd C1 (Cminus c C1)) at 1 by ring. apply Cmod_triangle.
  - rewrite Cmod_C1_eq1. apply Rle_refl.
Qed.

Lemma Pprod_mod_le : forall f N, Cmod (Pprod f N) <= RPdev (dev f) N.
Proof.
  intros f N. induction N as [| N IH]; simpl.
  - apply Cmod_shift1.
  - rewrite Cmod_mul. apply Rmult_le_compat;
      [ apply Cmod_nonneg | apply Cmod_nonneg | exact IH | apply Cmod_shift1 ].
Qed.

Lemma Pprod_dev_bound : forall f N,
  Cmod (Cminus (Pprod f N) C1) <= RPdev (dev f) N - 1.
Proof.
  intros f N. induction N as [| N IH]; simpl.
  - unfold dev; lra.
  - replace (Cminus (Cmul (Pprod f N) (f (S N))) C1)
       with (Cadd (Cmul (Pprod f N) (Cminus (f (S N)) C1)) (Cminus (Pprod f N) C1)) by ring.
    eapply Rle_trans; [ apply Cmod_triangle | ]. rewrite Cmod_mul.
    eapply Rle_trans.
    + apply Rplus_le_compat.
      * apply Rmult_le_compat_r; [ apply Cmod_nonneg | apply Pprod_mod_le ].
      * exact IH.
    + apply Req_le. unfold dev. ring.
Qed.

Lemma Pprod_S : forall f n, Pprod f (S n) = Cmul (Pprod f n) (f (S n)).
Proof. reflexivity. Qed.

Lemma Pprod_split : forall f M k,
  Pprod f (S (M + k)) = Cmul (Pprod f M) (Pprod (fun j => f (S (M + j))) k).
Proof.
  intros f M k. induction k as [| k IH].
  - simpl. rewrite Nat.add_0_r. reflexivity.
  - replace (M + S k)%nat with (S (M + k))%nat by lia.
    rewrite (Pprod_S f (S (M + k))), IH, (Pprod_S (fun j => f (S (M + j))) k).
    replace (M + S k)%nat with (S (M + k))%nat by lia. ring.
Qed.

Lemma sumtail_eq : forall b M J,
  sum_f_R0 (fun j => b (S (M + j))) J = sum_f_R0 b (S (M + J)) - sum_f_R0 b M.
Proof.
  intros b M J. induction J as [| J IH].
  - simpl. rewrite !Nat.add_0_r. ring.
  - rewrite (tech5 (fun j => b (S (M + j))) J). rewrite IH.
    replace (M + S J)%nat with (S (M + J))%nat by lia.
    rewrite (tech5 b (S (M + J))). ring.
Qed.

(* ----------------------------------------------------------------- *)
(*  the Cauchy tail bound and convergence                            *)
(* ----------------------------------------------------------------- *)
Section Converge.
Variable f : nat -> C.
Variable T : R.
Hypothesis HT : Un_cv (sum_f_R0 (dev f)) T.

Lemma sum_dev_le_T : forall N, sum_f_R0 (dev f) N <= T.
Proof.
  intro N. apply (growing_ineq (sum_f_R0 (dev f))); [ | exact HT ].
  intro n. rewrite tech5. pose proof (dev_nonneg f (S n)); lra.
Qed.

Lemma tail_bound : forall M n, (M <= n)%nat ->
  Cmod (Cminus (Pprod f n) (Pprod f M))
    <= exp T * (exp (T - sum_f_R0 (dev f) M) - 1).
Proof.
  intros M n Hle.
  assert (Hpos : 0 <= exp (T - sum_f_R0 (dev f) M) - 1).
  { pose proof (sum_dev_le_T M).
    assert (1 <= exp (T - sum_f_R0 (dev f) M))
      by (rewrite <- exp_0; apply exp_le; lra). lra. }
  destruct (Nat.eq_dec M n) as [Heq | Hne].
  - subst n. replace (Cminus (Pprod f M) (Pprod f M)) with C0 by ring.
    assert (Cmod C0 = 0) by (apply (proj2 (Cmod0 _)); reflexivity).
    rewrite H. apply Rmult_le_pos; [ left; apply exp_pos | exact Hpos ].
  - assert (Hk : exists k, n = S (M + k)%nat) by (exists (n - M - 1)%nat; lia).
    destruct Hk as [k Hk]. subst n.
    rewrite Pprod_split.
    replace (Cminus (Cmul (Pprod f M) (Pprod (fun j => f (S (M + j))) k)) (Pprod f M))
       with (Cmul (Pprod f M) (Cminus (Pprod (fun j => f (S (M + j))) k) C1)) by ring.
    rewrite Cmod_mul.
    apply Rmult_le_compat.
    + apply Cmod_nonneg.
    + apply Cmod_nonneg.
    + (* Cmod (Pprod f M) <= exp T *)
      eapply Rle_trans; [ apply Pprod_mod_le | ].
      eapply Rle_trans; [ apply (RPdev_le_exp (dev f) (dev_nonneg f) M) | ].
      apply exp_le. apply sum_dev_le_T.
    + (* Cmod (Pprod shifted - 1) <= exp (T - sum M) - 1 *)
      eapply Rle_trans; [ apply (Pprod_dev_bound (fun j => f (S (M + j))) k) | ].
      apply Rplus_le_compat_r.
      eapply Rle_trans;
        [ apply (RPdev_le_exp (dev (fun j => f (S (M + j)))) (dev_nonneg _)) | ].
      apply exp_le.
      (* sum_f_R0 (dev shifted) k = sum (dev f) (S(M+k)) - sum (dev f) M <= T - sum M *)
      change (dev (fun j => f (S (M + j)))) with (fun j => dev f (S (M + j))).
      rewrite sumtail_eq. pose proof (sum_dev_le_T (S (M + k))). lra.
Qed.

Theorem Pprod_cv : { P : C | CUn_cv (Pprod f) P }.
Proof.
  (* Re and Im are real Cauchy sequences *)
  assert (Hcau : forall eps, 0 < eps -> exists N, forall n m, (N <= n)%nat -> (N <= m)%nat ->
            Cmod (Cminus (Pprod f n) (Pprod f m)) < eps).
  { intros eps Heps.
    (* choose M with exp T (exp(T - sum M) - 1) < eps/2 *)
    assert (Hcv : Un_cv (fun M => exp T * (exp (T - sum_f_R0 (dev f) M) - 1)) 0).
    { assert (H1 : Un_cv (fun M => T - sum_f_R0 (dev f) M) 0).
      { replace 0 with (T - T) by ring. apply CV_minus; [ apply CV_const | exact HT ]. }
      assert (H2 : Un_cv (fun M => exp (T - sum_f_R0 (dev f) M)) 1).
      { replace 1 with (exp 0) by (rewrite exp_0; reflexivity).
        apply (continuity_seq exp (fun M => T - sum_f_R0 (dev f) M) 0); [ | exact H1 ].
        apply derivable_continuous; apply derivable_exp. }
      assert (H3 : Un_cv (fun M => exp (T - sum_f_R0 (dev f) M) - 1) 0).
      { replace 0 with (1 - 1) by ring. apply CV_minus; [ exact H2 | apply CV_const ]. }
      replace 0 with (exp T * 0) by ring.
      apply CV_mult; [ apply CV_const | exact H3 ]. }
    destruct (Hcv (eps / 2) ltac:(lra)) as [M HM].
    exists M. intros n m Hn Hm.
    pose proof (HM M (le_n M)) as HMM. unfold R_dist in HMM. rewrite Rminus_0_r in HMM.
    assert (Hb : forall p, (M <= p)%nat -> Cmod (Cminus (Pprod f p) (Pprod f M)) < eps / 2).
    { intros p Hp. eapply Rle_lt_trans; [ apply tail_bound; exact Hp | ].
      rewrite Rabs_right in HMM; [ exact HMM | ].
      apply Rle_ge. eapply Rle_trans; [ | apply tail_bound with (n := M) (M := M); lia ].
      apply Cmod_nonneg. }
    eapply Rle_lt_trans.
    - replace (Cminus (Pprod f n) (Pprod f m))
         with (Cadd (Cminus (Pprod f n) (Pprod f M)) (Cminus (Pprod f M) (Pprod f m))) by ring.
      apply Cmod_triangle.
    - assert (H1 : Cmod (Cminus (Pprod f n) (Pprod f M)) < eps / 2) by (apply Hb; exact Hn).
      assert (H2 : Cmod (Cminus (Pprod f M) (Pprod f m)) < eps / 2).
      { rewrite <- Cmod_opp. replace (Copp (Cminus (Pprod f M) (Pprod f m)))
          with (Cminus (Pprod f m) (Pprod f M)) by ring. apply Hb; exact Hm. }
      lra. }
  (* real Cauchy => converge, componentwise *)
  assert (HReC : Cauchy_crit (fun n => Re (Pprod f n))).
  { intros eps Heps. destruct (Hcau eps Heps) as [N HN]. exists N. intros n m Hn Hm.
    unfold R_dist. eapply Rle_lt_trans; [ | apply (HN n m Hn Hm) ].
    replace (Re (Pprod f n) - Re (Pprod f m)) with (Re (Cminus (Pprod f n) (Pprod f m)))
      by (unfold Cminus, Cadd, Copp; cbn [Re Im]; ring).
    apply Cmod_Re_le. }
  assert (HImC : Cauchy_crit (fun n => Im (Pprod f n))).
  { intros eps Heps. destruct (Hcau eps Heps) as [N HN]. exists N. intros n m Hn Hm.
    unfold R_dist. eapply Rle_lt_trans; [ | apply (HN n m Hn Hm) ].
    replace (Im (Pprod f n) - Im (Pprod f m)) with (Im (Cminus (Pprod f n) (Pprod f m)))
      by (unfold Cminus, Cadd, Copp; cbn [Re Im]; ring).
    apply Cmod_Im_le. }
  destruct (R_complete _ HReC) as [lr Hlr].
  destruct (R_complete _ HImC) as [li Hli].
  exists (mkC lr li). apply (proj2 (CUn_cv_comp (Pprod f) (mkC lr li))).
  split; [ exact Hlr | exact Hli ].
Qed.

End Converge.

Print Assumptions Pprod_cv.
