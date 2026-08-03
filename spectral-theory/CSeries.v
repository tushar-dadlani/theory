(* ================================================================= *)
(*  CSeries.v  —  convergence of complex sequences and series.         *)
(*                                                                    *)
(*  The Sigma-analogue of the CImp layer: complex sequence limits      *)
(*  reduce componentwise to stdlib Un_cv, complex partial sums reduce  *)
(*  to sum_f_R0, and |Sum| <= Sum|.| (Cseries_triangle) mirrors        *)
(*  CImp_triangle.  This is the convergence groundwork for a complex   *)
(*  Dirichlet/Euler-Maclaurin zeta on the critical strip.  Axiom-clean.*)
(* ================================================================= *)

From Stdlib Require Import Reals Lra FunctionalExtensionality.
Require Import ComplexField Cmodulus.
Open Scope R_scope.

(* --- modulus vs. real/imaginary components --- *)

Lemma Cmod_Re_le : forall c, Rabs (Re c) <= Cmod c.
Proof.
  intro c; unfold Cmod; rewrite <- (sqrt_Rsqr_abs (Re c)).
  apply sqrt_le_1_alt; unfold Rsqr, Cnorm2.
  pose proof (Rle_0_sqr (Im c)); unfold Rsqr in *; lra.
Qed.

Lemma Cmod_Im_le : forall c, Rabs (Im c) <= Cmod c.
Proof.
  intro c; unfold Cmod; rewrite <- (sqrt_Rsqr_abs (Im c)).
  apply sqrt_le_1_alt; unfold Rsqr, Cnorm2.
  pose proof (Rle_0_sqr (Re c)); unfold Rsqr in *; lra.
Qed.

Lemma Cmod_le_sum : forall c, Cmod c <= Rabs (Re c) + Rabs (Im c).
Proof.
  intro c; apply Rsqr_incr_0_var;
    [ | pose proof (Rabs_pos (Re c)); pose proof (Rabs_pos (Im c)); lra ].
  rewrite Cmod_sqr; unfold Cnorm2, Rsqr.
  pose proof (Rsqr_abs (Re c)); pose proof (Rsqr_abs (Im c)); unfold Rsqr in *.
  pose proof (Rabs_pos (Re c)); pose proof (Rabs_pos (Im c)); nra.
Qed.

Lemma Cmod_diff_le : forall a b, Rabs (Cmod a - Cmod b) <= Cmod (Cminus a b).
Proof.
  intros a b; apply Rabs_le; split.
  - pose proof (Cmod_triangle (Cminus b a) a) as H.
    replace (Cadd (Cminus b a) a) with b in H by ring.
    rewrite Cmod_opp with (a := Cminus b a) in H ||
      (replace (Cmod (Cminus b a)) with (Cmod (Cminus a b)) in H
         by (rewrite <- Cmod_opp; f_equal; ring)); lra.
  - pose proof (Cmod_triangle (Cminus a b) b) as H.
    replace (Cadd (Cminus a b) b) with a in H by ring; lra.
Qed.

(* --- complex sequence convergence --- *)

Definition CUn_cv (u : nat -> C) (l : C) : Prop :=
  forall eps, 0 < eps -> exists N, forall n, (n >= N)%nat -> Cmod (Cminus (u n) l) < eps.

Lemma CUn_cv_comp : forall u l,
  CUn_cv u l <->
  Un_cv (fun n => Re (u n)) (Re l) /\ Un_cv (fun n => Im (u n)) (Im l).
Proof.
  intros u l; split.
  - intro H; split; intros eps Heps; destruct (H eps Heps) as [N HN];
      exists N; intros n Hn; specialize (HN n Hn); unfold R_dist.
    + apply Rle_lt_trans with (Cmod (Cminus (u n) l)); [ | exact HN ].
      replace (Re (u n) - Re l) with (Re (Cminus (u n) l))
        by (unfold Cminus, Cadd, Copp; simpl; ring).
      apply Cmod_Re_le.
    + apply Rle_lt_trans with (Cmod (Cminus (u n) l)); [ | exact HN ].
      replace (Im (u n) - Im l) with (Im (Cminus (u n) l))
        by (unfold Cminus, Cadd, Copp; simpl; ring).
      apply Cmod_Im_le.
  - intros [HR HI] eps Heps.
    destruct (HR (eps / 2) ltac:(lra)) as [N1 HN1].
    destruct (HI (eps / 2) ltac:(lra)) as [N2 HN2].
    exists (max N1 N2); intros n Hn.
    apply Rle_lt_trans with (Rabs (Re (Cminus (u n) l)) + Rabs (Im (Cminus (u n) l)));
      [ apply Cmod_le_sum | ].
    specialize (HN1 n (Nat.le_trans _ _ _ (Nat.le_max_l N1 N2) Hn)).
    specialize (HN2 n (Nat.le_trans _ _ _ (Nat.le_max_r N1 N2) Hn)).
    unfold R_dist in *.
    replace (Re (Cminus (u n) l)) with (Re (u n) - Re l)
      by (unfold Cminus, Cadd, Copp; simpl; ring).
    replace (Im (Cminus (u n) l)) with (Im (u n) - Im l)
      by (unfold Cminus, Cadd, Copp; simpl; ring).
    lra.
Qed.

Lemma CUn_cv_unique : forall u l1 l2, CUn_cv u l1 -> CUn_cv u l2 -> l1 = l2.
Proof.
  intros u l1 l2 H1 H2.
  rewrite CUn_cv_comp in H1, H2.
  apply Ceq.
  - apply (UL_sequence (fun n => Re (u n))); [ apply H1 | apply H2 ].
  - apply (UL_sequence (fun n => Im (u n))); [ apply H1 | apply H2 ].
Qed.

(* --- complex partial sums --- *)

Fixpoint Cpsum (a : nat -> C) (N : nat) : C :=
  match N with
  | O => a O
  | S M => Cadd (Cpsum a M) (a (S M))
  end.

Lemma Re_Cpsum : forall a N, Re (Cpsum a N) = sum_f_R0 (fun k => Re (a k)) N.
Proof.
  intros a N; induction N as [| N IH]; simpl; [ reflexivity | ].
  unfold Cadd; simpl; rewrite IH; reflexivity.
Qed.

Lemma Im_Cpsum : forall a N, Im (Cpsum a N) = sum_f_R0 (fun k => Im (a k)) N.
Proof.
  intros a N; induction N as [| N IH]; simpl; [ reflexivity | ].
  unfold Cadd; simpl; rewrite IH; reflexivity.
Qed.

Definition Cseries_cv (a : nat -> C) (S : C) : Prop := CUn_cv (Cpsum a) S.

Lemma Cseries_cv_comp : forall a S,
  Cseries_cv a S <->
  Un_cv (sum_f_R0 (fun k => Re (a k))) (Re S) /\
  Un_cv (sum_f_R0 (fun k => Im (a k))) (Im S).
Proof.
  intros a S; unfold Cseries_cv; rewrite CUn_cv_comp.
  split; intros [HR HI]; split.
  - intros eps Heps; destruct (HR eps Heps) as [N HN]; exists N; intros n Hn;
      rewrite <- Re_Cpsum; apply HN; exact Hn.
  - intros eps Heps; destruct (HI eps Heps) as [N HN]; exists N; intros n Hn;
      rewrite <- Im_Cpsum; apply HN; exact Hn.
  - intros eps Heps; destruct (HR eps Heps) as [N HN]; exists N; intros n Hn;
      rewrite Re_Cpsum; apply HN; exact Hn.
  - intros eps Heps; destruct (HI eps Heps) as [N HN]; exists N; intros n Hn;
      rewrite Im_Cpsum; apply HN; exact Hn.
Qed.

(* finite triangle inequality for complex partial sums *)
Lemma Cmod_Cpsum_le : forall a N,
  Cmod (Cpsum a N) <= sum_f_R0 (fun k => Cmod (a k)) N.
Proof.
  intros a N; induction N as [| N IH]; simpl; [ apply Rle_refl | ].
  eapply Rle_trans; [ apply Cmod_triangle | ].
  apply Rplus_le_compat_r; exact IH.
Qed.

(* the series triangle inequality  |Sum a| <= Sum |a| *)
Lemma Cseries_triangle : forall a S T,
  Cseries_cv a S ->
  Un_cv (sum_f_R0 (fun k => Cmod (a k))) T ->
  Cmod S <= T.
Proof.
  intros a S T HS HT.
  apply Rle_cv_lim with (Un := fun N => Cmod (Cpsum a N))
                        (Vn := sum_f_R0 (fun k => Cmod (a k))).
  - intro N; apply Cmod_Cpsum_le.
  - intros eps Heps; destruct (HS eps Heps) as [N HN]; exists N; intros n Hn.
    unfold R_dist; eapply Rle_lt_trans; [ apply Cmod_diff_le | apply HN; exact Hn ].
  - exact HT.
Qed.

(* --- absolute convergence implies convergence --- *)

(* real: via the c⁺/c⁻ split, each part nonneg, bounded, monotone-convergent *)
Lemma Rseries_abs_cv : forall c b,
  (forall n, Rabs (c n) <= b n) ->
  { T | Un_cv (sum_f_R0 b) T } ->
  { S | Un_cv (sum_f_R0 c) S }.
Proof.
  intros c b Hbound [T HT].
  assert (Hbpos : forall n, 0 <= b n)
    by (intro n; apply Rle_trans with (Rabs (c n)); [ apply Rabs_pos | apply Hbound ]).
  set (cp := fun k => Rmax (c k) 0).
  set (cm := fun k => Rmax (- c k) 0).
  assert (Hsplit : forall k, c k = cp k - cm k)
    by (intro k; unfold cp, cm, Rmax;
        destruct (Rle_dec (c k) 0); destruct (Rle_dec (- c k) 0); lra).
  assert (Hcpb : forall n, cp n <= b n).
  { intro n; unfold cp; apply Rmax_lub;
      [ apply Rle_trans with (Rabs (c n)); [ apply Rle_abs | apply Hbound ] | apply Hbpos ]. }
  assert (Hcmb : forall n, cm n <= b n).
  { intro n; unfold cm; apply Rmax_lub;
      [ apply Rle_trans with (Rabs (c n));
          [ rewrite <- Rabs_Ropp; apply Rle_abs | apply Hbound ]
      | apply Hbpos ]. }
  assert (HbT : forall n, sum_f_R0 b n <= T)
    by (apply growing_ineq; [ intro n; simpl; pose proof (Hbpos (S n)); lra | exact HT ]).
  assert (Hpartb : forall g : nat -> R,
            (forall n, g n <= b n) -> (forall n, 0 <= g n) -> { L | Un_cv (sum_f_R0 g) L }).
  { intros g Hgb Hg0; apply growing_cv.
    - intro n; simpl; pose proof (Hg0 (S n)); lra.
    - exists T; intros x [n ->]; apply Rle_trans with (sum_f_R0 b n);
        [ apply sum_Rle; intros i _; apply Hgb | apply HbT ]. }
  destruct (Hpartb cp Hcpb (fun n => Rmax_r (c n) 0)) as [Sp HSp].
  destruct (Hpartb cm Hcmb (fun n => Rmax_r (- c n) 0)) as [Sm HSm].
  exists (Sp - Sm).
  assert (Heq : sum_f_R0 c = fun N => sum_f_R0 cp N - sum_f_R0 cm N).
  { apply functional_extensionality; intro N.
    rewrite <- minus_sum; apply sum_eq; intros i _; apply Hsplit. }
  rewrite Heq; apply CV_minus; [ exact HSp | exact HSm ].
Qed.

(* complex: dominated by a convergent real series ⇒ the complex series converges *)
Lemma Cseries_abs_cv : forall a b,
  (forall n, Cmod (a n) <= b n) ->
  { T | Un_cv (sum_f_R0 b) T } ->
  { S | Cseries_cv a S }.
Proof.
  intros a b Hbound HT.
  destruct (Rseries_abs_cv (fun k => Re (a k)) b
             (fun n => Rle_trans _ _ _ (Cmod_Re_le (a n)) (Hbound n)) HT) as [SR HSR].
  destruct (Rseries_abs_cv (fun k => Im (a k)) b
             (fun n => Rle_trans _ _ _ (Cmod_Im_le (a n)) (Hbound n)) HT) as [SI HSI].
  exists (mkC SR SI).
  rewrite Cseries_cv_comp; simpl; split; [ exact HSR | exact HSI ].
Qed.

Print Assumptions CUn_cv_comp.
Print Assumptions Cseries_triangle.
Print Assumptions Cseries_abs_cv.

(* ================================================================= *)
(*  END CSeries.v (part 1).                                            *)
(* ================================================================= *)
