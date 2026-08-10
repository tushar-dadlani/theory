(* ================================================================= *)
(*  PerronSeriesInt.v  —  Perron A2: termwise integration of a           *)
(*  uniformly (Weierstrass-M) convergent C-valued series.               *)
(*                                                                    *)
(*  Cintf_series : if each f n is continuous on [a,b], |f n t| ≤ M n     *)
(*  with Σ M n convergent, and Σ_n f n t = S t pointwise, then           *)
(*                                                                    *)
(*     ∫_a^b S  =  Σ_n ∫_a^b f n.                                       *)
(*                                                                    *)
(*  Proof:  ∫S − Σ_{n≤N} ∫f n = ∫(S − Σ_{n≤N} f n),  ML-bounded by        *)
(*  2(b−a)·sup|tail| ≤ 2(b−a)(SM − Σ_{n≤N} M n) → 0.                     *)
(*  This is the interchange behind  (1/2π)∫ Φ(s) x^s/s = Σ Λ(n)·Vperron.  *)
(*  Axiom-clean.                                                         *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import ComplexField Cmodulus CSeries CIntegral2 CSegInt CGoursatLin CLeibniz.
Open Scope R_scope.

Lemma Cmod_C0 : Cmod C0 = 0.
Proof. apply (proj2 (Cmod0 C0)); reflexivity. Qed.

Lemma Ccont_minus : forall g h, Ccont g -> Ccont h -> Ccont (fun u => Cminus (g u) (h u)).
Proof.
  intros g h [Hgr Hgi] [Hhr Hhi]; split; intro x; unfold Cminus; cbn [Re Im];
    apply continuity_pt_minus; auto.
Qed.

Lemma Cmod_Cminus_sym : forall a b, Cmod (Cminus a b) = Cmod (Cminus b a).
Proof.
  intros a b; replace (Cminus a b) with (Copp (Cminus b a)) by ring; apply Cmod_opp.
Qed.

(* difference of partial sums is bounded by the difference of the majorant sums *)
Lemma Cpsum_shift_bound : forall (g : nat -> C) (Mg : nat -> R),
  (forall n, Cmod (g n) <= Mg n) ->
  forall N k, Cmod (Cminus (Cpsum g (N + k)) (Cpsum g N))
              <= sum_f_R0 Mg (N + k) - sum_f_R0 Mg N.
Proof.
  intros g Mg Hg N k; induction k as [|k IH].
  - rewrite Nat.add_0_r; replace (Cminus (Cpsum g N) (Cpsum g N)) with C0 by ring.
    rewrite Cmod_C0; lra.
  - rewrite Nat.add_succ_r.
    change (Cpsum g (S (N + k))) with (Cadd (Cpsum g (N + k)) (g (S (N + k)))).
    change (sum_f_R0 Mg (S (N + k))) with (sum_f_R0 Mg (N + k) + Mg (S (N + k))).
    eapply Rle_trans;
      [ replace (Cminus (Cadd (Cpsum g (N + k)) (g (S (N + k)))) (Cpsum g N))
          with (Cadd (Cminus (Cpsum g (N + k)) (Cpsum g N)) (g (S (N + k)))) by ring;
        apply Cmod_triangle
      | pose proof (Hg (S (N + k))); lra ].
Qed.

Lemma Un_cv_const : forall c : R, Un_cv (fun _ => c) c.
Proof.
  intros c eps Heps; exists 0%nat; intros n _; unfold R_dist;
    replace (c - c) with 0 by ring; rewrite Rabs_R0; exact Heps.
Qed.

Lemma Un_cv_shift : forall u l N, Un_cv u l -> Un_cv (fun k => u (N + k)%nat) l.
Proof.
  intros u l N Hu eps Heps; destruct (Hu eps Heps) as [n0 Hn0].
  exists n0; intros k Hk; apply Hn0; lia.
Qed.

Section CintfSeries.
Variables (f : nat -> R -> C) (Sfun : R -> C) (a b : R) (M : nat -> R) (SM : R).
Hypothesis Hab : a <= b.
Hypothesis Hfc : forall n, Ccont (f n).
Hypothesis HSc : Ccont Sfun.
Hypothesis Hbd : forall n t, a <= t <= b -> Cmod (f n t) <= M n.
Hypothesis HMcv : Un_cv (sum_f_R0 M) SM.
Hypothesis Hptw : forall t, a <= t <= b -> Cseries_cv (fun n => f n t) (Sfun t).

Lemma Mnn : forall n, 0 <= M n.
Proof. intro n; eapply Rle_trans; [ apply Cmod_nonneg | apply (Hbd n a); lra ]. Qed.

Lemma sum_M_le : forall N, sum_f_R0 M N <= SM.
Proof.
  intro N; apply growing_ineq; [ | exact HMcv ].
  intro n; simpl; pose proof (Mnn (S n)); lra.
Qed.

Lemma partial_cont : forall N, Ccont (fun t => Cpsum (fun n => f n t) N).
Proof.
  induction N as [|N IH]; [ apply Hfc | simpl; apply Ccont_add; [ exact IH | apply Hfc ] ].
Qed.

Lemma Cintf_Cpsum : forall N,
  Cintf (fun t => Cpsum (fun n => f n t) N) (partial_cont N) a b
  = Cpsum (fun n => Cintf (f n) (Hfc n) a b) N.
Proof.
  induction N as [|N IH]; [ apply Cintf_ext; intro u; reflexivity | ].
  simpl.
  rewrite (Cintf_add (fun t => Cpsum (fun n => f n t) N) (f (S N))
             (partial_cont N) (Hfc (S N)) (partial_cont (S N)) a b Hab).
  rewrite IH; reflexivity.
Qed.

Lemma tail_bound : forall N t, a <= t <= b ->
  Cmod (Cminus (Sfun t) (Cpsum (fun n => f n t) N)) <= SM - sum_f_R0 M N.
Proof.
  intros N t Ht.
  apply Rle_cv_lim with
    (Un := fun k => Cmod (Cminus (Cpsum (fun n => f n t) (N + k)) (Cpsum (fun n => f n t) N)))
    (Vn := fun k => sum_f_R0 M (N + k) - sum_f_R0 M N).
  - intro k; apply (Cpsum_shift_bound (fun n => f n t) M (fun n => Hbd n t Ht) N k).
  - intros eps Heps; destruct (Hptw t Ht eps Heps) as [n0 Hn0].
    exists n0; intros k Hk; unfold R_dist.
    eapply Rle_lt_trans; [ apply Cmod_diff_le | ].
    replace (Cminus (Cminus (Cpsum (fun n => f n t) (N + k)) (Cpsum (fun n => f n t) N))
                    (Cminus (Sfun t) (Cpsum (fun n => f n t) N)))
      with (Cminus (Cpsum (fun n => f n t) (N + k)) (Sfun t)) by ring.
    apply Hn0; lia.
  - apply (CV_minus (fun k => sum_f_R0 M (N + k)) (fun _ => sum_f_R0 M N) SM (sum_f_R0 M N));
      [ apply Un_cv_shift; exact HMcv | apply Un_cv_const ].
Qed.

Theorem Cintf_series :
  Cseries_cv (fun n => Cintf (f n) (Hfc n) a b) (Cintf Sfun HSc a b).
Proof.
  intros eps Heps.
  destruct (HMcv (eps / (2 * (b - a) + 1))
              ltac:(apply Rdiv_lt_0_compat; [ exact Heps | lra ])) as [N0 HN0].
  exists N0; intros N HN.
  assert (Hdiff : Ccont (fun t => Cminus (Cpsum (fun n => f n t) N) (Sfun t)))
    by (apply Ccont_minus; [ apply partial_cont | exact HSc ]).
  unfold Cpsum; fold (Cpsum (fun n => Cintf (f n) (Hfc n) a b) N).
  rewrite <- (Cintf_Cpsum N).
  eapply Rle_lt_trans.
  - rewrite <- (Cintf_sub (fun t => Cpsum (fun n => f n t) N) Sfun
                 (partial_cont N) HSc Hdiff a b Hab).
    apply (Cintf_ML _ Hdiff a b (SM - sum_f_R0 M N) Hab).
    intros u Hu; rewrite Cmod_Cminus_sym; apply tail_bound; exact Hu.
  - pose proof (HN0 N HN) as H; unfold R_dist in H.
    pose proof (sum_M_le N) as Hle.
    assert (SM - sum_f_R0 M N < eps / (2 * (b - a) + 1))
      by (rewrite Rabs_minus_sym, Rabs_pos_eq in H by lra; lra).
    assert (0 <= b - a) by lra.
    apply Rle_lt_trans with (2 * (eps / (2 * (b - a) + 1)) * (b - a));
      [ apply Rmult_le_compat_r; [ lra | apply Rmult_le_compat_l; lra ] | ].
    apply Rmult_lt_reg_r with (2 * (b - a) + 1); [ lra | ].
    field_simplify; [ nra | lra ].
Qed.

End CintfSeries.

Print Assumptions Cintf_series.

(* ================================================================= *)
(*  END PerronSeriesInt.v — the series↔integral interchange for Perron.  *)
(* ================================================================= *)
