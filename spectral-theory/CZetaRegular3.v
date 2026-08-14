(* ================================================================= *)
(*  CZetaRegular3.v   (Phase B2, part 2: the per-term limit)           *)
(*                                                                    *)
(*  gtermC z n  ->  RtoC (ell n)   as  z -> 1  (z <> 1).               *)
(*                                                                    *)
(*  gtermC s n = gC s (n+1) - (GC s (n+2) - GC s (n+1)), with          *)
(*    gC s x  = x^{-s}                    -> x^{-1} = 1/(n+1)           *)
(*    GC-diff = (x2^{1-s}-x1^{1-s})/(1-s) -> ln(n+2) - ln(n+1).         *)
(*  The second limit is a difference quotient of  w |-> x^{1-w}  at 1   *)
(*  (derivative -ln x), handled by diffquot_of_deriv + cpw_1minus_holo. *)
(*                                                                    *)
(*  Axioms: standard classical-Reals only.                            *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import ComplexField Cmodulus Holomorphic CDeriv CHoloCalculus
        CexpFull EulerFormula CPower CZetaTerm CZetaRegular CZetaRegular2.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  difference quotient tends to the derivative (when F(z0)=0)         *)
(* ----------------------------------------------------------------- *)
Lemma diffquot_of_deriv : forall F z0 d,
  is_Cderiv F z0 d -> F z0 = C0 ->
  forall eps, 0 < eps -> exists del, 0 < del /\
    forall s, Cmod (Cminus s z0) < del -> Cminus s z0 <> C0 ->
      Cmod (Cminus (Cmul (F s) (Cinv (Cminus s z0))) d) <= eps.
Proof.
  intros F z0 d Hd HF0 eps Heps.
  destruct (Hd eps Heps) as [del [Hdel Hb]].
  exists del; split; [ exact Hdel | ].
  intros s Hs Hne.
  pose proof (Hb (Cminus s z0) Hs) as Hbnd.
  replace (Cadd z0 (Cminus s z0)) with s in Hbnd by ring.
  rewrite HF0 in Hbnd.
  assert (Hrw : Cminus (Cmul (F s) (Cinv (Cminus s z0))) d
              = Cmul (Cminus (Cminus (F s) C0) (Cmul d (Cminus s z0)))
                     (Cinv (Cminus s z0))).
  { field. exact Hne. }
  rewrite Hrw, Cmod_mul, Cmod_inv by exact Hne.
  assert (Hpos : 0 < Cmod (Cminus s z0)).
  { pose proof (Cmod_nonneg (Cminus s z0)).
    assert (Cmod (Cminus s z0) <> 0)
      by (intro Hc; apply Hne; apply (proj1 (Cmod0 _)); exact Hc). lra. }
  apply Rmult_le_reg_r with (Cmod (Cminus s z0)); [ exact Hpos | ].
  rewrite Rmult_assoc, (Rinv_l (Cmod (Cminus s z0))) by lra.
  rewrite Rmult_1_r. exact Hbnd.
Qed.

(* ----------------------------------------------------------------- *)
(*  values / derivatives of the power pieces at s = 1                 *)
(* ----------------------------------------------------------------- *)
Lemma Cpw_negC1 : forall c, 0 < c -> Cpw c (Copp C1) = RtoC (/ c).
Proof.
  intros c Hc. unfold Cpw.
  replace (Cmul (Copp C1) (RtoC (ln c))) with (RtoC (- ln c))
    by (apply Ceq; unfold Cmul, Copp, C1, RtoC; cbn [Re Im]; ring).
  rewrite Cexpf_RtoC. f_equal. rewrite exp_Ropp, exp_ln by exact Hc. reflexivity.
Qed.

Lemma phi_deriv1 : forall c, 0 < c ->
  is_Cderiv (fun w => Cpw c (Cminus C1 w)) C1 (Copp (RtoC (ln c))).
Proof.
  intros c Hc. pose proof (cpw_1minus_holo c Hc C1) as H.
  replace (Cmul (Copp C1) (Cmul (RtoC (ln c)) (Cpw c (Cminus C1 C1))))
     with (Copp (RtoC (ln c))) in H; [ exact H | ].
  replace (Cminus C1 C1) with C0
    by (apply Ceq; unfold Cminus, Cadd, Copp, C0, C1; cbn [Re Im]; ring).
  rewrite Cpw_C0. apply Ceq; unfold Cmul, Copp, C1, RtoC; cbn [Re Im]; ring.
Qed.

(* the limit values *)
Definition gClim (n : nat) : C := RtoC (/ INR (S n)).
Definition GCdifflim (n : nat) : C := RtoC (ln (INR (S (S n))) - ln (INR (S n))).

Lemma ell_as_diff : forall n, RtoC (ell n) = Cminus (gClim n) (GCdifflim n).
Proof.
  intro n. unfold gClim, GCdifflim, ell.
  assert (Hln : ln (INR (S (S n)) / INR (S n)) = ln (INR (S (S n))) - ln (INR (S n))).
  { unfold Rdiv. rewrite ln_mult by (try apply Snpos; apply Rinv_0_lt_compat; apply Snpos).
    rewrite ln_Rinv by apply Snpos. ring. }
  rewrite Hln. apply Ceq; unfold Cminus, Cadd, Copp, RtoC; cbn [Re Im]; ring.
Qed.

(* ----------------------------------------------------------------- *)
(*  the gC piece:  Cpw (n+1) (Copp s)  ->  RtoC (1/(n+1))              *)
(* ----------------------------------------------------------------- *)
Lemma gC_limit : forall n eps, 0 < eps -> exists del, 0 < del /\
  forall s, Cmod (Cminus s C1) < del ->
    Cmod (Cminus (Cpw (INR (S n)) (Copp s)) (gClim n)) < eps.
Proof.
  intros n eps Heps.
  pose proof (cpw_neg_holo (INR (S n)) (INR_S_pos n) C1) as Hd.
  destruct (is_Cderiv_cont _ C1 _ Hd eps Heps) as [del [Hdel Hc]].
  exists del; split; [ exact Hdel | ].
  intros s Hs.
  pose proof (Hc (Cminus s C1) Hs) as Hcc.
  replace (Cadd C1 (Cminus s C1)) with s in Hcc by ring.
  unfold gClim. rewrite <- (Cpw_negC1 (INR (S n)) (INR_S_pos n)). exact Hcc.
Qed.

(* ----------------------------------------------------------------- *)
(*  the GC-difference piece  ->  RtoC (ln(n+2) - ln(n+1))             *)
(* ----------------------------------------------------------------- *)
Definition psi (n : nat) (s : C) : C :=
  Cminus (Cpw (INR (S (S n))) (Cminus C1 s)) (Cpw (INR (S n)) (Cminus C1 s)).

Lemma psi_at1 : forall n, psi n C1 = C0.
Proof.
  intro n. unfold psi.
  replace (Cminus C1 C1) with C0
    by (apply Ceq; unfold Cminus, Cadd, Copp, C0, C1; cbn [Re Im]; ring).
  rewrite !Cpw_C0. apply Ceq; unfold Cminus, Cadd, Copp, C0, C1; cbn [Re Im]; ring.
Qed.

Lemma psi_deriv1 : forall n,
  is_Cderiv (psi n) C1
    (Cminus (Copp (RtoC (ln (INR (S (S n)))))) (Copp (RtoC (ln (INR (S n)))))).
Proof.
  intro n. unfold psi.
  apply (Cderiv_minus (fun w => Cpw (INR (S (S n))) (Cminus C1 w))
                      (fun w => Cpw (INR (S n)) (Cminus C1 w)));
    apply phi_deriv1; apply INR_S_pos.
Qed.

(* GC s x = x^{1-s}/(1-s); the difference over the two args factors psi *)
Lemma GCdiff_eq : forall n s, Cminus s C1 <> C0 ->
  Cminus (GC s (INR (S (S n)))) (GC s (INR (S n)))
  = Copp (Cmul (psi n s) (Cinv (Cminus s C1))).
Proof.
  intros n s Hne. unfold GC, psi.
  assert (Hne' : Cminus C1 s <> C0).
  { intro Hc; apply Hne. apply Ceq; apply (f_equal Re) in Hc + apply (f_equal Im) in Hc;
    unfold Cminus, Cadd, Copp, C0 in *; cbn [Re Im] in *; lra. }
  field. split; assumption.
Qed.

Lemma GCdiff_limit : forall n eps, 0 < eps -> exists del, 0 < del /\
  forall s, Cmod (Cminus s C1) < del -> Cminus s C1 <> C0 ->
    Cmod (Cminus (Cminus (GC s (INR (S (S n)))) (GC s (INR (S n)))) (GCdifflim n)) < eps.
Proof.
  intros n eps Heps.
  destruct (diffquot_of_deriv (psi n) C1 _ (psi_deriv1 n) (psi_at1 n) (eps/2) ltac:(lra))
    as [del [Hdel Hq]].
  exists del; split; [ exact Hdel | ].
  intros s Hs Hne.
  rewrite (GCdiff_eq n s Hne).
  (* GCdifflim n = Copp (psi'(1)) *)
  assert (Hlim : GCdifflim n
    = Copp (Cminus (Copp (RtoC (ln (INR (S (S n)))))) (Copp (RtoC (ln (INR (S n))))))).
  { unfold GCdifflim. apply Ceq; unfold Copp, Cminus, Cadd, RtoC; cbn [Re Im]; ring. }
  rewrite Hlim.
  (* |Copp A - Copp B| = |A - B| <= eps/2 < eps *)
  replace (Cminus (Copp (Cmul (psi n s) (Cinv (Cminus s C1))))
                  (Copp (Cminus (Copp (RtoC (ln (INR (S (S n)))))) (Copp (RtoC (ln (INR (S n))))))))
     with (Copp (Cminus (Cmul (psi n s) (Cinv (Cminus s C1)))
                        (Cminus (Copp (RtoC (ln (INR (S (S n)))))) (Copp (RtoC (ln (INR (S n))))))))
     by ring.
  rewrite Cmod_opp.
  pose proof (Hq s Hs Hne) as Hqq. lra.
Qed.

Lemma Cmod_minus_le : forall a b, Cmod (Cminus a b) <= Cmod a + Cmod b.
Proof.
  intros a b.
  replace (Cminus a b) with (Cadd a (Copp b))
    by (apply Ceq; unfold Cminus, Cadd, Copp; cbn [Re Im]; ring).
  eapply Rle_trans; [ apply Cmod_triangle | ]. rewrite Cmod_opp. lra.
Qed.

(* ----------------------------------------------------------------- *)
(*  the per-term limit:  gtermC s n -> RtoC (ell n)                   *)
(* ----------------------------------------------------------------- *)
Theorem gtermC_term_limit : forall n eps, 0 < eps -> exists del, 0 < del /\
  forall s, Cmod (Cminus s C1) < del -> Cminus s C1 <> C0 ->
    Cmod (Cminus (gtermC s n) (RtoC (ell n))) < eps.
Proof.
  intros n eps Heps.
  destruct (gC_limit n (eps/2) ltac:(lra)) as [d1 [Hd1 Hg]].
  destruct (GCdiff_limit n (eps/2) ltac:(lra)) as [d2 [Hd2 HG]].
  exists (Rmin d1 d2); split; [ apply Rmin_pos; assumption | ].
  intros s Hs Hne.
  assert (Hs1 : Cmod (Cminus s C1) < d1) by (eapply Rlt_le_trans; [ exact Hs | apply Rmin_l ]).
  assert (Hs2 : Cmod (Cminus s C1) < d2) by (eapply Rlt_le_trans; [ exact Hs | apply Rmin_r ]).
  pose proof (Hg s Hs1) as Hg'.
  pose proof (HG s Hs2 Hne) as HG'.
  unfold gtermC, gC.
  rewrite ell_as_diff.
  (* gtermC - (gClim - GCdifflim) = (gC - gClim) - (GCdiff - GCdifflim) *)
  replace (Cminus (Cminus (Cpw (INR (S n)) (Copp s))
                          (Cminus (GC s (INR (S (S n)))) (GC s (INR (S n)))))
                  (Cminus (gClim n) (GCdifflim n)))
     with (Cminus (Cminus (Cpw (INR (S n)) (Copp s)) (gClim n))
                  (Cminus (Cminus (GC s (INR (S (S n)))) (GC s (INR (S n)))) (GCdifflim n)))
     by ring.
  eapply Rle_lt_trans; [ apply Cmod_minus_le | ].
  lra.
Qed.

Print Assumptions gtermC_term_limit.
