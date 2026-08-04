(* ================================================================= *)
(*  CDirichlet.v  —  the complex Dirichlet series Σ n^{-s} and its     *)
(*  identification with zetaC on Re s > 1.                            *)
(*                                                                    *)
(*  zetaC is defined as the Euler–Maclaurin continuation              *)
(*  1/(s-1) + Σ gtermC.  Here we hook it back to the DIRICHLET series  *)
(*  Σ (n+1)^{-s}: for Re s > 1 the Dirichlet partial sums converge to  *)
(*  zetaC s (`zetaC_eq_dirichlet`).                                   *)
(*                                                                    *)
(*  The bridge is the complex analogue of ZetaContinuation's          *)
(*  zeta_EM_identity + zeta_continuation_extends: gtermC telescopes    *)
(*  the antiderivative GC, so                                         *)
(*    Cpsum (cterm s) N = Cpsum (gtermC s) N + (GC s (n+2) - GC s 1),  *)
(*  and for Re s > 1 the tail GC s (n+2) -> 0 (Rpower decay), leaving   *)
(*    Σ (n+1)^{-s}  ->  Zg - GC s 1 = 1/(s-1) + Zg = zetaC s.          *)
(*                                                                    *)
(*  Uses the classical Reals axioms (quarantined, via zetaC / Rpower). *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import ComplexField Cmodulus CexpFull CSeries CZetaTerm CZeta
        CDeriv ZetaContinuation CPowMul.
Open Scope R_scope.

(* ================================================================= *)
(*  0.  small complex-limit combinators                              *)
(* ================================================================= *)

Lemma CUn_cv_ext : forall u v l, (forall n, u n = v n) -> CUn_cv u l -> CUn_cv v l.
Proof.
  intros u v l He H eps Heps; destruct (H eps Heps) as [N HN]; exists N; intros n Hn;
    rewrite <- He; apply HN; exact Hn.
Qed.

Lemma CUn_cv_const : forall c, CUn_cv (fun _ => c) c.
Proof. intro c; rewrite CUn_cv_comp; split; apply Un_cv_const. Qed.

Lemma CUn_cv_add : forall u v a b, CUn_cv u a -> CUn_cv v b ->
  CUn_cv (fun n => Cadd (u n) (v n)) (Cadd a b).
Proof.
  intros u v a b Hu Hv.
  apply CUn_cv_comp; rewrite CUn_cv_comp in Hu, Hv.
  destruct Hu as [HuR HuI]; destruct Hv as [HvR HvI]; split.
  - apply (Un_cv_ext (fun n => Re (u n) + Re (v n)));
      [ intro n; unfold Cadd; reflexivity | ].
    replace (Re (Cadd a b)) with (Re a + Re b) by (unfold Cadd; reflexivity).
    apply CV_plus; assumption.
  - apply (Un_cv_ext (fun n => Im (u n) + Im (v n)));
      [ intro n; unfold Cadd; reflexivity | ].
    replace (Im (Cadd a b)) with (Im a + Im b) by (unfold Cadd; reflexivity).
    apply CV_plus; assumption.
Qed.

Lemma CUn_cv_mod0 : forall u, Un_cv (fun n => Cmod (u n)) 0 -> CUn_cv u C0.
Proof.
  intros u H eps Heps; destruct (H eps Heps) as [N HN]; exists N; intros n Hn.
  specialize (HN n Hn); unfold R_dist in HN.
  rewrite Rminus_0_r, Rabs_right in HN by (apply Rle_ge, Cmod_nonneg).
  replace (Cminus (u n) C0) with (u n) by ring; exact HN.
Qed.

(* ================================================================= *)
(*  1.  the complex Dirichlet term (n+1)^{-s} and its convergence     *)
(* ================================================================= *)

Definition cterm (s : C) (n : nat) : C := gC s (INR (S n)).

Lemma Cmod_cterm : forall s n, Cmod (cterm s n) = Rpower (INR (S n)) (- Re s).
Proof.
  intros s n; unfold cterm, gC; rewrite Cpw_mod.
  f_equal; unfold Copp; cbn [Re]; ring.
Qed.

Lemma cdirichlet_cv : forall s, 1 < Re s -> { S | Cseries_cv (cterm s) S }.
Proof.
  intros s Hs.
  apply (Cseries_abs_cv (cterm s) (fun n => Rpower (INR (S n)) (- Re s))).
  - intro n; rewrite Cmod_cterm; apply Rle_refl.
  - apply (pseries_cv (Re s)); exact Hs.
Qed.

(* ================================================================= *)
(*  2.  GC s 1 = 1/(1-s)  (using Cpw_one from CPowMul)                 *)
(* ================================================================= *)

Lemma GC_one : forall s, GC s (INR 1) = Cinv (Cminus C1 s).
Proof.
  intro s; unfold GC; rewrite INR_1, Cpw_one; ring.
Qed.

(* ================================================================= *)
(*  3.  the telescoping EM identity (complex)                        *)
(* ================================================================= *)

Lemma czeta_EM_identity : forall s N,
  Cpsum (cterm s) N
  = Cadd (Cpsum (gtermC s) N) (Cminus (GC s (INR (S (S N)))) (GC s (INR 1))).
Proof.
  intros s N; induction N as [| N IH].
  - cbn [Cpsum]; unfold cterm, gtermC; ring.
  - cbn [Cpsum]; rewrite IH; unfold cterm, gtermC; ring.
Qed.

(* ================================================================= *)
(*  4.  the antiderivative tail GC s (n+2) -> 0 for Re s > 1          *)
(* ================================================================= *)

Lemma Cmod_GC : forall s x, 0 < x -> Cminus C1 s <> C0 ->
  Cmod (GC s x) = Rpower x (1 - Re s) * / Cmod (Cminus C1 s).
Proof.
  intros s x Hx Hs.
  assert (HRe : Re (Cminus C1 s) = 1 - Re s)
    by (unfold Cminus, Cadd, Copp, C1; cbn [Re]; ring).
  unfold GC; rewrite Cmod_mul, Cpw_mod, Cmod_inv by exact Hs; rewrite HRe; reflexivity.
Qed.

Lemma GC_decay : forall s, 1 < Re s -> Cminus C1 s <> C0 ->
  CUn_cv (fun N => GC s (INR (S (S N)))) C0.
Proof.
  intros s Hs Hs1; apply CUn_cv_mod0.
  apply (Un_cv_ext (fun N => Rpower (INR (S (S N))) (1 - Re s) * / Cmod (Cminus C1 s))).
  - intro N; symmetry; apply Cmod_GC; [ apply lt_0_INR; lia | exact Hs1 ].
  - replace 0 with (0 * / Cmod (Cminus C1 s)) by ring.
    apply CV_mult; [ | apply Un_cv_const ].
    apply (Un_cv_S (fun n => Rpower (INR (S n)) (1 - Re s))).
    apply Rpower_neg_cv0; lra.
Qed.

(* ================================================================= *)
(*  5.  THE BRIDGE: Σ (n+1)^{-s} -> zetaC s for Re s > 1              *)
(* ================================================================= *)

Theorem zetaC_eq_dirichlet : forall s (H0 : 0 < Re s) (H1 : Cminus C1 s <> C0),
  1 < Re s -> Cseries_cv (cterm s) (zetaC s H0 H1).
Proof.
  intros s H0 H1 Hs.
  assert (Hs1' : Cminus s C1 <> C0).
  { intro Hc; apply H1; replace (Cminus C1 s) with (Copp (Cminus s C1)) by ring;
      rewrite Hc; ring. }
  unfold Cseries_cv.
  apply (CUn_cv_ext
           (fun N => Cadd (Cpsum (gtermC s) N)
                          (Cminus (GC s (INR (S (S N)))) (GC s (INR 1))))).
  - intro N; symmetry; apply czeta_EM_identity.
  - set (Zg := proj1_sig (gtermC_cv s H0 H1)).
    replace (zetaC s H0 H1) with (Cadd Zg (Cminus C0 (GC s (INR 1)))).
    2:{ unfold zetaC; fold Zg; rewrite GC_one; field; split; assumption. }
    apply CUn_cv_add.
    + exact (zetaC_series_cv s H0 H1).
    + apply (CUn_cv_ext
               (fun N => Cadd (GC s (INR (S (S N)))) (Copp (GC s (INR 1))))).
      * intro N; unfold Cminus; reflexivity.
      * replace (Cminus C0 (GC s (INR 1)))
          with (Cadd C0 (Copp (GC s (INR 1)))) by (unfold Cminus; reflexivity).
        apply CUn_cv_add; [ apply GC_decay; [ exact Hs | exact H1 ] | apply CUn_cv_const ].
Qed.

Print Assumptions zetaC_eq_dirichlet.

(* ================================================================= *)
(*  END CDirichlet.v                                                  *)
(*  The complex Dirichlet series Σ (n+1)^{-s} converges to zetaC s     *)
(*  for Re s > 1 — the EM↔Dirichlet bridge, ready to feed the complex  *)
(*  Euler product and the nonvanishing argument.                      *)
(* ================================================================= *)
