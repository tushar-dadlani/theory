(* ================================================================= *)
(*  CZeta.v  —  the Riemann zeta function on the critical strip.       *)
(*                                                                    *)
(*  zetaC s = 1/(s-1) + Sum gtermC s   (the complex Euler–Maclaurin    *)
(*  continuation), well-defined for 0 < Re s, s <> 1, and agreeing     *)
(*  with the real continuation zeta_cont on the real axis.  Axiom-clean.*)
(* ================================================================= *)

From Stdlib Require Import Reals Lra FunctionalExtensionality.
Require Import ComplexField Cmodulus CexpFull CSeries CZetaTerm
        ZetaContinuation Ell2ZetaCont.
Open Scope R_scope.

(* --- RtoC homomorphism helpers --- *)

Lemma RtoC1 : RtoC 1 = C1.
Proof. reflexivity. Qed.

Lemma RtoC_opp : forall r, Copp (RtoC r) = RtoC (- r).
Proof. intro r; unfold Copp, RtoC; cbn; f_equal; ring. Qed.

Lemma RtoC_minus : forall r u, Cminus (RtoC r) (RtoC u) = RtoC (r - u).
Proof. intros r u; unfold Cminus, RtoC; cbn; f_equal; ring. Qed.

Lemma Cinv_RtoC : forall r, r <> 0 -> Cinv (RtoC r) = RtoC (/ r).
Proof.
  intros r Hr.
  assert (Hrr : r * r + 0 * 0 <> 0)
    by (replace (r * r + 0 * 0) with (r * r) by ring;
        intro Hc; destruct (Rmult_integral _ _ Hc); apply Hr; assumption).
  unfold Cinv, RtoC, Cnorm2; cbn; apply Ceq; cbn; field; try exact Hrr; exact Hr.
Qed.

(* --- the complex EM term is real at real argument --- *)

Lemma gtermC_RtoC : forall s n, s <> 1 -> gtermC (RtoC s) n = RtoC (gterm s n).
Proof.
  intros s n Hs.
  assert (H1s : 1 - s <> 0) by (intro Hc; apply Hs; lra).
  unfold gtermC, gC, GC.
  rewrite RtoC_opp, Cpw_RtoC.
  replace (Cminus C1 (RtoC s)) with (RtoC (1 - s))
    by (rewrite <- RtoC1, RtoC_minus; reflexivity).
  rewrite !Cpw_RtoC.
  rewrite Cinv_RtoC by exact H1s.
  rewrite <- !RtoC_mul, !RtoC_minus.
  f_equal; unfold gterm; field; exact H1s.
Qed.

(* --- zeta on the strip --- *)

Definition zetaC (s : C) (H0 : 0 < Re s) (H1 : Cminus C1 s <> C0) : C :=
  Cadd (Cinv (Cminus s C1)) (proj1_sig (gtermC_cv s H0 H1)).

Lemma zetaC_series_cv : forall s H0 H1,
  Cseries_cv (gtermC s) (proj1_sig (gtermC_cv s H0 H1)).
Proof. intros s H0 H1; exact (proj2_sig (gtermC_cv s H0 H1)). Qed.

(* --- zetaC restricts to the real continuation zeta_cont --- *)

Lemma zetaC_agree : forall s (Hs0 : 0 < s) (Hs1 : s <> 1) H0 H1,
  zetaC (RtoC s) H0 H1 = RtoC (zeta_cont s Hs0 Hs1).
Proof.
  intros s Hs0 Hs1 H0 H1; unfold zetaC, zeta_cont.
  assert (Hsum : proj1_sig (gtermC_cv (RtoC s) H0 H1)
               = RtoC (proj1_sig (gterm_cv s Hs0 Hs1))).
  { pose proof (proj2_sig (gtermC_cv (RtoC s) H0 H1)) as HZ.
    pose proof (proj2_sig (gterm_cv s Hs0 Hs1)) as HL.
    apply Cseries_cv_comp in HZ; destruct HZ as [HZr HZi].
    assert (Heqr : (fun n => Re (gtermC (RtoC s) n)) = gterm s).
    { apply functional_extensionality; intro n;
        rewrite gtermC_RtoC by exact Hs1; cbn [Re]; reflexivity. }
    assert (Heqi : (fun n => Im (gtermC (RtoC s) n)) = fun _ : nat => 0).
    { apply functional_extensionality; intro n;
        rewrite gtermC_RtoC by exact Hs1; cbn [Im]; reflexivity. }
    rewrite Heqr in HZr; rewrite Heqi in HZi.
    apply Ceq; cbn [Re Im].
    - apply (UL_sequence (sum_f_R0 (gterm s))); [ exact HZr | exact HL ].
    - assert (Hsz : sum_f_R0 (fun _ : nat => 0) = fun _ : nat => 0).
      { apply functional_extensionality; intro N; induction N as [| N IH];
          [ reflexivity | rewrite tech5, IH; ring ]. }
      rewrite Hsz in HZi.
      apply (UL_sequence (fun _ : nat => 0)); [ exact HZi | apply Un_cv_const ]. }
  rewrite Hsum, RtoC_add; f_equal.
  replace (Cminus (RtoC s) C1) with (RtoC (s - 1))
    by (rewrite <- RtoC1, RtoC_minus; reflexivity).
  apply Cinv_RtoC; intro Hc; apply Hs1; lra.
Qed.

Print Assumptions zetaC.
Print Assumptions zetaC_agree.

(* ================================================================= *)
(*  END CZeta.v (part 1).                                              *)
(* ================================================================= *)
