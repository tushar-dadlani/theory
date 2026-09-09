(* ================================================================= *)
(*  CVonMangoldtChi.v  --  Phi(s,chi) = sum Lambda(n) chi(n) n^{-s},  *)
(*  absolutely convergent on Re s > 1.                                *)
(*                                                                    *)
(*  The twisted analogue of CVonMangoldtSeries.Phi, and the input the  *)
(*  log-derivative identity Phi(s,chi) L(s,chi) = -L'(s,chi) needs.    *)
(*                                                                    *)
(*  THE TWIST IS FREE.  |chi(n)| <= 1 (CharModulus.Cmod_dchar_le, and  *)
(*  packaged already as CTwistedCoeff.Gchi_mod_le), so the twisted     *)
(*  term is dominated by the SAME majorant blam s n = ln(n) n^{-Re s}  *)
(*  that CVonMangoldtSeries uses for the untwisted one.  Nothing about *)
(*  the convergence has to be redone: blam_sum_cv is reused verbatim,  *)
(*  and the whole file is the domination estimate plus the packaging.  *)
(*                                                                    *)
(*  Both shapes are provided: Cseries_cv (for CLSeries/CLHolo-style    *)
(*  statements) and Rls (seq 1 N) (which is what                       *)
(*  CDirichletProduct.cdirichlet_product consumes).                    *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia List.
Require Import ComplexField Cmodulus CexpFull CSeries Ell2Zeta RealMobius
        RootsOfUnity ZmodOrder DirichletModP CTwistedCoeff CLSeries
        VonMangoldtGlobal Chebyshev CVonMangoldtSeries CVonMangoldtZeta.
Import ListNotations.
Open Scope R_scope.

Lemma Un_cv_unshift_R : forall (u : nat -> R) l, Un_cv (fun N => u (S N)) l -> Un_cv u l.
Proof.
  intros u l H eps He. destruct (H eps He) as [N HN].
  exists (S N). intros n Hn. destruct n as [| m]; [ lia | ]. apply HN. lia.
Qed.

Section VMChi.

Variable p g A : nat.
Hypothesis Hg : (1 <= g <= p - 1)%nat.
Hypothesis Hord : ord p g = (p - 1)%nat.
Variable s : C.
Hypothesis Hs : 1 < Re s.

(* 1-indexed (matches Gchi / cdirichlet_product) and 0-indexed (matches Lterm) *)
Definition achi (n : nat) : C := Cmul (RtoC (Lam n)) (Gchi p g A s n).
Definition pchi (n : nat) : C := Cmul (RtoC (Lam (S n))) (Lterm p g A s n).

Lemma achi_S : forall k, achi (S k) = pchi k.
Proof. intro k. unfold achi, pchi, Lterm. reflexivity. Qed.

Lemma Cmod_pchi_le : forall n, Cmod (pchi n) <= blam s n.
Proof.
  intro n. unfold pchi, blam.
  rewrite Cmod_mul, Cmod_RtoC, (Rabs_pos_eq _ (Lam_nonneg (S n))).
  apply Rmult_le_compat.
  - apply Lam_nonneg.
  - apply Cmod_nonneg.
  - apply Lam_le_ln. lia.
  - unfold Lterm.
    pose proof (Gchi_mod_le p g A Hg Hord s (S n)) as H.
    replace (z (Re s) (S n)) with (Rpower (INR (S n)) (- Re s)) in H by reflexivity.
    exact H.
Qed.

(* ---- the series, in Cseries_cv form ---- *)

Lemma pchi_cv : { P | Cseries_cv pchi P }.
Proof.
  apply (Cseries_abs_cv pchi (blam s));
    [ apply Cmod_pchi_le | apply blam_sum_cv; exact Hs ].
Qed.

Definition Phichi : C := proj1_sig pchi_cv.

Lemma Phichi_spec : Cseries_cv pchi Phichi.
Proof. unfold Phichi; exact (proj2_sig pchi_cv). Qed.

(* ---- absolute convergence, in the Rls (seq 1 N) form ---- *)

Lemma achi_abs_cv : { T | Un_cv (fun N => Rls (seq 1 N) (fun d => Cmod (achi d))) T }.
Proof.
  assert (Hmaj : forall n, Rabs (Cmod (achi (S n))) <= blam s n).
  { intro n. rewrite Rabs_pos_eq by apply Cmod_nonneg.
    rewrite achi_S. apply Cmod_pchi_le. }
  destruct (Rseries_abs_cv (fun n => Cmod (achi (S n))) (blam s) Hmaj
              (blam_sum_cv s Hs)) as [Ta HTa].
  exists Ta. apply Un_cv_unshift_R.
  apply (Un_cv_ext (sum_f_R0 (fun k => Cmod (achi (S k))))); [ | exact HTa ].
  intro N. symmetry. apply Rls_seq_S_eq_sumf.
Qed.

End VMChi.

Print Assumptions Phichi_spec.
Print Assumptions achi_abs_cv.

(* ================================================================= *)
(*  END CVonMangoldtChi.v                                             *)
(* ================================================================= *)
