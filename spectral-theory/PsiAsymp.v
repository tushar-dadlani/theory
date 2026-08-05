(* ================================================================= *)
(*  PsiAsymp.v  —  RUNG 4: limsup Vrem = 0  =>  psi ~ x  =>  PNT.       *)
(*                                                                    *)
(*  The short capstone that closes the Erdos-Selberg chain modulo the   *)
(*  single research lemma `avg_below`.  The bridge is the identity      *)
(*      |psi n / n - 1| = |Rem n| / n = Vrem n     (n >= 1),            *)
(*  so  Un_cv Vrem 0  <=>  psi(x) ~ x.  Chaining:                        *)
(*                                                                    *)
(*   Vrem_cv0             : is_limsup Vrem 0 -> Un_cv Vrem 0            *)
(*   psi_asymp_cv         : Un_cv Vrem 0 -> Un_cv (psi/N) 1            *)
(*   psi_asymp_of_avg_below :                                          *)
(*       (forall L, is_limsup Vrem L -> avg_below L) -> Un_cv (psi/N) 1 *)
(*   pnt_of_avg_below     : same hypothesis -> Un_cv (pi/(N/ln N)) 1    *)
(*                                                                    *)
(*  So the ENTIRE Prime Number Theorem is now formalised, axiom-clean,   *)
(*  modulo the one lemma  `avg_below (limsup Vrem)`  (Rung 3c-B).        *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia Arith Lists.List.
Import ListNotations.
Require Import Chebyshev ChebyshevBound ChebyshevPrime PrimePowerReindex
        VonMangoldtGlobal RealMobius SelbergEndgame SelbergAverage
        LimSup SelbergCollapse PNTConditional.
Open Scope R_scope.

(* Vrem is bounded on all of nat (Vrem 0 = 0), so its limsup exists. *)
Lemma Vrem_bound_all : forall n, Vrem n <= Kup - 1.
Proof.
  assert (HK : 0 <= Kup - 1) by (unfold Kup; pose proof ln2_pos; lra).
  intro n; destruct n as [| m]; [ | apply Vrem_bound; lia ].
  assert (H0 : Vrem 0 = 0).
  { unfold Vrem, Rem.
    replace (psi 0) with 0 by reflexivity.
    replace (INR 0) with 0 by reflexivity.
    rewrite Rminus_0_r, Rabs_R0; unfold Rdiv; rewrite Rmult_0_l; reflexivity. }
  rewrite H0; exact HK.
Qed.

Lemma Vrem_cv0 : is_limsup Vrem 0 -> Un_cv Vrem 0.
Proof.
  intros [Ha _] eps Heps.
  destruct (Ha eps Heps) as [N0 HN0].
  exists N0; intros n Hn.
  unfold R_dist; rewrite Rminus_0_r, Rabs_pos_eq by apply Vrem_nonneg.
  specialize (HN0 n Hn); lra.
Qed.

Lemma psi_asymp_cv : Un_cv Vrem 0 -> Un_cv (fun N => psi N / INR N) 1.
Proof.
  intros H eps Heps.
  destruct (H eps Heps) as [N HN].
  exists (Nat.max N 1); intros n Hn.
  assert (Hne : INR n <> 0) by (apply not_0_INR; lia).
  unfold R_dist.
  replace (psi n / INR n - 1) with (Rem n / INR n) by (unfold Rem; field; exact Hne).
  assert (HV : Rabs (Rem n / INR n) = Vrem n).
  { unfold Vrem, Rdiv; rewrite Rabs_mult, (Rabs_right (/ INR n))
      by (apply Rle_ge; left; apply Rinv_0_lt_compat; apply lt_0_INR; lia); reflexivity. }
  rewrite HV.
  specialize (HN n ltac:(lia)); unfold R_dist in HN;
    rewrite Rminus_0_r, Rabs_pos_eq in HN by apply Vrem_nonneg.
  exact HN.
Qed.

Theorem psi_asymp_of_avg_below :
  (forall L, is_limsup Vrem L -> avg_below L) ->
  Un_cv (fun N => psi N / INR N) 1.
Proof.
  intro Hdens.
  assert (Hlb : exists m, forall n, m <= Vrem n) by (exists 0; apply Vrem_nonneg).
  assert (Hub : exists M, forall n, Vrem n <= M) by (exists (Kup - 1); apply Vrem_bound_all).
  destruct (limsup_exists Vrem Hlb Hub) as [L HL].
  assert (HL0 : L = 0) by (apply (selberg_collapse L HL); apply Hdens; exact HL).
  rewrite HL0 in HL.
  apply psi_asymp_cv, Vrem_cv0; exact HL.
Qed.

Theorem pnt_of_avg_below :
  (forall L, is_limsup Vrem L -> avg_below L) ->
  Un_cv (fun N => pi_count N / (INR N / ln (INR N))) 1.
Proof.
  intro Hdens; apply pi_asymp_of_psi, psi_asymp_of_avg_below; exact Hdens.
Qed.

Print Assumptions pnt_of_avg_below.

(* ================================================================= *)
(*  END PsiAsymp.v  —  RUNG 4: PNT modulo `avg_below (limsup Vrem)`.    *)
(* ================================================================= *)
