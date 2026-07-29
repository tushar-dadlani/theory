(* ================================================================= *)
(*  Ell2ZetaConverge.v  —  STAGE 5: the ζ-operator partition-function  *)
(*  trace CONVERGES (for s ≥ 2).                                      *)
(*                                                                    *)
(*  In Ell2Zeta.v the partial trace of the ζ-operator Z_s was          *)
(*      dzeta s N = Tr_N Z_s = Σ_{n=1}^{N} n^{-s}.                     *)
(*  Here we prove this sequence CONVERGES as N → ∞ for every s ≥ 2,    *)
(*  so the partition function  ζ(s) = Tr Z_s  exists as a genuine      *)
(*  limit.  The s = 2 case is transferred from ZetaConverge's          *)
(*  zeta2_converges (Σ 1/n² converges by monotone-bounded), and s ≥ 2  *)
(*  follows by comparison with the s = 2 limit (n^{-s} ≤ n^{-2}).      *)
(*                                                                    *)
(*  HONEST SCOPE: proves the limit EXISTS for s ≥ 2; does not compute  *)
(*  the value (π²/6 at s=2), the range 1 < s < 2, the Euler product,   *)
(*  analytic continuation, or anything about the zeta zeros / RH —     *)
(*  the same boundary as ZetaConverge.                                *)
(*                                                                    *)
(*  Axiom footprint: the von Mangoldt / Chebyshev tree's standard set  *)
(*  (inherited through Ell2Zeta).                                     *)
(* ================================================================= *)

Require Import Ell2 Ell2Operator Ell2Basis Ell2Zeta.
Require Import ZetaConverge Chebyshev.
From Stdlib Require Import Reals Rpower Lra Lia List.
Import ListNotations.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  Elementary fold / dzeta toolkit.                                 *)
(* ----------------------------------------------------------------- *)

Lemma fold_Rplus_app : forall l1 l2,
  fold_right Rplus 0 (l1 ++ l2) = (fold_right Rplus 0 l1 + fold_right Rplus 0 l2)%R.
Proof. intros l1 l2; induction l1 as [| a l1 IH]; simpl; [ ring | rewrite IH; ring ]. Qed.

Lemma dzeta_succ : forall s N, dzeta s (S N) = (dzeta s N + z s (S N))%R.
Proof.
  intros s N; unfold dzeta.
  rewrite seq_S, map_app, fold_Rplus_app; simpl.
  replace (1 + N)%nat with (S N) by lia; ring.
Qed.

Lemma fold_Rplus_le : forall (f g : nat -> R) l,
  (forall x, f x <= g x) -> fold_right Rplus 0 (map f l) <= fold_right Rplus 0 (map g l).
Proof.
  intros f g l H; induction l as [| a l IH]; simpl; [ lra | pose proof (H a); lra ].
Qed.

(* ----------------------------------------------------------------- *)
(*  STAGE 5a — bridge to ZetaConverge at s = 2.                       *)
(* ----------------------------------------------------------------- *)

(* n^{-2} = 1/n²  (the Rpower computation) *)
Lemma z2_recip : forall n, (1 <= n)%nat -> z 2 n = / (INR n) ^ 2.
Proof.
  intros n Hn; unfold z; destruct n as [| m]; [ lia | ].
  rewrite Rpower_Ropp; replace 2 with (INR 2) at 1 by (simpl; ring).
  rewrite Rpower_pow by (apply lt_0_INR; lia); reflexivity.
Qed.

Lemma z2_eq_zterm : forall k, z 2 (S k) = zterm k.
Proof. intro k; unfold zterm; rewrite z2_recip by lia; reflexivity. Qed.

(* the operator trace at s=2 is exactly ZetaConverge's partial sum *)
Lemma dzeta2_eq_zpart : forall M, dzeta 2 (S M) = zpart M.
Proof.
  induction M as [| M IH].
  - rewrite dzeta_succ; unfold dzeta, zpart; simpl.
    rewrite z2_eq_zterm; unfold zterm; simpl; ring.
  - rewrite dzeta_succ, IH.
    change (zpart (S M)) with (zpart M + zterm (S M))%R.
    rewrite z2_eq_zterm; ring.
Qed.

(* dropping a leading shift preserves the limit *)
Lemma Un_cv_unshift : forall U l, Un_cv (fun M => U (S M)) l -> Un_cv U l.
Proof.
  intros U l H eps Heps; destruct (H eps Heps) as [N HN].
  exists (S N); intros n Hn; destruct n as [| m]; [ lia | ].
  apply HN; lia.
Qed.

(* STAGE 5a: the s=2 partition trace converges (from ZetaConverge) *)
Lemma dzeta2_converges : { l : R | Un_cv (fun N => dzeta 2 N) l }.
Proof.
  destruct zeta2_converges as [l Hl]; exists l.
  apply Un_cv_unshift.
  apply (Un_cv_eq zpart); [ intro M; symmetry; apply dzeta2_eq_zpart | exact Hl ].
Qed.

(* ----------------------------------------------------------------- *)
(*  STAGE 5b — monotone-bounded convergence for every s ≥ 2.          *)
(* ----------------------------------------------------------------- *)

Lemma exp_le_compat : forall x y, x <= y -> exp x <= exp y.
Proof.
  intros x y H; destruct (Rle_lt_or_eq_dec x y H) as [Hlt | Heq];
    [ left; apply exp_increasing; exact Hlt | rewrite Heq; apply Rle_refl ].
Qed.

(* n^{-s} ≤ n^{-2}  for s ≥ 2 *)
Lemma z_mono : forall s n, 2 <= s -> z s n <= z 2 n.
Proof.
  intros s n Hs; unfold z; destruct (Nat.eqb n 0) eqn:E; [ apply Rle_refl | ].
  apply Nat.eqb_neq in E.
  assert (Hln : 0 <= ln (INR n)) by (apply ln_ge0; rewrite <- INR_1; apply le_INR; lia).
  unfold Rpower; apply exp_le_compat; nra.
Qed.

Lemma dzeta_mono_s : forall s N, 2 <= s -> dzeta s N <= dzeta 2 N.
Proof. intros s N Hs; unfold dzeta; apply fold_Rplus_le; intro n; apply z_mono; exact Hs. Qed.

Lemma dzeta_growing : forall s, 0 <= s -> Un_growing (dzeta s).
Proof.
  intros s Hs n; rewrite dzeta_succ; pose proof (z_bounds s (S n) Hs) as [Hlo _]; lra.
Qed.

(* STAGE 5b: the s≥2 partition trace converges (monotone + bounded) *)
Theorem zeta_trace_converges : forall s, 2 <= s -> { l : R | Un_cv (fun N => dzeta s N) l }.
Proof.
  intros s Hs; destruct dzeta2_converges as [l2 Hl2].
  apply growing_cv.
  - apply dzeta_growing; lra.
  - exists l2; intros x [n ->]; apply Rle_trans with (dzeta 2 n).
    + apply dzeta_mono_s; exact Hs.
    + apply (growing_ineq (dzeta 2)); [ apply dzeta_growing; lra | exact Hl2 ].
Qed.

(* the OPERATOR statement: the spectral trace of Z_s converges — the
   partition function ζ(s) = Tr Z_s exists for s ≥ 2. *)
Theorem zeta_partition_converges :
  forall s, 2 <= s -> { l : R | Un_cv (fun N => diag_trace (z s) N) l }.
Proof.
  intros s Hs; destruct (zeta_trace_converges s Hs) as [l Hl]; exists l.
  apply (Un_cv_eq (fun N => dzeta s N)); [ intro N; symmetry; apply zeta_partition | exact Hl ].
Qed.

(* flagship: the primon-gas partition function at s = 2 converges *)
Corollary zeta_partition_converges_2 : { l : R | Un_cv (fun N => diag_trace (z 2) N) l }.
Proof. apply zeta_partition_converges; lra. Qed.

Print Assumptions zeta_trace_converges.
Print Assumptions zeta_partition_converges.

(* ================================================================= *)
(*  END Ell2ZetaConverge.v                                           *)
(*  The ζ-operator's partition-function trace Tr_N Z_s = Σ n^{-s}      *)
(*  converges as N → ∞ for every s ≥ 2, so ζ(s) = Tr Z_s exists as a   *)
(*  limit — the operator-side realization of ZetaConverge's infinite   *)
(*  primon-gas partition function.                                    *)
(* ================================================================= *)
