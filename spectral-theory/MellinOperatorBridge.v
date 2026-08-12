(* ================================================================= *)
(*  MellinOperatorBridge.v  —  the diagonal (prime) operator mapped to    *)
(*  the archimedean Mellin/Gamma transform.                             *)
(*                                                                    *)
(*  The Mellin transform is the Fourier transform of the multiplicative  *)
(*  group R_+; it carries the diagonal operator's multiplicative-         *)
(*  character eigenvalue  z s n = n^{-s}  into the archimedean Gamma       *)
(*  world.  Since  mellin s c = c^{-s} Gam s  (MellinKernel.mellin_scale), *)
(*                                                                    *)
(*      mode_mellin  :  mellin s n  =  (n^{-s}) * Gam s  =  z s n * Gam s, *)
(*                                                                    *)
(*  i.e. the operator's n-th eigenvalue IS its Mellin transform / Gam s.   *)
(*  Summing the modes gives the heat-kernel/spectral-zeta representation   *)
(*      sum_{n<=N} mellin s n  =  Gam s * Tr(D z_s over first N modes)     *)
(*      ->  Gam(s) * zeta(s)   (s > 1),                                    *)
(*  the operator-theoretic form of  zeta(s) Gam(s) = int_0^oo (sum e^{-nt})*)
(*  t^{s-1} dt.  This is the concrete map from the diagonal prime operator *)
(*  to the repo's Fourier/Mellin (archimedean) machinery.  Axiom-clean.    *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia List.
Import ListNotations.
Require Import Ell2 Ell2Zeta Ell2ZetaCont GammaReal MellinKernel.
Open Scope R_scope.

(*  the operator eigenvalue n^{-s} = its Mellin transform, divided by Gam s  *)
Lemma mode_mellin : forall s n (Hs : 0 < s) (Hc : 0 < INR (S n)),
  mellin s (INR (S n)) Hs Hc = z s (S n) * Gam s Hs.
Proof.
  intros s n Hs Hc; rewrite (mellin_scale s (INR (S n)) Hs Hc); unfold z; reflexivity.
Qed.

(*  distributing a scalar over a real fold-sum  *)
Lemma fold_scal : forall (c : R) (l : list R),
  fold_right Rplus 0 (map (fun x => c * x) l) = c * fold_right Rplus 0 l.
Proof. intros c l; induction l as [| x l IH]; simpl; [ ring | rewrite IH; ring ]. Qed.

(*  the Gamma-weighted partial trace = the sum of the per-mode Mellin       *)
(*  transforms (each summand Gam s * z s n = mellin s n, by mode_mellin)    *)
Lemma trace_mellin_eq : forall s (Hs : 0 < s) N,
  Gam s Hs * diag_trace (z s) N
  = fold_right Rplus 0 (map (fun n => Gam s Hs * z s n) (seq 1 N)).
Proof.
  intros s Hs N; rewrite (diag_trace_eq (z s) N), <- fold_scal, map_map; reflexivity.
Qed.

(*  the summed Mellin transforms converge to  Gam(s) * zeta(s)  (s > 1) --   *)
(*  the heat-kernel/spectral-zeta representation, operator-theoretically     *)
Theorem mellin_trace_cv : forall s (Hs0 : 0 < s) (Hs1 : s <> 1), 1 < s ->
  Un_cv (fun N => Gam s Hs0 * diag_trace (z s) N) (Gam s Hs0 * zeta_cont s Hs0 Hs1).
Proof.
  intros s Hs0 Hs1 H.
  exact (Un_cv_scal (fun N => diag_trace (z s) N) (zeta_cont s Hs0 Hs1) (Gam s Hs0)
           (operator_zeta_eq_cont s Hs0 Hs1 H)).
Qed.

Print Assumptions mode_mellin.
Print Assumptions mellin_trace_cv.

(* ================================================================= *)
(*  END MellinOperatorBridge.v — diagonal prime operator <-> Mellin/Gamma. *)
(*  mode_mellin identifies the operator's eigenvalue n^{-s} with its         *)
(*  archimedean Mellin transform / Gam s; mellin_trace_cv realizes           *)
(*  Gam(s) zeta(s) as the summed per-mode Mellin transforms = Gam s times    *)
(*  the operator's spectral-zeta trace.  This is the operator side meeting   *)
(*  the archimedean Fourier (Mellin) side.  The Hilbert-Polya gap that       *)
(*  remains is NOT here: it is the identification of the operator's spectrum *)
(*  with the zeta ZEROS (the Berry-Keating link) -- see docs.               *)
(* ================================================================= *)
