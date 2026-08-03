(* ================================================================= *)
(*  CZetaHolo.v  —  item 4: zetaC is holomorphic on the strip.         *)
(*                                                                    *)
(*  Part 1: the per-term second-order remainder bound.  Along the      *)
(*  segment s' = z + t*h, phi(t) = Re/Im(gtermC(z+t h,n)) is C^2 with   *)
(*    phi'(t)  = Re/Im(dgtermC(z+t h)·h)        (line-bridge o 2b.2),   *)
(*    phi''(t) = Re/Im(d2gtermC(z+t h)·h·h)     (line-bridge o 2b.2),   *)
(*  so order2_bound gives  |phi(1)-phi(0)-phi'(0)| <= B_n·|h|^2 for any  *)
(*  uniform bound B_n on Cmod(d2gtermC) over the segment.  Axiom-clean. *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import ComplexField Cmodulus CexpFull Holomorphic CexpRemainder
               CSeries CDeriv CDerivLine CBaseDeriv CBaseDeriv2
               CZetaTerm CZetaTerm2 CZetaDeriv2.
Open Scope R_scope.

(* derivative of  w |-> F w · c  (c constant) is  dF · c *)
Lemma Cderiv_mul_const_r : forall F z dF c,
  is_Cderiv F z dF -> is_Cderiv (fun w => Cmul (F w) c) z (Cmul dF c).
Proof.
  intros F z dF c HF.
  apply (is_Cderiv_eq _ _ (Cadd (Cmul dF c) (Cmul (F z) C0))).
  - apply Cderiv_mul; [ exact HF | apply Cderiv_const ].
  - ring.
Qed.

Section Remainder.
Variables (z h : C) (n : nat).
Hypothesis Hseg : forall t, 0 <= t <= 1 -> Cminus C1 (Cadd z (Cmul (RtoC t) h)) <> C0.

Lemma line_phi'_Re : forall t, 0 <= t <= 1 ->
  derivable_pt_lim (fun u => Re (gtermC (Cadd z (Cmul (RtoC u) h)) n)) t
    (Re (Cmul (dgtermC (Cadd z (Cmul (RtoC t) h)) n) h)).
Proof.
  intros t Ht.
  apply (is_Cderiv_line_Re (fun w => gtermC w n) z h).
  apply gtermC_sderiv; apply Hseg; exact Ht.
Qed.

Lemma line_phi''_Re : forall t, 0 <= t <= 1 ->
  derivable_pt_lim (fun u => Re (Cmul (dgtermC (Cadd z (Cmul (RtoC u) h)) n) h)) t
    (Re (Cmul (Cmul (d2gtermC (Cadd z (Cmul (RtoC t) h)) n) h) h)).
Proof.
  intros t Ht.
  apply (is_Cderiv_line_Re (fun w => Cmul (dgtermC w n) h) z h).
  apply Cderiv_mul_const_r; apply dgtermC_sderiv; apply Hseg; exact Ht.
Qed.

Lemma line_phi'_Im : forall t, 0 <= t <= 1 ->
  derivable_pt_lim (fun u => Im (gtermC (Cadd z (Cmul (RtoC u) h)) n)) t
    (Im (Cmul (dgtermC (Cadd z (Cmul (RtoC t) h)) n) h)).
Proof.
  intros t Ht.
  apply (is_Cderiv_line_Im (fun w => gtermC w n) z h).
  apply gtermC_sderiv; apply Hseg; exact Ht.
Qed.

Lemma line_phi''_Im : forall t, 0 <= t <= 1 ->
  derivable_pt_lim (fun u => Im (Cmul (dgtermC (Cadd z (Cmul (RtoC u) h)) n) h)) t
    (Im (Cmul (Cmul (d2gtermC (Cadd z (Cmul (RtoC t) h)) n) h) h)).
Proof.
  intros t Ht.
  apply (is_Cderiv_line_Im (fun w => Cmul (dgtermC w n) h) z h).
  apply Cderiv_mul_const_r; apply dgtermC_sderiv; apply Hseg; exact Ht.
Qed.

(* the second-order remainder along the segment, both components *)
Lemma remainder_Re : forall Bn, 0 <= Bn ->
  (forall t, 0 <= t <= 1 -> Cmod (d2gtermC (Cadd z (Cmul (RtoC t) h)) n) <= Bn) ->
  Rabs (Re (gtermC (Cadd z (Cmul (RtoC 1) h)) n)
        - Re (gtermC (Cadd z (Cmul (RtoC 0) h)) n)
        - Re (Cmul (dgtermC (Cadd z (Cmul (RtoC 0) h)) n) h))
    <= Bn * (Cmod h * Cmod h).
Proof.
  intros Bn HBn Hbd.
  apply (order2_bound
    (fun u => Re (gtermC (Cadd z (Cmul (RtoC u) h)) n))
    (fun t => Re (Cmul (dgtermC (Cadd z (Cmul (RtoC t) h)) n) h))
    (fun t => Re (Cmul (Cmul (d2gtermC (Cadd z (Cmul (RtoC t) h)) n) h) h))).
  - apply Rmult_le_pos; [ exact HBn | apply Rmult_le_pos; apply Cmod_nonneg ].
  - apply line_phi'_Re.
  - apply line_phi''_Re.
  - intros t Ht.
    eapply Rle_trans; [ apply Cmod_Re_le | ].
    rewrite !Cmod_mul.
    replace (Bn * (Cmod h * Cmod h)) with (Bn * Cmod h * Cmod h) by ring.
    apply Rmult_le_compat_r; [ apply Cmod_nonneg | ].
    apply Rmult_le_compat_r; [ apply Cmod_nonneg | ].
    apply Hbd; exact Ht.
Qed.

Lemma remainder_Im : forall Bn, 0 <= Bn ->
  (forall t, 0 <= t <= 1 -> Cmod (d2gtermC (Cadd z (Cmul (RtoC t) h)) n) <= Bn) ->
  Rabs (Im (gtermC (Cadd z (Cmul (RtoC 1) h)) n)
        - Im (gtermC (Cadd z (Cmul (RtoC 0) h)) n)
        - Im (Cmul (dgtermC (Cadd z (Cmul (RtoC 0) h)) n) h))
    <= Bn * (Cmod h * Cmod h).
Proof.
  intros Bn HBn Hbd.
  apply (order2_bound
    (fun u => Im (gtermC (Cadd z (Cmul (RtoC u) h)) n))
    (fun t => Im (Cmul (dgtermC (Cadd z (Cmul (RtoC t) h)) n) h))
    (fun t => Im (Cmul (Cmul (d2gtermC (Cadd z (Cmul (RtoC t) h)) n) h) h))).
  - apply Rmult_le_pos; [ exact HBn | apply Rmult_le_pos; apply Cmod_nonneg ].
  - apply line_phi'_Im.
  - apply line_phi''_Im.
  - intros t Ht.
    eapply Rle_trans; [ apply Cmod_Im_le | ].
    rewrite !Cmod_mul.
    replace (Bn * (Cmod h * Cmod h)) with (Bn * Cmod h * Cmod h) by ring.
    apply Rmult_le_compat_r; [ apply Cmod_nonneg | ].
    apply Rmult_le_compat_r; [ apply Cmod_nonneg | ].
    apply Hbd; exact Ht.
Qed.

End Remainder.

Print Assumptions remainder_Re.

(* ================================================================= *)
(*  END CZetaHolo.v (part 1: per-term second-order remainder bound).  *)
(* ================================================================= *)
