(* ================================================================= *)
(*  ZetaCompleted.v  —  Riemann FE milestone R3, capstone:          *)
(*  the completed zeta as the symmetric J.                          *)
(*                                                                    *)
(*     π^{−s/2}·Γ(s/2)·ζ(s) = J(s)   (s > 1),                        *)
(*  which with R1's  J(s) = J(1−s)  is Riemann's functional equation *)
(*  in integral form.  Per-term, `gnear_k + gtail_k = mellin_k =     *)
(*  π^{−s/2}·Γ(s/2)·(k+1)^{−s}` (mellin_scale + Rpower algebra); the  *)
(*  head/tail series (R3 files 2,3) sum these to Hu+T = J (xi_eq_J);  *)
(*  and Σ_k (k+1)^{−s} = ζ(s) = zeta_cont via Zpart.                 *)
(*  No new axioms (classical Reals only).                            *)
(* ================================================================= *)

From Stdlib Require Import Reals Rpower Lra Lia.
Require Import GammaReal MellinKernel MellinTail MellinHead RiemannThetaFE
        MellinTailSeries MellinHeadSeries ImproperCv1
        Ell2ZetaCont ZetaContinuation HagedornTransition.
Open Scope R_scope.

(* --- per-n Rpower algebra --- *)

Lemma per_n_pow : forall s k,
  Rpower (PI * INR (S k) ^ 2) (- (s / 2)) = Rpower PI (- (s / 2)) * Rpower (INR (S k)) (- s).
Proof.
  intros s k.
  assert (Hpi : 0 < PI) by apply PI_RGT_0.
  assert (Hn : 0 < INR (S k)) by (apply lt_0_INR; lia).
  rewrite (Rpower_mult_base PI (INR (S k) ^ 2) (- (s / 2)) Hpi (pow_lt _ 2 Hn)).
  f_equal.
  rewrite <- (Rpower_pow 2 (INR (S k)) Hn), Rpower_mult.
  f_equal; simpl; field.
Qed.

Lemma per_n_val : forall s (Hs2 : 0 < s / 2) k,
  gnl s Hs2 k + gtl s k = Rpower PI (- (s / 2)) * Gam (s / 2) Hs2 * Rpower (INR (S k)) (- s).
Proof.
  intros s Hs2 k.
  assert (Heq : gnl s Hs2 k + gtl s k = mellin (s / 2) (PI * INR (S k) ^ 2) Hs2 (PIn2_pos k))
    by (unfold gnl, gtl, mellin; reflexivity).
  rewrite Heq, (mellin_scale (s / 2) (PI * INR (S k) ^ 2) Hs2 (PIn2_pos k)), per_n_pow; ring.
Qed.

(* --- ζ(s) = lim Zpart s = zeta_cont s  (s>1) --- *)

Lemma zeta_hookup : forall s (Hs0 : 0 < s) (Hs1 : s <> 1), 1 < s ->
  Un_cv (Zpart s) (zeta_cont s Hs0 Hs1).
Proof.
  intros s Hs0 Hs1 Hs.
  destruct (Zpart_cv s Hs) as [Z HZ].
  assert (Z = zeta_cont s Hs0 Hs1).
  { apply (UL_sequence (fun N => / (s - 1) + sum_f_R0 (gterm s) N));
      [ apply zeta_continuation_extends; assumption | apply zeta_cont_series ]. }
  rewrite <- H; exact HZ.
Qed.

(* --- the completed-zeta identity --- *)

Theorem zeta_completed_eq_J : forall s (Hs0 : 0 < s) (Hs1 : s <> 1) (Hs2 : 0 < s / 2), 1 < s ->
  Rpower PI (- (s / 2)) * Gam (s / 2) Hs2 * zeta_cont s Hs0 Hs1 = J s.
Proof.
  intros s Hs0 Hs1 Hs2 Hs.
  set (C := Rpower PI (- (s / 2)) * Gam (s / 2) Hs2).
  (* the two series converge to Hu s + T s *)
  assert (Hsum : Un_cv (fun M => sum_f_R0 (gnl s Hs2) M + sum_f_R0 (gtl s) M) (Hu s + T s))
    by (apply CV_plus; [ exact (head_series s Hs2 Hs) | exact (tail_series s Hs) ]).
  (* and to C · Zpart s M *)
  assert (Heq : forall M, sum_f_R0 (gnl s Hs2) M + sum_f_R0 (gtl s) M = C * Zpart s M).
  { intro M; unfold Zpart, C; induction M.
    - cbn [sum_f_R0]; exact (per_n_val s Hs2 0).
    - replace (sum_f_R0 (gnl s Hs2) (S M) + sum_f_R0 (gtl s) (S M))
        with ((sum_f_R0 (gnl s Hs2) M + sum_f_R0 (gtl s) M)
              + (gnl s Hs2 (S M) + gtl s (S M))) by (cbn [sum_f_R0]; ring).
      rewrite IHM, (per_n_val s Hs2 (S M)); cbn [sum_f_R0]; ring. }
  assert (Hlim2 : Un_cv (fun M => sum_f_R0 (gnl s Hs2) M + sum_f_R0 (gtl s) M)
                        (C * zeta_cont s Hs0 Hs1)).
  { apply (Un_cv_ext (fun M => C * Zpart s M)); [ intro M; symmetry; apply Heq | ].
    apply (CV_mult (fun _ => C) (Zpart s) C (zeta_cont s Hs0 Hs1));
      [ apply Un_cv_const | apply zeta_hookup; assumption ]. }
  assert (Heq2 : Hu s + T s = C * zeta_cont s Hs0 Hs1)
    by (apply (UL_sequence (fun M => sum_f_R0 (gnl s Hs2) M + sum_f_R0 (gtl s) M));
        [ exact Hsum | exact Hlim2 ]).
  unfold C in *; rewrite <- (xi_eq_J s Hs), Heq2; reflexivity.
Qed.

Print Assumptions zeta_completed_eq_J.

(* π^{−s/2}·Γ(s/2)·ζ(s) = J(s) (this file), and J(s)=J(1−s)
   (RiemannThetaFE.J_symmetric): the completed zeta equals the symmetric J —
   Riemann's functional equation in integral form. *)

(* ================================================================= *)
(*  END ZetaCompleted.v.  π^{−s/2}·Γ(s/2)·ζ(s) = J(s)  (s>1).         *)
(* ================================================================= *)
