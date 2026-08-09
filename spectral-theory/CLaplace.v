(* ================================================================= *)
(*  CLaplace.v  —  Milestone C, brick C4-7: the truncated Laplace       *)
(*  transform  g_T(z) = ∫₀ᵀ f(t) e^{−zt} dt  is entire in z, with        *)
(*  g_T'(z) = ∫₀ᵀ f(t)(−t) e^{−zt} dt.                                   *)
(*                                                                     *)
(*  Complex differentiation is direct (not the real-parameter Leibniz):  *)
(*  the increment integrand is f(t)·e^{−zt}·(e^{u}−1−u), u = −h·t, and    *)
(*  CexpRemainder.Cexpf_remainder gives |e^u−1−u| ≤ 3|u|²e^{|u|}, so the  *)
(*  whole increment is O(|h|²) = o(|h|) by the ML estimate.              *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra.
Require Import ComplexField Cmodulus CIntegral2 CSegInt CLeibniz
        CExpKernel CexpFull CexpRemainder Holomorphic.
Open Scope R_scope.

Lemma exp_le_compat : forall a b, a <= b -> exp a <= exp b.
Proof.
  intros a b Hab. destruct (Rle_lt_or_eq_dec a b Hab) as [Hlt | Heq].
  - left; apply exp_increasing; exact Hlt.
  - rewrite Heq; apply Rle_refl.
Qed.

Section Laplace.
Variable f : R -> C.
Hypothesis Hfc : Ccont f.
Variable T : R.
Hypothesis HT : 0 <= T.
Hypothesis Hfb : exists B, forall t, 0 <= t <= T -> Cmod (f t) <= B.

(* the integrand  f(t)e^{−zt}  and the derivative integrand  f(t)(−t)e^{−zt} *)
Definition lint  (z : C) (t : R) : C := Cmul (f t) (cexpzt (Copp z) t).
Definition ldint (z : C) (t : R) : C :=
  Cmul (f t) (Cmul (Copp (RtoC t)) (cexpzt (Copp z) t)).

Lemma negRtoC_cont : Ccont (fun t => Copp (RtoC t)).
Proof.
  apply Ccont_opp, (Ccont_RtoC (fun t => t)); intro x;
    apply derivable_continuous_pt, derivable_pt_id.
Qed.

Lemma lint_cont : forall z, Ccont (fun t => lint z t).
Proof. intro z; apply Ccont_mul; [ exact Hfc | apply Ccont_cexpzt ]. Qed.

Lemma ldint_cont : forall z, Ccont (fun t => ldint z t).
Proof.
  intro z; apply Ccont_mul;
    [ exact Hfc | apply Ccont_mul; [ apply negRtoC_cont | apply Ccont_cexpzt ] ].
Qed.

Definition g_T  (z : C) : C := Cintf (fun t => lint z t)  (lint_cont z)  0 T.
Definition g_T' (z : C) : C := Cintf (fun t => ldint z t) (ldint_cont z) 0 T.

(* e^{−(z+h)t} = e^{−zt} · e^{−ht} *)
Lemma cexpzt_add : forall z h t,
  cexpzt (Copp (Cadd z h)) t
  = Cmul (cexpzt (Copp z) t) (Cexpf (Cmul (Copp h) (RtoC t))).
Proof.
  intros z h t. unfold cexpzt.
  assert (Hsplit : Cmul (Copp (Cadd z h)) (RtoC t)
                 = Cadd (Cmul (Copp z) (RtoC t)) (Cmul (Copp h) (RtoC t)))
    by (apply Ceq; unfold Cmul, Copp, Cadd, RtoC; cbn; ring).
  rewrite Hsplit, Cexpf_add; reflexivity.
Qed.

(* the increment integrand equals f(t)·e^{−zt}·(e^{u}−1−u), u = −h·t *)
Lemma lint_increment : forall z h t,
  Cminus (Cminus (lint (Cadd z h) t) (lint z t)) (Cmul h (ldint z t))
  = Cmul (f t) (Cmul (cexpzt (Copp z) t)
                     (Cminus (Cminus (Cexpf (Cmul (Copp h) (RtoC t))) C1)
                             (Cmul (Copp h) (RtoC t)))).
Proof.
  intros z h t. unfold lint, ldint. rewrite cexpzt_add. ring.
Qed.

(* pointwise modulus of the increment integrand *)
Lemma lint_increment_mod : forall z h t, 0 <= t ->
  Cmod (Cminus (Cminus (lint (Cadd z h) t) (lint z t)) (Cmul h (ldint z t)))
  <= Cmod (f t) * exp (- Re z * t) * (3 * (Cmod h * t) ^ 2 * exp (Cmod h * t)).
Proof.
  intros z h t Ht. rewrite lint_increment, !Cmod_mul, Cmod_cexpzt.
  assert (HRe : Re (Copp z) * t = - Re z * t) by (unfold Copp; cbn; ring).
  rewrite HRe.
  assert (Hu : Cmod (Cmul (Copp h) (RtoC t)) = Cmod h * t)
    by (rewrite Cmod_mul, Cmod_opp, Cmod_RtoC, (Rabs_pos_eq t Ht); reflexivity).
  apply Rle_trans with
    (Cmod (f t) * (exp (- Re z * t) * (3 * (Cmod h * t) ^ 2 * exp (Cmod h * t)))).
  - apply Rmult_le_compat_l; [ apply Cmod_nonneg | ].
    apply Rmult_le_compat_l; [ left; apply exp_pos | ].
    eapply Rle_trans; [ apply (Cexpf_remainder (Cmul (Copp h) (RtoC t))) | ].
    rewrite Hu; apply Rle_refl.
  - apply Req_le; ring.
Qed.

(* g_T is entire, with derivative g_T' *)
Theorem gT_holo : forall z, is_Cderiv g_T z (g_T' z).
Proof.
  intros z eps Heps. destruct Hfb as [B HB].
  assert (HB0 : 0 <= B)
    by (apply Rle_trans with (Cmod (f 0)); [ apply Cmod_nonneg | apply HB; lra ]).
  set (EB := exp (Rabs (Re z) * T)). set (ET := exp T).
  assert (HEB : 0 < EB) by apply exp_pos. assert (HET : 0 < ET) by apply exp_pos.
  set (K0 := 3 * B * (T * T) * EB * ET).
  assert (HK0 : 0 <= K0) by (unfold K0; repeat apply Rmult_le_pos; lra).
  set (K := 2 * K0 * T + 1).
  assert (HK : 0 < K) by (unfold K; assert (0 <= 2 * K0 * T) by (repeat apply Rmult_le_pos; lra); lra).
  exists (Rmin 1 (eps / K)); split; [ apply Rmin_pos; [ lra | apply Rdiv_lt_0_compat; lra ] | ].
  intros h Hh.
  assert (Hh1 : Cmod h < 1) by (eapply Rlt_le_trans; [ exact Hh | apply Rmin_l ]).
  assert (HhK : Cmod h < eps / K) by (eapply Rlt_le_trans; [ exact Hh | apply Rmin_r ]).
  assert (Hh0 : 0 <= Cmod h) by apply Cmod_nonneg.
  (* rewrite the increment as one integral of the increment integrand *)
  assert (Hincf : Ccont (fun t => Cminus (Cminus (lint (Cadd z h) t) (lint z t))
                                         (Cmul h (ldint z t)))).
  { apply Ccont_sub; [ apply Ccont_sub; [ apply lint_cont | apply lint_cont ]
                     | apply Ccont_scal, ldint_cont ]. }
  assert (Hrw : Cminus (Cminus (g_T (Cadd z h)) (g_T z)) (Cmul (g_T' z) h)
              = Cintf (fun t => Cminus (Cminus (lint (Cadd z h) t) (lint z t))
                                       (Cmul h (ldint z t))) Hincf 0 T).
  { unfold g_T, g_T'.
    rewrite (Cintf_sub (fun t => Cminus (lint (Cadd z h) t) (lint z t))
               (fun t => Cmul h (ldint z t))
               (Ccont_sub _ _ (lint_cont (Cadd z h)) (lint_cont z))
               (Ccont_scal _ _ (ldint_cont z)) Hincf 0 T HT).
    rewrite (Cintf_sub (fun t => lint (Cadd z h) t) (fun t => lint z t)
               (lint_cont (Cadd z h)) (lint_cont z)
               (Ccont_sub _ _ (lint_cont (Cadd z h)) (lint_cont z)) 0 T HT).
    rewrite (Cintf_cmul_l h (fun t => ldint z t) (ldint_cont z)
               (Ccont_scal _ _ (ldint_cont z)) 0 T HT).
    ring. }
  rewrite Hrw.
  (* ML estimate with the uniform per-t bound K0 * Cmod h^2 *)
  eapply Rle_trans.
  { apply (Cintf_ML _ Hincf 0 T (K0 * Cmod h ^ 2) HT).
    intros t Ht. eapply Rle_trans; [ apply lint_increment_mod; lra | ].
    (* Cmod(f t)*exp(-Re z t)*(3(Cmod h t)² exp(Cmod h t)) <= K0 * Cmod h^2 *)
    assert (E1 : exp (- Re z * t) <= EB).
    { apply exp_le_compat.
      apply Rle_trans with (Rabs (Re z) * t).
      - apply Rmult_le_compat_r; [ lra | ].
        eapply Rle_trans; [ apply Rle_abs | rewrite Rabs_Ropp; apply Rle_refl ].
      - apply Rmult_le_compat_l; [ apply Rabs_pos | lra ]. }
    assert (E2 : exp (Cmod h * t) <= ET).
    { apply exp_le_compat.
      apply Rle_trans with (1 * T); [ | lra ].
      apply Rmult_le_compat; lra. }
    assert (Hf0 : 0 <= Cmod (f t)) by apply Cmod_nonneg.
    assert (Hft : Cmod (f t) <= B) by (apply HB; lra).
    assert (Ht2 : (Cmod h * t) ^ 2 <= Cmod h ^ 2 * (T * T)).
    { rewrite Rpow_mult_distr. apply Rmult_le_compat_l; [ apply pow2_ge_0 | ].
      replace (t ^ 2) with (t * t) by ring. apply Rmult_le_compat; lra. }
    (* now combine, all factors nonneg *)
    apply Rle_trans with (B * EB * (3 * (Cmod h ^ 2 * (T * T)) * ET)).
    - apply Rmult_le_compat.
      + apply Rmult_le_pos; [ exact Hf0 | left; apply exp_pos ].
      + apply Rmult_le_pos; [ apply Rmult_le_pos; [ lra | apply pow2_ge_0 ] | left; apply exp_pos ].
      + apply Rmult_le_compat; [ exact Hf0 | left; apply exp_pos | exact Hft | exact E1 ].
      + apply Rmult_le_compat.
        * apply Rmult_le_pos; [ lra | apply pow2_ge_0 ].
        * left; apply exp_pos.
        * apply Rmult_le_compat_l; [ lra | exact Ht2 ].
        * exact E2.
    - unfold K0; apply Req_le; ring. }
  (* 2 * (K0 * Cmod h^2) * (T - 0) <= eps * Cmod h *)
  replace (T - 0) with T by ring.
  apply Rle_trans with ((2 * K0 * T) * Cmod h * Cmod h); [ apply Req_le; ring | ].
  apply Rle_trans with (eps * Cmod h); [ | apply Rle_refl ].
  apply Rmult_le_compat_r; [ exact Hh0 | ].
  (* 2 K0 T * Cmod h <= eps *)
  apply Rle_trans with (2 * K0 * T * (eps / K)).
  - apply Rmult_le_compat_l; [ repeat apply Rmult_le_pos; lra | left; exact HhK ].
  - unfold K. apply Rle_trans with (K * (eps / K)); [ | apply Req_le; field; lra ].
    apply Rmult_le_compat_r; [ apply Rlt_le, Rdiv_lt_0_compat; lra | unfold K; lra ].
Qed.

Print Assumptions gT_holo.

End Laplace.
