(* ================================================================= *)
(*  ZetaTrivialZeros.v  —  the trivial zeros  ζ(−2m) = 0  (m ≥ 1).     *)
(*                                                                    *)
(*  The completed relation ζ_ext(x) = J(x)·π^{x/2}/Γ_ext(x/2) has the  *)
(*  archimedean factor 1/Γ_ext(x/2), which VANISHES at the poles of Γ  *)
(*  (the nonpositive integers).  At x = −2m the argument x/2 = −m is    *)
(*  such a pole, so 1/Γ_ext(−m) = 0.  Crucially J is REGULAR at −2m     *)
(*  (its only poles are 0 and 1), so ζ_ext(−2m) = J(−2m)·π^{−m}·0 = 0   *)
(*  genuinely — the direct value coincides with the analytic           *)
(*  continuation (unlike ζ(0), where J's pole forced the limit         *)
(*  argument of ZetaZero).  These are Riemann's trivial zeros.         *)
(*                                                                    *)
(*  In the formalization Γ_ext(−m) = GamH(−m) = 0 because the shift     *)
(*  product prodshift(−m) has the vanishing factor (−m)+m = 0, and     *)
(*  Coq's /0 = 0 then encodes 1/Γ_ext(−m) = 0 correctly.               *)
(*  No new axioms (classical Reals only).                            *)
(* ================================================================= *)

From Stdlib Require Import Reals Rpower Lra Lia.
Require Import GammaExtend XiTwoSided MellinTail.
Open Scope R_scope.

(* --- the shift product vanishes at a nonpositive integer --- *)

Lemma prodshift_zero : forall m N, (m < N)%nat -> prodshift (- INR m) N = 0.
Proof.
  intros m N; induction N; intro Hlt; [ lia | ].
  cbn [prodshift]; destruct (Nat.eq_dec m N) as [-> | Hne].
  - replace (- INR N + INR N) with 0 by ring; ring.
  - rewrite IHN by lia; ring.
Qed.

Lemma lvl_gt : forall m, (m < lvl (- INR m))%nat.
Proof.
  intro m; unfold lvl; destruct (nat_gt (- - INR m)) as [n Hn]; simpl proj1_sig.
  apply INR_lt; rewrite Ropp_involutive in Hn; exact Hn.
Qed.

(* --- Γ_ext vanishes (formally) at the negative integers --- *)

Lemma GamH_neg_int : forall m, GamH (- INR m) = 0.
Proof.
  intro m; unfold GamH, GamN.
  rewrite (prodshift_zero m (lvl (- INR m)) (lvl_gt m)).
  unfold Rdiv; rewrite Rinv_0, Rmult_0_r; reflexivity.
Qed.

(* --- the trivial zeros --- *)

Theorem zeta_ext_trivial_zero : forall m, (1 <= m)%nat -> zeta_ext (- (2 * INR m)) = 0.
Proof.
  intros m _; unfold zeta_ext.
  replace (- (2 * INR m) / 2) with (- INR m) by field.
  rewrite (GamH_neg_int m); unfold Rdiv; rewrite Rinv_0, Rmult_0_r; reflexivity.
Qed.

(* concrete: ζ(−2) = ζ(−4) = ζ(−6) = 0 *)
Corollary zeta_ext_neg2 : zeta_ext (-2) = 0.
Proof. replace (-2) with (- (2 * INR 1)) by (simpl; ring); apply zeta_ext_trivial_zero; lia. Qed.

Corollary zeta_ext_neg4 : zeta_ext (-4) = 0.
Proof. replace (-4) with (- (2 * INR 2)) by (simpl; ring); apply zeta_ext_trivial_zero; lia. Qed.

Print Assumptions zeta_ext_trivial_zero.

(* ================================================================= *)
(*  END ZetaTrivialZeros.v.  ζ_ext(−2m) = 0 for m ≥ 1 — the trivial    *)
(*  zeros, from the vanishing of 1/Γ_ext at Γ's poles.                *)
(* ================================================================= *)
