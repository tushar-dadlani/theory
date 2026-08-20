(* ================================================================= *)
(*  CEfacLower.v  —  LOWER bounds for a single Weierstrass factor.     *)
(*                                                                    *)
(*    Efac_lower_far  : 10 |z| <= |rho|  ==>                           *)
(*        exp (-2 |z|^2 / |rho|^2)  <=  |E(z/rho)|                     *)
(*    Efac_lower_near : always,                                        *)
(*        (|rho - z| / |rho|) . exp (- |z|/|rho|)  <=  |E(z/rho)|      *)
(*                                                                    *)
(*  Every previous estimate on Efac was an UPPER bound (Efac_dev_le,   *)
(*  driving convergence).  The minimum modulus of the product needs    *)
(*  the opposite, and the two regimes are genuinely different:         *)
(*                                                                    *)
(*   * far from the zero the factor is close to 1 and the deviation is *)
(*     QUADRATIC -- the whole point of the e^{z/rho} correction, which *)
(*     cancels the linear term.  Getting that cancellation without a   *)
(*     complex logarithm is the content of exp_neg_quad_le: the        *)
(*     identity |1-w|^2 = 1 - 2 Re w + |w|^2 turns the claim into a    *)
(*     REAL inequality, exp(-t-t^2) <= 1-t, and t^2 <= 4|w|^2 is what  *)
(*     absorbs the correction.  Proved from exp s >= (1 + s/2)^2, i.e. *)
(*     exp_ineq1_le squared -- e is never evaluated.                   *)
(*   * near the zero nothing cancels and the bound is simply the       *)
(*     distance |rho - z|, which is why the caller has to choose a     *)
(*     circle that keeps away from the zeros.                          *)
(*                                                                    *)
(*  The cut is at |rho| >= 10 |z| rather than the sharper 2 |z|; the   *)
(*  constant only has to make the quadratic branch's arithmetic close, *)
(*  and the o(r^2) target has room to spare.                           *)
(*  Axiom-clean.                                                       *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra.
Require Import ComplexField Cmodulus CDeriv CexpFull CSeries CInfProd XiHadamardProd.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  A.  two real inequalities                                          *)
(* ----------------------------------------------------------------- *)
Lemma exp_quad_lower : forall s, 0 <= s -> 1 + s + s ^ 2 / 4 <= exp s.
Proof.
  intros s Hs.
  replace s with (s / 2 + s / 2) at 3 by field.
  rewrite exp_plus.
  pose proof (exp_ineq1_le (s / 2)) as H.
  assert (H0 : 0 <= s / 2) by lra.
  nra.
Qed.

Lemma exp_neg_quad_le : forall t, -1/2 <= t -> t <= 1/5 ->
  exp (- t - t ^ 2) <= 1 - t.
Proof.
  intros t Hlo Hhi.
  pose proof (exp_pos (t + t ^ 2)) as Hpos.
  assert (Hkey : 1 <= exp (t + t ^ 2) * (1 - t)).
  { destruct (Rle_lt_dec t 0) as [Ht | Ht].
    - pose proof (exp_ineq1_le (t + t ^ 2)) as H.
      assert (Hpr : (1 + (t + t ^ 2)) * (1 - t) <= exp (t + t ^ 2) * (1 - t))
        by (apply Rmult_le_compat_r; lra).
      assert (Hc : 0 <= - t ^ 3) by nra.
      lra.
    - assert (Hs0 : 0 <= t + t ^ 2) by nra.
      pose proof (exp_quad_lower (t + t ^ 2) Hs0) as H.
      assert (H3 : 0 <= t ^ 3) by nra.
      assert (H4 : 0 <= t ^ 4) by nra.
      assert (Hlb : 1 + t + 5/4 * t ^ 2 <= exp (t + t ^ 2)) by lra.
      assert (Hpr : (1 + t + 5/4 * t ^ 2) * (1 - t) <= exp (t + t ^ 2) * (1 - t))
        by (apply Rmult_le_compat_r; lra).
      assert (Hcube : 5/4 * t ^ 3 <= 1/4 * t ^ 2) by nra.
      lra. }
  replace (- t - t ^ 2) with (- (t + t ^ 2)) by ring.
  rewrite exp_Ropp.
  apply (Rmult_le_reg_l (exp (t + t ^ 2))); [ exact Hpos | ].
  rewrite <- Rinv_r_sym by lra. lra.
Qed.

(* ----------------------------------------------------------------- *)
(*  B.  the modulus of 1 - w                                           *)
(* ----------------------------------------------------------------- *)
Lemma Cnorm2_one_minus : forall w,
  Cnorm2 (Cminus C1 w) = 1 - 2 * Re w + Cnorm2 w.
Proof. intro w. unfold Cnorm2, Cminus, Cadd, Copp, C1; simpl; ring. Qed.

Lemma Cmod_one_minus_sq : forall w,
  Cmod (Cminus C1 w) ^ 2 = 1 - 2 * Re w + Cmod w ^ 2.
Proof.
  intro w.
  assert (H1 : Cmod (Cminus C1 w) ^ 2 = Cnorm2 (Cminus C1 w))
    by (rewrite <- Cmod_sqr; unfold Rsqr; ring).
  assert (H2 : Cmod w ^ 2 = Cnorm2 w)
    by (rewrite <- Cmod_sqr; unfold Rsqr; ring).
  rewrite H1, H2. apply Cnorm2_one_minus.
Qed.

(* ----------------------------------------------------------------- *)
(*  C.  the factor, split into its two pieces                          *)
(* ----------------------------------------------------------------- *)
Lemma Efac_mod : forall z rho,
  Cmod (Efac z rho) = Cmod (Cminus C1 (Cmul z (Cinv rho)))
                      * exp (Re (Cmul z (Cinv rho))).
Proof. intros z rho. unfold Efac. rewrite Cmod_mul, Cmod_Cexpf. reflexivity. Qed.

Lemma Cmod_quot : forall z rho, rho <> C0 ->
  Cmod (Cmul z (Cinv rho)) = Cmod z / Cmod rho.
Proof.
  intros z rho Hr.
  assert (Hm : 0 < Cmod rho)
    by (destruct (Cmod_nonneg rho) as [H | H];
        [ exact H | exfalso; apply Hr; apply (proj1 (Cmod0 rho)); lra ]).
  assert (Hid : Cmod rho * Cmod (Cinv rho) = 1).
  { rewrite <- Cmod_mul.
    assert (Hone : Cmul rho (Cinv rho) = C1) by (field; exact Hr).
    rewrite Hone. apply Cmod_C1. }
  assert (Hinv : Cmod (Cinv rho) = / Cmod rho)
    by (apply (Rmult_eq_reg_l (Cmod rho)); [ rewrite Hid; field; lra | lra ]).
  rewrite Cmod_mul, Hinv. unfold Rdiv. ring.
Qed.

(* ----------------------------------------------------------------- *)
(*  D.  FAR: the quadratic bound                                       *)
(* ----------------------------------------------------------------- *)
Theorem Efac_lower_far : forall z rho, rho <> C0 ->
  10 * Cmod z <= Cmod rho ->
  exp (- (2 * Cmod z ^ 2 / Cmod rho ^ 2)) <= Cmod (Efac z rho).
Proof.
  intros z rho Hr Hfar.
  set (w := Cmul z (Cinv rho)).
  assert (Hmz : 0 <= Cmod z) by apply Cmod_nonneg.
  assert (Hm : 0 < Cmod rho)
    by (destruct (Cmod_nonneg rho) as [H | H];
        [ exact H | exfalso; apply Hr; apply (proj1 (Cmod0 rho)); lra ]).
  assert (Hmw : Cmod w = Cmod z / Cmod rho) by (unfold w; apply Cmod_quot; exact Hr).
  set (m := Cmod w). set (u := Re w).
  assert (Hm10 : m <= 1/10)
    by (unfold m; rewrite Hmw; apply (Rmult_le_reg_r (Cmod rho)); [ lra | ];
        unfold Rdiv; rewrite Rmult_assoc, Rinv_l by lra; lra).
  assert (Hm0 : 0 <= m) by (unfold m; apply Cmod_nonneg).
  assert (Hu : Rabs u <= m) by (unfold u, m; apply Cmod_Re_le).
  assert (Hua : - m <= u <= m)
    by (pose proof (Rabs_le u); pose proof (Rle_abs u);
        pose proof (Rabs_Ropp u); pose proof (Rle_abs (- u)); lra).
  (* the real inequality at t = 2u *)
  assert (Hstep : exp (- (2 * u) - (2 * u) ^ 2) <= 1 - 2 * u)
    by (apply exp_neg_quad_le; lra).
  assert (Hsq : (2 * u) ^ 2 <= 4 * m ^ 2) by nra.
  assert (Hmono : exp (- 4 * m ^ 2 - 2 * u) <= exp (- (2 * u) - (2 * u) ^ 2))
    by (apply exp_le; lra).
  (* hence the squared bound *)
  assert (Hsqb : exp (- 4 * m ^ 2 - 2 * u) <= Cmod (Cminus C1 w) ^ 2).
  { rewrite Cmod_one_minus_sq. fold u. fold m. nra. }
  (* take square roots *)
  assert (Hhalf : exp (- 2 * m ^ 2 - u) <= Cmod (Cminus C1 w)).
  { assert (Hsame : exp (- 2 * m ^ 2 - u) ^ 2 = exp (- 4 * m ^ 2 - 2 * u)).
    { replace (exp (- 2 * m ^ 2 - u) ^ 2)
        with (exp (- 2 * m ^ 2 - u) * exp (- 2 * m ^ 2 - u)) by ring.
      rewrite <- exp_plus. f_equal. ring. }
    pose proof (exp_pos (- 2 * m ^ 2 - u)) as He.
    pose proof (Cmod_nonneg (Cminus C1 w)) as Hc. nra. }
  (* and multiply back the exponential factor *)
  rewrite (Efac_mod z rho). fold w. fold u.
  assert (Hprod : exp (- 2 * m ^ 2) = exp (- 2 * m ^ 2 - u) * exp u)
    by (rewrite <- exp_plus; f_equal; ring).
  assert (Hgoal : - (2 * Cmod z ^ 2 / Cmod rho ^ 2) = - 2 * m ^ 2).
  { unfold m. rewrite Hmw. field. lra. }
  rewrite Hgoal, Hprod.
  apply Rmult_le_compat_r; [ left; apply exp_pos | exact Hhalf ].
Qed.

(* ----------------------------------------------------------------- *)
(*  E.  NEAR: the distance bound                                       *)
(* ----------------------------------------------------------------- *)
Theorem Efac_lower_near : forall z rho, rho <> C0 ->
  Cmod (Cminus rho z) / Cmod rho * exp (- (Cmod z / Cmod rho))
  <= Cmod (Efac z rho).
Proof.
  intros z rho Hr.
  set (w := Cmul z (Cinv rho)).
  assert (Hm : 0 < Cmod rho)
    by (destruct (Cmod_nonneg rho) as [H | H];
        [ exact H | exfalso; apply Hr; apply (proj1 (Cmod0 rho)); lra ]).
  assert (Hmw : Cmod w = Cmod z / Cmod rho) by (unfold w; apply Cmod_quot; exact Hr).
  (* |1 - w| = |rho - z| / |rho| *)
  assert (Hdist : Cmod (Cminus C1 w) = Cmod (Cminus rho z) / Cmod rho).
  { assert (Heq : Cminus C1 w = Cmul (Cminus rho z) (Cinv rho))
      by (unfold w; field; exact Hr).
    rewrite Heq. apply Cmod_quot; exact Hr. }
  assert (Hu : - (Cmod z / Cmod rho) <= Re w).
  { pose proof (Cmod_Re_le w) as H.
    pose proof (Rabs_Ropp (Re w)) as H1. pose proof (Rle_abs (- Re w)) as H2.
    rewrite Hmw in H. lra. }
  rewrite (Efac_mod z rho). fold w. rewrite Hdist.
  apply Rmult_le_compat_l.
  - apply Rle_mult_inv_pos; [ apply Cmod_nonneg | exact Hm ].
  - apply exp_le; exact Hu.
Qed.

Print Assumptions Efac_lower_far.
Print Assumptions Efac_lower_near.
