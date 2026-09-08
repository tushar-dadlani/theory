(* ================================================================= *)
(*  CTwist341.v  --  the twisted 3-4-1 inequality at a single prime.   *)
(*                                                                    *)
(*  For a character chi = dchar p g A and the three shifted arguments  *)
(*                                                                    *)
(*    z0 = chi_0(q)   q^{-(a    )},                                    *)
(*    z1 = chi_A(q)   q^{-(a+ib)},                                     *)
(*    z2 = chi_{2A}(q) q^{-(a+2ib)},                                   *)
(*                                                                    *)
(*  we prove   1 <= |1-z0|^{-3} |1-z1|^{-4} |1-z2|^{-1}.               *)
(*                                                                    *)
(*  NO ARGUMENT FUNCTION IS USED.  The three moduli coincide (call it  *)
(*  r), and the algebraic identity                                     *)
(*                                                                    *)
(*        z1 * z1  =  z2 * r                                           *)
(*                                                                    *)
(*  (from chi_A^2 = chi_{2A} and q^{-(a+ib)}^2 = q^{-(a+2ib)} q^{-a})   *)
(*  lets us set c := Re z1 / r and READ OFF                            *)
(*                                                                    *)
(*        Re z0 = r,   Re z1 = r c,   Re z2 = r (2c^2 - 1),            *)
(*                                                                    *)
(*  which is exactly the (r, c) shape of                               *)
(*  CTwistPerPrime.per_prime_log_c.  c comes out of the algebra, not   *)
(*  out of an arg function -- which is what makes this work in a repo  *)
(*  that has no Carg.                                                  *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia ZArith Znumtheory.
Require Import ComplexField Cmodulus CexpFull CPowMul RootsOfUnity
        ZmodOrder DirichletModP CharModulus CTwistedCoeff
        LogGeomSeries EulerFactorLog CTwistPerPrime ThreeFourOne
        ZetaEMExtHolo.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  0.  elementary complex identities                                  *)
(* ----------------------------------------------------------------- *)

Lemma Cmod_sqr : forall z, (Cmod z) ^ 2 = Cnorm2 z.
Proof.
  intro z. unfold Cmod.
  assert (H : 0 <= Cnorm2 z)
    by (unfold Cnorm2; nra).
  rewrite <- Rsqr_pow2, Rsqr_sqrt by exact H. reflexivity.
Qed.

Lemma Cnorm2_one_minus : forall z,
  Cnorm2 (Cminus C1 z) = 1 - 2 * Re z + Cnorm2 z.
Proof.
  intro z. unfold Cnorm2, Cminus, Copp, C1; cbn [Re Im]; ring.
Qed.

Lemma Re_sq : forall z, Re (Cmul z z) = 2 * (Re z) ^ 2 - Cnorm2 z.
Proof.
  intro z. unfold Cnorm2, Cmul; cbn [Re Im]; ring.
Qed.

Lemma Re_le_Cmod : forall z, Rabs (Re z) <= Cmod z.
Proof.
  intro z. rewrite <- (Rabs_pos_eq (Cmod z)) by apply Cmod_nonneg.
  apply Rsqr_le_abs_0. rewrite !Rsqr_pow2, Cmod_sqr.
  unfold Cnorm2. nra.
Qed.

(* ================================================================= *)
Section Twist341.

Variable p g A : nat.
Hypothesis Hp : prime (Z.of_nat p).
Hypothesis Hg : (1 <= g <= p - 1)%nat.
Hypothesis Hord : ord p g = (p - 1)%nat.

Variable a b : R.
Hypothesis Ha : 1 < a.

Definition tz0 (q : Z) : C := Fchi p g 0           (mkC a 0)         q.
Definition tz1 (q : Z) : C := Fchi p g A           (mkC a b)         q.
Definition tz2 (q : Z) : C := Fchi p g (2 * A)     (mkC a (2 * b))   q.

(* the modulus of a character value is 0 or 1, independently of the index *)
Lemma Cmod_dchar_val : forall c n,
  Cmod (dchar p g c n) = (if (n mod p =? 0)%nat then 0 else 1).
Proof.
  intros c n. unfold dchar. destruct (n mod p =? 0)%nat.
  - apply (proj2 (Cmod0 C0) eq_refl).
  - rewrite Cmod_Cpow_loc, Cmod_w, pow1. reflexivity.
Qed.

Definition tr (q : Z) : R := Cmod (tz0 q).

Lemma Re_Copp_mkC : forall x y, Re (Copp (mkC x y)) = - x.
Proof. intros; unfold Copp; cbn; ring. Qed.

(* all three moduli agree *)
Lemma tmod_all : forall q,
  Cmod (tz1 q) = tr q /\ Cmod (tz2 q) = tr q.
Proof.
  intro q. unfold tr, tz0, tz1, tz2, Fchi.
  rewrite !Cmod_mul, !Cpw_mod, !Cmod_dchar_val, !Re_Copp_mkC.
  split; reflexivity.
Qed.

Lemma tr_nonneg : forall q, 0 <= tr q.
Proof. intro q. apply Cmod_nonneg. Qed.

(* z0 is a nonnegative real, equal to r *)
Lemma tz0_real : forall q, tz0 q = RtoC (tr q).
Proof.
  intro q. unfold tr, tz0, Fchi.
  assert (Hc : Copp (mkC a 0) = RtoC (- a))
    by (unfold RtoC; apply Ceq; cbn; ring).
  rewrite Hc, Cpw_RtoC. unfold dchar.
  destruct (Z.to_nat q mod p =? 0)%nat.
  - replace (Cmul C0 (RtoC (Rpower (IZR q) (- a)))) with C0 by ring.
    rewrite (proj2 (Cmod0 C0) eq_refl).
    unfold RtoC; apply Ceq; cbn; ring.
  - rewrite Nat.mul_0_l. cbn [Cpow].
    rewrite Cmod_mul, Cmod_C1_loc, Cmod_RtoC.
    rewrite (Rabs_pos_eq (Rpower (IZR q) (- a)))
      by (left; unfold Rpower; apply exp_pos).
    unfold RtoC; apply Ceq; cbn; ring.
Qed.

Lemma Re_tz0 : forall q, Re (tz0 q) = tr q.
Proof. intro q. rewrite tz0_real. unfold RtoC; cbn; reflexivity. Qed.

(* THE ALGEBRAIC IDENTITY: z1^2 = z2 * r *)
Lemma tz_sq : forall q,
  Cmul (tz1 q) (tz1 q) = Cmul (tz2 q) (RtoC (tr q)).
Proof.
  intro q.
  assert (Hc : Copp (mkC a 0) = RtoC (- a))
    by (unfold RtoC; apply Ceq; cbn; ring).
  (* r, split into its character part and its power part *)
  assert (Hr : RtoC (tr q)
               = Cmul (RtoC (Cmod (dchar p g 0 (Z.to_nat q))))
                      (Cpw (IZR q) (RtoC (- a)))).
  { unfold tr, tz0, Fchi. rewrite Hc, Cmod_mul, Cpw_RtoC, Cmod_RtoC.
    rewrite (Rabs_pos_eq (Rpower (IZR q) (- a)))
      by (left; unfold Rpower; apply exp_pos).
    unfold RtoC; apply Ceq; cbn; ring. }
  unfold tz1, tz2, Fchi. rewrite Hr.
  (* regroup both sides: characters together, powers together *)
  replace (Cmul (Cmul (dchar p g A (Z.to_nat q)) (Cpw (IZR q) (Copp (mkC a b))))
                (Cmul (dchar p g A (Z.to_nat q)) (Cpw (IZR q) (Copp (mkC a b)))))
    with (Cmul (Cmul (dchar p g A (Z.to_nat q)) (dchar p g A (Z.to_nat q)))
               (Cmul (Cpw (IZR q) (Copp (mkC a b)))
                     (Cpw (IZR q) (Copp (mkC a b))))) by ring.
  replace (Cmul (Cmul (dchar p g (2 * A) (Z.to_nat q))
                      (Cpw (IZR q) (Copp (mkC a (2 * b)))))
                (Cmul (RtoC (Cmod (dchar p g 0 (Z.to_nat q))))
                      (Cpw (IZR q) (RtoC (- a)))))
    with (Cmul (Cmul (dchar p g (2 * A) (Z.to_nat q))
                     (RtoC (Cmod (dchar p g 0 (Z.to_nat q)))))
               (Cmul (Cpw (IZR q) (Copp (mkC a (2 * b))))
                     (Cpw (IZR q) (RtoC (- a))))) by ring.
  rewrite (dchar_sq p g A (Z.to_nat q)), <- !Cpw_split.
  assert (Hexp : Cadd (Copp (mkC a b)) (Copp (mkC a b))
                 = Cadd (Copp (mkC a (2 * b))) (RtoC (- a)))
    by (unfold RtoC; apply Ceq; cbn; ring).
  rewrite Hexp. f_equal.
  (* the character factor absorbs |chi_0(q)| *)
  unfold dchar. destruct (Z.to_nat q mod p =? 0)%nat.
  - rewrite (proj2 (Cmod0 C0) eq_refl). unfold RtoC; apply Ceq; cbn; ring.
  - rewrite Nat.mul_0_l. cbn [Cpow]. rewrite Cmod_C1_loc.
    unfold RtoC, C1; apply Ceq; cbn; ring.
Qed.

(* ----------------------------------------------------------------- *)
(*  the per-prime 3-4-1 inequality                                     *)
(* ----------------------------------------------------------------- *)

Definition tQ (z : C) : R := / Cmod (Cminus C1 z).

Lemma tr_le_pow : forall q, tr q <= Rpower (IZR q) (- a).
Proof.
  intro q. unfold tr, tz0, Fchi.
  rewrite Cmod_mul, Cpw_mod, Cmod_dchar_val, Re_Copp_mkC.
  assert (Hp0 : 0 < Rpower (IZR q) (- a)) by (unfold Rpower; apply exp_pos).
  destruct (Z.to_nat q mod p =? 0)%nat; lra.
Qed.

Lemma tr_lt1 : forall q, 2 <= IZR q -> tr q < 1.
Proof.
  intros q Hq. eapply Rle_lt_trans; [ apply tr_le_pow | ].
  apply Rlt_le_trans with (Rpower (IZR q) 0).
  - apply Rpower_lt; lra.
  - rewrite Rpower_O by lra; apply Rle_refl.
Qed.

Lemma tnorm2 : forall q,
  Cnorm2 (tz0 q) = (tr q) ^ 2 /\ Cnorm2 (tz1 q) = (tr q) ^ 2
  /\ Cnorm2 (tz2 q) = (tr q) ^ 2.
Proof.
  intro q. destruct (tmod_all q) as [H1 H2].
  rewrite <- !Cmod_sqr, H1, H2. unfold tr. repeat split; reflexivity.
Qed.

Lemma ln_sqrt_loc : forall x, 0 < x -> ln (sqrt x) = / 2 * ln x.
Proof.
  intros x Hx.
  assert (H : sqrt x * sqrt x = x) by (apply sqrt_sqrt; lra).
  assert (Hs : 0 < sqrt x) by (apply sqrt_lt_R0; exact Hx).
  assert (E : ln x = ln (sqrt x) + ln (sqrt x))
    by (rewrite <- ln_mult by lra; rewrite H; reflexivity).
  lra.
Qed.

Lemma tQ_ln : forall z, 0 < Cnorm2 (Cminus C1 z) ->
  ln (tQ z) = - (/ 2) * ln (Cnorm2 (Cminus C1 z)).
Proof.
  intros z Hz. unfold tQ, Cmod.
  rewrite ln_Rinv by (apply sqrt_lt_R0; exact Hz).
  rewrite ln_sqrt_loc by exact Hz. ring.
Qed.

Lemma tQ_pos : forall z, 0 < Cnorm2 (Cminus C1 z) -> 0 < tQ z.
Proof.
  intros z Hz. unfold tQ, Cmod.
  apply Rinv_0_lt_compat, sqrt_lt_R0; exact Hz.
Qed.

Theorem tper_prime : forall q, 2 <= IZR q ->
  1 <= (tQ (tz0 q)) ^ 3 * (tQ (tz1 q)) ^ 4 * (tQ (tz2 q)).
Proof.
  intros q Hq.
  set (r := tr q).
  assert (Hr0 : 0 <= r) by apply tr_nonneg.
  assert (Hr1 : r < 1) by (apply tr_lt1; exact Hq).
  destruct (tnorm2 q) as [N0 [N1 N2]]. fold r in N0, N1, N2.
  destruct (tmod_all q) as [M1 M2]. fold r in M1, M2.
  (* the three squared denominators, in (r,c) form *)
  destruct (Rle_lt_or_eq_dec 0 r Hr0) as [Hrpos | Hr0eq].
  - set (c := Re (tz1 q) / r).
    assert (Hc1 : Re (tz1 q) = r * c) by (unfold c; field; lra).
    assert (Hcb : -1 <= c <= 1).
    { pose proof (Re_le_Cmod (tz1 q)) as HL. rewrite M1 in HL.
      unfold c. pose proof (Rabs_le_both (Re (tz1 q)) r HL) as [Ha1 Ha2].
      split; apply (Rmult_le_reg_r r); try lra;
        replace (Re (tz1 q) / r * r) with (Re (tz1 q)) by (field; lra); lra. }
    assert (Hc2 : Re (tz2 q) = r * (2 * c * c - 1)).
    { pose proof (tz_sq q) as HS.
      apply (f_equal Re) in HS.
      rewrite (Re_sq (tz1 q)) in HS.
      assert (HR : Re (Cmul (tz2 q) (RtoC (tr q))) = Re (tz2 q) * r)
        by (unfold r; unfold RtoC, Cmul; cbn [Re Im]; ring).
      rewrite HR, N1, Hc1 in HS.
      apply (Rmult_eq_reg_r r); [ | lra ]. nra. }
    (* denominators *)
    assert (Hre0 : Re (tz0 q) = r) by (unfold r; apply Re_tz0).
    assert (D0 : Cnorm2 (Cminus C1 (tz0 q)) = 1 - 2 * r * 1 + r ^ 2)
      by (rewrite Cnorm2_one_minus, Hre0, N0; ring).
    assert (D1 : Cnorm2 (Cminus C1 (tz1 q)) = 1 - 2 * r * c + r ^ 2)
      by (rewrite Cnorm2_one_minus, Hc1, N1; ring).
    assert (D2 : Cnorm2 (Cminus C1 (tz2 q))
                 = 1 - 2 * r * (2 * c * c - 1) + r ^ 2)
      by (rewrite Cnorm2_one_minus, Hc2, N2; ring).
    assert (Hpos : forall x, -1 <= x <= 1 -> 0 < 1 - 2 * r * x + r ^ 2).
    { intros x Hx. assert (H0 : 0 < 1 - r) by lra.
      assert (Hsq : 0 < (1 - r) * (1 - r)) by nra.
      assert (Hgap : 0 <= 2 * r * (1 - x)) by nra. nra. }
    assert (P0 : 0 < Cnorm2 (Cminus C1 (tz0 q)))
      by (rewrite D0; apply Hpos; lra).
    assert (P1 : 0 < Cnorm2 (Cminus C1 (tz1 q)))
      by (rewrite D1; apply Hpos; exact Hcb).
    assert (Hcc : -1 <= 2 * c * c - 1 <= 1) by nra.
    assert (P2 : 0 < Cnorm2 (Cminus C1 (tz2 q)))
      by (rewrite D2; apply Hpos; exact Hcc).
    (* logs *)
    set (X := tQ (tz0 q)); set (Y := tQ (tz1 q)); set (Z := tQ (tz2 q)).
    assert (HX : 0 < X) by (unfold X; apply tQ_pos; exact P0).
    assert (HY : 0 < Y) by (unfold Y; apply tQ_pos; exact P1).
    assert (HZ : 0 < Z) by (unfold Z; apply tQ_pos; exact P2).
    assert (HX3 : 0 < X ^ 3) by (apply pow_lt; exact HX).
    assert (HY4 : 0 < Y ^ 4) by (apply pow_lt; exact HY).
    assert (HXY : 0 < X ^ 3 * Y ^ 4) by (apply Rmult_lt_0_compat; assumption).
    assert (Hy : 0 < X ^ 3 * Y ^ 4 * Z)
      by (apply Rmult_lt_0_compat; assumption).
    assert (Hsum : 3 * ln X + 4 * ln Y + ln Z
                   = 3 * Lc 1 r + 4 * Lc c r + Lc (2 * c * c - 1) r).
    { unfold X, Y, Z. rewrite !tQ_ln by assumption.
      rewrite D0, D1, D2. unfold Lc. ring. }
    assert (Hnn : 0 <= 3 * ln X + 4 * ln Y + ln Z).
    { rewrite Hsum. apply per_prime_log_c; [ lra | exact Hcb ]. }
    assert (Hln : ln (X ^ 3 * Y ^ 4 * Z) = 3 * ln X + 4 * ln Y + ln Z).
    { rewrite (ln_mult (X ^ 3 * Y ^ 4) Z HXY HZ).
      rewrite (ln_mult (X ^ 3) (Y ^ 4) HX3 HY4).
      rewrite (ln_powS X 3 HX), (ln_powS Y 4 HY).
      simpl (INR 3); simpl (INR 4); ring. }
    rewrite <- exp_0. apply Rle_trans with (exp (ln (X ^ 3 * Y ^ 4 * Z))).
    + apply exp_le'. rewrite Hln; exact Hnn.
    + rewrite exp_ln by exact Hy; apply Rle_refl.
  - (* r = 0: all three coefficients vanish and every factor is 1 *)
    assert (Hz : forall z, Cmod z = 0 -> z = C0)
      by (intros z Hzz; apply (proj1 (Cmod0 z)); exact Hzz).
    assert (E0 : tz0 q = C0) by (apply Hz; unfold r, tr in Hr0eq; lra).
    assert (E1 : tz1 q = C0) by (apply Hz; rewrite M1; lra).
    assert (E2 : tz2 q = C0) by (apply Hz; rewrite M2; lra).
    rewrite E0, E1, E2. unfold tQ.
    replace (Cminus C1 C0) with C1 by ring.
    rewrite Cmod_C1_loc, Rinv_1. lra.
Qed.

End Twist341.

Print Assumptions Cmod_sqr.
Print Assumptions tper_prime.

(* ================================================================= *)
(*  END CTwist341.v  (part 1: the algebra)                            *)
(* ================================================================= *)
