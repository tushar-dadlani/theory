(* ================================================================= *)
(*  IntervalArithFun.v  --  computable enclosures of exp.              *)
(*                                                                    *)
(*    Iround  : outward dyadic rounding, to keep denominators bounded  *)
(*    Iexp_pt : an enclosure of exp q for rational q                   *)
(*                                                                    *)
(*  Stage 4a of the verified-quadrature route to the first zeta zero.  *)
(*  IntervalArith supplies +, -, * on rational intervals; the          *)
(*  integrand Psi(u) u^{-3/4} cos((t/2) ln u) needs transcendentals,   *)
(*  and Psi (ThetaTailSharp.Psi_sharp) is built from e^{-pi n^2 u}.    *)
(*                                                                    *)
(*  NO SERIES IS USED, deliberately.  Two routes were priced first:    *)
(*                                                                    *)
(*   * ExpEnclosure.exp_enclose_real gives (1+x/n)^n <= exp x <=       *)
(*     (1/(1-x/n))^n, but its relative error is ~x^2/(2n); at x = -16  *)
(*     reaching 1e-6 needs n ~ 1e8.  Unusable.                         *)
(*   * The Taylor series needs the tail of Coq's exp_in / exist_exp    *)
(*     unpicked, plus factorial rationals -- workable but long.        *)
(*                                                                    *)
(*  Instead: ARGUMENT REDUCTION.  exp x = (exp (x/2^m))^(2^m), and on  *)
(*  the tiny reduced argument z the elementary two-sided bound         *)
(*  1 + z <= exp z <= 1/(1-z) (exp_ineq1_le and ExpEnclosure           *)
(*  .exp_le_inv1) already has relative width ~z^2.  Squaring m times   *)
(*  multiplies the RELATIVE width by 2^m, so at m = 40 and x = -16 the *)
(*  final relative width is about 2^40 . (16/2^40)^2 = 2e-10.          *)
(*                                                                    *)
(*  Squaring doubles the digit count each time, so 40 squarings from a *)
(*  15-digit rational would end at 15.2^40 digits.  Iround is what     *)
(*  makes the scheme viable: rounding OUTWARD to a dyadic grid after   *)
(*  every squaring keeps the endpoints bounded while only ever         *)
(*  widening the enclosure, so soundness is preserved by construction. *)
(*  Axiom-clean.                                                      *)
(* ================================================================= *)

From Stdlib Require Import QArith Qreals Qround Reals Lra Lia.
Require Import IntervalArith ExpEnclosure.
Local Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  A.  Q/R plumbing                                                   *)
(* ----------------------------------------------------------------- *)
Lemma Q2R_inject : forall z : Z, Q2R (inject_Z z) = IZR z.
Proof. intro z. unfold Q2R, inject_Z; simpl. field. Qed.

Lemma pow2_pos : forall m, (0 < 2 ^ m)%nat.
Proof. induction m; simpl; lia. Qed.

(*  NOTE: the exponent is taken in Z, not nat.  Writing this as        *)
(*  inject_Z (Z.of_nat (2 ^ m)) is semantically identical but computes  *)
(*  2 ^ m in UNARY nat -- at m = 60 that is 10^18 successors and        *)
(*  vm_compute never returns.  Z.pow is binary.                         *)
Definition Qp2 (m : nat) : Q := inject_Z (2 ^ Z.of_nat m).

Lemma Qp2_nat : forall m, (2 ^ Z.of_nat m)%Z = Z.of_nat (2 ^ m).
Proof.
  induction m as [| m IH]; [ reflexivity | ].
  replace (2 ^ S m)%nat with (2 * 2 ^ m)%nat by (simpl; lia).
  replace (Z.of_nat (S m)) with (Z.of_nat m + 1)%Z by lia.
  rewrite Z.pow_add_r by lia. rewrite IH. lia.
Qed.

Lemma Qp2_pos : forall m, 0 < Q2R (Qp2 m).
Proof.
  intro m. unfold Qp2. rewrite Qp2_nat, Q2R_inject, <- INR_IZR_INZ.
  apply lt_0_INR. apply pow2_pos.
Qed.

Lemma Qp2_neq0 : forall m, ~ (Qp2 m == 0).
Proof.
  intro m. assert (H : (0 < 2 ^ m)%nat) by apply pow2_pos.
  unfold Qp2. rewrite Qp2_nat. unfold Qeq; simpl. lia.
Qed.

Lemma Q2R_Qp2 : forall m, Q2R (Qp2 m) = INR (2 ^ m).
Proof. intro m. unfold Qp2. rewrite Qp2_nat, Q2R_inject, <- INR_IZR_INZ. reflexivity. Qed.

(* ----------------------------------------------------------------- *)
(*  B.  outward dyadic rounding                                        *)
(* ----------------------------------------------------------------- *)
Definition Qfl (p : nat) (q : Q) : Q := inject_Z (Qfloor (q * Qp2 p)) / Qp2 p.
Definition Qce (p : nat) (q : Q) : Q := inject_Z (Qceiling (q * Qp2 p)) / Qp2 p.

(*  Qred is essential, not cosmetic: Qdiv leaves the result
    unnormalised, so without it the denominators grow through every
    Imul despite the rounding, and the whole point of Iround is lost. *)
Definition Iround (p : nat) (i : Itv) : Itv :=
  mkI (Qred (Qfl p (ilo i))) (Qred (Qce p (ihi i))).

Lemma Q2R_Qred : forall q, Q2R (Qred q) = Q2R q.
Proof. intro q. apply Qeq_eqR. apply Qred_correct. Qed.

Lemma Qfl_le : forall p q, Q2R (Qfl p q) <= Q2R q.
Proof.
  intros p q. pose proof (Qp2_pos p) as HP.
  assert (HPne : ~ Q2R (Qp2 p) = 0) by lra.
  unfold Qfl. rewrite Q2R_div by apply Qp2_neq0.
  rewrite Q2R_inject.
  apply (Rmult_le_reg_r (Q2R (Qp2 p))); [ exact HP | ].
  unfold Rdiv. rewrite Rmult_assoc. rewrite Rinv_l by lra. rewrite Rmult_1_r.
  pose proof (Qfloor_le (q * Qp2 p)) as H.
  apply Qle_Rle in H. rewrite Q2R_mult, Q2R_inject in H. lra.
Qed.

Lemma Qce_ge : forall p q, Q2R q <= Q2R (Qce p q).
Proof.
  intros p q. pose proof (Qp2_pos p) as HP.
  assert (HPne : ~ Q2R (Qp2 p) = 0) by lra.
  unfold Qce. rewrite Q2R_div by apply Qp2_neq0.
  rewrite Q2R_inject.
  apply (Rmult_le_reg_r (Q2R (Qp2 p))); [ exact HP | ].
  unfold Rdiv. rewrite Rmult_assoc. rewrite Rinv_l by lra. rewrite Rmult_1_r.
  pose proof (Qle_ceiling (q * Qp2 p)) as H.
  apply Qle_Rle in H. rewrite Q2R_mult, Q2R_inject in H. lra.
Qed.

Theorem Iround_sound : forall p i x, Icontains i x -> Icontains (Iround p i) x.
Proof.
  intros p i x [H1 H2]. unfold Icontains, Iround; cbn [ilo ihi].
  rewrite !Q2R_Qred.
  pose proof (Qfl_le p (ilo i)). pose proof (Qce_ge p (ihi i)). lra.
Qed.

(* ----------------------------------------------------------------- *)
(*  C.  the base enclosure on a REDUCED argument                       *)
(* ----------------------------------------------------------------- *)
(*  1 + z <= exp z <= 1/(1-z)  for -1 <= z < 1.  Relative width ~z^2,  *)
(*  which is why the argument is reduced by 2^m first.                 *)
Definition Iexp_base (z : Q) : Itv := mkI (1 + z) (/ (1 - z)).

Lemma Q2R_one : Q2R 1 = 1.
Proof. unfold Q2R; simpl; field. Qed.

Lemma Iexp_base_sound : forall z : Q, -1 <= Q2R z -> Q2R z < 1 ->
  Icontains (Iexp_base z) (exp (Q2R z)).
Proof.
  intros z Hlo Hhi. unfold Icontains, Iexp_base; simpl. split.
  - rewrite Q2R_plus, Q2R_one. apply exp_ineq1_le.
  - assert (Hne : ~ (1 - z == 0)).
    { intro Hc. apply Qeq_eqR in Hc. rewrite Q2R_minus, Q2R_one in Hc.
      assert (HZ : Q2R 0 = 0) by (unfold Q2R; simpl; field).
      rewrite HZ in Hc. lra. }
    rewrite Q2R_inv by exact Hne. rewrite Q2R_minus, Q2R_one.
    apply exp_le_inv1; exact Hhi.
Qed.

(* ----------------------------------------------------------------- *)
(*  D.  repeated squaring, with outward rounding between steps         *)
(* ----------------------------------------------------------------- *)
Fixpoint Isq_iter (p m : nat) (i : Itv) : Itv :=
  match m with
  | O => i
  | S m' => Isq_iter p m' (Iround p (Imul i i))
  end.

Lemma Isq_iter_sound : forall p m i x,
  Icontains i x -> Icontains (Isq_iter p m i) (x ^ (2 ^ m)).
Proof.
  intros p m. induction m as [| m IH]; intros i x H.
  - simpl. replace (x * 1) with x by ring. exact H.
  - simpl Isq_iter.
    assert (H2 : Icontains (Iround p (Imul i i)) (x * x))
      by (apply Iround_sound, Imul_sound; exact H).
    pose proof (IH _ _ H2) as H3.
    replace (2 ^ S m)%nat with (2 * 2 ^ m)%nat by (simpl; lia).
    rewrite pow_mult.
    replace (x ^ 2) with (x * x) by ring.
    exact H3.
Qed.

(* ----------------------------------------------------------------- *)
(*  E.  THE ENCLOSURE OF exp AT A RATIONAL POINT                       *)
(* ----------------------------------------------------------------- *)
Definition Iexp_pt (p m : nat) (q : Q) : Itv := Isq_iter p m (Iexp_base (q / Qp2 m)).

Theorem Iexp_pt_sound : forall p m q,
  -1 <= Q2R q / INR (2 ^ m) -> Q2R q / INR (2 ^ m) < 1 ->
  Icontains (Iexp_pt p m q) (exp (Q2R q)).
Proof.
  intros p m q Hlo Hhi.
  assert (HN : 0 < INR (2 ^ m)) by (apply lt_0_INR; apply pow2_pos).
  assert (Hz : Q2R (q / Qp2 m) = Q2R q / INR (2 ^ m))
    by (rewrite Q2R_div by apply Qp2_neq0; rewrite Q2R_Qp2; reflexivity).
  assert (Hbase : Icontains (Iexp_base (q / Qp2 m)) (exp (Q2R q / INR (2 ^ m))))
    by (rewrite <- Hz; apply Iexp_base_sound; rewrite Hz; assumption).
  pose proof (Isq_iter_sound p m _ _ Hbase) as H.
  unfold Iexp_pt.
  replace (exp (Q2R q)) with ((exp (Q2R q / INR (2 ^ m))) ^ (2 ^ m)).
  - exact H.
  - rewrite <- exp_INR_pow. f_equal. field. lra.
Qed.

Print Assumptions Iround_sound.
Print Assumptions Iexp_base_sound.
Print Assumptions Isq_iter_sound.
Print Assumptions Iexp_pt_sound.
