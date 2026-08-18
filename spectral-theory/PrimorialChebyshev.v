(* ================================================================= *)
(*  PrimorialChebyshev.v  —  the primorial as exp of Chebyshev's        *)
(*  function: attaching the Prime Number Theorem to the primorial^inf.  *)
(*                                                                    *)
(*  The log of a primorial is a Chebyshev prime-log sum:                *)
(*                                                                    *)
(*   (count-indexed, our tower)                                         *)
(*     log_nprimorial : ln (nprimorial Q k) = sum_{i<k} ln (Q i)        *)
(*       -- the log of OUR abstract primorial is the theta-type sum;    *)
(*          bounded below by k.ln2 (primorial >= 2^k), so -> +oo.       *)
(*   (magnitude-indexed, the repo's proven Chebyshev)                   *)
(*     Nprimorial N = prod_{p<=N} p   (the classic x# = product of      *)
(*       primes <= N), and                                              *)
(*     log_Nprimorial : ln (Nprimorial N) = theta N                     *)
(*       -- EXACTLY Chebyshev's theta.  Hence the PROVEN Chebyshev       *)
(*          bound psi<=Kup.N gives the unconditional ceiling            *)
(*          ln(Nprimorial N) <= Kup.N, i.e. x# <= e^{Kup.x}.            *)
(*                                                                    *)
(*  THE ATTACHMENT (honest):                                            *)
(*     pnt_iff_primorial_rate :                                         *)
(*       pnt_theta  <->  Un_cv (ln (Nprimorial N) / N) 1                *)
(*  i.e. sharp PNT (theta(x)/x -> 1) is EXACTLY the statement that the   *)
(*  primorial grows like e^x:  x# = e^{(1+o(1)) x}.                     *)
(*                                                                    *)
(*  HONESTY: `pnt_theta` (theta(x)/x -> 1) is NOT proved here.  It is    *)
(*  the repo's open sharp-PNT target, equivalent to the undischarged    *)
(*  research lemma `self_improve` (PNTUnconditional.v).  This file       *)
(*  proves only: the log-primorial = theta identity, the UNCONDITIONAL   *)
(*  Chebyshev ceiling, and the EQUIVALENCE "PNT <=> primorial ~ e^x".   *)
(*                                                                    *)
(*  Axiom-clean (only the 4 standard classical-Reals axioms).           *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia List.
Import ListNotations.
Require Import PrimorialRiemann ChebyshevPrime ChebyshevBound Chebyshev
        PrimePowerReindex.
Open Scope R_scope.

Lemma ln_mono_le : forall a b, 0 < a -> a <= b -> ln a <= ln b.
Proof.
  intros a b Ha Hab. destruct (Rle_lt_or_eq_dec a b Hab) as [Hlt | Heq].
  - apply Rlt_le, ln_increasing; assumption.
  - subst; apply Rle_refl.
Qed.

(* ----------------------------------------------------------------- *)
(*  (count-indexed) log of OUR abstract primorial = the theta-sum      *)
(* ----------------------------------------------------------------- *)

Section Abstract.
Variable Q : nat -> nat.
Hypothesis HQ : forall i, (2 <= Q i)%nat.

Fixpoint thetasum (k : nat) : R :=
  match k with 0 => 0 | S k' => thetasum k' + ln (INR (Q k')) end.

Lemma nprim_pos : forall k, (0 < nprimorial Q k)%nat.
Proof.
  intro k. apply Nat.lt_le_trans with (2 ^ k)%nat.
  - apply Nat.neq_0_lt_0, Nat.pow_nonzero; lia.
  - apply nprimorial_ge_pow2; exact HQ.
Qed.

Lemma log_nprimorial : forall k, ln (INR (nprimorial Q k)) = thetasum k.
Proof.
  induction k as [| k IH].
  - cbn [nprimorial thetasum]. change (INR 1) with 1. exact ln_1.
  - cbn [nprimorial thetasum]. rewrite mult_INR.
    assert (Hp1 : 0 < INR (nprimorial Q k)) by (apply lt_0_INR; apply nprim_pos).
    assert (Hp2 : 0 < INR (Q k)) by (apply lt_0_INR; pose proof (HQ k); lia).
    rewrite (ln_mult _ _ Hp1 Hp2), IH. reflexivity.
Qed.

(* primorial >= 2^k  in log form: the theta-sum is at least k.ln2 *)
Lemma thetasum_ge : forall k, INR k * ln 2 <= thetasum k.
Proof.
  induction k as [| k IH].
  - simpl; lra.
  - cbn [thetasum]. rewrite S_INR.
    assert (Hln : ln 2 <= ln (INR (Q k))).
    { apply ln_mono_le; [ lra | ].
      replace 2 with (INR 2) by (simpl; ring). apply le_INR; apply HQ. }
    replace ((INR k + 1) * ln 2) with (INR k * ln 2 + ln 2) by ring. lra.
Qed.

Lemma log_nprimorial_ge : forall k, INR k * ln 2 <= ln (INR (nprimorial Q k)).
Proof. intro k. rewrite log_nprimorial. apply thetasum_ge. Qed.

End Abstract.

(* ----------------------------------------------------------------- *)
(*  (magnitude-indexed) the classic primorial x# = prod_{p<=N} p       *)
(*  and log (x#) = Chebyshev's theta N  (EXACTLY)                       *)
(* ----------------------------------------------------------------- *)

Definition pfac (k : nat) : nat := if primeb k then k else 1.

Lemma pfac_pos : forall k, (1 <= pfac k)%nat.
Proof.
  intro k. unfold pfac. destruct (primeb k) eqn:E; [ | lia ].
  apply primeb_nprime in E. destruct E as [H2 _]. lia.
Qed.

Lemma fold_prod_pos : forall l, (0 < fold_right Nat.mul 1%nat (map pfac l))%nat.
Proof.
  induction l as [| a l IH]; cbn [map fold_right]; [ lia | ].
  pose proof (pfac_pos a). apply Nat.mul_pos_pos; [ lia | exact IH ].
Qed.

Lemma ln_INR_listprod : forall l,
  ln (INR (fold_right Nat.mul 1%nat (map pfac l)))
  = fold_right Rplus 0 (map tterm l).
Proof.
  induction l as [| a l IH]; cbn [map fold_right].
  - change (INR 1) with 1. exact ln_1.
  - rewrite mult_INR.
    assert (Hp1 : 0 < INR (pfac a)) by (apply lt_0_INR; pose proof (pfac_pos a); lia).
    assert (Hp2 : 0 < INR (fold_right Nat.mul 1%nat (map pfac l)))
      by (apply lt_0_INR; apply fold_prod_pos).
    rewrite (ln_mult _ _ Hp1 Hp2), IH. f_equal.
    unfold pfac, tterm. destruct (primeb a); [ reflexivity | ].
    change (INR 1) with 1. exact ln_1.
Qed.

Definition Nprimorial (N : nat) : nat :=
  fold_right Nat.mul 1%nat (map pfac (seq 1 N)).

(* THE identity: log of the primorial-of-primes-<=N is Chebyshev's theta *)
Theorem log_Nprimorial : forall N, ln (INR (Nprimorial N)) = theta N.
Proof.
  intro N. unfold Nprimorial, theta, ChebyshevBound.Rsum. apply ln_INR_listprod.
Qed.

(* UNCONDITIONAL Chebyshev ceiling: x# <= e^{Kup . x} *)
Theorem log_Nprimorial_upper : forall N, ln (INR (Nprimorial N)) <= INR N * Kup.
Proof.
  intro N. rewrite log_Nprimorial.
  apply Rle_trans with (psi N); [ apply theta_le_psi | apply psi_upper ].
Qed.

(* ----------------------------------------------------------------- *)
(*  THE ATTACHMENT: sharp PNT <=> the primorial grows like e^x         *)
(* ----------------------------------------------------------------- *)

(* sharp PNT, theta form.  NOT proved here: this is the repo's open     *)
(* target, equivalent to the undischarged self_improve (PNTUnconditional). *)
Definition pnt_theta : Prop := Un_cv (fun N => theta N / INR N) 1.

Theorem pnt_iff_primorial_rate :
  pnt_theta <-> Un_cv (fun N => ln (INR (Nprimorial N)) / INR N) 1.
Proof.
  unfold pnt_theta. split; intro H.
  - apply (Un_cv_ext (fun N => theta N / INR N));
      [ intro N; rewrite log_Nprimorial; reflexivity | exact H ].
  - apply (Un_cv_ext (fun N => ln (INR (Nprimorial N)) / INR N));
      [ intro N; rewrite log_Nprimorial; reflexivity | exact H ].
Qed.

(* ===== the whole attachment, bundled ===== *)
Theorem primorial_exp_chebyshev :
  (* log of the primorial x# is EXACTLY Chebyshev's theta *)
  (forall N, ln (INR (Nprimorial N)) = theta N)
  (* unconditional Chebyshev ceiling: x# <= e^{Kup . x} *)
  /\ (forall N, ln (INR (Nprimorial N)) <= INR N * Kup)
  (* sharp PNT (theta(x)/x -> 1)  <=>  x# = e^{(1+o(1)) x} *)
  /\ (pnt_theta <-> Un_cv (fun N => ln (INR (Nprimorial N)) / INR N) 1).
Proof.
  split; [ exact log_Nprimorial | ].
  split; [ exact log_Nprimorial_upper | exact pnt_iff_primorial_rate ].
Qed.

Print Assumptions log_Nprimorial.
Print Assumptions primorial_exp_chebyshev.
