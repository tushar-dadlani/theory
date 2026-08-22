(* ================================================================= *)
(*  IntervalCos.v  --  computable enclosures of cos, by double angle.  *)
(*                                                                    *)
(*  Stage 4a, second brick.  The integrand of Re TC carries            *)
(*  cos((t/2) ln u); with t <= 16 and u in [1,5] the argument reaches  *)
(*  |z| = 12.88.                                                      *)
(*                                                                    *)
(*  DIRECT TAYLOR AT z IS NOT AN OPTION, and the reason is not the     *)
(*  term count.  Stdlib's cos_bound is stated under -PI/2 <= a <= PI/2 *)
(*  and 12.88 is five times out of range, so the direct route would    *)
(*  need a hand-proved remainder bound.  It is also numerically ugly:  *)
(*  28 terms, highest power z^54, and a largest intermediate term of   *)
(*  4.4e4 against an answer of size 1 -- four orders of cancellation.  *)
(*                                                                    *)
(*  So: ARGUMENT REDUCTION again, now by the double angle              *)
(*  cos 2w = 2 cos^2 w - 1.  At m = 8 the reduced argument is          *)
(*  |w| <= 0.0503, comfortably inside cos_bound's range, so cos_bound  *)
(*  applies verbatim and NO remainder lemma is needed.  Each doubling  *)
(*  has derivative 4 cos w, so errors amplify by at most 4^m = 6.6e4;  *)
(*  with the base enclosure good to 5.5e-25 (n = 2, seven terms) the   *)
(*  final width is ~4e-20.  There is no divergence anywhere, including *)
(*  at z = 0 (that is u = 1, the left end of the integration range).   *)
(*                                                                    *)
(*  Factorials are taken in Z, not nat: fact 12 = 479001600 as a UNARY *)
(*  nat is half a billion constructors and cannot be evaluated.        *)
(*  Zfact is binary, and INR_fact_Zfact carries the bridge once and    *)
(*  for all rather than case by case.  Axiom-clean.                    *)
(* ================================================================= *)

From Stdlib Require Import QArith Qreals Reals Lra Lia.
Require Import IntervalArith IntervalArithFun CertifiedPi.
Local Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  A.  factorials in Z, and powers in Q                               *)
(* ----------------------------------------------------------------- *)
Fixpoint Zfact (n : nat) : Z :=
  match n with O => 1%Z | S k => (Z.of_nat (S k) * Zfact k)%Z end.

Lemma INR_fact_Zfact : forall n, INR (Factorial.fact n) = IZR (Zfact n).
Proof.
  induction n as [| n IH].
  - simpl. lra.
  - change (Factorial.fact (S n)) with (S n * Factorial.fact n)%nat.
    change (Zfact (S n)) with (Z.of_nat (S n) * Zfact n)%Z.
    rewrite mult_INR, IH, mult_IZR, INR_IZR_INZ. reflexivity.
Qed.

(* Qred at every accumulation: without it the denominators of the       *)
(* Taylor partial sums MULTIPLY term by term (each Qplus on Q is        *)
(* cross-multiplication, never reduced), and a 10-term series at a      *)
(* dyadic argument of denominator 2^20 ends up carrying a ~2^700        *)
(* denominator.  Measured: 0.50 s -> 0.145 s per cos node.  Q2R is      *)
(* invariant under Qred, so soundness is unaffected.                    *)
Fixpoint Qpow (a : Q) (n : nat) : Q :=
  match n with O => 1 | S k => Qred (a * Qpow a k) end.

Lemma Q2R_Qpow : forall a n, Q2R (Qpow a n) = (Q2R a) ^ n.
Proof.
  intros a n. induction n as [| n IH].
  - simpl. apply Q2R_one.
  - cbn [Qpow pow]. rewrite Q2R_Qred, Q2R_mult, IH. reflexivity.
Qed.

(* ----------------------------------------------------------------- *)
(*  B.  the Taylor terms of cos, over Q                                *)
(* ----------------------------------------------------------------- *)
Definition Qsgn (i : nat) : Q := if Nat.even i then 1 else -(1).

Lemma Q2R_Qsgn : forall i, Q2R (Qsgn i) = (-1) ^ i.
Proof.
  intro i. unfold Qsgn. destruct (Nat.even i) eqn:E.
  - rewrite Q2R_one. apply Nat.even_spec in E. destruct E as [k ->].
    rewrite pow_1_even. reflexivity.
  - assert (Ho : Nat.Odd i) by (apply Nat.odd_spec; rewrite <- Nat.negb_even, E; reflexivity).
    destruct Ho as [k ->].
    replace (2 * k + 1)%nat with (S (2 * k)) by lia.
    rewrite pow_1_odd.
    unfold Q2R; simpl; field.
Qed.

Definition Qcos_term (a : Q) (i : nat) : Q :=
  Qred (Qsgn i * (Qpow a (2 * i) / inject_Z (Zfact (2 * i)))).

Lemma Zfact_pos : forall n, (0 < Zfact n)%Z.
Proof.
  induction n as [| n IH].
  - simpl. lia.
  - change (Zfact (S n)) with (Z.of_nat (S n) * Zfact n)%Z.
    assert (H : (0 < Z.of_nat (S n))%Z) by lia. nia.
Qed.

(* the argument must stay opaque here: simpl would rewrite 2 * i to
   i + (i + 0) inside Zfact, breaking the match with Zfact_pos *)
Lemma inject_Z_neq0 : forall z, (z <> 0)%Z -> ~ (inject_Z z == 0).
Proof. intros z Hz Hc. apply Hz. unfold Qeq in Hc; simpl in Hc. lia. Qed.

Lemma Q2R_Qcos_term : forall a i, Q2R (Qcos_term a i) = cos_term (Q2R a) i.
Proof.
  intros a i. unfold Qcos_term, cos_term. rewrite Q2R_Qred.
  assert (Hne : ~ (inject_Z (Zfact (2 * i)) == 0)).
  { apply inject_Z_neq0. pose proof (Zfact_pos (2 * i)). lia. }
  rewrite Q2R_mult, Q2R_div by exact Hne.
  rewrite Q2R_Qsgn, Q2R_Qpow, Q2R_inject, <- INR_fact_Zfact. reflexivity.
Qed.

Fixpoint Qcos_approx (a : Q) (n : nat) : Q :=
  match n with
  | O => Qcos_term a 0
  | S k => Qred (Qcos_approx a k + Qcos_term a (S k))
  end.

Lemma Q2R_Qcos_approx : forall a n, Q2R (Qcos_approx a n) = cos_approx (Q2R a) n.
Proof.
  intros a n. induction n as [| n IH]; cbn [Qcos_approx]; unfold cos_approx.
  - simpl sum_f_R0. apply Q2R_Qcos_term.
  - rewrite tech5. rewrite Q2R_Qred, Q2R_plus.
    unfold cos_approx in IH. rewrite IH, Q2R_Qcos_term. reflexivity.
Qed.

(* ----------------------------------------------------------------- *)
(*  C.  the base enclosure, straight from Stdlib's cos_bound           *)
(* ----------------------------------------------------------------- *)
Definition Icos_base (a : Q) (n : nat) : Itv :=
  mkI (Qcos_approx a (2 * n + 1)) (Qcos_approx a (2 * (n + 1))).

Lemma Icos_base_sound : forall a n,
  - PI / 2 <= Q2R a -> Q2R a <= PI / 2 ->
  Icontains (Icos_base a n) (cos (Q2R a)).
Proof.
  intros a n Hlo Hhi. unfold Icontains, Icos_base; simpl.
  rewrite !Q2R_Qcos_approx. apply cos_bound; assumption.
Qed.

(* ----------------------------------------------------------------- *)
(*  D.  the doubling step, cos 2x = 2 cos^2 x - 1                      *)
(* ----------------------------------------------------------------- *)
Lemma Q2R_two : Q2R 2 = 2.
Proof. unfold Q2R; simpl; field. Qed.

Definition Idbl (i : Itv) : Itv := Isub (Imul (Iconst 2) (Imul i i)) (Iconst 1).

Lemma Idbl_sound : forall i x, Icontains i (cos x) -> Icontains (Idbl i) (cos (2 * x)).
Proof.
  intros i x H. unfold Idbl.
  assert (E : cos (2 * x) = 2 * (cos x * cos x) - 1)
    by (rewrite cos_2a_cos; ring).
  rewrite E. apply Isub_sound.
  - apply Imul_sound; [ | apply Imul_sound; exact H ].
    rewrite <- Q2R_two. apply Iconst_sound.
  - rewrite <- Q2R_one. apply Iconst_sound.
Qed.

Fixpoint Idbl_iter (p m : nat) (i : Itv) : Itv :=
  match m with O => i | S m' => Idbl_iter p m' (Iround p (Idbl i)) end.

Lemma Idbl_iter_sound : forall p m i x,
  Icontains i (cos x) -> Icontains (Idbl_iter p m i) (cos (INR (2 ^ m) * x)).
Proof.
  intros p m. induction m as [| m IH]; intros i x H.
  - simpl. replace (1 * x) with x by ring. exact H.
  - simpl Idbl_iter.
    assert (H2 : Icontains (Iround p (Idbl i)) (cos (2 * x)))
      by (apply Iround_sound, Idbl_sound; exact H).
    pose proof (IH _ _ H2) as H3.
    replace (2 ^ S m)%nat with (2 * 2 ^ m)%nat by (simpl; lia).
    rewrite mult_INR.
    replace (INR 2 * INR (2 ^ m) * x) with (INR (2 ^ m) * (2 * x))
      by (simpl INR; ring).
    exact H3.
Qed.

(* ----------------------------------------------------------------- *)
(*  E.  THE ENCLOSURE OF cos AT A RATIONAL POINT                       *)
(* ----------------------------------------------------------------- *)
Definition Icos_pt (p m n : nat) (a : Q) : Itv :=
  Idbl_iter p m (Icos_base (a / Qp2 m) n).

Theorem Icos_pt_sound : forall p m n a,
  - PI / 2 <= Q2R a / INR (2 ^ m) -> Q2R a / INR (2 ^ m) <= PI / 2 ->
  Icontains (Icos_pt p m n a) (cos (Q2R a)).
Proof.
  intros p m n a Hlo Hhi.
  assert (HN : 0 < INR (2 ^ m)) by (apply lt_0_INR; apply pow2_pos).
  assert (Hz : Q2R (a / Qp2 m) = Q2R a / INR (2 ^ m))
    by (rewrite Q2R_div by apply Qp2_neq0; rewrite Q2R_Qp2; reflexivity).
  assert (Hbase : Icontains (Icos_base (a / Qp2 m) n) (cos (Q2R a / INR (2 ^ m))))
    by (rewrite <- Hz; apply Icos_base_sound; rewrite Hz; assumption).
  pose proof (Idbl_iter_sound p m _ _ Hbase) as H.
  unfold Icos_pt.
  replace (Q2R a) with (INR (2 ^ m) * (Q2R a / INR (2 ^ m))) by (field; lra).
  exact H.
Qed.

Print Assumptions Icos_base_sound.
Print Assumptions Idbl_iter_sound.
Print Assumptions Icos_pt_sound.
