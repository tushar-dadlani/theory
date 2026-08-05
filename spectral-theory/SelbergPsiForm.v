(* ================================================================= *)
(*  SelbergPsiForm.v  —  Selberg's inequality, unconditional (2d v4b).  *)
(*                                                                    *)
(*  The Abel step:  D(N) := psi(N) ln N - Sum_{n<=N} Lam(n) ln n        *)
(*  satisfies D(S N) = D N + psi(N)(ln(N+1)-ln N), so a telescoping     *)
(*  induction (psi(n)<=Kup n, ln(n+1)-ln n<=1/n via harm_step) gives    *)
(*      0 <= D(N) <= Kup N.                                             *)
(*  Since Psiform(N) = Sum_{n<=N} Lam2(n) + D(N) (hyperbola_swap on the  *)
(*  convolution part), lam2_sum_bound (Sum Lam2 = 2N ln N + O(N)) gives  *)
(*      | Psiform(N) - 2N ln N | <= (88 + 3 Kup) N   (Psiform_bound),   *)
(*  which discharges selberg_R_form's hypothesis, making the remainder- *)
(*  form Selberg inequality UNCONDITIONAL:                              *)
(*      | R(N) ln N + Sum_{d<=N} Lam(d) R(floor(N/d)) | <= C N.          *)
(*  Axiom-clean.                                                        *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia Arith List.
Require Import VonMangoldtGlobal RealMobius SelbergSymmetry SelbergSum Chebyshev
        ChebyshevBound SelbergEndgame HarmonicSum MobiusOverD SelbergRForm SelbergMainTerm PartB.
Import ListNotations.
Open Scope R_scope.

Definition Llog (N : nat) : R := Rls (seq 1 N) (fun n => Lam n * ln (INR n)).
Definition D (N : nat) : R := psi N * ln (INR N) - Llog N.

Lemma Llog_rec : forall N, Llog (S N) = Llog N + Lam (S N) * ln (INR (S N)).
Proof.
  intro N; unfold Llog; rewrite seq_S, Rls_app, Rls_cons, Rls_nil2;
    replace (1 + N)%nat with (S N) by lia; ring.
Qed.

Lemma D_rec : forall N, D (S N) = D N + psi N * (ln (INR (S N)) - ln (INR N)).
Proof. intro N; unfold D; rewrite psi_succ, Llog_rec; ring. Qed.

Lemma D_bound : forall N, (1 <= N)%nat -> 0 <= D N <= Kup * INR N.
Proof.
  induction N as [|N IH]; intro HN; [ lia | ].
  destruct (Nat.eq_dec N 0) as [->|HN0].
  - unfold D, Llog; replace (seq 1 1) with (1%nat :: nil) by reflexivity;
      rewrite Rls_cons, Rls_nil2, INR_1, ln_1.
    assert (0 <= Kup) by (unfold Kup; pose proof ln2_pos; lra); lra.
  - specialize (IH ltac:(lia)); rewrite D_rec.
    pose proof (psi_nonneg N) as Hpn.
    pose proof (psi_upper N) as Hpu.
    pose proof (harm_step N ltac:(lia)) as [Hlo Hhi].
    assert (HN1 : 1 <= INR N) by (apply (le_INR 1); lia).
    assert (Hinv0 : 0 <= / INR (S N))
      by (apply Rlt_le, Rinv_0_lt_compat; apply lt_0_INR; lia).
    assert (Hstep0 : 0 <= psi N * (ln (INR (S N)) - ln (INR N)))
      by (apply Rmult_le_pos; [ exact Hpn | lra ]).
    assert (HstepK : psi N * (ln (INR (S N)) - ln (INR N)) <= Kup).
    { apply Rle_trans with (INR N * Kup * / INR N).
      - apply Rmult_le_compat; [ exact Hpn | lra | exact Hpu | exact Hhi ].
      - assert (Heq : INR N * Kup * / INR N = Kup) by (field; apply not_0_INR; lia).
        rewrite Heq; lra. }
    replace (Kup * INR (S N)) with (Kup * INR N + Kup) by (rewrite S_INR; ring); lra.
Qed.

(* Sum Lam2 splits: log-part + convolution-part (= Sum Lam(d) psi(floor(N/d))) *)
Lemma HLam2 : forall N,
  Rls (seq 1 N) Lam2 = Llog N + Rls (seq 1 N) (fun d => Lam d * psi (N / d)%nat).
Proof.
  intro N.
  rewrite (Rls_ext _ Lam2
             (fun n => Lam n * ln (INR n)
                       + Rls (divisors n) (fun d => Lam d * Lam (n / d)%nat)) (seq 1 N))
    by (intros; reflexivity).
  rewrite Rls_add; unfold Llog; apply Rplus_eq_compat_l.
  rewrite (hyperbola_swap (fun d m => Lam d * Lam m) N).
  apply Rls_ext; intros d _.
  rewrite <- Rls_scal; change (Rls (seq 1 (N / d)%nat) Lam) with (psi (N / d)%nat); reflexivity.
Qed.

Lemma Psiform_eq : forall N, Psiform N = Rls (seq 1 N) Lam2 + D N.
Proof. intro N; unfold Psiform, D; rewrite (HLam2 N); ring. Qed.

Theorem Psiform_bound : forall N, (1 <= N)%nat ->
  Rabs (Psiform N - 2 * INR N * ln (INR N)) <= (88 + 3 * Kup) * INR N.
Proof.
  intros N HN; rewrite (Psiform_eq N).
  pose proof (lam2_sum_bound N HN) as HL; apply abs_bnd in HL.
  pose proof (D_bound N HN) as [Hd0 Hd1].
  assert (HEQ : (88 + 3 * Kup) * INR N = (88 + 2 * Kup) * INR N + Kup * INR N) by ring.
  apply Rabs_le; split; rewrite HEQ; lra.
Qed.

(* Selberg's inequality in remainder form -- now UNCONDITIONAL *)
Theorem selberg_inequality : forall N, (1 <= N)%nat ->
  Rabs (Rform N) <= (88 + 3 * Kup + 1) * INR N.
Proof. exact (selberg_R_form (88 + 3 * Kup) Psiform_bound). Qed.

Print Assumptions selberg_inequality.

(* ================================================================= *)
(*  END SelbergPsiForm.v  —  Selberg's inequality, unconditional.       *)
(*  | R(N) ln N + Sum_{d<=N} Lam(d) R(floor(N/d)) | <= (89+3 Kup) N.     *)
(* ================================================================= *)
