(* ================================================================= *)
(*  HarmonicSum.v  —  the harmonic sum  Sum_{m<=N} 1/m = ln N + O(1)    *)
(*                    (Step 2d, iii).                                   *)
(*                                                                    *)
(*  With antiderivative ln x of 1/x, the MVT gives the per-step bracket  *)
(*      1/(n+1)  <=  ln(n+1) - ln(n)  <=  1/n,                           *)
(*  and two telescoping inductions pin the harmonic number:             *)
(*      ln N  <=  H(N)  <=  ln N + 1,   H(N) = Sum_{m<=N} 1/m.           *)
(*  This is the Euler estimate underlying the Mobius-Mertens sums in     *)
(*  the summed Selberg formula (the /d convolution sums).               *)
(*  No integrals — just MVT.  Axiom-clean.                             *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia Arith List.
Require Import RealMobius ChebyshevBound.
Import ListNotations.
Open Scope R_scope.

Definition Harm (N : nat) : R := Rls (seq 1 N) (fun m => / INR m).

Lemma Rls_nil' : forall A (f : A -> R), Rls (@nil A) f = 0.
Proof. reflexivity. Qed.

Lemma Harm_rec : forall N, Harm (S N) = Harm N + / INR (S N).
Proof.
  intro N; unfold Harm; rewrite seq_S, Rls_app.
  replace (1 + N)%nat with (S N) by lia.
  rewrite Rls_cons, Rls_nil'; ring.
Qed.

(* the MVT per-step increment bracket:  1/(n+1) <= ln(n+1)-ln n <= 1/n *)
Lemma harm_step : forall n, (1 <= n)%nat ->
  / INR (S n) <= ln (INR (S n)) - ln (INR n) <= / INR n.
Proof.
  intros n Hn.
  assert (H1 : 1 <= INR n) by (apply (le_INR 1); lia).
  assert (HSy : INR n < INR (S n)) by (rewrite S_INR; lra).
  destruct (MVT_cor2 ln (fun t => / t) (INR n) (INR (S n)) HSy
              (fun c Hc => derivable_pt_lim_ln c ltac:(lra))) as [xi [Heq Hrange]].
  replace (INR (S n) - INR n) with 1 in Heq by (rewrite S_INR; ring);
    rewrite Rmult_1_r in Heq.
  assert (Hxipos : 0 < xi) by lra.
  rewrite Heq; split.
  - apply Rinv_le_contravar; lra.
  - apply Rinv_le_contravar; lra.
Qed.

Lemma Harm_lower : forall N, (1 <= N)%nat -> ln (INR (S N)) <= Harm N.
Proof.
  induction N as [|N IH]; intro HN; [ lia | ].
  destruct (Nat.eq_dec N 0) as [->|HN0].
  - unfold Harm, Rls; cbn [seq map fold_right].
    rewrite INR_1, Rinv_1.
    assert (HI2 : INR 2 = 2) by (simpl; ring).
    pose proof (ln_self1 (INR 2) ltac:(rewrite HI2; lra)) as Hls.
    rewrite HI2 in Hls |- *; lra.
  - specialize (IH ltac:(lia)); rewrite Harm_rec.
    pose proof (harm_step (S N) ltac:(lia)) as [Hlo Hhi]; lra.
Qed.

Lemma Harm_upper : forall N, (1 <= N)%nat -> Harm N <= ln (INR N) + 1.
Proof.
  induction N as [|N IH]; intro HN; [ lia | ].
  destruct (Nat.eq_dec N 0) as [->|HN0].
  - unfold Harm, Rls; cbn [seq map fold_right].
    rewrite INR_1, Rinv_1, ln_1; lra.
  - specialize (IH ltac:(lia)); rewrite Harm_rec.
    pose proof (harm_step N ltac:(lia)) as [Hlo Hhi]; lra.
Qed.

Theorem Harm_bracket : forall N, (1 <= N)%nat ->
  ln (INR N) <= Harm N <= ln (INR N) + 1.
Proof.
  intros N HN; split.
  - eapply Rle_trans; [ | apply Harm_lower; exact HN ].
    apply ln_le; [ apply lt_0_INR; lia | rewrite S_INR; lra ].
  - apply Harm_upper; exact HN.
Qed.

Print Assumptions Harm_bracket.

(* ================================================================= *)
(*  END HarmonicSum.v                                                 *)
(*  ln N <= Sum_{m<=N} 1/m <= ln N + 1.                               *)
(* ================================================================= *)
