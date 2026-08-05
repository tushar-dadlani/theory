(* ================================================================= *)
(*  LogHarmonic.v  —  the log-harmonic sum  Sum_{m<=N} ln m / m.        *)
(*                                                                    *)
(*  With A(x) = (1/2) ln^2 x  (so A'(x) = ln x / x), the Mean Value      *)
(*  Theorem + telescoping give                                          *)
(*      Sum_{m<=N} (ln m)/m  =  (1/2) ln^2 N + O(1).                     *)
(*                                                                    *)
(*  The twist vs SumLogSq: ln t / t is DECREASING for t > e (we use      *)
(*  exp 1 <= 3), so the telescoping brackets are asymmetric (the lower   *)
(*  bound is shifted by one).  No integrals -- just MVT_cor2.  This is    *)
(*  the atomic estimate the Selberg log^2 inequality and the             *)
(*  Sum Lam_2(n)/n = ln^2 N + O(ln N) smoothing lemma both reduce to.    *)
(*  Axiom-clean.                                                         *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia Arith List.
Require Import RealMobius ChebyshevBound.
Import ListNotations.
Open Scope R_scope.

Definition Alh (x : R) : R := / 2 * (ln x * ln x).
Definition Slh (N : nat) : R := Rls (seq 1 N) (fun m => ln (INR m) / INR m).

(* A'(x) = ln x / x *)
Lemma dAlh : forall x, 0 < x -> derivable_pt_lim Alh x (ln x / x).
Proof.
  intros x Hx.
  assert (Hln : derivable_pt_lim ln x (/ x)) by (apply derivable_pt_lim_ln; exact Hx).
  assert (Hsq : derivable_pt_lim (fun t => ln t * ln t) x (/ x * ln x + ln x * / x))
    by (apply (derivable_pt_lim_mult ln ln x (/ x) (/ x)); exact Hln).
  assert (HA : derivable_pt_lim Alh x (/ 2 * (/ x * ln x + ln x * / x)))
    by (unfold Alh;
        apply (derivable_pt_lim_scal (fun t => ln t * ln t) (/ 2) x
                 (/ x * ln x + ln x * / x)); exact Hsq).
  replace (ln x / x) with (/ 2 * (/ x * ln x + ln x * / x)) by (field; lra).
  exact HA.
Qed.

(* ln t / t is decreasing on [3, oo) : uses exp 1 <= 3 so ln a >= 1. *)
Lemma lnx_dec : forall a b, 3 <= a -> a <= b -> ln b / b <= ln a / a.
Proof.
  intros a b Ha Hab.
  assert (Ha0 : 0 < a) by lra.
  assert (Hb0 : 0 < b) by lra.
  assert (Hla1 : 1 <= ln a).
  { rewrite <- (ln_exp 1); apply ln_le; [ apply exp_pos | ].
    apply Rle_trans with 3; [ apply exp_le_3 | exact Ha ]. }
  assert (Hkey : a * ln b <= b * ln a).
  { destruct (Rle_lt_or_eq_dec a b Hab) as [Hlt | Heqab]; [ | rewrite Heqab; lra ].
    assert (Hderiv : forall c, a <= c <= b ->
              derivable_pt_lim (fun t => ln a * t - a * ln t) c (ln a * 1 - a * / c)).
    { intros c [Hc1 Hc2]; assert (Hc0 : 0 < c) by lra.
      apply derivable_pt_lim_minus.
      - apply (derivable_pt_lim_scal (fun t => t) (ln a) c 1); apply derivable_pt_lim_id.
      - apply (derivable_pt_lim_scal ln a c (/ c)); apply derivable_pt_lim_ln; exact Hc0. }
    destruct (MVT_cor2 (fun t => ln a * t - a * ln t) (fun c => ln a * 1 - a * / c) a b Hlt Hderiv)
      as [xi [Heq [Hx1 Hx2]]].
    assert (Haxi : a * / xi <= 1)
      by (apply Rmult_le_reg_r with xi; [ lra | replace (a * / xi * xi) with a by (field; lra); lra ]).
    nra. }
  apply Rmult_le_reg_r with (a * b); [ apply Rmult_lt_0_compat; lra | ].
  replace (ln b / b * (a * b)) with (a * ln b) by (field; lra).
  replace (ln a / a * (a * b)) with (b * ln a) by (field; lra).
  exact Hkey.
Qed.

Lemma Rls_nil : forall A (f : A -> R), Rls [] f = 0.
Proof. reflexivity. Qed.

Lemma Slh_succ : forall y, Slh (S y) = Slh y + ln (INR (S y)) / INR (S y).
Proof.
  intro y; unfold Slh; rewrite seq_S, Rls_app; replace (1 + y)%nat with (S y) by lia.
  rewrite Rls_cons, Rls_nil; ring.
Qed.

(* Upper bound: Slh N <= (1/2) ln^2 N + C_up. *)
Lemma lh_upper : forall N, (3 <= N)%nat ->
  Slh N <= / 2 * (ln (INR N) * ln (INR N)) + (Slh 3 - / 2 * (ln 3 * ln 3)).
Proof.
  induction N as [| N IH]; intro HN; [ lia | ].
  destruct (Nat.eq_dec N 2) as [-> | Hne].
  - replace (INR 3) with 3 by (simpl; ring); lra.
  - specialize (IH ltac:(lia)).
    assert (H3N : 3 <= INR N) by (replace 3 with (INR 3) by (simpl; ring); apply le_INR; lia).
    assert (HSNgt : INR N < INR (S N)) by (rewrite S_INR; lra).
    destruct (MVT_cor2 Alh (fun t => ln t / t) (INR N) (INR (S N)) HSNgt
                (fun c Hc => dAlh c ltac:(lra))) as [xi [Heq [Hx1 Hx2]]].
    replace (INR (S N) - INR N) with 1 in Heq by (rewrite S_INR; ring);
      rewrite Rmult_1_r in Heq.
    assert (Hdec : ln (INR (S N)) / INR (S N) <= ln xi / xi) by (apply lnx_dec; lra).
    unfold Alh in Heq; rewrite (Slh_succ N); lra.
Qed.

(* Lower bound (shifted): (1/2) ln^2 (N+1) - C_lo <= Slh N. *)
Lemma lh_lower : forall N, (3 <= N)%nat ->
  / 2 * (ln (INR (S N)) * ln (INR (S N))) - (/ 2 * (ln (INR 4) * ln (INR 4)) - Slh 3) <= Slh N.
Proof.
  induction N as [| N IH]; intro HN; [ lia | ].
  destruct (Nat.eq_dec N 2) as [-> | Hne].
  - replace (S (S 2)) with 4%nat by reflexivity;
      replace (S 2) with 3%nat by reflexivity; lra.
  - specialize (IH ltac:(lia)).
    assert (H3N : 3 <= INR (S N)) by (replace 3 with (INR 3) by (simpl; ring); apply le_INR; lia).
    assert (HSNgt : INR (S N) < INR (S (S N))) by (rewrite (S_INR (S N)); lra).
    destruct (MVT_cor2 Alh (fun t => ln t / t) (INR (S N)) (INR (S (S N))) HSNgt
                (fun c Hc => dAlh c ltac:(lra))) as [xi [Heq [Hx1 Hx2]]].
    replace (INR (S (S N)) - INR (S N)) with 1 in Heq by (rewrite (S_INR (S N)); ring);
      rewrite Rmult_1_r in Heq.
    assert (Hdec : ln xi / xi <= ln (INR (S N)) / INR (S N)) by (apply lnx_dec; lra).
    unfold Alh in Heq; rewrite (Slh_succ N); lra.
Qed.

Theorem log_harmonic : forall N, (3 <= N)%nat ->
  / 2 * (ln (INR N) * ln (INR N)) - (/ 2 * (ln (INR 4) * ln (INR 4)) - Slh 3) <= Slh N
  /\ Slh N <= / 2 * (ln (INR N) * ln (INR N)) + (Slh 3 - / 2 * (ln 3 * ln 3)).
Proof.
  intros N HN; split; [ | apply lh_upper; exact HN ].
  eapply Rle_trans; [ | apply lh_lower; exact HN ].
  assert (Hmono : ln (INR N) <= ln (INR (S N)))
    by (apply ln_le; [ apply lt_0_INR; lia | apply le_INR; lia ]).
  assert (Hpos : 0 <= ln (INR N))
    by (rewrite <- ln_1; apply ln_le; [ lra | replace 1 with (INR 1) by (simpl; ring); apply le_INR; lia ]).
  assert (Hsq : ln (INR N) * ln (INR N) <= ln (INR (S N)) * ln (INR (S N))) by nra.
  lra.
Qed.

Print Assumptions log_harmonic.

(* ================================================================= *)
(*  END LogHarmonic.v  —  Sum_{m<=N} ln m/m = (1/2) ln^2 N + O(1).      *)
(* ================================================================= *)
