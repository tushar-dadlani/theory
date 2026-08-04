(* ================================================================= *)
(*  SumLogSq.v  —  the asymptotic  Sum_{m<=y} ln^2 m  (Step 2d).       *)
(*                                                                    *)
(*  With A(x) = x ln^2 x - 2 x ln x + 2 x  (so A'(x) = ln^2 x), the      *)
(*  Mean Value Theorem gives  A(m) - A(m-1) = ln^2(xi) in [ln^2(m-1),   *)
(*  ln^2 m], and a telescoping induction yields                         *)
(*      A(y) - 2  <=  Sum_{m<=y} ln^2 m  <=  A(y) - 2 + ln^2 y.          *)
(*  No integrals — just MVT.  Axiom-clean.                             *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia Arith List.
Require Import DirichletConv VonMangoldtGlobal RealMobius MuLog SelbergSymmetry
        SelbergSum ChebyshevBound.
Import ListNotations.
Open Scope R_scope.

Definition Alsq (x : R) : R := x * (ln x * ln x) - 2 * (x * ln x) + 2 * x.

(* A'(x) = ln^2 x *)
Lemma dAlsq : forall x, 0 < x -> derivable_pt_lim Alsq x (ln x * ln x).
Proof.
  intros x Hx.
  assert (Hln : derivable_pt_lim ln x (/ x)) by (apply derivable_pt_lim_ln; exact Hx).
  assert (Hsq : derivable_pt_lim (fun t => ln t * ln t) x (/ x * ln x + ln x * / x))
    by (apply (derivable_pt_lim_mult ln ln x (/ x) (/ x)); exact Hln).
  assert (H1 : derivable_pt_lim (fun t => t * (ln t * ln t)) x
                 (1 * (ln x * ln x) + x * (/ x * ln x + ln x * / x))).
  { apply (derivable_pt_lim_mult (fun t => t) (fun t => ln t * ln t) x 1
             (/ x * ln x + ln x * / x)); [ apply derivable_pt_lim_id | exact Hsq ]. }
  assert (Hxln : derivable_pt_lim (fun t => t * ln t) x (1 * ln x + x * / x))
    by (apply (derivable_pt_lim_mult (fun t => t) ln x 1 (/ x));
        [ apply derivable_pt_lim_id | exact Hln ]).
  assert (H2 : derivable_pt_lim (fun t => 2 * (t * ln t)) x (2 * (1 * ln x + x * / x)))
    by (apply (derivable_pt_lim_scal (fun t => t * ln t) 2 x (1 * ln x + x * / x)); exact Hxln).
  assert (H3 : derivable_pt_lim (fun t => 2 * t) x (2 * 1))
    by (apply (derivable_pt_lim_scal (fun t => t) 2 x 1); apply derivable_pt_lim_id).
  assert (Hm : derivable_pt_lim (fun t => t * (ln t * ln t) - 2 * (t * ln t)) x
                 ((1 * (ln x * ln x) + x * (/ x * ln x + ln x * / x)) - 2 * (1 * ln x + x * / x)))
    by (apply derivable_pt_lim_minus; [ exact H1 | exact H2 ]).
  assert (HA : derivable_pt_lim Alsq x
    (((1 * (ln x * ln x) + x * (/ x * ln x + ln x * / x)) - 2 * (1 * ln x + x * / x)) + 2 * 1))
    by (unfold Alsq; apply derivable_pt_lim_plus; [ exact Hm | exact H3 ]).
  replace (ln x * ln x) with
    (((1 * (ln x * ln x) + x * (/ x * ln x + ln x * / x)) - 2 * (1 * ln x + x * / x)) + 2 * 1)
    by (field; lra).
  exact HA.
Qed.

(* ln^2 is nondecreasing on [1, oo) *)
Lemma lnsq_mono : forall a b, 1 <= a -> a <= b -> ln a * ln a <= ln b * ln b.
Proof.
  intros a b Ha Hab.
  assert (0 <= ln a) by (rewrite <- ln_1; apply ln_le; lra).
  assert (ln a <= ln b) by (apply ln_le; lra).
  nra.
Qed.

Lemma Rls_nil : forall A (f : A -> R), Rls [] f = 0.
Proof. reflexivity. Qed.

Lemma Slog2_succ : forall y, Slog2 (S y) = Slog2 y + (ln (INR (S y))) ^ 2.
Proof.
  intro y; unfold Slog2; rewrite seq_S, Rls_app; replace (1 + y)%nat with (S y) by lia.
  rewrite Rls_cons, Rls_nil; ring.
Qed.

(* the telescoping bracket *)
Theorem Slog2_bracket : forall y, (1 <= y)%nat ->
  Alsq (INR y) - 2 <= Slog2 y <= Alsq (INR y) - 2 + ln (INR y) * ln (INR y).
Proof.
  induction y as [|y IH]; intro Hy; [ lia | ].
  destruct (Nat.eq_dec y 0) as [->|Hy0].
  - unfold Slog2, Alsq, Rls; cbn [seq map fold_right]; rewrite INR_1, ln_1; nra.
  - specialize (IH ltac:(lia)); destruct IH as [IHlo IHhi].
    assert (HyR : 1 <= INR y) by (apply (le_INR 1); lia).
    rewrite Slog2_succ.
    assert (HSy : INR y < INR (S y)) by (rewrite S_INR; lra).
    destruct (MVT_cor2 Alsq (fun t => ln t * ln t) (INR y) (INR (S y)) HSy
                (fun c Hc => dAlsq c ltac:(lra))) as [xi [Heq Hrange]].
    replace (INR (S y) - INR y) with 1 in Heq by (rewrite S_INR; ring);
      rewrite Rmult_1_r in Heq.
    assert (Hb1 : ln (INR y) * ln (INR y) <= ln xi * ln xi) by (apply lnsq_mono; lra).
    assert (Hb2 : ln xi * ln xi <= ln (INR (S y)) * ln (INR (S y))) by (apply lnsq_mono; lra).
    assert (Hpow : (ln (INR (S y))) ^ 2 = ln (INR (S y)) * ln (INR (S y))) by (simpl; ring).
    rewrite Hpow; split; lra.
Qed.

Print Assumptions Slog2_bracket.

(* ================================================================= *)
(*  END SumLogSq.v                                                    *)
(*  A(y) - 2 <= Sum_{m<=y} ln^2 m <= A(y) - 2 + ln^2 y,                *)
(*  A(x) = x ln^2 x - 2 x ln x + 2 x.                                  *)
(* ================================================================= *)
