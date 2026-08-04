(* ================================================================= *)
(*  StirlingSharp.v  —  sharp log-factorial estimate (Step 2d, i).     *)
(*                                                                    *)
(*  With B(x) = x ln x - x  (so B'(x) = ln x), the Mean Value Theorem   *)
(*  gives  B(k) - B(k-1) = ln(xi) in [ln(k-1), ln k], and a telescoping *)
(*  induction sharpens the Stirling bracket to                          *)
(*      N ln N - N + 1  <=  Tlog N  <=  N ln N - N + 1 + ln N,           *)
(*  i.e.  Tlog N = N ln N - N + O(ln N)   (Tlog N = ln(N!)).             *)
(*  This is the precision needed for the O(N) cancellation in the        *)
(*  summed Selberg formula (the old bracket was only O(N)).             *)
(*  No integrals — just MVT.  Axiom-clean.                             *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia Arith List.
Require Import Chebyshev ChebyshevBound.
Import ListNotations.
Open Scope R_scope.

Definition Blog (x : R) : R := x * ln x - x.

(* B'(x) = ln x *)
Lemma dBlog : forall x, 0 < x -> derivable_pt_lim Blog x (ln x).
Proof.
  intros x Hx.
  assert (Hln : derivable_pt_lim ln x (/ x)) by (apply derivable_pt_lim_ln; exact Hx).
  assert (Hxln : derivable_pt_lim (fun t => t * ln t) x (1 * ln x + x * / x))
    by (apply (derivable_pt_lim_mult (fun t => t) ln x 1 (/ x));
        [ apply derivable_pt_lim_id | exact Hln ]).
  assert (Hid : derivable_pt_lim (fun t => t) x 1) by apply derivable_pt_lim_id.
  assert (Hm : derivable_pt_lim Blog x ((1 * ln x + x * / x) - 1))
    by (unfold Blog; apply derivable_pt_lim_minus; [ exact Hxln | exact Hid ]).
  replace (ln x) with ((1 * ln x + x * / x) - 1) by (field; lra).
  exact Hm.
Qed.

(* the sharp telescoping bracket *)
Theorem Tlog_sharp : forall N, (1 <= N)%nat ->
  INR N * ln (INR N) - INR N + 1 <= Tlog N
  <= INR N * ln (INR N) - INR N + 1 + ln (INR N).
Proof.
  induction N as [|N IH]; intro HN; [ lia | ].
  destruct (Nat.eq_dec N 0) as [->|HN0].
  - unfold Tlog; cbn [seq map fold_right]; rewrite INR_1, ln_1; lra.
  - specialize (IH ltac:(lia)); destruct IH as [IHlo IHhi].
    assert (HyR : 1 <= INR N) by (apply (le_INR 1); lia).
    rewrite Tlog_rec.
    assert (HSy : INR N < INR (S N)) by (rewrite S_INR; lra).
    destruct (MVT_cor2 Blog (fun t => ln t) (INR N) (INR (S N)) HSy
                (fun c Hc => dBlog c ltac:(lra))) as [xi [Heq Hrange]].
    replace (INR (S N) - INR N) with 1 in Heq by (rewrite S_INR; ring);
      rewrite Rmult_1_r in Heq.
    assert (Hb1 : ln (INR N) <= ln xi) by (apply ln_le; lra).
    assert (Hb2 : ln xi <= ln (INR (S N))) by (apply ln_le; lra).
    unfold Blog in Heq.
    split; lra.
Qed.

Print Assumptions Tlog_sharp.

(* ================================================================= *)
(*  END StirlingSharp.v                                               *)
(*  N ln N - N + 1 <= Tlog N <= N ln N - N + 1 + ln N.                 *)
(* ================================================================= *)
