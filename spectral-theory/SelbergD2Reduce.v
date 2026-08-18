(* ================================================================= *)
(*  SelbergD2Reduce.v  —  PNT step 1a: isolate the degree-2 average D2   *)
(*  to the log-weighted not-trough mass Wc.                             *)
(*                                                                    *)
(*  Combining the proven signed star identity                           *)
(*    star_signed :  |Vsig N.ln^2 N - D2 + 2 Dlog| <= O(ln N)           *)
(*  with the proven Dlog upper bound                                    *)
(*    dlog_upper  :  Dlog <= (-a+d).ln^2 N/2 + (Kup-1+a-d).Wc + O(ln N)  *)
(*  gives directly                                                      *)
(*                                                                    *)
(*    D2 <= Vsig N.ln^2 N + 2.(dlog_upper RHS) + (star slack).          *)
(*                                                                    *)
(*  At a peak (Vsig N <= alpha) this is  D2 <= (small).ln^2 N +          *)
(*  2(Kup-1+alpha).Wc + O(ln N), so the remaining input to  D2 = o(ln^2)*)
(*  is exactly  Wc = o(ln^2 N)  (the Stage-3 log-weighted concentration).*)
(*  Axiom-clean.                                                        *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia Arith Lists.List.
Import ListNotations.
Require Import Chebyshev ChebyshevBound VonMangoldtGlobal RealMobius
        SelbergSymmetry SelbergAverage SelbergAverageSigned SelbergStarSigned
        SelbergDlogControl SelbergSignedConc MertensVonMangoldt.
Open Scope R_scope.

Lemma Rabs_le_inv2 : forall x M, Rabs x <= M -> - M <= x <= M.
Proof. intros x M H; unfold Rabs in H; destruct (Rcase_abs x); lra. Qed.

(* the reduction: D2 bounded by Vsig N.ln^2 N + 2.(dlog RHS) + star slack *)
Theorem D2_le_Wc : forall (N : nat) (alpha delta : R),
  0 <= alpha -> delta <= alpha -> (1 <= N)%nat ->
  Rls (seq 1 N) (fun n => Lam2 n / INR n * Vsig (N / n)%nat)
  <= Vsig N * (ln (INR N) * ln (INR N))
     + 2 * ((- alpha + delta) * (ln (INR N) * ln (INR N)) / 2
            + (Kup - 1 - (- alpha + delta))
              * Rls (seq 1 N) (fun n => w n * wnt alpha delta N n)
            + (alpha - delta) * (2 * Kup * ln (INR N) + 1))
     + ((Cs + (Kup - 1) * ln 2) * msum N + Cs * ln (INR N)).
Proof.
  intros N alpha delta Ha Hda HN.
  pose proof (star_signed N HN) as Hstar. apply Rabs_le_inv2 in Hstar.
  pose proof (dlog_upper N alpha delta Ha Hda HN) as Hdl.
  assert (HDeq : Dlogf N
    = Rls (seq 1 N) (fun n => Lam n * ln (INR n) / INR n * Vsig (N / n)%nat))
    by (unfold Dlogf, w; reflexivity).
  rewrite HDeq in Hdl.
  set (L2 := ln (INR N) * ln (INR N)) in *.
  set (LN := ln (INR N)) in *.
  set (D2 := Rls (seq 1 N) (fun n => Lam2 n / INR n * Vsig (N / n)%nat)) in *.
  set (Dlog := Rls (seq 1 N) (fun n => Lam n * ln (INR n) / INR n * Vsig (N / n)%nat)) in *.
  set (Wc := Rls (seq 1 N) (fun n => w n * wnt alpha delta N n)) in *.
  set (DLR := (- alpha + delta) * L2 / 2
              + (Kup - 1 - (- alpha + delta)) * Wc
              + (alpha - delta) * (2 * Kup * LN + 1)) in *.
  set (SR := (Cs + (Kup - 1) * ln 2) * msum N + Cs * LN) in *.
  set (VN2 := Vsig N * L2) in *.
  destruct Hstar as [Hlo _]. lra.
Qed.

Print Assumptions D2_le_Wc.
