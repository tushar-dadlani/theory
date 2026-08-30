(* ================================================================= *)
(*  SecondZeroChk22.v  --  THE COMPUTATION at t = 22.                  *)
(*                                                                    *)
(*  512 Simpson panels on [0,2], so 1536 integrand evaluations.        *)
(*  Isolated in its own file: a .vo persists, so a mistake downstream  *)
(*  costs seconds rather than re-running it.                          *)
(*                                                                    *)
(*  PRECISION.  p = 60, not the 46 the first-zero runs used.  Iexp_pt  *)
(*  p m has effective RELATIVE precision 2^(m-p), because each of the  *)
(*  m squarings doubles the rounding error; at p = 46, m = 25 that is  *)
(*  2^-21 = 4.8e-7, which on e^{-pi} = 0.0432 gives 2e-8 -- measured   *)
(*  as a 2.8e-8 enclosure width, against a window of only 1e-9.        *)
(*  This was invisible on the first zero because PI's own 1e-5 width   *)
(*  dominated; sharpening PI did not create the problem, it exposed    *)
(*  the next one down.  At p = 60 (p - m = 35) the width is 5.9e-9.    *)
(*  p = 66 gains nothing further, so a third source binds below that   *)
(*  -- most likely Idbl_iter's 4^mc amplification of the cosine's      *)
(*  rounding floor.  Not worth chasing: 5.9e-9 leaves a 1.16e-8        *)
(*  window, and the decimal below sits about one width from each edge. *)
(*                                                                    *)
(*  The enclosure is never TRANSCRIBED; the computation ends in a      *)
(*  BOOLEAN which reflection turns into a real inequality downstream.  *)
(* ================================================================= *)

From Stdlib Require Import QArith Reals.
Require Import IntervalArith XirSignChange.

Lemma chk22 :
  match Issum 60 25 40 14 40 12 40 5 4 60 22 (1 # 256) 512 with
  | Some i => Qle_bool (ihi i) (1032517 # 1000000000)
  | None => false
  end = true.
Proof. vm_compute. reflexivity. Qed.
