(* ================================================================= *)
(*  ThirdZeroChk26.v  --  THE COMPUTATION at t = 26.                   *)
(*                                                                    *)
(*  1024 Simpson panels on [0,2], so 3072 integrand evaluations.       *)
(*                                                                    *)
(*  PRECISION.  m = 36 halvings, not the 25 used for the first two     *)
(*  zeros -- and the reason is NOT rounding.  Raising every rounding   *)
(*  precision (pc, p2, p3, p) moved the enclosure width by 0.1%: it    *)
(*  stayed at 5.9e-9 against a window of 7.8e-10.  The real source is  *)
(*  Iexp_base itself, which is only a FIRST-ORDER bracket              *)
(*  [1+z, 1/(1-z)], so its relative width is about z^2; with           *)
(*  z = q/2^m the m squarings of Isq_iter amplify that by 2^m, leaving *)
(*  relative width about q^2/2^m.  At q = -pi, m = 25 that is          *)
(*  pi^2/2^25 = 2.9e-7, and on e^{-pi} = 0.0432 that is 1.3e-8.        *)
(*  Measured against the prediction: m=25 -> 5.9e-9, m=32 -> 7.6e-11,  *)
(*  m=36 -> 1.8e-11.  So the fix is more HALVINGS, not more bits.      *)
(*  At m = 36 the width is 44x inside the window.                      *)
(*                                                                    *)
(*  Here xir 26 < 0, so the decimal is a LOWER bound on the sum.       *)
(*  It is set from the measured ilo = 0.000739372481, never from a     *)
(*  float estimate.                                                    *)
(* ================================================================= *)

From Stdlib Require Import QArith Reals.
Require Import IntervalArith XirSignChange.

Lemma chk26 :
  match Issum 80 36 56 24 56 22 40 5 4 80 26 (1 # 512) 1024 with
  | Some i => Qle_bool (7393721 # 10000000000) (ilo i)
  | None => false
  end = true.
Proof. vm_compute. reflexivity. Qed.
