(* ================================================================= *)
(*  FirstZeroChk16.v  --  THE COMPUTATION at t = 16.                     *)
(*                                                                    *)
(*  Isolated in its own file: a .vo persists, so a mistake downstream  *)
(*  costs seconds rather than re-running 2048 midpoint panels.         *)
(*                                                                    *)
(*  The Imsum application is INLINED rather than named.  A named       *)
(*  Definition would be transparent, and a later conversion between    *)
(*  the name and its body makes the kernel whnf the application --     *)
(*  i.e. re-run the whole quadrature in the ORDINARY evaluator.        *)
(*  vm_compute's VM cast protects only this file's own Qed.            *)
(*                                                                    *)
(*  The enclosure is never TRANSCRIBED -- pasting a 40-digit rational  *)
(*  out of a vm_compute back into source is an unchecked step.  The    *)
(*  computation ends in a BOOLEAN, which reflection turns into a real  *)
(*  inequality downstream.                                             *)
(* ================================================================= *)

From Stdlib Require Import QArith Reals.
Require Import IntervalArith XirSignChange.

Lemma chk16 :
  match Imsum 46 25 32 14 32 12 30 5 4 46 16 (13 # 16384) 2048 with
  | Some i => Qle_bool (1954 # 1000000) (ilo i)
  | None => false
  end = true.
Proof. vm_compute. reflexivity. Qed.
