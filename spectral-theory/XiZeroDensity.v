(* ================================================================= *)
(*  XiZeroDensity.v  —  the zero-counting FUNCTION for xi.             *)
(*                                                                    *)
(*    xi_count_below : any NoDup list of zeros of XiC all of modulus   *)
(*      < R has length at most  Bxi R := ln (4 . XiM (8(R+1))) / ln 3. *)
(*                                                                    *)
(*  xi_zero_count produces its list and its Jensen radius              *)
(*  EXISTENTIALLY, which is fine as a statement but useless as an       *)
(*  input: a caller who cares about a particular disk cannot aim it.    *)
(*  This file turns it into a counting function.  Two things make that  *)
(*  work:                                                              *)
(*                                                                    *)
(*   * the LOWER bound Rc/8 <= Rj.  Choosing the circle Rc := 8(R+1)    *)
(*     forces Rj >= R+1 > R, so the disk we care about really is inside *)
(*     the counted one.                                                *)
(*   * COMPLETENESS of the produced list.  Every zero in |z| < Rj is in *)
(*     l, so any NoDup list of such zeros is included in l, and         *)
(*     NoDup_incl_length bounds its length by length l.                *)
(*                                                                    *)
(*  This is the form the Hadamard programme consumes: it is what lets   *)
(*  one count zeros in dyadic annuli and so bound sum 1/|rho|^2.        *)
(*  Axiom-clean.                                                       *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia List.
Require Import ComplexField Cmodulus Holomorphic CPathIntegral
        RiemannXiEntire XiGrowthBound XiZeroCount CDyadicSum.
Open Scope R_scope.

(* the counting majorant *)
Definition Bxi (r : R) : R := ln (4 * XiM (8 * (r + 1))) / ln 3.

Theorem xi_count_below : forall (r : R) (s : list C),
  0 < r -> NoDup s ->
  (forall rho, In rho s -> XiC rho = C0) ->
  (forall rho, In rho s -> Cmod rho < r) ->
  INR (length s) <= Bxi r.
Proof.
  intros r s HR Hnd Hzero Hsmall.
  destruct (xi_zero_count (8 * (r + 1)) ltac:(lra))
    as [l [Rj [HRj0 [HRjb [HRjlo [Hin [Hzl [Hcomp [Hcount _]]]]]]]]].
  (* the lower bound on Rj puts our disk strictly inside the counted one *)
  assert (HRRj : r < Rj) by lra.
  (* completeness: s is included in l *)
  assert (Hincl : incl s l).
  { intros rho Hrho. apply Hcomp.
    - apply Rlt_trans with r; [ apply Hsmall; exact Hrho | exact HRRj ].
    - apply Hzero; exact Hrho. }
  pose proof (NoDup_incl_length Hnd Hincl) as Hlen.
  unfold Bxi.
  apply Rle_trans with (INR (length l)); [ apply le_INR; exact Hlen | exact Hcount ].
Qed.

Print Assumptions xi_count_below.

(* ================================================================= *)
(*  THE GENUS-1 CONVERGENCE INPUT for the Hadamard product.            *)
(*                                                                    *)
(*  Feeding xi_count_below to CDyadicSum.dyadic_sum_bound turns the    *)
(*  counting bound into a SUMMABILITY bound:  sum 1/|rho|^2 over any    *)
(*  finite set of zeros of xi of modulus >= 1 is at most 4a.           *)
(*                                                                    *)
(*  HONEST STATUS.  This is a REDUCTION, not yet an unconditional       *)
(*  theorem: the growth hypothesis Hgrow -- that Bxi (2^{k+1}) is       *)
(*  O((k+1) 2^k) -- is left as a hypothesis.  It is TRUE, and true      *)
(*  with a modest explicit constant (a = 12 comfortably suffices,       *)
(*  since Bxi(2^{k+1}) ~ 2^k (11.8 + 5.05 k) by the leading             *)
(*  (t/2) ln (t/pi) term of ln Tgb with t = 16.2^k + 9).  Discharging   *)
(*  it needs numeric control of Rpower, exp, ln and pi that this        *)
(*  development does not yet have -- see the note in the file header    *)
(*  of CDyadicSum.  Everything ELSE in the chain is unconditional.      *)
(* ================================================================= *)
Theorem xi_sum_inv_sq : forall a : R,
  0 <= a ->
  (forall k : nat, Bxi (2 ^ (S k)) <= a * INR (S k) * 2 ^ k) ->
  forall s : list C,
    NoDup s ->
    (forall x, In x s -> XiC x = C0) ->
    (forall x, In x s -> 1 <= Cmod x) ->
    sumlist invsq s <= 4 * a.
Proof.
  intros a Ha Hgrow s Hnd HP Hlow.
  exact (dyadic_sum_bound (fun z => XiC z = C0) Bxi xi_count_below
           a Ha Hgrow s Hnd HP Hlow).
Qed.

Print Assumptions xi_sum_inv_sq.
