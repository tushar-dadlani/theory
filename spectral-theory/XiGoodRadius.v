(* ================================================================= *)
(*  XiGoodRadius.v  —  a circle that misses the zeros of xi.           *)
(*                                                                    *)
(*    xi_good_radius : for every r > 0 and every covering radius cov   *)
(*      there are rr in [2r, 4r] and del > 0 with                      *)
(*                                                                    *)
(*        r / (Bxi cov + 1)  <=  del  <=  |w - rho|                    *)
(*                                                                    *)
(*      for EVERY zero rho of xi of modulus < cov and every w on the   *)
(*      circle |w| = rr.                                               *)
(*                                                                    *)
(*  The geometry is CGoodRadius.good_radius_list; all that happens     *)
(*  here is aiming it at xi's zero set.  Two clauses of                *)
(*  xi_zero_count do the work, and both are already tuned for this:    *)
(*                                                                    *)
(*   * running it on the circle Rc := 8(cov+1) makes its lower bound   *)
(*     Rc/8 <= Rj force Rj >= cov + 1 > cov, so its COMPLETENESS       *)
(*     clause covers every zero the caller cares about.  This is the   *)
(*     same aiming trick xi_count_below already uses.                  *)
(*   * at that Rc its count clause reads INR (length l) <=             *)
(*     ln (4 XiM Rc)/ln 3, which IS Bxi cov -- definitionally, no      *)
(*     estimate needed.                                                *)
(*                                                                    *)
(*  Quantifying over ZEROS rather than over a list is what the         *)
(*  consumer wants: it will apply this to the enumerated rho_n with    *)
(*  |rho_n| < 10 rr <= 40 r, so it calls this at cov := 40 r.  The     *)
(*  constant is left as a parameter because it is fixed downstream, by *)
(*  the 10|z| <= |rho| cut in CEfacLower.Efac_lower_far.               *)
(*                                                                    *)
(*  NOTE the bound is RADIAL only: a zero of modulus exactly rr would  *)
(*  give nothing even for a w on the far side of the circle.  That is  *)
(*  inherent to reducing the circle to its radius, and is exactly what *)
(*  a minimum-modulus estimate needs -- no consumer should read        *)
(*  angular separation into it.  Axiom-clean.                          *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia List.
Require Import ComplexField Cmodulus Holomorphic CDeriv
        JensenMultiZero CZeroListFactor CGoodRadius
        RiemannXiEntire XiZeroCount XiZeroDensity.
Open Scope R_scope.

Theorem xi_good_radius : forall r cov : R, 0 < r -> 0 < cov ->
  exists rr del : R,
    2 * r <= rr /\ rr <= 4 * r /\ 0 < del /\
    r / (Bxi cov + 1) <= del /\
    forall rho, XiC rho = C0 -> Cmod rho < cov ->
      forall w, Cmod w = rr -> del <= Cmod (Cminus w rho).
Proof.
  intros r cov Hr Hcov.
  (* the complete zero list of the disk |z| < Rj, with Rj > cov *)
  destruct (xi_zero_count (8 * (cov + 1)) ltac:(lra))
    as [l [Rj [HRj0 [HRjb [HRjlo [Hin [Hzl [Hcomp [Hcount _]]]]]]]]].
  assert (HcovRj : cov < Rj) by lra.
  destruct (good_radius_list r l Hr) as [rr [Hlo [Hhi Hb]]].
  assert (HN0 : 0 <= INR (length l)) by apply pos_INR.
  assert (HBx : INR (length l) <= Bxi cov) by (unfold Bxi; exact Hcount).
  exists rr, (r / (INR (length l) + 1)).
  split; [ exact Hlo | ]. split; [ exact Hhi | ].
  split; [ apply Rdiv_lt_0_compat; lra | ].
  split.
  - unfold Rdiv. apply Rmult_le_compat_l;
      [ lra | apply Rinv_le_contravar; lra ].
  - intros rho Hz Hm w Hw.
    apply Hb; [ apply Hcomp; [ lra | exact Hz ] | exact Hw ].
Qed.

Print Assumptions xi_good_radius.
