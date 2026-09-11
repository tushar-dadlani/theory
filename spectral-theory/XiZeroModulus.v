(* ================================================================= *)
(*  XiZeroModulus.v  --  the zeros of xi are bounded away from 0.      *)
(*                                                                    *)
(*    xi_zero_modulus_lower :                                         *)
(*      exists r0, 0 < r0 /\ forall z, XiC z = C0 -> r0 <= Cmod z     *)
(*                                                                    *)
(*  This is the mathematical content of the `Hlow` hypothesis that the *)
(*  whole Hadamard chain carries                                       *)
(*    (XiHadamardOrderOne, XiSubQuadLog, XiLogDerivZeros, ... :        *)
(*     Hypothesis Hlow : forall n, 1 <= Cmod (rho n))                  *)
(*  and that no file in the repo discharges.                           *)
(*                                                                    *)
(*  NO NUMERICS ARE NEEDED, and that is the point.  One might expect a *)
(*  lower bound on |rho| to require knowing where the lowest zero      *)
(*  actually sits (it is at height 14.134...), but it does not.  Two   *)
(*  facts already in the repo suffice:                                 *)
(*                                                                    *)
(*    XiZeroCount.Cmod_XiC_C0 : Cmod (XiC C0) = / 2   -- xi(0) <> 0    *)
(*    XiZeroCount.xi_zero_count : for each radius there is a FINITE    *)
(*        list l containing every zero of modulus < Rj, each of which  *)
(*        has 0 < Cmod                                                 *)
(*                                                                    *)
(*  A finite set of points, none of them 0, has a positive minimum     *)
(*  modulus; every other zero is outside radius Rj.  Take the smaller. *)
(*  Called at Rc = 8, so Rj lies in [1, 2).                            *)
(*                                                                    *)
(*  WHAT THIS DOES AND DOES NOT SETTLE.  It settles that `Hlow` is a   *)
(*  NORMALISATION question, not a mathematical one: some positive      *)
(*  lower bound always exists.  It does NOT produce the constant 1.    *)
(*  Getting r0 = 1 means showing l is empty -- that xi has no zero of  *)
(*  modulus < 1 -- and since ZetaOpenStrip pins zeros to 0 < Re z < 1, *)
(*  that is exactly "no zero with |Im z| < 1", which ZetaZeroFree does *)
(*  not reach (it needs 2 <= |Im z|).  That step does need the low-box *)
(*  numerics.  The alternative is to relax Hlow from 1 to r0 through   *)
(*  the chain; see the note at the foot of this file for the cost.     *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia List.
Require Import ComplexField Cmodulus Holomorphic CDeriv
        RiemannXiEntire XiZeroCount XiZeroEnum.
Import ListNotations.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  Part A -- minimum modulus over a finite list, with a default.      *)
(* ----------------------------------------------------------------- *)

Fixpoint minmod (l : list C) (d : R) : R :=
  match l with
  | nil => d
  | c :: t => Rmin (Cmod c) (minmod t d)
  end.

Lemma Rmin_pos_both : forall x y, 0 < x -> 0 < y -> 0 < Rmin x y.
Proof. intros x y Hx Hy. unfold Rmin; destruct (Rle_dec x y); lra. Qed.

Lemma minmod_pos : forall l d,
  0 < d -> (forall c, In c l -> 0 < Cmod c) -> 0 < minmod l d.
Proof.
  induction l as [| a l IH]; intros d Hd H; [ exact Hd | ].
  cbn [minmod]. apply Rmin_pos_both.
  - apply H. left; reflexivity.
  - apply IH; [ exact Hd | intros c Hc; apply H; right; exact Hc ].
Qed.

Lemma minmod_le_in : forall l d c, In c l -> minmod l d <= Cmod c.
Proof.
  induction l as [| a l IH]; intros d c Hin; [ contradiction | ].
  cbn [minmod]. destruct Hin as [-> | Hin].
  - apply Rmin_l.
  - apply Rle_trans with (minmod l d); [ apply Rmin_r | apply IH; exact Hin ].
Qed.

Lemma minmod_le_default : forall l d, minmod l d <= d.
Proof.
  induction l as [| a l IH]; intro d; [ apply Rle_refl | ].
  cbn [minmod]. apply Rle_trans with (minmod l d); [ apply Rmin_r | apply IH ].
Qed.

(* ----------------------------------------------------------------- *)
(*  Part B -- the lower bound.                                         *)
(* ----------------------------------------------------------------- *)

Theorem xi_zero_modulus_lower :
  exists r0 : R, 0 < r0 /\ forall z, XiC z = C0 -> r0 <= Cmod z.
Proof.
  destruct (xi_zero_count 8 ltac:(lra))
    as [l [Rj [HRj0 [_ [_ [Hin [_ [Hcomp [_ _]]]]]]]]].
  exists (minmod l Rj). split.
  - apply minmod_pos; [ exact HRj0 | ].
    intros c Hc. exact (proj1 (Hin c Hc)).
  - intros z Hz. destruct (Rlt_le_dec (Cmod z) Rj) as [Hlt | Hge].
    + apply (minmod_le_in l Rj z). apply Hcomp; assumption.
    + apply Rle_trans with Rj; [ apply minmod_le_default | exact Hge ].
Qed.

Print Assumptions xi_zero_modulus_lower.

(* ----------------------------------------------------------------- *)
(*  Part C -- in the form the Hadamard chain wants: the same bound     *)
(*  for every term of an arbitrary enumeration.  This is exactly       *)
(*  `Hlow` with the literal 1 replaced by r0.                          *)
(* ----------------------------------------------------------------- *)

Lemma enum_term_is_zero : forall rho, ZeroEnum rho ->
  forall n, XiC (rho n) = C0.
Proof.
  intros rho Henum n.
  apply (enum_is_zero rho Henum (rho n) (S n)).
  unfold takeN. apply in_map. apply in_seq. lia.
Qed.

Theorem enum_modulus_lower : forall rho, ZeroEnum rho ->
  exists r0 : R, 0 < r0 /\ forall n, r0 <= Cmod (rho n).
Proof.
  intros rho Henum.
  destruct xi_zero_modulus_lower as [r0 [Hr0 Hall]].
  exists r0. split; [ exact Hr0 | ].
  intro n. apply Hall. apply enum_term_is_zero; exact Henum.
Qed.

Print Assumptions enum_modulus_lower.

(* ================================================================= *)
(*  THE REMAINING COST, measured rather than guessed.                 *)
(*                                                                    *)
(*  To turn enum_modulus_lower into the `Hlow` the chain actually      *)
(*  takes, the literal 1 has to become r0 in 18 files and 188          *)
(*  occurrences (XiHadamardGlue, XiHadamardUnif, XiHgrow,              *)
(*  XiHadamardOrderOne, XiHadamardLocal, XiHadamardProd, XiHcofCoh,    *)
(*  XiHcof, XiHDiskBound, XiLogDerivZeros, XiProdLower, XiProdLimit,   *)
(*  XiTailProd, XiSubQuadLog, XiTMSelect, XiTMHolo, XiZeroEnum,        *)
(*  XiZeroDensity).                                                    *)
(*                                                                    *)
(*  Most of those are inert -- Hlow is threaded as a section argument  *)
(*  and only used as `pose proof (Hlow n); lra` to get 0 < Cmod rho.   *)
(*  The constant is load-bearing in exactly one place,                 *)
(*  XiHadamardUnif.dev_unif (:113-121), which reads                    *)
(*                                                                    *)
(*    eapply Rle_trans; [ apply Efac_dev_le; apply Hlow | ]            *)
(*                                                                    *)
(*  Efac_dev_le bounds |(1 - z/rho) e^{z/rho} - 1| by KR (Cmod z) /    *)
(*  |rho|^2, and 1 <= |rho| is what keeps |z/rho| <= |z| so that the   *)
(*  exponential factor stays dominated by e^{|z|}.  With r0 instead    *)
(*  the same proof gives KR (Cmod z / r0), and KR is increasing, so    *)
(*  the uniform-on-disks argument downstream is unaffected in shape --  *)
(*  every later constant just picks up a 1/r0.                         *)
(*                                                                    *)
(*  So the refactor is mechanical but wide, and it rewrites proven      *)
(*  quantitative code.  It is not attempted here.                      *)
(* ================================================================= *)
