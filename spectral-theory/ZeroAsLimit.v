(* ================================================================= *)
(*  ZeroAsLimit.v  —  zeros, and the zeta zeros, as a limit-at-infinity.  *)
(*                                                                    *)
(*  The tactful bridge from the count-2 "collapse to 0" thread to the      *)
(*  zeros of zeta.  A ZERO of an analytic function is a value that is 0;    *)
(*  via the eta identity  eta(s) = lim_M (alternating partial sums)         *)
(*  (EtaZeta.eta_zeta_cont), that value IS the limit at infinity of a       *)
(*  sequence -- so a zero of eta is exactly that alternating sum            *)
(*  COLLAPSING TO 0 at infinity, the same collapse as (x+/-y)/2^n -> 0.     *)
(*  And  eta = (1 - 2^{1-s}) zeta  routes the collapse to zeta's own zeros. *)
(*                                                                    *)
(*    eta_zero_iff_collapse    : (1-2^{1-s}) zeta(s) = 0  <->  the           *)
(*        alternating sum collapses to 0 at infinity.                      *)
(*    eta_collapse_iff_zeta_zero : away from the first-prime factor zeros    *)
(*        (1-2^{1-s} <> 0), that collapse  <->  zeta(s) = 0.                *)
(*                                                                    *)
(*  HONESTY.  Proved for real s>1 (absolute convergence), where in fact     *)
(*  BOTH sides are false (zeta>0) -- the content is the *equivalence/       *)
(*  structure*, not an exhibited zero.  The NONTRIVIAL zeros live in the    *)
(*  continued strip 0<Re s<1 (at Re=1/2), where the alternating series      *)
(*  still converges but eta_zeta_cont (real s>1) does NOT yet reach;        *)
(*  extending it there is what would let this collapse argument *see* them, *)
(*  and RH is the statement that every such collapse happens exactly at     *)
(*  Re s = 1/2.  Here that horizon is only NAMED (nontrivial_zero via       *)
(*  XiC z = C0, whose zeta-equivalence is the already-proven                *)
(*  GammaCNe0.XiC_zero_iff_zetaC_zero_final) -- never asserted.             *)
(*                                                                    *)
(*  Axioms: standard classical-Reals only.                            *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import EtaZeta CountTwoCollapse Ell2Zeta Ell2ZetaCont
        ComplexField RiemannXiEntire.
Open Scope R_scope.

(* A "zero reached at infinity": a sequence whose limit at infinity is 0 --
   the same collapse as (x +/- y)/2^n -> 0 from the count-2 thread. *)
Definition collapses (u : nat -> R) : Prop := Un_cv u 0.

(* the count-2 collapses ARE zeros-at-infinity *)
Lemma count_collapse_is_zero : forall x y, collapses (fun n => (x + y) / 2 ^ n).
Proof. intros x y. apply sum_over_pow2_cv0. Qed.

(* the alternating partial sums of the (-2)^inf-oscillating series *)
Definition eta_partial (s : R) (M : nat) : R :=
  sum_f_R0 (fun i => (-1) ^ i * z s (S i)) (2 * M + 1).

(* ===== the tactful limit-at-infinity argument for a zero ===== *)
(* a zero of eta  IS  the alternating sum collapsing to 0 at infinity *)
Theorem eta_zero_iff_collapse : forall s (Hs0 : 0 < s) (Hs1 : s <> 1), 1 < s ->
  ((1 - Rpower 2 (1 - s)) * zeta_cont s Hs0 Hs1 = 0 <-> collapses (eta_partial s)).
Proof.
  intros s Hs0 Hs1 Hgt. unfold collapses, eta_partial. split.
  - intro Hz. pose proof (eta_zeta_cont s Hs0 Hs1 Hgt) as H. rewrite Hz in H. exact H.
  - intro Hc. pose proof (eta_zeta_cont s Hs0 Hs1 Hgt) as H.
    exact (UL_sequence _ _ _ H Hc).
Qed.

(* away from the FIRST-PRIME factor zeros (1 - 2^{1-s} <> 0), that collapse is
   exactly a ZERO OF ZETA -- the alternating sum collapses to 0 at infinity
   iff zeta(s) = 0. *)
Corollary eta_collapse_iff_zeta_zero : forall s (Hs0 : 0 < s) (Hs1 : s <> 1),
  1 < s -> 1 - Rpower 2 (1 - s) <> 0 ->
  (collapses (eta_partial s) <-> zeta_cont s Hs0 Hs1 = 0).
Proof.
  intros s Hs0 Hs1 Hgt Hfac.
  rewrite <- (eta_zero_iff_collapse s Hs0 Hs1 Hgt).
  split.
  - intro Hz. apply Rmult_integral in Hz. destruct Hz as [Hz | Hz];
      [ exfalso; apply Hfac; exact Hz | exact Hz ].
  - intro Hz. rewrite Hz. ring.
Qed.

(* ===== the honest horizon: the nontrivial zeros (named, not asserted) ===== *)
(* The DEEP zeros -- the ones the whole edifice points at -- are the zeros of
   the completed xi (equivalently zeta on 0<Re<1, via GammaCNe0.
   XiC_zero_iff_zetaC_zero_final).  They live in the continued strip where the
   alternating series still converges but eta_zeta_cont (real s>1) does not yet
   reach.  Extending the collapse argument there would let it SEE these zeros;
   RH is the (open) statement that every such collapse sits exactly on Re = 1/2.
   We only NAME this horizon as a typed object -- no location is claimed. *)
Definition nontrivial_zero (z : C) : Prop := XiC z = C0.

Print Assumptions eta_zero_iff_collapse.
Print Assumptions eta_collapse_iff_zeta_zero.
