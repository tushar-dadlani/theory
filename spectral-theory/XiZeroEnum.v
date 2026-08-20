(* ================================================================= *)
(*  XiZeroEnum.v  —  what it means to ENUMERATE the zeros of xi.       *)
(*                                                                    *)
(*  The Hadamard product needs a single sequence rho : nat -> C listing *)
(*  every zero of XiC with its multiplicity.  xi_zero_count gives only  *)
(*  a finite complete list PER RADIUS, and those lists are unrelated    *)
(*  existential objects.                                               *)
(*                                                                    *)
(*  Turning them into a function is exactly `choice`: `exists` lives in *)
(*  Prop, a function is data, and Coq forbids that elimination.  So     *)
(*  this file follows the pattern that already worked twice here --     *)
(*  BorelCaratheodory stated as a Prop and proved separately, DivBy     *)
(*  taking its list as an INPUT -- and makes the enumeration a          *)
(*  HYPOTHESIS.  The product theorem can then be proved over an         *)
(*  arbitrary enumeration, choice-free; existence is a separate         *)
(*  question, deliberately deferred.                                    *)
(*                                                                    *)
(*    ZeroEnum rho  :  rho enumerates the zeros of xi with multiplicity *)
(*    enum_sum_bound : sum_{n<N} 1/|rho n|^2 <= 4 agrow, UNIFORMLY in N *)
(*                                                                    *)
(*  SORTEDNESS IS DELIBERATELY ABSENT.  With sum 1/|rho n|^2 finite and *)
(*  |rho n| -> oo the product converges unconditionally, so the order   *)
(*  is irrelevant; clauses 2 and 4 already pin down completeness WITH   *)
(*  multiplicity.  Demanding a sorted enumeration would force a total   *)
(*  order on C and a tie-break between rho and conj rho, for no gain.   *)
(*  Axiom-clean -- in particular NO choice and NO description.          *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia List.
Require Import ComplexField Cmodulus Holomorphic CDeriv
        JensenMultiZero CZeroListFactor CDyadicSum
        JensenCountComplete RiemannXiEntire XiZeroCount XiZeroDensity XiHgrow.
Open Scope R_scope.

(* the first N terms of the enumeration *)
Definition takeN (rho : nat -> C) (N : nat) : list C := map rho (seq 0 N).

Definition ZeroEnum (rho : nat -> C) : Prop :=
  (* the origin is not a zero of xi, so it is never listed *)
  (forall n, rho n <> C0)
  (* the moduli escape every bounded region *)
  /\ (forall B, exists N, forall n, (N <= n)%nat -> B <= Cmod (rho n))
  (* every prefix divides xi, leaving a regular cofactor *)
  /\ (forall N, XiPeel (takeN rho N))
  (* and for each radius SOME prefix has already caught everything *)
  /\ (forall R, 0 < R -> exists N G,
        (forall z, XiC z = Cmul (prodfac (takeN rho N) z) (G z))
        /\ ptcont G /\ (forall R2, disk_holo G R2)
        /\ (forall z, Cmod z < R -> G z <> C0)).

(* ----------------------------------------------------------------- *)
(*  A.  every listed point really is a zero                            *)
(* ----------------------------------------------------------------- *)
Lemma enum_is_zero : forall rho, ZeroEnum rho ->
  forall x N, In x (takeN rho N) -> XiC x = C0.
Proof.
  intros rho [_ [_ [Hpre _]]] x N Hin.
  destruct (Hpre N) as [G [Hid _]].
  rewrite (Hid x). rewrite (prodfac_zero_in (takeN rho N) x Hin). ring.
Qed.

(* ----------------------------------------------------------------- *)
(*  B.  THE CONVERGENCE INPUT, in sequence form.                       *)
(*                                                                    *)
(*  Every prefix is a peel list, so the multiplicity-aware sum bound    *)
(*  applies to it -- and the bound 4 agrow does not depend on N.  That  *)
(*  uniformity is precisely what makes the infinite product converge.   *)
(* ----------------------------------------------------------------- *)
Theorem enum_sum_bound : forall rho, ZeroEnum rho ->
  (forall n, 1 <= Cmod (rho n)) ->
  forall N, sumlist invsq (takeN rho N) <= 4 * agrow.
Proof.
  intros rho Henum Hlow N.
  destruct Henum as [Hne [Hesc [Hpre Hcomp]]] eqn:E.
  apply xi_sum_inv_sq_mult_uncond.
  - exact (Hpre N).
  - intros x Hx. apply (enum_is_zero rho Henum x N Hx).
  - intros x Hx.
    apply in_map_iff in Hx. destruct Hx as [n [Hn _]]. rewrite <- Hn. apply Hlow.
Qed.

Print Assumptions enum_sum_bound.
