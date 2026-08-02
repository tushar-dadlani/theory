(* ================================================================= *)
(*  RiemannXiEntire.v  —  the completed Riemann ξ is entire and         *)
(*  satisfies ξ(z) = ξ(1−z).                                            *)
(*                                                                    *)
(*  Using the pole-free form  XiC z = ½ + ½·z·(z−1)·(TC z + TC(1−z)),   *)
(*  which equals ½·z·(z−1)·J(z) (the z(z−1) factor cancels the poles    *)
(*  of −/z + /(z−1)).  It is manifestly entire (TC is entire, the rest  *)
(*  is polynomial) and its s↔1−s symmetry is pure field algebra.       *)
(*  XiC is written in the affine-combinator shape so that XiC_entire is *)
(*  a direct chain of the Holomorphic.v derivative rules.  Axiom-clean. *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra.
Require Import ComplexField Cmodulus Holomorphic MellinTail ThetaTailEntire.
Open Scope R_scope.

(* XiC z = ½ + (0·z+½)·(1·z+0)·(1·z−1)·(TC z + TC(−1·z+1))
        = ½ + ½·z·(z−1)·(TC z + TC(1−z)). *)
Definition XiC (z : C) : C :=
  Cadd (RtoC (/ 2))
    (Cmul (Cadd (Cmul C0 z) (RtoC (/ 2)))
      (Cmul (Cadd (Cmul C1 z) C0)
        (Cmul (Cadd (Cmul C1 z) (Copp C1))
          (Cadd (TC z) (TC (Cadd (Cmul (Copp C1) z) C1)))))).

(* --- XiC is entire --- *)
Theorem XiC_entire : HolomorphicOn XiC (fun _ => True).
Proof.
  intros z _; unfold XiC; eexists.
  apply Cderiv_add; [ apply Cderiv_const | ].
  apply Cderiv_mul_affine.
  apply Cderiv_mul_affine.
  apply Cderiv_mul_affine.
  apply Cderiv_add; [ apply TC_entire | ].
  apply Cderiv_comp_affine.
  apply TC_entire.
Qed.

(* --- the functional equation ξ(z) = ξ(1−z) --- *)
Theorem XiC_symmetric : forall z, XiC z = XiC (Cminus C1 z).
Proof.
  intro z; unfold XiC.
  replace (Cadd (Cmul (Copp C1) z) C1) with (Cminus C1 z) by ring.
  replace (Cadd (Cmul (Copp C1) (Cminus C1 z)) C1) with z by ring.
  ring.
Qed.

(* --- XiC restricts to the real pole-free completed xi --- *)
Theorem XiC_agree : forall s,
  XiC (RtoC s) = RtoC (/ 2 + / 2 * (s * ((s - 1) * (T s + T (1 - s))))).
Proof.
  intro s; unfold XiC.
  rewrite TC_agree.
  replace (Cadd (Cmul (Copp C1) (RtoC s)) C1) with (RtoC (1 - s))
    by (apply Ceq; simpl; lra).
  rewrite TC_agree.
  apply Ceq; simpl; field.
Qed.

Print Assumptions XiC_entire.
Print Assumptions XiC_symmetric.
Print Assumptions XiC_agree.

(* ================================================================= *)
(*  END RiemannXiEntire.v.                                             *)
(* ================================================================= *)
